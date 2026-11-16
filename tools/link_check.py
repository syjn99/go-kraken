#!/usr/bin/env python3
# Source: methodical-ssz commit 320929dd, fv/kraken/link/check.py (SSZ-specific parts removed).
"""Link-level check: the converted assembly that Lean reads is the code in the ELF.

Usage: link_check.py <outdir>      (outdir = targets/<name>/build, after build_target.sh)
       link_check.py --selftest <outdir>

Inputs in <outdir>: target-amd64 (ELF), target.objdump, target-amd64.nm, norm/*.S,
data/*.data (no data files: the data set is empty, and (f) says so).
Writes <outdir>/RESULT. Exit status 1 on any failure.

Checks:
 (a) every function: ELF .symtab address and size; objdump instructions cover
     exactly [addr, addr+size) without gaps; objdump bytes = ELF file bytes;
     LLVM (llvm-objdump, an independent decoder) has the same instruction
     boundaries; every label `L_<fn>_<off>` in the .S sits before the
     instruction at fn+off.
 (b) every global label in the .S (call target, `sym+off(%rip)`): the symbol
     exists in the ELF .symtab, its section, and that `addr + len + disp` of the
     original instruction is `sym + off`.
 (c) LabelsFresh in the host program all.S: every label is defined once, so no
     label of a function occurs before it; external labels are not defined in
     all.S (they are the host's other code and data).
 (d) the .S instructions, assembled again by clang --target=x86_64-linux-gnu at
     the original addresses, give the ELF bytes (spelling map for clang only:
     direct `jmpq L` -> `jmp L`). A difference is "encoding" if
     LLVM decodes both byte strings to the same text, "padding" if it is a
     normalized nop, else FAIL. At a padding position the .S instruction must
     be `nop`, its new byte must be 0x90, and LLVM must decode the original
     bytes as a nop (a `retq` there used to pass).
 (e) all.S has the same directives as the per-function .S files, in order
     (instructions included, not only labels).
 (f) every data file data/<id>.data that Lean includes (`data_include`):
     its `at <label> <off>` names one ELF symbol; the file's
     `bytes` are the ELF file bytes there, and each `word <s> <o>` is the
     8-byte little-endian value address(s) + o at its position; every byte
     of the file is printable ASCII or a newline (the rule of data_include).
     With no data file, (f) reports that the data set is empty.
     This checker does not read Lean sources: which definitions a theorem uses is
     read from the theorem statements, not checked here. Items that the
     proven code addresses with `lea` are bound to their id by the proofs;
     the items that only a contract uses are bound by the contract
     hypothesis. This check binds neither.
The bundle hash (sha256 over RESULT up to and including the last PASS line,
which covers the ELF, the .S files and the data files) is the last line.
"""
import hashlib
import importlib.util
import pathlib
import re
import shutil
import struct
import subprocess
import sys
import tempfile

HERE = pathlib.Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("conv", HERE / "convert_objdump.py")
conv = importlib.util.module_from_spec(spec)
spec.loader.exec_module(conv)


class Fail(Exception):
    pass


def need(cond, msg):
    if not cond:
        raise Fail(msg)


def sha(p):
    return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()


# ---------------------------------------------------------------- ELF reading
def read_elf(path):
    b = pathlib.Path(path).read_bytes()
    need(b[:6] == b"\x7fELF\x02\x01", "not an ELF64 LSB file")
    shoff, = struct.unpack_from("<Q", b, 0x28)
    shentsize, shnum, shstrndx = struct.unpack_from("<HHH", b, 0x3A)
    secs = []
    for i in range(shnum):
        nm, typ, flags, addr, off, size, link, info, align, entsize = struct.unpack_from(
            "<IIQQQQIIQQ", b, shoff + i * shentsize)
        secs.append(dict(nm=nm, typ=typ, addr=addr, off=off, size=size, link=link, entsize=entsize))
    strtab = secs[shstrndx]
    for s in secs:
        o = strtab["off"] + s["nm"]
        s["name"] = b[o:b.index(b"\0", o)].decode()
    syms = {}
    for s in secs:
        if s["typ"] != 2:  # SHT_SYMTAB
            continue
        st = secs[s["link"]]
        for j in range(s["size"] // 24):
            nm, info, other, shndx, value, size = struct.unpack_from("<IBBHQQ", b, s["off"] + j * 24)
            o = st["off"] + nm
            name = b[o:b.index(b"\0", o)].decode()
            sec = secs[shndx]["name"] if 0 < shndx < len(secs) else str(shndx)
            if name:
                syms.setdefault(name, (value, size, sec))
    return b, secs, syms


def elf_bytes(b, secs, addr, n):
    for s in secs:
        if s["typ"] == 1 and s["addr"] <= addr and addr + n <= s["addr"] + s["size"]:  # PROGBITS
            o = s["off"] + addr - s["addr"]
            return b[o:o + n]
    raise Fail(f"no file bytes at {addr:#x}")


def section_of(secs, addr):
    for s in secs:
        if s["addr"] and s["addr"] <= addr < s["addr"] + s["size"]:
            return s["name"]
    return "?"


# ------------------------------------------------------------ LLVM decoding
def tool(name):
    p = shutil.which(name)
    if p:
        return p
    return subprocess.check_output(["xcrun", "--find", name], text=True).strip()


def llvm_decode(elf, lo, hi):
    text = subprocess.check_output(
        [tool("llvm-objdump"), "-d", f"--start-address={lo}", f"--stop-address={hi}", str(elf)], text=True)
    out = {}
    for line in text.splitlines():
        # `addr: bytes<TAB>text`; a 10-byte instruction fills the byte column, so its last byte is
        # followed by the tab, not by a space (movabs in the Go 1.26.10 ELF)
        m = re.match(r"\s*([0-9a-f]+):\s((?:[0-9a-f]{2} ?)+?) *\t(.*)$", line)
        if m:
            out[int(m[1], 16)] = (bytes.fromhex(m[2].replace(" ", "")), re.sub(r"\s+", " ", m[3]).split(" <")[0].strip())
    return out


# ---------------------------------------------------------------- the check
def parse_S(path):
    """Directives of a converted .S: ('label', name) or ('ins', text)."""
    out = []
    for line in pathlib.Path(path).read_text().splitlines():
        if not line.strip():
            continue
        if line.startswith("  "):
            out.append(("ins", line.strip()))
        else:
            need(line.endswith(":"), f"{path}: bad line {line!r}")
            out.append(("label", line[:-1]))
    return out


PINS = {"elf sha256": "target-amd64", "objdump sha256": "target.objdump", "nm sha256": "target-amd64.nm"}


def check_pins(outdir):
    """The ELF, the disassembly and the symbol listing must have the sha256 values of build-ids.txt."""
    ids = {}
    for line in (outdir / "build-ids.txt").read_text().splitlines():
        k, _, v = line.partition(": ")
        ids[k] = v
    for k, f in PINS.items():
        need(ids.get(k) == sha(outdir / f), f"{f}: sha256 {sha(outdir / f)} is not the pin {k} {ids.get(k)}")


def run(outdir, log):
    outdir = pathlib.Path(outdir)
    elf = outdir / "target-amd64"
    check_pins(outdir)
    log("PASS pins: the ELF, the disassembly and the symbol listing have the sha256 values of build-ids.txt")
    b, secs, esyms = read_elf(elf)
    conv.CLEANED.clear()
    fns = conv.read_objdump(outdir / "target.objdump")
    nm = conv.read_nm(outdir / "target-amd64.nm")
    # Go's nm adds size-0 group symbols (`type:*`, `go:string.*`) that are not in
    # the ELF .symtab; they are taken from nm with the section of their address.
    nmonly = set()
    for a, sz, name in nm:
        if name not in esyms:
            esyms[name] = (a, sz, section_of(secs, a))
            nmonly.add(name)
    # Sanitized name -> original names over the whole binary: a referenced name
    # must have exactly one original (stricter than convert_objdump.py, which sees only used names).
    rev = {}
    for name in esyms:
        rev.setdefault(conv.short(name), set()).add(name)

    def orig(g):
        need(len(rev.get(g, ())) == 1, f"name {g} has originals {sorted(rev.get(g, ()))}")
        return next(iter(rev[g]))
    raw = {}
    for line in (outdir / "target.objdump").read_text().splitlines():
        m = re.match(r"\s+\S+\s+0x([0-9a-f]+)\s+([0-9a-f]+)\s+", line)
        if m:
            raw[int(m[1], 16)] = bytes.fromhex(m[2])
    clean2orig = {}
    hostlabels = []  # all.S labels in order
    externals = {}   # clean name -> (addr, section, kind)
    per_fn = []
    for f in fns:
        name = conv.clean(f["name"])
        clean2orig[name] = f["name"]
        ins = f["ins"]
        lo, hi = ins[0][0], ins[-1][0] + ins[-1][1]
        # (a) symbol extent
        need(f["name"] in esyms, f"{f['name']}: not in ELF .symtab")
        sa, ss, ssec = esyms[f["name"]]
        need((sa, ss) == (lo, hi - lo), f"{name}: symtab {sa:#x}+{ss} vs objdump {lo:#x}+{hi - lo}")
        need(ssec == ".text", f"{name}: section {ssec}")
        dec = llvm_decode(elf, lo, hi)
        need(set(dec) == {a for a, _, _ in ins}, f"{name}: LLVM instruction boundaries differ")
        for a, n, _ in ins:
            need(raw[a] == elf_bytes(b, secs, a, n) == dec[a][0], f"{name}: bytes differ at {a:#x}")
        # (a) labels of the .S against instruction addresses
        S = parse_S(outdir / "norm" / f"{name}.S")
        need(S[0] == ("label", name), f"{name}: first directive is not the function label")
        k = 0
        for d in S[1:]:
            if d[0] == "label":
                m = re.fullmatch(re.escape(f"L_{name}_") + r"([0-9a-f]+)", d[1])
                need(m, f"{name}: unexpected local label {d[1]}")
                need(k < len(ins) and ins[k][0] == lo + int(m[1], 16),
                     f"{name}: label {d[1]} not before the instruction at its address")
            else:
                k += 1
        need(k == len(ins), f"{name}: .S has {k} instructions, objdump {len(ins)}")
        defined = {d[1] for d in S if d[0] == "label"}
        for d in S:
            for ref in re.findall(re.escape(f"L_{name}_") + r"[0-9a-f]+", d[1]) if d[0] == "ins" else ():
                need(ref in defined, f"{name}: the instruction {d[1]!r} names the label {ref}, which the .S does not define")
        hostlabels += [d[1] for d in S if d[0] == "label"]
        # (b) global references
        sins = [d[1] for d in S if d[0] == "ins"]
        for (a, n, att), st in zip(ins, sins):
            br = conv.BRANCH.match(att)
            if br and not (lo <= int(br[2], 16) < hi):
                t = int(br[2], 16)
                g = st.split()[-1]
                o = orig(g)
                need(esyms[o][0] == t, f"{name}: call/jump target {g} != {t:#x}")
                externals.setdefault(g, (t, esyms[o][2], "code"))
            r = conv.RIP.search(att)
            if r:
                t = a + n + int(r[1], 0)
                m = re.search(r"([A-Za-z0-9_.]+)(?:\+(\d+))?\(%rip\)", st)
                need(m, f"{name}: rip operand not converted: {st}")
                g, off = m[1], int(m[2] or 0)
                o = orig(g)
                sa, ss, ssec = esyms[o]
                need(sa + off == t, f"{name}: {g}+{off} = {sa + off:#x}, instruction refers to {t:#x}")
                kind = "in-symbol" if off < max(ss, 1) else "group(nearest preceding symbol)"
                if o in nmonly:
                    kind += ", nm-only symbol"
                externals.setdefault(g if not off else f"{g}+{off}", (t, ssec, kind))
        per_fn.append((name, lo, hi, ins, sins, {d[1] for d in S if d[0] == "label"}))
        log(f"PASS (a) {name}: {len(ins)} instructions, {hi - lo} bytes, symtab/objdump/LLVM/ELF bytes and labels agree")
    # (b) report
    for g, (t, sec, kind) in sorted(externals.items(), key=lambda x: x[1][0]):
        log(f"PASS (b) {g} = {t:#x} {sec} {kind}")
    # (c) label uniqueness in the host program all.S
    allS = parse_S(outdir / "norm" / "all.S")
    labs = [d[1] for d in allS if d[0] == "label"]
    need(labs == hostlabels, "all.S labels are not the concatenation of the functions' labels")
    dup = {l for l in labs if labs.count(l) > 1}
    need(not dup, f"duplicate labels in all.S: {sorted(dup)}")
    fnames = {x[0] for x in per_fn}
    clash = ({g.split("+")[0] for g in externals} & set(labs)) - fnames
    need(not clash, f"external labels defined in all.S: {sorted(clash)}")
    internal = sorted({g for g in externals} & fnames)
    for g in internal:
        need(externals[g][0] == next(lo for n, lo, *_ in per_fn if n == g), f"call to {g} not at its entry")
    log(f"PASS (c) all.S: {len(labs)} labels, each defined once; {len(externals) - len(internal)} external "
        f"references not defined in all.S; {len(internal)} calls to target functions at their entry: {internal}")
    # (e) all.S directives = per-function directives
    want = []
    for name, *_ in per_fn:
        want += parse_S(outdir / "norm" / f"{name}.S")
    need(allS == want, "all.S directives differ from the per-function .S files" +
         next((f" (first at directive {i}: {x} vs {y})" for i, (x, y) in enumerate(zip(allS, want)) if x != y),
              f" (lengths {len(allS)} vs {len(want)})"))
    log(f"PASS (e) all.S: {len(allS)} directives equal the {len(per_fn)} function files in order")
    # (f) data files = ELF bytes
    datas = sorted((outdir / "data").glob("*.data"))
    if not datas:
        log("PASS (f) the data set is empty: no data files in data/")
    for p in datas:
        at, pos, n_b, n_w = None, 0, 0, 0
        raw = p.read_bytes()
        need(all(c == 10 or 0x20 <= c <= 0x7e for c in raw),
             f"(f) {p.name}: a byte that is not printable ASCII or a newline (same rule as data_include)")
        for line in raw.decode("ascii").split("\n"):
            w = line.split()
            if not w or w[0].startswith("#"):
                continue
            need(all(re.fullmatch(r"[0-9a-f]{2}", x) for x in w[1:]) if w[0] == "bytes" else
                 len(w) != 3 or w[0] not in ("at", "word") or re.fullmatch(r"[0-9]+", w[2]),
                 f"(f) {p.name}: token not in the data_include grammar: {line!r}")
            if w[0] == "at" and len(w) == 3 and at is None and pos == 0:
                at = esyms[orig(w[1])][0] + int(w[2])
            elif w[0] == "bytes" and at is not None:
                bs = bytes(int(x, 16) for x in w[1:])
                need(all(len(x) == 2 for x in w[1:]) and elf_bytes(b, secs, at + pos, len(bs)) == bs,
                     f"(f) {p.name}: bytes at {at + pos:#x} differ from the ELF")
                pos += len(bs); n_b += len(bs)
            elif w[0] == "word" and len(w) == 3 and at is not None:
                v, = struct.unpack("<Q", elf_bytes(b, secs, at + pos, 8))
                need(v == esyms[orig(w[1])][0] + int(w[2]),
                     f"(f) {p.name}: word at {at + pos:#x} is {v:#x}, not {w[1]}+{w[2]}")
                pos += 8; n_w += 1
            else:
                need(False, f"(f) {p.name}: bad directive {line!r}")
        need(at is not None, f"(f) {p.name}: no `at` directive")
        log(f"PASS (f) {p.name}: {at:#x}, {n_b} bytes and {n_w} words = ELF")
    # (d) reassembly
    diffs = reassemble(per_fn, {g.split("+")[0]: orig(g.split("+")[0]) for g in externals}, esyms, b, secs, outdir)
    for name, a, kind, orig, new, txt in diffs:
        log(f"DIFF (d) {name} {a:#x} {kind}: elf {orig.hex()} asm {new.hex()} {txt}")
    need(all(k != "FAIL" for _, _, k, _, _, _ in diffs), "reassembly mismatch (see DIFF FAIL lines)")
    n_ins = sum(len(x[3]) for x in per_fn)
    log(f"PASS (d) {n_ins} instructions reassembled by clang x86_64-linux-gnu: "
        f"{n_ins - len(diffs)} byte-identical, {sum(d[2] == 'encoding' for d in diffs)} encoding, "
        f"{sum(d[2] == 'padding' for d in diffs)} padding")
    return per_fn


def reassemble(per_fn, externals, esyms, b, secs, outdir):
    """One section, every function and external symbol at its ELF address via .org."""
    anchors = []
    for name, lo, hi, ins, sins, labels in per_fn:
        anchors.append((lo, name, ins, sins, labels))
    fnames = {x[0] for x in per_fn}
    for g in externals:
        if g not in fnames:
            anchors.append((esyms[externals[g]][0], g, None, None, None))
    anchors.sort(key=lambda x: (x[0], x[2] is not None))
    base = anchors[0][0]
    lines = [".text", ".att_syntax", ".code64"]
    for a, name, ins, sins, labels in anchors:
        lines.append(f".org {a - base:#x}")
        if ins is None:
            lines.append(f"{name}:")
            continue
        lines.append(f"{name}:")
        for (ia, n, att), st in zip(ins, sins):
            lines.append(f".org {ia - base:#x}")
            off = ia - a
            lab = f"L_{name}_{off:x}"
            # Only the labels of the .S text. A jump to a label that the text does not define
            # then stays a relocation, and the check fails.
            if lab in labels:
                lines.append(f"{lab}:")
            # spelling only: LLVM's assembler takes `jmp L`, not `jmpq L`, for a direct jump
            lines.append("  " + re.sub(r"^jmpq (?=[A-Za-z_])", "jmp ", st))
    with tempfile.TemporaryDirectory() as d:
        src = pathlib.Path(d) / "re.S"
        obj = pathlib.Path(d) / "re.o"
        src.write_text("\n".join(lines) + "\n")
        r = subprocess.run([tool("clang"), "--target=x86_64-linux-gnu", "-c", "-x", "assembler", str(src),
                            "-o", str(obj)], capture_output=True, text=True)
        need(r.returncode == 0, "clang: " + r.stderr[:2000])
        ob, osecs, _ = read_elf(obj)
        rel = [s for s in osecs if s["name"] == ".rela.text"]
        need(not rel or rel[0]["size"] == 0, "reassembly left relocations in .text")
        text = next(s for s in osecs if s["name"] == ".text")
        body = ob[text["off"]:text["off"] + text["size"]]
    diffs = []
    for name, lo, hi, ins, sins, _ in per_fn:
        for (a, n, att), st in zip(ins, sins):
            orig = elf_bytes(b, secs, a, n)
            new = body[a - base:a - base + n]
            if orig == new:
                continue
            if att in conv.NORM:
                t0 = decode_bytes(orig, a, outdir)
                okpad = (st == "nop" and new[:1] == b"\x90" and not any(new[1:])
                         and t0 is not None and t0[0] == n
                         and re.match(r"^(data16 )*(nop[lwq]?|xchg %ax, ?%ax)( |$)", t0[1]))
                diffs.append((name, a, "padding" if okpad else "FAIL", orig, new.rstrip(b"\0"),
                              f"{att} -> {st} | {t0}"))
                continue
            t1, t2 = decode_bytes(orig, a, outdir), decode_bytes(new, a, outdir)
            diffs.append((name, a, "encoding" if t1 == t2 and t1 else "FAIL", orig, new, f"{att} | {t1} | {t2}"))
    return diffs


def decode_bytes(bs, addr, outdir):
    """LLVM text of the first instruction of bs, decoded as x86-64 at addr."""
    with tempfile.TemporaryDirectory() as d:
        s = pathlib.Path(d) / "d.S"
        o = pathlib.Path(d) / "d.o"
        s.write_text(".text\n.byte " + ",".join(str(x) for x in bs) + "\n")
        subprocess.run([tool("clang"), "--target=x86_64-linux-gnu", "-c", "-x", "assembler", str(s), "-o", str(o)],
                       check=True, capture_output=True)
        text = subprocess.check_output([tool("llvm-objdump"), "-d", f"--adjust-vma={addr}", str(o)], text=True)
    for line in text.splitlines():
        m = re.match(r"\s*[0-9a-f]+:\s+((?:[0-9a-f]{2} )+)\s*(.*)$", line)
        if m:
            return (len(bytes.fromhex(m[1])), re.sub(r"\s+", " ", m[2]).split(" <")[0].strip())
    return None


def main(outdir):
    outdir = pathlib.Path(outdir)
    lines = []

    def log(s):
        print(s)
        lines.append(s)

    try:
        run(outdir, log)
    except (Fail, SystemExit) as e:
        log(f"FAIL {e}")
        (outdir / "RESULT").write_text("\n".join(lines) + "\n")
        return 1
    log(f"elf sha256 {sha(outdir / 'target-amd64')}")
    for p in sorted((outdir / "norm").glob("*.S")):
        log(f"S sha256 {sha(p)} {p.name}")
    for p in sorted((outdir / "data").glob("*.data")):
        log(f"data sha256 {sha(p)} {p.name}")
    log("PASS all")
    body = "\n".join(lines) + "\n"
    body += f"BUNDLE sha256 {hashlib.sha256(body.encode()).hexdigest()}\n"
    (outdir / "RESULT").write_text(body)
    print(body.splitlines()[-1])
    return 0


def repin(t):
    """Write the sha256 values of the changed files of a copy into its build-ids.txt, so that a later check fails."""
    p = t / "build-ids.txt"
    s = p.read_text()
    for k, f in PINS.items():
        s = re.sub(rf"^{k}: .*$", f"{k}: {sha(t / f)}", s, flags=re.M)
    p.write_text(s)


def selftest(outdir):
    """Sensitivity: mutated inputs must fail; an unchanged copy must pass.
    Each case finds its place in the link set. A case that needs a kind of input that the link set
    does not have (a data file, a `sym+off(%rip)` operand, a padding nop) is reported as skipped."""
    outdir = pathlib.Path(outdir)
    fn_files = sorted(p for p in (outdir / "norm").glob("*.S") if p.name != "all.S")
    datas = sorted((outdir / "data").glob("*.data"))
    if not fn_files:
        print(f"selftest: no function .S file in {outdir / 'norm'}")
        return 1
    imm = re.compile(r"\$0x([0-9a-f]+)")

    def bump(text):
        """The text with its first immediate operand increased by one."""
        m = imm.search(text)
        assert m, "no immediate operand"
        return text[:m.start(1)] + f"{int(m[1], 16) + 1:x}" + text[m.end(1):]

    def first(pred, items):
        return next((x for x in items if pred(x)), None)

    cases = []
    with tempfile.TemporaryDirectory() as d:
        def copy():
            t = pathlib.Path(tempfile.mkdtemp(dir=d))
            shutil.copytree(outdir, t, dirs_exist_ok=True)
            return t
        f0 = fn_files[0].name
        # 1. drop one instruction from a .S
        t = copy(); p = t / "norm" / f0
        ls = p.read_text().splitlines()
        del ls[next(j for j in range(min(5, len(ls) - 1), len(ls)) if ls[j].startswith("  "))]
        p.write_text("\n".join(ls) + "\n")
        cases.append(("drop an instruction", t, False))
        # 2. change an immediate
        f = first(lambda q: imm.search(q.read_text()), fn_files)
        if f:
            t = copy(); p = t / "norm" / f.name
            p.write_text(bump(p.read_text()))
            cases.append(("change an immediate", t, False))
        else:
            cases.append(("change an immediate", None, "no immediate operand in a function file"))
        # 3. move a label one instruction later
        lab = lambda q: next((j for j, l in enumerate(q.read_text().splitlines()) if l.startswith("L_") and j > 2), None)
        f = first(lambda q: lab(q) is not None, fn_files)
        if f:
            t = copy(); p = t / "norm" / f.name
            ls = p.read_text().splitlines(); i = lab(p)
            ls[i], ls[i + 1] = ls[i + 1], ls[i]; p.write_text("\n".join(ls) + "\n")
            cases.append(("move a label", t, False))
        else:
            cases.append(("move a label", None, "no local label in a function file"))
        # 4. objdump line without // (converter must fail)
        t = copy(); p = t / "target.objdump"
        s = p.read_text(); assert "// " in s; p.write_text(re.sub(r"// [^\n]*", "", s, count=1))
        repin(t)
        cases.append(("objdump line without //", t, False))
        # 5. global reference with the wrong offset
        f = first(lambda q: "(%rip)" in q.read_text(), fn_files)
        if f:
            t = copy(); p = t / "norm" / f.name
            s = p.read_text()
            m = re.search(r"([A-Za-z0-9_.]+)(\+\d+)?\(%rip\)", s)
            p.write_text(s[:m.start()] + (f"{m[1]}(%rip)" if m[2] else f"{m[1]}+8(%rip)") + s[m.end():])
            cases.append(("wrong global offset", t, False))
        else:
            cases.append(("wrong global offset", None, "no sym+off(%rip) operand in the link set"))
        # 6. a padding nop becomes retq in the function file and in all.S
        f = first(lambda q: "  nop" in q.read_text().split("\n"), fn_files)
        if f:
            t = copy(); p = t / "norm" / f.name
            ls = p.read_text().split("\n"); j = ls.index("  nop"); ls[j] = "  retq"; p.write_text("\n".join(ls))
            p = t / "norm" / "all.S"
            ls = p.read_text().split("\n"); i = ls.index(f"{f.stem}:") + j
            assert ls[i] == "  nop"; ls[i] = "  retq"; p.write_text("\n".join(ls))
            cases.append(("padding nop -> retq", t, False))
        else:
            cases.append(("padding nop -> retq", None, "no padding nop in a function file"))
        # 7. all.S instruction differs from the function file (labels unchanged)
        t = copy(); p = t / "norm" / "all.S"
        if imm.search(p.read_text()):
            p.write_text(bump(p.read_text()))
            cases.append(("all.S instruction changed", t, False))
        else:
            cases.append(("all.S instruction changed", None, "no immediate operand in all.S"))
        # 8. a data file byte
        f = first(lambda q: re.search(r"^bytes [0-9a-f]{2}", q.read_text(), re.M), datas)
        if f:
            t = copy(); p = t / "data" / f.name
            s = p.read_text(); m = re.search(r"^bytes ([0-9a-f]{2})", s, re.M)
            p.write_text(s[:m.start(1)] + f"{int(m[1], 16) ^ 1:02x}" + s[m.end(1):])
            cases.append(("data file byte changed", t, False))
        else:
            cases.append(("data file byte changed", None, "the data set has no bytes line (empty data set)"))
        # 9. the ELF word at the first `word` line of a data file points 8 bytes later
        f = first(lambda q: re.search(r"^word ", q.read_text(), re.M), datas)
        if f:
            t = copy(); p = t / "target-amd64"
            e = bytearray(p.read_bytes()); _, es, sy = read_elf(p)
            addrs = {conv.short(n): v[0] for n, v in sy.items()}
            for a, _, n in conv.read_nm(t / "target-amd64.nm"):
                addrs.setdefault(conv.short(n), a)
            at, pos = None, 0
            for w in (l.split() for l in f.read_text().split("\n")):
                if not w or w[0].startswith("#"):
                    continue
                if w[0] == "at":
                    at = addrs[w[1]] + int(w[2])
                elif w[0] == "bytes":
                    pos += len(w) - 1
                elif w[0] == "word":
                    break
            ia = at + pos
            o = next(s["off"] + ia - s["addr"] for s in es if s["typ"] == 1 and s["addr"] <= ia < s["addr"] + s["size"])
            struct.pack_into("<Q", e, o, struct.unpack_from("<Q", e, o)[0] + 8); p.write_bytes(bytes(e))
            repin(t)
            cases.append(("ELF word of a data file changed", t, False))
        else:
            cases.append(("ELF word of a data file changed", None, "the data set has no word line (empty data set)"))
        # 10. a carriage return inside a data file (data_include splits on \n only)
        if datas:
            t = copy(); p = t / "data" / datas[0].name
            p.write_bytes(p.read_bytes().replace(b"\n", b"\r", 1))
            cases.append(("data file with a carriage return", t, False))
        else:
            cases.append(("data file with a carriage return", None, "the data set is empty"))
        # 11. a jump target label is removed from the function file and from all.S
        f = first(lambda q: lab(q) is not None, fn_files)
        if f:
            t = copy()
            name = f.read_text().splitlines()[lab(f)]
            for p in (t / "norm" / f.name, t / "norm" / "all.S"):
                ls = p.read_text().split("\n"); ls.remove(name); p.write_text("\n".join(ls))
            cases.append(("jump target label removed", t, False))
        else:
            cases.append(("jump target label removed", None, "no local label in a function file"))
        # 12. the ELF pin of build-ids.txt is wrong
        t = copy(); p = t / "build-ids.txt"
        p.write_text(re.sub(r"^elf sha256: .*$", "elf sha256: " + "0" * 64, p.read_text(), flags=re.M))
        cases.append(("wrong ELF pin", t, False))
        # 13. unchanged copy passes
        t = copy()
        cases.append(("unchanged copy", t, True))
        ok = True
        for name, t, expect in cases:
            if t is None:
                print(f"selftest {name}: skipped ({expect})")
                continue
            why = ""
            try:
                conv.CLEANED.clear()
                run(t, lambda s: None)
                got = True
            except (Fail, SystemExit) as e:
                got, why = False, str(e).splitlines()[0][:120]
            print(f"selftest {name}: {'pass' if got else 'fail'} (expected {'pass' if expect else 'fail'}) {why}")
            ok &= got == expect
    return 0 if ok else 1


if __name__ == "__main__":
    if sys.argv[1] == "--selftest":
        sys.exit(selftest(sys.argv[2]))
    sys.exit(main(sys.argv[1]))
