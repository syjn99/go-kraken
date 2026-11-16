#!/usr/bin/env python3
"""Link check: the converted assembly that Lean reads is the code of the pinned ELF.

Usage: link_check.py <build directory>
       link_check.py --selftest <build directory>

The build directory is targets/<name>/build, after tools/build_target.sh.
It holds target-amd64 (the ELF), target.objdump, target-amd64.nm, build-ids.txt, norm/*.S and data/*.data.
A target without data items has no data files.
The check writes <build directory>/RESULT. The exit status is 1 on a failure.

These are the checks:
- Pins: the ELF, target.objdump and target-amd64.nm have the sha256 values of build-ids.txt.
- Code: for each function, the ELF symbol table gives the address and the size.
  The objdump instructions cover the range [addr, addr+size) without gaps.
  The objdump bytes are the ELF file bytes.
  LLVM (llvm-objdump, a second decoder) finds the same instruction boundaries.
  Each label L_<fn>_<off> of the .S file is before the instruction at fn+off.
  Each local label that an instruction names has a definition in the .S file.
- Global references: each global label in a .S file (a call target or sym+off(%rip)) names a symbol of the ELF.
  For a reference relative to rip, addr + len + disp of the original instruction is sym + off.
- Labels: in the host program all.S, each label has one definition.
  Thus no label of a function occurs before that function (LabelsFresh).
  all.S does not define an external label. External labels are the other code and data of the host.
- Host program: all.S has the same directives as the function files, in the same order.
  The comparison includes the instructions, not only the labels.
- Data: the `at <label> <off>` line of each data file data/<id>.data names one ELF symbol.
  The `bytes` of the file are the ELF file bytes at that place.
  Each `word <s> <o>` is the 8-byte little-endian value address(s) + o at its position.
  Each byte of the file is printable ASCII or a newline, which is the rule of the data include command.
  Without data files, the check reports that the data set is empty.
- Reassembly: clang --target=x86_64-linux-gnu assembles the .S instructions again at the original addresses.
  The result must be the ELF bytes. For clang only, a direct `jmpq L` becomes `jmp L`.
  A difference is "encoding" if LLVM decodes both byte strings to the same text.
  A difference is "padding" if the converter changed the original nop form to `nop`.
  At a padding position, the .S instruction must be `nop` and its new byte must be 0x90.
  LLVM must also decode the original bytes as a nop. Each other difference is a failure.

The check does not read the Lean sources.
A reader reads the theorem statements to see which definitions a theorem uses.
The proofs bind an item that the proved code addresses with `lea` to its identifier.
A contract hypothesis binds an item that only a contract uses. This check binds neither.
The last line is the bundle hash: the sha256 over RESULT up to the line "PASS all".
That part covers the ELF, the .S files and the data files.
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
    need(b[:6] == b"\x7fELF\x02\x01", "the file is not a 64-bit little-endian ELF file")
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
    raise Fail(f"the ELF file has no bytes at {addr:#x}")


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
    arm64 = struct.unpack_from("<H", pathlib.Path(elf).read_bytes(), 18)[0] == 183
    out = {}
    for line in text.splitlines():
        # The form is `addr: bytes<TAB>text`. A 10-byte instruction fills the byte column.
        # Thus a tab follows its last byte, not a space (movabs in the Go 1.26.10 ELF).
        m = re.match(r"\s*([0-9a-f]+):\s((?:[0-9a-f]{2} ?)+?) *\t(.*)$", line)
        if m:
            out[int(m[1], 16)] = (conv.instruction_bytes(m[2].replace(" ", ""), "arm64" if arm64 else "amd64"), re.sub(r"\s+", " ", m[3]).split(" <")[0].strip())
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
            need(line.endswith(":"), f"{path}: the line {line!r} is not a label or an instruction")
            out.append(("label", line[:-1]))
    return out


def architecture(outdir):
    ids = (pathlib.Path(outdir) / "build-ids.txt").read_text()
    m = re.search(r"^env: .*\bGOARCH=(amd64|arm64)\b", ids, re.M)
    need(m is not None, "build-ids.txt has no supported GOARCH")
    return m[1]


def pins(outdir):
    arch = architecture(outdir)
    return {"elf sha256": f"target-{arch}", "objdump sha256": "target.objdump", "nm sha256": f"target-{arch}.nm"}


def check_pins(outdir):
    """The ELF, the disassembly and the symbol listing must have the sha256 values of build-ids.txt."""
    ids = {}
    for line in (outdir / "build-ids.txt").read_text().splitlines():
        k, _, v = line.partition(": ")
        ids[k] = v
    for k, f in pins(outdir).items():
        need(ids.get(k) == sha(outdir / f), f"{f}: sha256 {sha(outdir / f)} is not the pin {k} {ids.get(k)}")


def run(outdir, log):
    outdir = pathlib.Path(outdir)
    arch = architecture(outdir)
    elf = outdir / f"target-{arch}"
    check_pins(outdir)
    log("PASS pins: the ELF, the disassembly and the symbol listing have the sha256 values of build-ids.txt")
    b, secs, esyms = read_elf(elf)
    need(struct.unpack_from("<H", b, 18)[0] == (183 if arch == "arm64" else 62), "the ELF machine differs from GOARCH")
    conv.CLEANED.clear()
    fns = conv.read_objdump(outdir / "target.objdump", arch)
    nm = conv.read_nm(outdir / f"target-{arch}.nm")
    # Go nm adds group symbols of size 0 (`type:*`, `go:string.*`) that the ELF symbol table does not have.
    # The check takes them from nm, with the section of their address.
    nmonly = set()
    for a, sz, name in nm:
        if name not in esyms:
            esyms[name] = (a, sz, section_of(secs, a))
            nmonly.add(name)
    # Each clean name maps to its original names over the whole binary. A referenced name must have one original.
    # This rule is stricter than the rule of convert_objdump.py, which sees only the names that the code uses.
    rev = {}
    for name in esyms:
        rev.setdefault(conv.short(name), set()).add(name)

    def orig(g):
        need(len(rev.get(g, ())) == 1, f"the name {g} does not have exactly one original: {sorted(rev.get(g, ()))}")
        return next(iter(rev[g]))
    raw = {}
    for line in (outdir / "target.objdump").read_text().splitlines():
        m = re.match(r"\s+\S+\s+0x([0-9a-f]+)\s+([0-9a-f]+)\s+", line)
        if m:
            raw[int(m[1], 16)] = conv.instruction_bytes(m[2], arch)
    clean2orig = {}
    hostlabels = []  # the labels of all.S, in order
    externals = {}   # clean name: (address, section, kind)
    per_fn = []
    for f in fns:
        name = conv.clean(f["name"])
        clean2orig[name] = f["name"]
        ins = f["ins"]
        lo, hi = ins[0][0], ins[-1][0] + ins[-1][1]
        # Code: the extent of the symbol
        need(f["name"] in esyms, f"{f['name']}: the ELF symbol table does not have this symbol")
        sa, ss, ssec = esyms[f["name"]]
        need((sa, ss) == (lo, hi - lo), f"{name}: the symbol table gives {sa:#x}+{ss}, objdump gives {lo:#x}+{hi - lo}")
        need(ssec == ".text", f"{name}: the section is {ssec}, not .text")
        dec = llvm_decode(elf, lo, hi)
        need(set(dec) == {a for a, _, _ in ins}, f"{name}: LLVM finds other instruction boundaries")
        for a, n, _ in ins:
            need(raw[a] == elf_bytes(b, secs, a, n) == dec[a][0], f"{name}: the objdump, ELF and LLVM bytes are not equal at {a:#x}")
        # Code: the labels of the .S file against the instruction addresses
        S = parse_S(outdir / "norm" / f"{name}.S")
        need(S[0] == ("label", name), f"{name}: the first directive is not the function label")
        k = 0
        for d in S[1:]:
            if d[0] == "label":
                m = re.fullmatch(re.escape(f"L_{name}_") + r"([0-9a-f]+)", d[1])
                need(m, f"{name}: the local label {d[1]} does not have the form L_<fn>_<offset>")
                need(k < len(ins) and ins[k][0] == lo + int(m[1], 16),
                     f"{name}: the label {d[1]} is not before the instruction at its address")
            else:
                k += 1
        need(k == len(ins), f"{name}: the .S file has {k} instructions, objdump has {len(ins)}")
        defined = {d[1] for d in S if d[0] == "label"}
        for d in S:
            for ref in re.findall(re.escape(f"L_{name}_") + r"[0-9a-f]+", d[1]) if d[0] == "ins" else ():
                need(ref in defined, f"{name}: the instruction {d[1]!r} names the label {ref}, which the .S file does not define")
        hostlabels += [d[1] for d in S if d[0] == "label"]
        # Global references
        sins = [d[1] for d in S if d[0] == "ins"]
        for (a, n, att), st in zip(ins, sins):
            br = conv.branch(att, a, arch)
            if br and not (lo <= br[1] < hi):
                t = br[1]
                g = st.split()[-1]
                o = orig(g)
                need(esyms[o][0] == t, f"{name}: the call or jump target {g} is not at {t:#x}")
                externals.setdefault(g, (t, esyms[o][2], "code"))
            r = conv.RIP.search(att)
            if r:
                t = a + n + int(r[1], 0)
                m = re.search(r"([A-Za-z0-9_.]+)(?:\+(\d+))?\(%rip\)", st)
                need(m, f"{name}: the converter did not change the rip operand: {st}")
                g, off = m[1], int(m[2] or 0)
                o = orig(g)
                sa, ss, ssec = esyms[o]
                need(sa + off == t, f"{name}: {g}+{off} is {sa + off:#x}, but the instruction refers to {t:#x}")
                kind = "in-symbol" if off < max(ss, 1) else "group(nearest preceding symbol)"
                if o in nmonly:
                    kind += ", nm-only symbol"
                externals.setdefault(g if not off else f"{g}+{off}", (t, ssec, kind))
        per_fn.append((name, lo, hi, ins, sins, {d[1] for d in S if d[0] == "label"}))
        log(f"PASS code {name}: {len(ins)} instructions, {hi - lo} bytes. The symbol table, objdump, LLVM, the ELF bytes and the labels agree")
    # Global references: the report
    for g, (t, sec, kind) in sorted(externals.items(), key=lambda x: x[1][0]):
        log(f"PASS global reference {g} = {t:#x} {sec} {kind}")
    # Labels: one definition for each label of the host program all.S
    allS = parse_S(outdir / "norm" / "all.S")
    labs = [d[1] for d in allS if d[0] == "label"]
    need(labs == hostlabels, "the labels of all.S are not the labels of the function files in order")
    dup = {l for l in labs if labs.count(l) > 1}
    need(not dup, f"all.S defines these labels more than one time: {sorted(dup)}")
    fnames = {x[0] for x in per_fn}
    clash = ({g.split("+")[0] for g in externals} & set(labs)) - fnames
    need(not clash, f"all.S defines these external labels: {sorted(clash)}")
    internal = sorted({g for g in externals} & fnames)
    for g in internal:
        need(externals[g][0] == next(lo for n, lo, *_ in per_fn if n == g), f"a call to {g} is not at its entry")
    log(f"PASS labels all.S: {len(labs)} labels, each with one definition. {len(externals) - len(internal)} external "
        f"references, which all.S does not define. {len(internal)} calls to target functions at their entry: {internal}")
    # Host program: the directives of all.S are the directives of the function files
    want = []
    for name, *_ in per_fn:
        want += parse_S(outdir / "norm" / f"{name}.S")
    need(allS == want, "the directives of all.S are not the directives of the function files" +
         next((f" (the first difference is at directive {i}: {x} and {y})" for i, (x, y) in enumerate(zip(allS, want)) if x != y),
              f" (the lengths are {len(allS)} and {len(want)})"))
    log(f"PASS host program all.S: its {len(allS)} directives are the directives of the {len(per_fn)} function files in order")
    # Data: the data files are the ELF bytes
    datas = sorted((outdir / "data").glob("*.data"))
    if not datas:
        log("PASS data: the data set is empty. The directory data/ has no data files")
    for p in datas:
        at, pos, n_b, n_w = None, 0, 0, 0
        raw = p.read_bytes()
        need(all(c == 10 or 0x20 <= c <= 0x7e for c in raw),
             f"data file {p.name}: a byte is not printable ASCII or a newline (the rule of the data include command)")
        for line in raw.decode("ascii").split("\n"):
            w = line.split()
            if not w or w[0].startswith("#"):
                continue
            need(all(re.fullmatch(r"[0-9a-f]{2}", x) for x in w[1:]) if w[0] == "bytes" else
                 len(w) != 3 or w[0] not in ("at", "word") or re.fullmatch(r"[0-9]+", w[2]),
                 f"data file {p.name}: a token is not in the grammar of the data include command: {line!r}")
            if w[0] == "at" and len(w) == 3 and at is None and pos == 0:
                at = esyms[orig(w[1])][0] + int(w[2])
            elif w[0] == "bytes" and at is not None:
                bs = bytes(int(x, 16) for x in w[1:])
                need(all(len(x) == 2 for x in w[1:]) and elf_bytes(b, secs, at + pos, len(bs)) == bs,
                     f"data file {p.name}: the bytes at {at + pos:#x} are not the ELF bytes")
                pos += len(bs); n_b += len(bs)
            elif w[0] == "word" and len(w) == 3 and at is not None:
                v, = struct.unpack("<Q", elf_bytes(b, secs, at + pos, 8))
                need(v == esyms[orig(w[1])][0] + int(w[2]),
                     f"data file {p.name}: the word at {at + pos:#x} is {v:#x}, not {w[1]}+{w[2]}")
                pos += 8; n_w += 1
            else:
                need(False, f"data file {p.name}: the directive {line!r} is not valid")
        need(at is not None, f"data file {p.name}: the file has no `at` directive")
        log(f"PASS data {p.name}: {at:#x}, {n_b} bytes and {n_w} words are the ELF bytes")
    # Reassembly
    diffs = reassemble(per_fn, {g.split("+")[0]: orig(g.split("+")[0]) for g in externals}, esyms, b, secs, outdir)
    for name, a, kind, orig, new, txt in diffs:
        log(f"DIFF reassembly {name} {a:#x} {kind}: elf {orig.hex()} asm {new.hex()} {txt}")
    need(all(k != "FAIL" for _, _, k, _, _, _ in diffs), "the reassembly gives other bytes (see the DIFF lines with FAIL)")
    n_ins = sum(len(x[3]) for x in per_fn)
    log(f"PASS reassembly: clang {'aarch64' if arch == 'arm64' else 'x86_64'}-linux-gnu assembled {n_ins} instructions again: "
        f"{n_ins - len(diffs)} with the same bytes, {sum(d[2] == 'encoding' for d in diffs)} with another encoding, "
        f"{sum(d[2] == 'padding' for d in diffs)} padding")
    return per_fn


def reassemble(per_fn, externals, esyms, b, secs, outdir):
    """One section. Each function and each external symbol is at its ELF address, with .org."""
    anchors = []
    for name, lo, hi, ins, sins, labels in per_fn:
        anchors.append((lo, name, ins, sins, labels))
    fnames = {x[0] for x in per_fn}
    for g in externals:
        if g not in fnames:
            anchors.append((esyms[externals[g]][0], g, None, None, None))
    anchors.sort(key=lambda x: (x[0], x[2] is not None))
    base = anchors[0][0]
    arch = architecture(outdir)
    triple = "aarch64-linux-gnu" if arch == "arm64" else "x86_64-linux-gnu"
    lines = [".text"] if arch == "arm64" else [".text", ".att_syntax", ".code64"]
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
            # A spelling change only: the LLVM assembler accepts `jmp L`, not `jmpq L`, for a direct jump.
            lines.append("  " + re.sub(r"^jmpq (?=[A-Za-z_])", "jmp ", st))
    with tempfile.TemporaryDirectory() as d:
        src = pathlib.Path(d) / "re.S"
        obj = pathlib.Path(d) / "re.o"
        src.write_text("\n".join(lines) + "\n")
        r = subprocess.run([tool("clang"), f"--target={triple}", "-c", "-x", "assembler", str(src),
                            "-o", str(obj)], capture_output=True, text=True)
        need(r.returncode == 0, "clang: " + r.stderr[:2000])
        ob, osecs, _ = read_elf(obj)
        rel = [s for s in osecs if s["name"] == ".rela.text"]
        need(not rel or rel[0]["size"] == 0, "the reassembly has relocations in .text")
        text = next(s for s in osecs if s["name"] == ".text")
        body = ob[text["off"]:text["off"] + text["size"]]
    diffs = []
    for name, lo, hi, ins, sins, _ in per_fn:
        for (a, n, att), st in zip(ins, sins):
            orig = elf_bytes(b, secs, a, n)
            new = body[a - base:a - base + n]
            if orig == new:
                continue
            if arch == "arm64":
                diffs.append((name, a, "FAIL", orig, new, att))
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
    """The LLVM text of the first instruction of bs, decoded as x86-64 at addr."""
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
    log(f"elf sha256 {sha(outdir / pins(outdir)['elf sha256'])}")
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
    for k, f in pins(t).items():
        s = re.sub(rf"^{k}: .*$", f"{k}: {sha(t / f)}", s, flags=re.M)
    p.write_text(s)


def selftest(outdir):
    """Sensitivity: each changed copy of the inputs must fail. An unchanged copy must pass.
    Each case finds its place in the link set.
    Some cases need an input that the link set can lack: a data file, a `sym+off(%rip)` operand or a padding nop.
    If the input is not there, the self-test reports the case as skipped."""
    outdir = pathlib.Path(outdir)
    fn_files = sorted(p for p in (outdir / "norm").glob("*.S") if p.name != "all.S")
    datas = sorted((outdir / "data").glob("*.data"))
    if not fn_files:
        print(f"selftest: {outdir / 'norm'} has no function .S file")
        return 1
    arch = architecture(outdir)
    imm = re.compile(r"[#]0x([0-9a-f]+)" if arch == "arm64" else r"\$0x([0-9a-f]+)")

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
        # Remove one instruction from a .S file.
        t = copy(); p = t / "norm" / f0
        ls = p.read_text().splitlines()
        del ls[next(j for j in range(min(5, len(ls) - 1), len(ls)) if ls[j].startswith("  "))]
        p.write_text("\n".join(ls) + "\n")
        cases.append(("remove an instruction", t, False))
        # Change an immediate operand.
        f = first(lambda q: imm.search(q.read_text()), fn_files)
        if f:
            t = copy(); p = t / "norm" / f.name
            p.write_text(bump(p.read_text()))
            cases.append(("change an immediate", t, False))
        else:
            cases.append(("change an immediate", None, "a function file has no immediate operand"))
        # Change the same immediate in both assembly files, so reassembly must detect the change.
        if f:
            t = copy()
            for p in (t / "norm" / f.name, t / "norm" / "all.S"):
                p.write_text(bump(p.read_text()))
            cases.append(("matching assembly immediate changed", t, False))
        # Move a label one instruction later.
        lab = lambda q: next((j for j, l in enumerate(q.read_text().splitlines()) if l.startswith("L_") and j > 2), None)
        f = first(lambda q: lab(q) is not None, fn_files)
        if f:
            t = copy(); p = t / "norm" / f.name
            ls = p.read_text().splitlines(); i = lab(p)
            ls[i], ls[i + 1] = ls[i + 1], ls[i]; p.write_text("\n".join(ls) + "\n")
            cases.append(("move a label", t, False))
        else:
            cases.append(("move a label", None, "a function file has no local label"))
        # Remove the // part of an objdump line. The converter must fail.
        t = copy(); p = t / "target.objdump"
        s = p.read_text(); assert "// " in s; p.write_text(re.sub(r"// [^\n]*", "", s, count=1))
        repin(t)
        cases.append(("objdump line without //", t, False))
        # Give a global reference the wrong offset.
        f = first(lambda q: "(%rip)" in q.read_text(), fn_files)
        if f:
            t = copy(); p = t / "norm" / f.name
            s = p.read_text()
            m = re.search(r"([A-Za-z0-9_.]+)(\+\d+)?\(%rip\)", s)
            p.write_text(s[:m.start()] + (f"{m[1]}(%rip)" if m[2] else f"{m[1]}+8(%rip)") + s[m.end():])
            cases.append(("wrong global offset", t, False))
        else:
            cases.append(("wrong global offset", None, "the link set has no sym+off(%rip) operand"))
        # Change a padding nop to retq in the function file and in all.S.
        f = first(lambda q: "  nop" in q.read_text().split("\n"), fn_files)
        if f:
            t = copy(); p = t / "norm" / f.name
            ls = p.read_text().split("\n"); j = ls.index("  nop"); ls[j] = "  retq"; p.write_text("\n".join(ls))
            p = t / "norm" / "all.S"
            ls = p.read_text().split("\n"); i = ls.index(f"{f.stem}:") + j
            assert ls[i] == "  nop"; ls[i] = "  retq"; p.write_text("\n".join(ls))
            cases.append(("padding nop changed to retq", t, False))
        else:
            cases.append(("padding nop changed to retq", None, "a function file has no padding nop"))
        # Change an instruction of all.S, but not of the function file. The labels do not change.
        t = copy(); p = t / "norm" / "all.S"
        if imm.search(p.read_text()):
            p.write_text(bump(p.read_text()))
            cases.append(("all.S instruction changed", t, False))
        else:
            cases.append(("all.S instruction changed", None, "all.S has no immediate operand"))
        # Change a byte of a data file.
        f = first(lambda q: re.search(r"^bytes [0-9a-f]{2}", q.read_text(), re.M), datas)
        if f:
            t = copy(); p = t / "data" / f.name
            s = p.read_text(); m = re.search(r"^bytes ([0-9a-f]{2})", s, re.M)
            p.write_text(s[:m.start(1)] + f"{int(m[1], 16) ^ 1:02x}" + s[m.end(1):])
            cases.append(("data file byte changed", t, False))
        else:
            cases.append(("data file byte changed", None, "the data set is empty, so it has no bytes line"))
        # Add 8 to the ELF word at the first `word` line of a data file.
        f = first(lambda q: re.search(r"^word ", q.read_text(), re.M), datas)
        if f:
            t = copy(); p = t / f"target-{arch}"
            e = bytearray(p.read_bytes()); _, es, sy = read_elf(p)
            addrs = {conv.short(n): v[0] for n, v in sy.items()}
            for a, _, n in conv.read_nm(t / f"target-{arch}.nm"):
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
            cases.append(("ELF word of a data file changed", None, "the data set is empty, so it has no word line"))
        # Put a carriage return into a data file. The data include command splits lines only at \n.
        if datas:
            t = copy(); p = t / "data" / datas[0].name
            p.write_bytes(p.read_bytes().replace(b"\n", b"\r", 1))
            cases.append(("data file with a carriage return", t, False))
        else:
            cases.append(("data file with a carriage return", None, "the data set is empty"))
        # Remove a jump target label from the function file and from all.S.
        f = first(lambda q: lab(q) is not None, fn_files)
        if f:
            t = copy()
            name = f.read_text().splitlines()[lab(f)]
            for p in (t / "norm" / f.name, t / "norm" / "all.S"):
                ls = p.read_text().split("\n"); ls.remove(name); p.write_text("\n".join(ls))
            cases.append(("jump target label removed", t, False))
        else:
            cases.append(("jump target label removed", None, "a function file has no local label"))
        # Make the ELF pin of build-ids.txt wrong.
        t = copy(); p = t / "build-ids.txt"
        p.write_text(re.sub(r"^elf sha256: .*$", "elf sha256: " + "0" * 64, p.read_text(), flags=re.M))
        cases.append(("wrong ELF pin", t, False))
        # An unchanged copy passes.
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
