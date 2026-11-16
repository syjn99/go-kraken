#!/usr/bin/env python3
"""Convert the output of `go tool objdump -gnu` into labeled AMD64 or ARM64 assembly for Kraken.

Usage: convert_objdump.py <objdump> <nm> <output directory> [--norm] [--arch=amd64|arm64]

<objdump> is the output of `go tool objdump -gnu -s <regexp> <elf>`.
<nm> is the output of `go tool nm -size -sort address <elf>`.
The converter writes one `<fn>.S` file for each function, and `all.S` with all functions in address order.

ARM64 instruction words use little-endian ELF bytes. Relative branch offsets use the instruction address.
The converter replaces ARM64 branch offsets with labels.
The AMD64 converter changes these items:
- An absolute jump or call target becomes a label. Inside the function, the label is `L_<fn>_<hexoff>`.
  Outside the function, the label is the symbol name.
- `disp(%rip)` becomes `sym+off(%rip)`, for the symbol that holds the target.
- In a symbol name, `(*T)` becomes `T`. Each character outside `[A-Za-z0-9_.]` becomes `_`.
  Thus the name is one identifier token of Kraken.
With --norm, the converter also makes these changes:
- Each padding form of the table NORM becomes `nop`. The Kraken parser does not know these forms.
  This is not a change of the semantics: a Kraken layout is abstract and does not use the byte length of a nop.
  The link check compares the original bytes.
- The converter removes the zero index `,%riz,1)` of a SIB operand (RIZ). The address does not change.
- A negative 32-bit displacement gets its signed form (DISP32).

The converter fails with exit status 1 on these inputs:
- an instruction line without the GNU form (`// ...`),
- an address gap between two instructions,
- a branch into the middle of an instruction,
- two symbol names that have the same clean name.
"""
import re
import sys

CLEANED = {}


def short(name):
    """The clean form of a symbol name. link_check.py uses it for each symbol of the ELF."""
    out = re.sub(r"\(\*(\w+)\)", r"\1", name)  # (*T) -> T
    return re.sub(r"[^A-Za-z0-9_.]", "_", out)


def clean(name):
    """The clean form of a symbol name. Fail if two names have the same clean form."""
    out = short(name)
    if CLEANED.setdefault(out, name) != name:
        raise SystemExit(f"two names have the same clean name: {name!r} and {CLEANED[out]!r} both become {out!r}")
    return out


def read_nm(path):
    syms = []
    for line in open(path):
        p = line.split()
        if len(p) >= 4:
            syms.append((int(p[0], 16), int(p[1]), p[3]))
    # Sort the symbols. Then the order of two symbols at one address (for example `runtime.types` and `type:*`)
    # does not depend on the order of the go nm output.
    return sorted(syms)


def sym_at(syms, addr):
    """The symbol whose range [start, start+size) holds addr, as (name, offset)."""
    best, near, exact = None, None, None
    for start, size, name in syms:
        if start == addr:
            exact = (name, 0)  # the last symbol at this address in the sorted order, for each nm order
        if start <= addr < start + max(size, 1):
            best = (name, addr - start)
        if start <= addr:
            near = (name, addr - start)
    # Go nm lists the type descriptors as one group of size 0 (`type:*`).
    # Thus the name of an address inside the group is the nearest symbol before it, with an offset.
    if exact:
        return exact
    if best is None and near is None:
        raise SystemExit(f"no symbol holds the address {addr:#x}")
    return best or near


def instruction_bytes(hexword, arch):
    raw = bytes.fromhex(hexword)
    if arch == "arm64":
        if len(raw) != 4:
            raise SystemExit("an ARM64 instruction must have four bytes")
        return raw[::-1]
    return raw


def read_objdump(path, arch="amd64"):
    fns, cur = [], None
    for line in open(path):
        if line.startswith("TEXT "):
            cur = {"name": line.split()[1].removesuffix("(SB)"), "ins": []}
            fns.append(cur)
            continue
        if not line.strip():
            continue
        m = re.match(r"\s+\S+\s+0x([0-9a-f]+)\s+([0-9a-f]+)\s+.*?// (.*)$", line)
        if not m or cur is None:
            raise SystemExit(f"the objdump line does not have the GNU form with a // part: {line.rstrip()!r}")
        att = re.sub(r"\s+", " ", m.group(3)).strip()
        a, n = int(m.group(1), 16), len(instruction_bytes(m.group(2), arch))
        if cur["ins"] and cur["ins"][-1][0] + cur["ins"][-1][1] != a:
            raise SystemExit(f"{cur['name']} has an address gap before {a:#x}")
        cur["ins"].append((a, n, att))
    return fns


BRANCH = re.compile(r"^(j[a-z]+|callq?|jmpq?) 0x([0-9a-f]+)$")
RIP = re.compile(r"(-?0x[0-9a-f]+|-?\d+)\(%rip\)")
NORM = {"nopl (%rax)": "nop", "data16 nop": "nop", "nopw 0x0(%rax,%rax,1)": "nop",
        "nopw (%rax,%rax,1)": "nop", "nopl 0x0(%rax)": "nop", "nopl 0x0(%rax,%rax,1)": "nop", "nopl (%rax,%rax,1)": "nop",
        "nopw %cs:0x0(%rax,%rax,1)": "nop", "data16 nopw %cs:0x0(%rax,%rax,1)": "nop", "xchg %ax,%ax": "nop"}
# `%riz` (Go 1.26.10): GNU objdump prints a SIB byte without an index register with the index `%riz`.
# An example is `0x10(%r12,%riz,1)`, because the base r12 needs a SIB byte. The index is zero.
# Thus the address is `0x10(%r12)`. The Kraken parser has no `riz` register.
# The address and the bytes do not change. The reassembly of the link check compares the bytes.
RIZ = re.compile(r",%riz,1\)")
# `go tool objdump -gnu` prints a negative 32-bit memory displacement as an unsigned hexadecimal number of 8 digits.
# An example is `lea 0xffffff1c(%rdi),%rdx` for -228. x86-64 extends disp32 with its sign.
# The Kraken parser reads the token as +4294967068, and clang rejects it.
# With --norm, the converter writes such a displacement in its signed form `-0xe4(%rdi)`.
# Such a displacement has exactly 8 hexadecimal digits, has the top bit set, and is directly before `(%`.
# It is not an immediate `$0x...` and not relative to `%rip`.
# The address and the bytes do not change. The reassembly of the link check compares the line with the ELF.
DISP32 = re.compile(r"(?<![\w$\-])0x([89a-f][0-9a-f]{7})(?=\(%(?!rip))")


def signed_disp32(att):
    return DISP32.sub(lambda m: f"-0x{(1 << 32) - int(m.group(1), 16):x}", att)


ARM_BRANCH = re.compile(r"^(b(?:\.[a-z]+)?|bl|cbn?z [wx][0-9]+,|tbn?z [wx][0-9]+, #[0-9]+,) \.\+0x([0-9a-f]+)$")


def branch(att, addr, arch):
    m = (ARM_BRANCH if arch == "arm64" else BRANCH).match(att)
    if m is None:
        return None
    target = int(m[2], 16)
    if arch == "arm64":
        if target >= 2 ** 63:
            target -= 2 ** 64
        target += addr
    return m[1], target


def convert(fn, syms, norm, arch="amd64"):
    name = clean(fn["name"])
    lo = fn["ins"][0][0]
    hi = fn["ins"][-1][0] + fn["ins"][-1][1]
    lab = lambda a: f"L_{name}_{a - lo:x}"
    starts = {a for a, _, _ in fn["ins"]}
    targets, body = set(), []
    for addr, ln, att in fn["ins"]:
        m = branch(att, addr, arch)
        if m:
            t = m[1]
            if lo <= t < hi:
                if t not in starts:
                    raise SystemExit(f"{name} has a branch into the middle of an instruction: {t:#x}")
                targets.add(t)
                att = f"{m[0]} {lab(t)}"
            else:
                s, off = sym_at(syms, t)
                if off:
                    raise SystemExit(f"a branch goes into the middle of {s}")
                att = f"{m[0]} {clean(s)}"
        else:
            r = RIP.search(att)
            if r:
                t = addr + ln + int(r.group(1), 0)
                s, off = sym_at(syms, t)
                ref = clean(s) + (f"+{off}" if off else "")
                att = att[: r.start()] + f"{ref}(%rip)" + att[r.end():]
        if norm:
            att = NORM.get(att, att)
            att = RIZ.sub(")", att)
            att = signed_disp32(att)
        body.append((addr, att))
    out = [f"{name}:"]
    for addr, att in body:
        if addr in targets:
            out.append(f"{lab(addr)}:")
        out.append(f"  {att}")
    return name, "\n".join(out) + "\n"


def main():
    objdump, nm, outdir = sys.argv[1:4]
    norm = "--norm" in sys.argv
    arch = next((a.split("=", 1)[1] for a in sys.argv[4:] if a.startswith("--arch=")), "amd64")
    if arch not in ("amd64", "arm64"):
        raise SystemExit(f"unsupported architecture: {arch}")
    syms = read_nm(nm)
    allS = []
    for fn in read_objdump(objdump, arch):
        name, text = convert(fn, syms, norm, arch)
        open(f"{outdir}/{name}.S", "w").write(text)
        allS.append(text)
    open(f"{outdir}/all.S", "w").write("".join(allS))


def selftest():
    syms = [(0x100, 0x20, "pkg.f"), (0x200, 16, "pkg.Err")]
    fn = {"name": "pkg.f", "ins": [(0x100, 2, "jae 0x104"), (0x102, 2, "mov 0xfc(%rip),%rax"),
                                   (0x104, 1, "retq")]}
    _, text = convert(fn, syms, False)
    assert "jae L_pkg.f_4" in text and "L_pkg.f_4:\n  retq" in text, text
    assert "mov pkg.Err(%rip),%rax" in text, text
    for bad in ({"name": "pkg.g", "ins": [(0x100, 2, "jmp 0x101"), (0x102, 1, "retq")]},):
        try:
            convert(bad, syms, False)
            raise AssertionError("the converter accepted a branch into the middle of an instruction")
        except SystemExit:
            pass
    riz = {"name": "pkg.r", "ins": [(0x100, 6, "mov 0x10(%r12,%riz,1),%r12"), (0x106, 1, "retq")]}
    assert "  mov 0x10(%r12),%r12\n" in convert(riz, syms, True)[1]
    assert "%riz" in convert(riz, syms, False)[1]
    d32 = {"name": "pkg.d", "ins": [(0x100, 7, "lea 0xffffff1c(%rdi),%rdx"), (0x107, 7, "mov $0xffffff1c,%rax"),
                                    (0x10e, 6, "mov 0x7fffffff(%rax),%rcx"), (0x114, 8, "mov %rbx,0x80000000(%rsi,%rcx,8)"),
                                    (0x11c, 1, "retq")]}
    t = convert(d32, syms, True)[1]
    assert "  lea -0xe4(%rdi),%rdx\n" in t, t
    assert "  mov $0xffffff1c,%rax\n" in t, t
    assert "  mov 0x7fffffff(%rax),%rcx\n" in t, t
    assert "  mov %rbx,-0x80000000(%rsi,%rcx,8)\n" in t, t
    assert "  lea 0xffffff1c(%rdi),%rdx\n" in convert(d32, syms, False)[1]
    clean("pkg.h[uint8]")
    try:
        clean("pkg.h_uint8_")
        raise AssertionError("the converter accepted two names with the same clean name")
    except SystemExit:
        pass
    assert instruction_bytes("f90007e0", "arm64") == bytes.fromhex("e00700f9")
    arm = {"name": "pkg.arm", "ins": [(0x100, 4, "b .+0x8"),
                                       (0x104, 4, "b.cs .+0xfffffffffffffffc"), (0x108, 4, "ret")]}
    text = convert(arm, syms, False, "arm64")[1]
    assert "b L_pkg.arm_8" in text and "b.cs L_pkg.arm_0" in text, text
    assert branch("cbz x0, .+0x8", 0x100, "arm64") == ("cbz x0,", 0x108)
    assert branch("tbz w0, #7, .+0x8", 0x100, "arm64") == ("tbz w0, #7,", 0x108)
    CLEANED.clear()


if __name__ == "__main__":
    selftest()
    main()
