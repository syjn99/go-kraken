#!/usr/bin/env python3
"""Negative cases: each mutant must fail inside its designated theorem. Each control must pass.

Usage. A run is a Lean job. The working directory does not matter.
  negative.py <cases.json> <work directory> <result.json> [<case id>...]
  negative.py --check-cases <cases.json>...        builds the mutant text of each case, without Lean
  negative.py --reclassify <result.json> [<work directory>]   calculates the classes of a result file again
  negative.py --selftest                           checks the classifier and the case range
  negative.py --selftest-timeout                   checks the cleanup after a timeout, with a fake child process

cases.json is a list of cases. Each case has these fields:
- "id", "module" (a path under lean/, for example "Uvarint/Amd64/DecodeLoop.lean"), "theorem".
- "kind": "code", "statement" or "control".
- For "code": "code_definition" (the Lean name of the included program, for example "uvarint"),
  "assembly" (the path of the .S file from the repository root), "old" and "new".
  "old" is one exact instruction line, unique in the file. With "line", "old" is at that line (1-based) of the file.
- For "statement": "old" and "new", an exact text that is unique inside the theorem statement.
- For "control": optional "code_definition" and "assembly". Then the mutant file includes an unchanged copy of the .S file.
- Optional for "code" and "control": "code_namespace", the namespace of the code constant.
  It is necessary when "code_definition" is not a full name.
  Without "code_namespace", the runner declares a full name in "code_definition" with `_root_`.
- Optional for each kind: "mutant_imports", a list of module names. The mutant file also imports them.
  The case module does not change. Thus a mutant can name a declaration of another module.
- Optional for each kind: "inline", a list of module paths under lean/, in import order.
  The mutant file holds a copy of each module, each in its own `section`, before the case module.
  The code rename then also changes these copies. List each module between the code module and the case module.
  Then no imported lemma names the original program.
- Optional for "statement": "statement_def", the full name of a `def` in an inlined module.
  "old" and "new" then apply inside that definition. The case range stays the theorem.

"theorem" is the full Lean name, or the name as written on the declaration line.
The full name selects the namespace block when one module holds the same written name two times.

The mutant file of a case is the text of the module up to the end of the designated theorem.
The next top-level `theorem`, `def`, `end`, `example` or `/--` after the theorem ends the text.
A `theorem <thm>_kind` directly after the theorem stays, and it is part of the case range.
The case range starts at the first line of the command of the theorem.
The `set_option ... in` lines and the doc comment directly above the `theorem` line are part of the command.
Lean reports an error of the whole declaration at that line, for example a heartbeat timeout.
For a code case, the runner adds a constant `<code namespace>.<code_definition>Mut`.
This constant includes the changed copy of the .S file, with its absolute path in the work directory.
After the imports, the runner renames each whole-word use of <code_definition> to that constant.

The runner runs `lake env lean <file>` from lean/, under the memory limit of tools/memory_limit.py.
A mutant passes when these conditions are true:
- Lean reports an error, and each error line is inside the case range.
- The first error is not a resource error, not a wrong_target form and not a mixed_programs form.
A later heartbeat or recursion error after a real first error goes into "later_resource_error". It does not change the class.
A control passes when Lean reports no error.

Each result has a "class":
- control_pass, control_fail: the result of a control.
- inside: a pass of a mutant. outside: an error line is outside the case range. no_error: Lean reports no error.
- killed: the memory limit stopped Lean. timeout_wall: the case time (CASE_TIMEOUT) ended.
- abnormal_exit: an exit status other than 0 and 1.
- timeout_heartbeat: the first error is the Lean "(deterministic) timeout".
- recursion_limit: the first error is "maximum recursion depth has been reached".
- mixed_programs: the first error names the original program and the mutant program.
- wrong_target: the first error is a parse error or a name resolution error of the list WRONG_TARGET.
  Such a mutant does not get to its target.
Only control_pass and inside are a pass.

After a case timeout, the runner kills the whole process tree.
This tree is memory_limit.py and lake and lean in their own session.
The runner makes sure that no process of the tree is alive before the next case.
Before the first case, `lake build --no-build <imports of the case modules>` must exit with 0.
`lake env lean` does not check that the build is current. If the check fails, no case runs and the exit status is 2.
The argument list and the exit status of that check go into "precheck" of <result.json>.
<result.json> holds only the cases of this run.
A <case id> that matches no case is a usage error: no case runs and the exit status is 2.
The runner writes <result.json>. For each case, it writes <work directory>/<id>/ with mut.lean, mut.S, diff and log.
The tool uses only the Python 3 standard library.
"""
import difflib
import json
import os
import pathlib
import re
import signal
import subprocess
import sys
import time

HERE = pathlib.Path(__file__).resolve().parent
KR = HERE.parent
LEAN = KR / "lean"
MEMORY_LIMIT = KR / "tools" / "memory_limit.py"
CAP = str(6 * 2 ** 30)
CASE_TIMEOUT = 300  # seconds per case
HEARTBEAT = "(deterministic) timeout"
RECDEPTH = "maximum recursion depth has been reached"
# A first error that is a parse error or a name resolution error says nothing about the changed hypothesis
# or instruction. The mutant does not get to its target. Its class is wrong_target, which is never a pass.
# The list comes from the message strings in the sources of the pinned toolchain, not only from observed records.
# The sources are Lean/Parser, Lean/ResolveName.lean and Lean/Elab/* (`errorAtSavedPos`, `throwError`, `logError`).
# The pattern must match at the start of the first error message, after `error:` or `error(<kind>):`.
# The match ignores the case of letters:
#   parse:            unknown tactic | unexpected token/end of input/identifier/command/tactic | expected <x>
#                     | unknown syntax category | unknown category | unknown parser
#   name resolution:  unknown identifier/constant/namespace/declaration/universe level/attribute/hypothesis
#                     /local declaration/alternative name/tag | unknown `grind` attribute
#                     | Invalid field `f`: The environment does not contain … (and the old lower-case form)
#                     | ambiguous identifier/namespace/…, possible interpretations
#   option or case:   Unknown option `o` | Case tag `t` not found
# THE LIST IS NOT COMPLETE. It covers the forms above and no other forms.
# A first error of a parse or name form that is not in the list gets the class inside. Read the first error of each row.
# These forms are not in the list, because they are internal errors of the elaborator, not parse or name errors:
# unknown metavariable, free variable, goal, let-declaration, parameter, local function, function.
WRONG_TARGET = re.compile(
    r"error(\([\w.]+\))?: "
    r"(unknown (tactic|identifier|constant|namespace|declaration|universe level|attribute|hypothesis"
    r"|local declaration|alternative name|tag|syntax category|category|parser)\b"
    r"|unknown `grind` attribute"
    r"|unknown option\b"
    r"|case tag\b.*\bnot found"
    r"|invalid field\b.*\benvironment does not contain"
    r"|ambiguous\b"
    r"|unexpected (token|end of input|identifier|command|tactic)\b"
    r"|expected [^\s])", re.I)
TOP = re.compile(r"^((theorem|def|end|example|set_option|abbrev|structure|instance|namespace|section|open)\b|/--|/-!)")


DECL_AT = re.compile(r"^(?:private )?(theorem|def) ([^\s:({\[]+)")


def find_decl(lines, name, kinds=("theorem",)):
    """(index, name as written) of the declaration line of `name` in a module.
    `name` is the full name or the name as written on the line.
    The full name is the namespace blocks above the line and the written name. A `_root_.` prefix also works.
    A match of the full name wins. Exactly one line must match, else the function raises ValueError.
    Two blocks of one module can hold the same written name, for example `theorem Decode.accept` of two types."""
    stack, full_hits, written_hits = [], [], []
    for i, l in enumerate(lines):
        m = re.match(r"^namespace (\S+)\s*$", l)
        if m:
            stack.append(m.group(1))
            continue
        if re.match(r"^section\b", l):
            stack.append("")
            continue
        if re.match(r"^end\b", l) and stack:
            stack.pop()
            continue
        m = DECL_AT.match(l)
        if not m or m.group(1) not in kinds:
            continue
        w = m.group(2)
        ns = ".".join(x for x in stack if x)
        full = w[7:] if w.startswith("_root_.") else (ns + "." if ns else "") + w
        if full == name:
            full_hits.append((i, w))
        if w == name:
            written_hits.append((i, w))
    hits = full_hits or written_hits
    if len(hits) != 1:
        raise ValueError(f"{name}: {len(hits)} declaration lines match")
    return hits[0]


def code_namespace_of(c):
    """The namespace of the code constant of a case: `code_namespace`, else `_root_` for a full name in `code_definition`.
    A short name without `code_namespace` is an error of the case."""
    if "code_namespace" in c:
        return c["code_namespace"]
    if "." in c["code_definition"]:
        return "_root_"
    raise ValueError(f"{c['id']}: code_definition {c['code_definition']} is not a full name, and the case has no code_namespace")


ATTRIBUTE_LINE = re.compile(r"^@\[[^\]]*\]\s*$")


def block_comments(lines):
    """The top-level block comments of a Lean text: (start line, start column, end line, end column, doc), 0-based.
    The end column is after `-/`. Block comments can be inside other block comments.
    The function skips line comments (`--`) and string literals."""
    out, depth, start, doc = [], 0, None, False
    for ln, line in enumerate(lines):
        k, instr = 0, False
        while k < len(line):
            two = line[k:k + 2]
            if depth == 0 and instr:
                if line[k] == "\\":
                    k += 2; continue
                if line[k] == '"':
                    instr = False
                k += 1; continue
            if depth == 0 and two == "--":
                break
            if depth == 0 and line[k] == '"':
                instr = True; k += 1; continue
            if two == "/-":
                if depth == 0:
                    start, doc = (ln, k), line[k:k + 3] == "/--"
                depth += 1; k += 2; continue
            if two == "-/" and depth > 0:
                depth -= 1; k += 2
                if depth == 0:
                    out.append((start[0], start[1], ln, k, doc))
                continue
            k += 1
    return out


def command_start(lines, start):
    """The first line (0-based) of the Lean command whose `theorem` line is `lines[start]`.
    Above the `theorem` line, the command holds these lines, from the bottom:
    attribute lines `@[…]`, one doc comment `/-- … -/`, and `set_option … in` lines.
    The doc comment must start a line and end at the end of the line directly above the attribute lines.
    A line comment, a plain `/- … -/` or a module comment `/-! … -/` above the theorem is not part of the command.
    Each other line stops the walk."""
    i = start
    while i > 0 and ATTRIBUTE_LINE.match(lines[i - 1]):
        i -= 1
    if i > 0 and lines[i - 1].rstrip().endswith("-/"):
        for sl, sc, el, ec, doc in block_comments(lines[:i]):
            if el == i - 1 and doc and not lines[el][ec:].strip() and not lines[sl][:sc].strip():
                i = sl
                break
    while i > 0 and lines[i - 1].startswith("set_option") and lines[i - 1].rstrip().endswith(" in"):
        i -= 1
    return i


def cut(text, thm):
    lines = text.split("\n")
    start, written = find_decl(lines, thm)
    thm = written
    # Include the set_option lines above the theorem that belong to it.
    s0 = start
    while s0 > 0 and lines[s0 - 1].startswith("set_option") and lines[s0 - 1].rstrip().endswith(" in"):
        s0 -= 1
    end = next((i for i in range(start + 1, len(lines)) if TOP.match(lines[i])), len(lines))
    # A theorem `<thm>_kind` directly after the theorem checks the whole declared type of the theorem.
    # It stays in the mutant and in the case range.
    j = end
    while j < len(lines) and (lines[j].strip() == "" or lines[j].lstrip().startswith("--")):
        j += 1
    if j < len(lines) and re.match(rf"^theorem {re.escape(thm)}_kind\b", lines[j]):
        end = next((i for i in range(j + 1, len(lines)) if TOP.match(lines[i])), len(lines))
    while end > start and lines[end - 1].strip() == "":
        end -= 1
    ns = [l for l in lines[:s0] if l.startswith("namespace ")]
    body = lines[:end]
    tail = [f"end {n.split()[1]}" for n in reversed(ns)
            if not any(l.strip() == f"end {n.split()[1]}" for l in lines[:s0])]
    return body + [""] + tail, start + 1, end  # 1-based start, inclusive end


def _ps_table():
    """pid: (ppid, sid, state) from `ps`, for a system without /proc (macOS).
    macOS `ps` prints 0 for the `sess` keyword. Thus os.getsid gives the session id.
    If getsid fails for a process, the process ended or is a zombie. The table does not hold it, so it is not alive."""
    t = {}
    out = subprocess.run(["ps", "-axo", "pid=,ppid=,state="], capture_output=True, text=True, check=True).stdout
    for line in out.splitlines():
        f = line.split()
        try:
            pid = int(f[0])
            t[pid] = (int(f[1]), os.getsid(pid), f[2][0])  # first state letter, `Z` for a zombie as in /proc
        except (OSError, ValueError, IndexError):
            continue
    return t


def _proc_table():
    """pid: (ppid, sid, state) from /proc (Linux), else from `ps` (macOS)."""
    if not os.path.isdir("/proc"):
        return _ps_table()
    t = {}
    for p in os.listdir("/proc"):
        if not p.isdigit():
            continue
        try:
            st = open(f"/proc/{p}/stat").read()
            f = st[st.rindex(")") + 2:].split()
            t[int(p)] = (int(f[1]), int(f[3]), f[0])
        except (OSError, ValueError, IndexError):
            continue
    return t


def _tree(root):
    """The root, its live descendants, and each other member of their sessions.
    memory_limit.py puts lake and lean into a new session. The tree does not include the session of this runner."""
    t = _proc_table()
    own = os.getsid(0)
    pids, todo = {root}, [root]
    while todo:
        q = todo.pop()
        for p, (pp, _, _) in t.items():
            if pp == q and p not in pids:
                pids.add(p)
                todo.append(p)
    sids = {t[p][1] for p in pids if p in t} - {own}
    pids |= {p for p, (_, sid, _) in t.items() if sid in sids}
    return pids, sids


def _alive(pids):
    t = _proc_table()
    return sorted(p for p in pids if p in t and t[p][2] != "Z")


def kill_tree(root):
    """Send SIGKILL to the root, its descendants and their sessions. Wait up to 10 s.
    If a process is still alive, raise RuntimeError. A kill of memory_limit.py alone can leave lake and lean alive."""
    pids, sids = _tree(root)
    for p in pids:  # stop each process first, so that no process forks during the collection
        try:
            os.kill(p, signal.SIGSTOP)
        except ProcessLookupError:
            pass
    pids2, sids2 = _tree(root)
    pids |= pids2
    sids |= sids2
    for s in sids:
        try:
            os.killpg(s, signal.SIGKILL)
        except (ProcessLookupError, PermissionError):
            pass
    for p in pids:
        try:
            os.kill(p, signal.SIGKILL)
        except ProcessLookupError:
            pass
    deadline = time.time() + 10
    while _alive(pids) and time.time() < deadline:
        time.sleep(0.1)
    left = _alive(pids)
    if left:
        raise RuntimeError(f"cleanup after the timeout: these processes are still alive: {left}")
    return sorted(pids)


def run_capped(argv, cwd, timeout):
    """Run argv. On a timeout, kill the whole process tree, which includes the new sessions below it.
    Make sure that no process is alive before the caller starts the next case.
    The result is (log, rc, timed_out, reaped pids)."""
    p = subprocess.Popen(argv, cwd=cwd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
                         errors="replace")
    try:
        out, err = p.communicate(timeout=timeout)
        return out + err, p.returncode, False, []
    except subprocess.TimeoutExpired:  # a class of its own, which is never a pass
        reaped = kill_tree(p.pid)
        out, err = p.communicate()
        return (out or "") + (err or ""), None, True, reaped


def module_name(path):
    """The module name of a path, for example `Uvarint.Amd64.Statements` for `Uvarint/Amd64/Statements.lean`."""
    return path[:-len(".lean")].replace("/", ".")


def import_names(line):
    """Read Lean imports without treating visibility modifiers as module names."""
    words = line.split("--", 1)[0].split()
    while words and words[0] in ("public", "meta"):
        words = words[1:]
    if not words or words[0] != "import":
        return []
    words = words[1:]
    return words[1:] if words and words[0] == "all" else words


def import_closure(mods):
    """The modules of the tree that the given modules import, directly or through other modules of the tree."""
    seen, todo = set(), list(mods)
    while todo:
        m = todo.pop()
        f = LEAN / (m.replace(".", "/") + ".lean")
        if m in seen or not f.exists():
            continue
        seen.add(m)
        todo += [x for l in f.read_text().split("\n") for x in import_names(l)]
    return seen


def inline_modules(c, lines):
    """Copy the modules of `inline` into the mutant text, before the case module.
    Each copy goes into its own `section`, so its `open` and `variable` commands stay local.
    Their imports go to the top, without the imports of copied modules. The case module also loses those imports.
    The result is the new lines and the shift of the line numbers of the case module."""
    paths = c.get("inline", [])
    if not paths:
        return lines, 0
    names = [module_name(m) for m in paths]
    if module_name(c["module"]) in names or len(set(names)) != len(names):
        raise ValueError(f"{c['id']}: inline holds the case module or a module two times")
    k = max((i + 1 for i, l in enumerate(lines) if l.startswith("import ")), default=0)
    head = []
    for l in lines[:k]:
        if l.startswith("import "):
            keep = [x for x in l.split()[1:] if x not in names]
            if keep:
                head.append("import " + " ".join(keep))
        else:
            head.append(l)
    body = []
    for m in paths:
        ml = (LEAN / m).read_text().split("\n")
        if any(l.startswith(("module", "public import", "meta import")) for l in ml):
            raise ValueError(f"{c['id']}: inline module {m} uses the module system")
        for l in ml:
            if l.startswith("import "):
                for x in l.split()[1:]:
                    if x not in names and f"import {x}" not in head:
                        head.append(f"import {x}")
        body += ["", f"section -- inlined {m}"] + [l for l in ml if not l.startswith("import ")] + ["end", ""]
    kept = [x for l in head if l.startswith("import ") for x in l.split()[1:]]
    clash = import_closure(kept) & set(names)
    if clash:
        raise ValueError(f"{c['id']}: an import that stays also imports the inlined modules {sorted(clash)}")
    out = head + body + lines[k:]
    return out, len(out) - len(lines)


def build_mutant(c, sdir):
    """The mutant Lean text of a case, its range and its diff. A code case includes the .S file `sdir/mut.S`.
    The result is (text, lo, hi, changed .S text or None, diff).
    For a case that the function cannot build, it raises ValueError."""
    src = (LEAN / c["module"]).read_text()
    lines, lo, hi = cut(src, c["theorem"])
    # The lines of the command above the `theorem` line: set_option … in lines and the doc comment.
    # The import and code lines that the function adds go above the command.
    # Thus this count does not change, and the case range is [lo - head, hi].
    head = (lo - 1) - command_start(lines, lo - 1)
    extra = [f"import {m}" for m in c.get("mutant_imports", [])]
    if extra:  # after the last import line of the copy. The range of the theorem moves with these lines.
        k = max(i for i, l in enumerate(lines) if import_names(l)) + 1
        lines = lines[:k] + extra + lines[k:]
        lo += len(extra)
        hi += len(extra)
    lines, shift = inline_modules(c, lines)
    lo += shift
    hi += shift
    text = "\n".join(lines)
    diff, S2 = "", None
    if c.get("code_definition"):
        S = (KR / c["assembly"]).read_text()
        if c["kind"] == "code":
            if "line" in c:  # 1-based line of the .S file, for an instruction that occurs two times
                sl = S.split("\n")
                if sl[c["line"] - 1] != c["old"]:
                    raise ValueError(f"{c['id']}: line {c['line']} does not hold the old instruction")
                sl[c["line"] - 1] = c["new"]
                S2 = "\n".join(sl)
            else:
                if S.count(c["old"] + "\n") != 1:
                    raise ValueError(f"{c['id']}: the old instruction is not unique")
                S2 = S.replace(c["old"] + "\n", c["new"] + "\n")
            diff = "".join(difflib.unified_diff(S.splitlines(True), S2.splitlines(True), "orig.S", "mut.S"))
        else:
            S2 = S
        name = c["code_definition"]
        tl = text.split("\n")
        k = max(i for i, l in enumerate(tl) if import_names(l)) + 1
        rest, n = re.subn(rf"(?<![A-Za-z0-9_.']){re.escape(name)}(?![A-Za-z0-9_'])", name + "Mut", "\n".join(tl[k:]))
        if not n:
            raise ValueError(f"{c['id']}: code_definition {name} is not used after the imports")
        ns = code_namespace_of(c)
        reader = "include_arm64_code" if "/Arm64/" in c["module"] else "include_x64_code"
        visibility = "public " if "module" in tl[:k] else ""
        decl = f'{visibility}def {ns}.{name}Mut : Program := {reader} "{sdir / "mut.S"}"'
        text = "\n".join(tl[:k] + ["", decl] + [rest])
        lo += 2
        hi += 2
    if c["kind"] == "statement":
        tl = text.split("\n")
        if c.get("statement_def"):  # the statement is a definition in an inlined module
            s, _ = find_decl(tl, c["statement_def"], ("def",))
            e = next((i for i in range(s + 1, len(tl)) if TOP.match(tl[i])), len(tl))
            if e > lo - 1 - head:
                raise ValueError(f"{c['id']}: statement_def {c['statement_def']} is not above the theorem")
        else:
            s, e = lo - 1, hi
        seg = "\n".join(tl[s:e])
        if seg.count(c["old"]) != 1:
            raise ValueError(f"{c['id']}: the statement text is not unique")
        seg2 = seg.replace(c["old"], c["new"])
        diff = "".join(difflib.unified_diff(seg.splitlines(True), seg2.splitlines(True), "orig", "mut"))
        text = "\n".join(tl[:s] + seg2.split("\n") + tl[e:])
    return text, lo - head, hi, S2, diff


def first_message(log, f):
    """The text of the first error message of the log, up to the next message."""
    out, on = [], False
    for l in log.splitlines():
        if re.match(rf"{re.escape(str(f))}:\d+:\d+: (error|warning|info)", l) or (on and l.startswith(str(f))):
            if on:
                break
            on = ": error" in l
        if on:
            out.append(l)
    return "\n".join(out)


def run_case(c, work):
    d = work / c["id"]
    d.mkdir(parents=True, exist_ok=True)
    text, lo, hi, S2, diff = build_mutant(c, d)
    if S2 is not None:
        (d / "mut.S").write_text(S2)
    f = d / "mut.lean"
    f.write_text(text)
    (d / "diff").write_text(diff)
    t0 = time.time()
    log, rc, timed_out, reaped = run_capped(
        ["python3", "-I", str(MEMORY_LIMIT), CAP, "--per-proc", CAP, "--", "lake", "env", "lean", str(f)], LEAN, CASE_TIMEOUT)
    (d / "log").write_text(log)
    errs = [int(m[1]) for m in re.finditer(rf"{re.escape(str(f))}:(\d+):\d+: error", log)]
    first = next((l for l in log.splitlines() if ": error" in l), None)
    killed = "killed=True" in log
    errl = [l for l in log.splitlines() if ": error" in l]
    later = next((l for l in errl[1:] if HEARTBEAT in l or RECDEPTH in l), None)
    # A first error that names the original program and the mutant program is a mismatch of two program constants.
    # An example is a lemma about the original program. It is not an effect of the mutation.
    mixed = False
    if c.get("code_definition"):
        msg, name = first_message(log, f), c["code_definition"]
        mixed = (re.search(rf"(?<![A-Za-z0-9_']){re.escape(name)}Mut(?![A-Za-z0-9_'])", msg) is not None
                 and re.search(rf"(?<![A-Za-z0-9_']){re.escape(name)}(?![A-Za-z0-9_'])", msg) is not None)
    # The result file holds no absolute path of the work directory.
    first, later = [x.replace(str(work), "<work>") if x else x for x in (first, later)]
    r = {"id": c["id"], "kind": c["kind"], "module": c["module"], "theorem": c["theorem"],
         "range": [lo, hi], "error_lines": errs, "first_error": first, "rc": rc,
         "killed": killed, "timeout": timed_out, "timeout_reaped_pids": reaped, "later_resource_error": later,
         "mixed_programs": mixed, "seconds": round(time.time() - t0, 1), "diff": diff}
    return classify(r)


def classify(r):
    """The class and the pass flag, from the recorded fields only. --reclassify also applies it to old results.
    The FIRST error line decides the resource classes.
    A later heartbeat or recursion error after a real first error stays as a flag (`later_resource_error`)."""
    errs, lo, hi = r["error_lines"], r["range"][0], r["range"][1]
    first = r.get("first_error") or ""
    hb = HEARTBEAT in first
    rd = RECDEPTH in first
    r["heartbeat_timeout"] = hb
    r["recursion_limit"] = rd
    if "later_resource_error" not in r:
        r["later_resource_error"] = None
    if r["timeout"]:
        k = "timeout_wall"
    elif r["killed"]:
        k = "killed"
    elif r["rc"] not in (0, 1):  # Lean exits with 1 on an error. Another status is a crash.
        k = "abnormal_exit"
    elif r["kind"] == "control":
        k = "control_pass" if r["rc"] == 0 and not errs else "control_fail"
    elif hb:
        k = "timeout_heartbeat"
    elif rd:
        k = "recursion_limit"
    elif r.get("mixed_programs"):
        k = "mixed_programs"
    elif errs and WRONG_TARGET.search(first):
        k = "wrong_target"
    elif not errs:
        k = "no_error"
    else:
        k = "inside" if all(lo <= e <= hi for e in errs) else "outside"
    r["class"] = k
    r["pass"] = k in ("control_pass", "inside")
    return r


def reclassify(out, work=None):
    d = json.load(open(out))
    for c in d["cases"]:  # fill the flag later_resource_error from the log, if the log exists
        lp = pathlib.Path(work) / c["id"] / "log" if work else None
        if lp and lp.exists():
            errl = [l for l in lp.read_text(errors="replace").splitlines() if ": error" in l]
            c["later_resource_error"] = next((l for l in errl[1:] if HEARTBEAT in l or RECDEPTH in l), None)
    d["cases"] = [classify(c) for c in d["cases"]]
    cls = {}
    for c in d["cases"]:
        cls[c["class"]] = cls.get(c["class"], 0) + 1
    d.update({"pass": sum(c["pass"] for c in d["cases"]), "total": len(d["cases"]), "classes": cls})
    json.dump(d, open(out, "w"), indent=1)
    print(json.dumps({"pass": d["pass"], "total": d["total"], "classes": cls}))
    return 0


def imports_of(modules):
    """The module names that the given files import (paths under lean/)."""
    mods = set()
    for m in modules:
        for l in (LEAN / m).read_text().split("\n"):
            mods.update(import_names(l))
    return sorted(mods)


def precheck(modules, extra=()):
    """`lake env lean` does not check that the build is current, so it can use an old .olean file.
    Before the first case, `lake build --no-build <imports>` must exit with 0.
    Then each imported module is current, also each module of `mutant_imports`."""
    imps = sorted(set(imports_of(modules)) | set(extra))
    argv = ["lake", "build", "--no-build"] + imps
    r = subprocess.run(argv, cwd=LEAN, capture_output=True, text=True)
    tail = [l for l in (r.stdout + r.stderr).splitlines() if l.startswith("- ") or "error" in l][-20:]
    print("PRECHECK", "rc", r.returncode, " ".join(argv), flush=True)
    return {"argv": argv, "rc": r.returncode, "failures": tail}


def main(cases, work, out, *ids):
    cs = json.load(open(cases))
    if ids:
        missing = sorted(set(ids) - {c["id"] for c in cs})
        cs = [c for c in cs if c["id"] in ids]
        if missing or not cs:  # an id that matches no case is a usage error, not a run of 0 cases
            print("NO SUCH CASE:", missing, ". No case ran.", flush=True)
            return 2
    work = pathlib.Path(work).resolve()
    work.mkdir(parents=True, exist_ok=True)
    pc = precheck(sorted({c["module"] for c in cs}), sorted({m for c in cs for m in c.get("mutant_imports", [])}))
    if pc["rc"] != 0:
        print("PRECHECK FAILED: an imported module is old or missing. No case ran.", pc["failures"], flush=True)
        return 2
    res = []
    for c in cs:
        r = run_case(c, work)
        print(("PASS" if r["pass"] else "FAIL"), r["class"], r["id"], r["kind"], r["theorem"], r["range"], r["error_lines"][:5],
              (r["first_error"] or "")[-160:], flush=True)
        res.append(r)
    cls = {}
    for r in res:
        cls[r["class"]] = cls.get(r["class"], 0) + 1
    json.dump({"cases": res, "pass": sum(r["pass"] for r in res), "total": len(res), "classes": cls,
               "case_timeout_s": CASE_TIMEOUT, "precheck": pc}, open(out, "w"), indent=1)
    print(json.dumps({"pass": sum(r["pass"] for r in res), "run": len(res), "classes": cls}))
    return 0 if all(r["pass"] for r in res) else 1


def selftest():
    """Fixtures of the classifier and the case range. For example, a heartbeat timeout and a wall timeout are never a pass."""
    assert import_names("import A B") == ["A", "B"]
    assert import_names("public import A") == ["A"]
    assert import_names("import all A -- body access") == ["A"]
    assert import_names("public meta import A") == ["A"]
    assert import_names("module") == []
    base = dict(kind="statement", range=[1, 9], rc=1, killed=False, timeout=False)
    fx = [("hb", dict(error_lines=[5], first_error="x:5:1: error: (deterministic) timeout at `whnf`"), "timeout_heartbeat"),
          ("in", dict(error_lines=[5], first_error="x:5:1: error: type mismatch"), "inside"),
          ("wall", dict(error_lines=[], first_error=None, rc=None, timeout=True), "timeout_wall"),
          ("out", dict(error_lines=[12], first_error="x:12:1: error: e"), "outside"),
          ("none", dict(error_lines=[], first_error=None, rc=0), "no_error"),
          ("rd", dict(error_lines=[5], first_error="x:5:0: error: maximum recursion depth has been reached"), "recursion_limit"),
          ("later_hb", dict(error_lines=[5, 7], first_error="x:5:1: error: ecancel failed",
                            later_resource_error="x:7:1: error: (deterministic) timeout at `whnf`"), "inside"),
          ("ctl", dict(kind="control", error_lines=[], first_error=None, rc=0), "control_pass"),
          # A name resolution error or a parse error inside the range is wrong_target, not inside.
          ("wt_uid", dict(error_lines=[5], first_error="x:5:47: error(lean.unknownIdentifier): Unknown identifier `hms`"),
           "wrong_target"),
          ("wt_uid_old", dict(error_lines=[5], first_error="x:5:47: error: unknown identifier 'hms'"), "wrong_target"),
          ("wt_ucst", dict(error_lines=[5], first_error="x:5:3: error(lean.unknownConstant): Unknown constant `Lib.foo`"),
           "wrong_target"),
          ("wt_ucst_old", dict(error_lines=[5], first_error="x:5:3: error: unknown constant 'Lib.foo'"), "wrong_target"),
          ("wt_parse", dict(error_lines=[5], first_error="x:5:0: error: unexpected token 'theorem'; expected term"),
           "wrong_target"),
          ("wt_parse2", dict(error_lines=[5], first_error="x:5:9: error: expected ':=', 'where' or '|'"), "wrong_target"),
          ("wt_eoi", dict(error_lines=[9], first_error="x:9:0: error: unexpected end of input"), "wrong_target"),
          # A real record (`exact` changed to `exactt`) and made forms.
          ("wt_tactic", dict(error_lines=[54], first_error="x:54:3: error: unknown tactic", range=[1, 60]), "wrong_target"),
          ("wt_ns", dict(error_lines=[5], first_error="x:5:5: error: unknown namespace `Foo`"), "wrong_target"),
          ("wt_field", dict(error_lines=[5], first_error="x:5:2: error: Invalid field `foo`: The environment does not "
                                                          "contain `Nat.foo`, so it is not possible to project"),
           "wrong_target"),
          ("wt_field_old", dict(error_lines=[5], first_error="x:5:2: error: invalid field 'foo', the environment does "
                                                              "not contain 'Nat.foo'"), "wrong_target"),
          ("wt_ambig", dict(error_lines=[5], first_error="x:5:2: error: Ambiguous identifier `f`; possible "
                                                          "interpretations: [A.f, B.f]"), "wrong_target"),
          ("wt_ambig_old", dict(error_lines=[5], first_error="x:5:2: error: ambiguous, possible interpretations"),
           "wrong_target"),
          ("wt_decl", dict(error_lines=[5], first_error="x:5:2: error: unknown declaration 'Lib.foo'"), "wrong_target"),
          ("wt_univ", dict(error_lines=[5], first_error="x:5:2: error: unknown universe level `v`"), "wrong_target"),
          ("wt_attr", dict(error_lines=[5], first_error="x:5:2: error: Unknown attribute `[simpp]`"), "wrong_target"),
          ("wt_hyp", dict(error_lines=[5], first_error="x:5:2: error: unknown hypothesis `h`"), "wrong_target"),
          ("wt_kind", dict(error_lines=[5], first_error="x:5:2: error(lean.unknownIdentifier): Unknown identifier `h`"),
           "wrong_target"),
          ("wt_cmd", dict(error_lines=[5], first_error="x:5:0: error: unexpected command"), "wrong_target"),
          # Two real first errors of the pinned toolchain, which the list did not catch before.
          ("wt_option", dict(error_lines=[54], first_error="x:54:2: error: Unknown option `rv.nosuch`", range=[21, 55]),
           "wrong_target"),
          ("wt_casetag", dict(error_lines=[54], first_error="x:54:2: error: Case tag `rvnosuch` not found.",
                              range=[21, 55]), "wrong_target"),
          ("wt_casetag_hint", dict(error_lines=[5], first_error="x:5:2: error: Case tag `h` not found.\nHint: x"),
           "wrong_target"),
          # A message that has such words only later is a real failure.
          ("in_mentions_expected", dict(error_lines=[5], first_error="x:5:1: error: Application type mismatch: "
                                                                         "hms has type True but is expected to have type"),
           "inside"),
          ("in_unknown_later", dict(error_lines=[5], first_error="x:5:1: error: omega could not prove the goal: "
                                                                     "unknown identifier in a hint"), "inside"),
          ("wt_unexp_tactic", dict(error_lines=[5], first_error="x:5:1: error: Unexpected tactic"), "wrong_target"),
          # A later unknown identifier after a real first error does not change the class.
          ("in_then_uid", dict(error_lines=[5, 6], first_error="x:5:1: error: Type mismatch"), "inside"),
          ("in_unsolved", dict(error_lines=[5], first_error="x:5:1: error: unsolved goals"), "inside"),
          ("crash_after_error", dict(error_lines=[5], first_error="x:5:1: error: type mismatch", rc=-11), "abnormal_exit"),
          ("mixed", dict(error_lines=[5], first_error="x:5:1: error: Application type mismatch", mixed_programs=True),
           "mixed_programs"),
          ("in_expected_type", dict(error_lines=[5], first_error="x:5:1: error: Application type mismatch: expected type"),
           "inside")]
    bad = []
    for name, f, want in fx:
        r = classify({**base, "id": name, **f})
        if r["class"] != want or r["pass"] != (want in ("inside", "control_pass")):
            bad.append((name, r["class"], want))
    # The case range starts at the command of the theorem: its set_option … in lines and its doc comment.
    src = ["import X", "", "set_option maxHeartbeats 400 in", "set_option maxRecDepth 10 in", "/-- doc", "-/",
           "theorem T.a : True := by", "  trivial", "", "/-- next -/", "theorem T.b : True := trivial"]
    lines, lo, hi = cut("\n".join(src), "T.a")
    for name, got, want in (("range_theorem_line", lo, 7), ("range_command", command_start(lines, lo - 1) + 1, 3),
                            ("range_end", hi, 8)):
        if got != want:
            bad.append((name, got, want))
    src2 = ["import X", "/-- one line -/", "theorem T.c : True := trivial"]
    if command_start(src2, 2) != 1:
        bad.append(("range_doc_one_line", command_start(src2, 2), 1))
    src3 = ["import X", "theorem T.d : True := trivial", "theorem T.e : True := trivial"]
    if command_start(src3, 2) != 2:
        bad.append(("range_no_prefix", command_start(src3, 2), 2))
    # A comment that is not the doc comment of the theorem stops the walk: a plain, a module or a line comment.
    for name, cmt in (("range_plain_comment", ["/- plain comment", "-/"]), ("range_module_comment", ["/-! section", "-/"]),
                      ("range_line_comment", ["-- note -/"]), ("range_plain_one_line", ["/- plain -/"])):
        s4 = ["import X", "/-- doc of a -/", "theorem T.a : True := trivial", ""] + cmt + ["theorem T.b : True := trivial"]
        got = command_start(s4, len(s4) - 1)
        if got != len(s4) - 1:
            bad.append((name, got, len(s4) - 1))
    # The expected start is 6, which is the `theorem` line itself, not 1.
    s5 = ["import X", "/-- doc of a -/", "theorem T.a : True := trivial", "", "/- plain comment", "-/",
          "theorem T.b : True := trivial"]
    if command_start(s5, 6) != 6:
        bad.append(("range_review_example", command_start(s5, 6), 6))
    # The walk does not take a doc comment above a set_option … in line of another command. The walk ends at TOP.
    s6 = ["import X", "/-- doc", "of a -/", "theorem T.a : True := by", "  trivial", "  -/", "theorem T.b : True := trivial"]
    if command_start(s6, 6) != 6:
        bad.append(("range_body_comment_end", command_start(s6, 6), 6))
    # Attribute lines are part of the command: set_option, doc comment, @[simp], theorem.
    s7 = ["import X", "set_option maxRecDepth 10 in", "/-- doc -/", "@[simp]", "theorem T.f : True := trivial"]
    if command_start(s7, 4) != 1:
        bad.append(("range_attribute", command_start(s7, 4), 1))
    # A doc comment of more than one line, with an empty line inside, counts.
    s8 = ["import X", "/-- first", "", "second -/", "theorem T.g : True := trivial"]
    if command_start(s8, 4) != 1:
        bad.append(("range_doc_blank_inside", command_start(s8, 4), 1))
    # An error of the whole declaration at its first line is inside, also with a later heartbeat timeout.
    r = classify({**base, "id": "cmd", "range": [34, 84], "error_lines": [60, 36],
                  "first_error": "x:60:61: error: Application type mismatch: The argument",
                  "later_resource_error": "x:36:0: error: (deterministic) timeout at `whnf`"})
    if r["class"] != "inside":
        bad.append(("command_start_error", r["class"], "inside"))
    print("selftest", "PASS" if not bad else f"FAIL {bad}")
    return 1 if bad else 0


def selftest_timeout():
    """A fake child process (no Lean) starts a grandchild in a NEW session, as memory_limit.py does.
    Both processes sleep. After the timeout, no process of the tree can be alive."""
    code = ("import subprocess,sys,time\n"
            "g=subprocess.Popen([sys.executable,'-c','import time\\ntime.sleep(600)'],start_new_session=True)\n"
            "print('grandchild',g.pid,flush=True)\n"
            "time.sleep(600)\n")
    t0 = time.time()
    log, rc, to, reaped = run_capped([sys.executable, "-I", "-c", code], "/", 2)
    gc = int(re.search(r"grandchild (\d+)", log)[1])
    left = _alive([gc] + reaped)
    ok = to and rc is None and gc in reaped and not left and time.time() - t0 < 30
    print("selftest-timeout", "PASS" if ok else "FAIL", {"timed_out": to, "grandchild": gc, "reaped": reaped,
                                                         "survivors": left, "s": round(time.time() - t0, 1)})
    # Control: a quick child process is not a timeout.
    log2, rc2, to2, _ = run_capped([sys.executable, "-I", "-c", "print('ok')"], "/", 20)
    ok2 = rc2 == 0 and not to2 and log2.strip() == "ok"
    print("selftest-timeout-control", "PASS" if ok2 else "FAIL")
    return 0 if ok and ok2 else 1


def check_cases(*paths):
    """A run without Lean: build the mutant text of each case of each case file, as the run does.
    Each module of "mutant_imports" must exist under lean/, must not be the case module or one of its imports,
    and must occur once. The function prints one line for each failure, and a summary."""
    bad, n = [], 0
    for p in paths:
        for c in json.load(open(p)):
            n += 1
            try:
                build_mutant(c, pathlib.Path("/mutant-directory"))
            except (OSError, ValueError, StopIteration, KeyError) as e:
                bad.append(f"{p}: {c.get('id')}: {type(e).__name__} {e}")
                continue
            src = (LEAN / c["module"]).read_text()
            mi = c.get("mutant_imports", [])
            own = module_name(c["module"])
            if not isinstance(mi, list) or len(set(mi)) != len(mi):
                bad.append(f"{p}: {c['id']}: mutant_imports is not a list of distinct module names")
                mi = []
            for m in mi:
                if not (LEAN / (m.replace(".", "/") + ".lean")).exists():
                    bad.append(f"{p}: {c['id']}: mutant_imports: no module {m}")
                elif m == own or f"import {m}" in src.split("\n"):
                    bad.append(f"{p}: {c['id']}: mutant_imports: {m} is the case module or one of its imports")
    for b in bad:
        print("CHECK FAIL", b)
    print(f"check-cases: {n} cases, {len(bad)} failures")
    return 1 if bad else 0


if __name__ == "__main__":
    if sys.argv[1:2] == ["--check-cases"]:
        sys.exit(check_cases(*sys.argv[2:]))
    if sys.argv[1:] == ["--selftest"]:
        sys.exit(selftest())
    if sys.argv[1:] == ["--selftest-timeout"]:
        sys.exit(selftest_timeout())
    if sys.argv[1:2] == ["--reclassify"]:
        sys.exit(reclassify(*sys.argv[2:4]))
    sys.exit(main(*sys.argv[1:]))
