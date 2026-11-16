import Lean

/-!
# Declaration dump: one stable record for each declaration

The program uses only the core `Lean` library.
`tools/axioms_gate.py` runs it. A run is a heavy Lean job.

    LEAN_PATH=<directory of the .olean files> lean --run decl_dump.lean [--root R]... Module...

The program imports the given modules.
It prints one line for each declaration whose module has one of the roots.
Without `--root`, the roots are the roots of the given modules.
Tabs separate the fields of a line. The lines are in the order of the names:

    name  kind  type-hash  value-hash  axioms

* `type-hash`: the `Expr.hash` of the declared type, as 16 hexadecimal digits.
* `value-hash`: the `Expr.hash` of the value of a `def` or an `opaque`. For each other kind, the field is `-`.
  The program does not calculate a hash of a theorem proof. A changed proof is visible only if it changes the axiom set.
* `axioms`: the result of `Lean.collectAxioms` in order, with commas between the names. If the set is empty, the field is `-`.

The first line is a header with the Lean version and the Git hash.

Limits: `Expr.hash` is a structural hash.
On the tested toolchain, the hash has only 32 bits, and the upper 8 hexadecimal digits are 0.
The hash ignores the names of binders and their kind (explicit, implicit, instance-implicit).
It is not a check of definitional equality.
Compare two dumps only when the same Lean build made them.
The exit status is 0 on success.
It is 2 on a usage error, or when no declaration has one of the roots.
-/

open Lean

def kindOf : ConstantInfo → String × Option Expr
  | .axiomInfo _  => ("axiom", none)
  | .defnInfo v   => ("def", some v.value)
  | .thmInfo _    => ("theorem", none)
  | .opaqueInfo v => ("opaque", some v.value)
  | .quotInfo _   => ("quot", none)
  | .inductInfo _ => ("inductive", none)
  | .ctorInfo _   => ("ctor", none)
  | .recInfo _    => ("recursor", none)

def hex16 (h : UInt64) : String :=
  let ds := Nat.toDigits 16 h.toNat
  "".pushn '0' (16 - ds.length) ++ String.join (ds.map toString)

def parseArgs : List String → List Name → List Name → Except String (List Name × List Name)
  | [], roots, mods => .ok (roots.reverse, mods.reverse)
  | "--root" :: r :: rest, roots, mods => parseArgs rest (r.toName :: roots) mods
  | "--root" :: [], _, _ => .error "--root needs a value"
  | m :: rest, roots, mods =>
    if m.startsWith "-" then .error s!"unknown option {m}"
    else parseArgs rest roots (m.toName :: mods)

def dumpRows (env : Environment) (roots : List Name) : CoreM (Array String) := do
  let mut rows : Array (String × String) := #[]
  for (n, ci) in env.constants.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let mod := env.header.moduleNames[idx.toNat]!
    unless roots.any (fun root => root.isPrefixOf mod) do continue
    let (kind, val) := kindOf ci
    let vh := match val with
      | some v => hex16 v.hash
      | none => "-"
    let axs ← Lean.collectAxioms n
    let axStrs := (axs.map toString).qsort (· < ·)
    let axCol := if axStrs.isEmpty then "-" else ",".intercalate axStrs.toList
    let key := toString n
    rows := rows.push (key, s!"{key}\t{kind}\t{hex16 ci.type.hash}\t{vh}\t{axCol}")
  return (rows.qsort (fun a b => a.1 < b.1)).map (·.2)

def main (args : List String) : IO UInt32 := do
  match parseArgs args [] [] with
  | .error e =>
    IO.eprintln s!"decl_dump: {e}"
    return 2
  | .ok (roots, mods) =>
    if mods.isEmpty then
      IO.eprintln "usage: lean --run decl_dump.lean [--root R]... Module..."
      return 2
    let roots := if roots.isEmpty then mods.map Name.getRoot else roots
    initSearchPath (← findSysroot)
    let env ← importModules (mods.map fun m => ({ module := m } : Import)).toArray {}
    let ctx : Core.Context := { fileName := "<decl_dump>", fileMap := default }
    let st : Core.State := { env }
    let (rows, _) ← (dumpRows env roots).toIO ctx st
    if rows.isEmpty then
      IO.eprintln s!"decl_dump: no declaration under roots {roots}"
      return 2
    IO.println s!"# decl_dump v1 lean={Lean.versionString} githash={Lean.githash} roots={",".intercalate (roots.map toString)}"
    for r in rows do IO.println r
    return 0
