import Uvarint.Arm64.Witness
import Kraken.AArch64.Parser

/-! Execute the converted ARM64 code in Kraken. This test does not execute the ELF or prove the full statement. -/

def main (args : List String) : IO UInt32 := do
  let code ← match args with
    | [] => pure Uvarint.Arm64.Code.uvarint
    | [path] =>
      let text ← IO.FS.readFile path
      match Kraken.AArch64.Parser.parse (Kraken.AArch64.Parser.stripDirectives text) with
      | .ok code => pure code
      | .error error => throw (IO.userError error)
    | _ => throw (IO.userError "usage: SelfTest.lean [assembly]")
  let executable := Uvarint.Arm64.Code.layout code code
  for (buf, expected) in Uvarint.knownAnswers do
    if !Uvarint.Arm64.Witness.check executable buf expected.machineForm then
      IO.eprintln s!"FAIL ARM64 model: {repr buf}, expected {repr expected}"
      return 1
  IO.println s!"PASS ARM64 model: {Uvarint.knownAnswers.length} cases, 256-step bound, complete memory and preserved registers"
  return 0
