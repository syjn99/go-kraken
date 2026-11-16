module
public import Kraken.X64.Syntax
public meta import Kraken.X64.Parser
public meta import Lean

/-!
`include_amd64_code "file.S"` parses a file with the runtime parser of Kraken.
It changes the result into a term with the `Lean.ToExpr` instances that Kraken derives for `Directive`.

This command is part of this repository. It is not a change of Kraken.
-/

open Lean Elab Term

elab "include_amd64_code" path:str : term => do
  let s ← IO.FS.readFile path.getString
  match Kraken.X64.Parser.parse (Kraken.Parser.stripDirectives s) with
  | .ok p => return toExpr p
  | .error e => throwError "Kraken runtime parser: {e}"
