module
public import Kraken.AArch64.Syntax
public meta import Kraken.AArch64.Parser
public meta import Lean

open Lean Elab Term

elab "include_arm64_code" path:str : term => do
  let s ← IO.FS.readFile path.getString
  match Kraken.AArch64.Parser.parse (Kraken.AArch64.Parser.stripDirectives s) with
  | .ok p => return toExpr p
  | .error e => throwError "Kraken runtime parser: {e}"
