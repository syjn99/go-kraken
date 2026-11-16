/-
Differential run of the uvarint specification.
Run from go-kraken/lean: `lake env lean --run <this file> <case list>`.
For each case line it prints the case as written, then x and n.
The line `-` is the empty buffer.
The mapping from a result to x and n is written here again on purpose.
It does not use `Uvarint.Result.machineForm`.
-/
import Uvarint.Spec

namespace UvarintDifferential

/-- The value of one lowercase hexadecimal digit. -/
def hexDigit (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else none

/-- The bytes of a hexadecimal text with an even number of digits. -/
def hexBytes : List Char → Option (List UInt8)
  | [] => some []
  | a :: b :: rest => do
    let hi ← hexDigit a
    let lo ← hexDigit b
    let tail ← hexBytes rest
    pure (UInt8.ofNat (16 * hi + lo) :: tail)
  | [_] => none

/-- The buffer of one case line. -/
def parseCase (line : String) : Option (List UInt8) :=
  if line = "-" then some []
  else if line.isEmpty then none
  else hexBytes line.toList

/-- x and n as `binary.Uvarint` returns them. -/
def render : Uvarint.Result → String
  | .value x n => s!"{x.toNat} {n}"
  | .incomplete => "0 0"
  | .overflow n => s!"0 -{n}"

def main (args : List String) : IO UInt32 := do
  let [path] := args
    | IO.eprintln "usage: lake env lean --run Differential.lean <case list>"
      return 2
  let text ← IO.FS.readFile path
  let out ← IO.getStdout
  for line in text.splitOn "\n" do
    if line.isEmpty then continue
    match parseCase line with
    | some buf => out.putStrLn s!"{line} {render (Uvarint.decode buf)}"
    | none =>
      IO.eprintln s!"bad case line: {line}"
      return 1
  return 0

end UvarintDifferential

def main (args : List String) : IO UInt32 := UvarintDifferential.main args
