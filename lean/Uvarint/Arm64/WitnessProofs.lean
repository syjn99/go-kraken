module
public import Uvarint.Arm64.Witness
import all Kraken.AArch64.Semantics
import all Kraken.Layout
import all Kraken.Mem
import all Kraken.ToBytes

@[expose] public section

open Uvarint.Arm64.Code

namespace Uvarint.Arm64.Witness

/-- The Boolean check gives a terminating execution with the stated complete machine state. -/
theorem check_sound (e : Executable) (buf : List UInt8) (expected : UInt64 × UInt64) (h : check e buf expected = true) :
    execution_statement e buf expected := by
  unfold check at h
  cases hr : Machine.Arm64.run e 0x40000 256 ⟨initial buf, 0x8d090⟩ with
  | none => simp [hr] at h
  | some t =>
    simp only [hr] at h
    have hm : Matches (initial buf) expected t := of_decide_eq_true h
    exact eventually_weaken (step1 e) (fun st => st = t) (Matches (initial buf) expected)
      _ (fun _ he => he ▸ hm)
      (Machine.Arm64.run_sound _ _ _ _ _ hr)

end Uvarint.Arm64.Witness
