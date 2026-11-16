import Uvarint.Arm64.Statements
import Uvarint.SpecKnownAnswers
import Machine.Arm64.Run
import Kraken.AArch64.Sep
import Kraken.SeparationTactics

namespace Uvarint.Arm64.Witness

abbrev zeros (n : Nat) : List UInt8 := List.replicate n 0

def block (buf : List UInt8) : List UInt8 := zeros 8 ++ (zeros 8 ++ (buf ++ zeros 8))

def initial (buf : List UInt8) : MachineData :=
  { regs := {
      X0 := 0x10010, X1 := UInt64.ofNat buf.length, X2 := UInt64.ofNat buf.length,
      X7 := 7, X8 := 8, X9 := 9, X10 := 10, X11 := 11, X12 := 12, X13 := 13, X14 := 14,
      X15 := 15, X16 := 16, X17 := 17, X18 := 18, X19 := 19, X20 := 20, X21 := 21,
      X22 := 22, X23 := 23, X24 := 24, X25 := 25, X26 := 26, X27 := 27,
      X28 := 0x70000, X29 := 0x60000, X30 := 0x40000, SP := 0x10000 },
    dmem := (block buf).At (0x10000 : BitVec 64) }

def frame (buf : List UInt8) : DataMem → Prop :=
  Eq ((zeros 8).At (0x10000 : BitVec 64)) ⋆
    Eq ((zeros 8).At ((0x10010 : BitVec 64) + BitVec.ofNat 64 buf.length))

/-- Restore the seven registers that the compiled function can change. -/
def restore (before after : Reg64s) : Reg64s :=
  { after with
    X0 := before.X0, X1 := before.X1, X2 := before.X2, X3 := before.X3,
    X4 := before.X4, X5 := before.X5, X6 := before.X6 }

/-- Check the complete concrete state, including every byte of memory and each preserved register. -/
def Matches (s : MachineData) (expected : UInt64 × UInt64) (t : MachineState) : Prop :=
  t.pc = Int64.ofBitVec s.regs.X30.toBitVec ∧
  (t.data.regs.X0, t.data.regs.X1) = expected ∧
  restore s.regs t.data.regs = s.regs ∧
  t.data.dmem = Mem.storeInt s.dmem (s.regs.SP.toBitVec + 8) 8 s.regs.X0.toBitVec.toInt

instance (s : MachineData) (v : UInt64 × UInt64) (t : MachineState) : Decidable (Matches s v t) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

def check (buf : List UInt8) (expected : UInt64 × UInt64) : Bool :=
  match Machine.Arm64.run Code.executable 0x40000 256 ⟨initial buf, 0x8d090⟩ with
  | none => false
  | some t => decide (Matches (initial buf) expected t)

/-- A concrete execution with complete state checks. -/
def execution_statement (buf : List UInt8) (expected : UInt64 × UInt64) : Prop :=
  Eventually (step1 Code.executable) (Matches (initial buf) expected) ⟨initial buf, 0x8d090⟩

end Uvarint.Arm64.Witness
