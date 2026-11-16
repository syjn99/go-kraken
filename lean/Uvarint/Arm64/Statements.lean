import Uvarint.Arm64.Program
import Uvarint.Spec
import Kraken.AArch64.OmniSemantics
import Kraken.SeparationMem

/-!
The ARM64 statement uses the pinned ELF addresses and Go ABIInternal, the internal Go calling convention.
The slice arguments occupy x0, x1, and x2: pointer, length, and capacity.
The results occupy x0 and x1. RET branches to x30 and keeps sp unchanged.
The code writes only the pointer spill at sp + 8. The caller owns that eight-byte slot.
The caller owns the complete input region. R describes every other byte of memory.
The code has no stack guard, runtime call, data reference, or write barrier.
The statement includes every result and termination. Its proof must preserve each condition.
-/

namespace Uvarint.Arm64

/-- Every general register except x0 through x6 keeps its entry value. -/
def Preserved (before after : MachineData) : Prop :=
  after.regs.SP = before.regs.SP ∧
  ∀ r : XReg, r ≠ .X0 → r ≠ .X1 → r ≠ .X2 → r ≠ .X3 → r ≠ .X4 → r ≠ .X5 → r ≠ .X6 →
    after.regs.getXReg r = before.regs.getXReg r

/-- The final state returns through x30, keeps the input and R, and replaces the pointer spill. -/
def Post (s : MachineData) (buf : List UInt8) (R : DataMem → Prop) (st : MachineState) : Prop :=
  st.pc = Int64.ofBitVec s.regs.X30.toBitVec ∧
  (st.data.regs.X0, st.data.regs.X1) = (decode buf).machineForm ∧
  Preserved s st.data ∧
  (Eq ((Int.toBytes 8 s.regs.X0.toBitVec.toInt).At (s.regs.SP.toBitVec + 8)) ⋆
    Eq (buf.At s.regs.X0.toBitVec) ⋆ R) st.data.dmem

/-- Complete Uvarint behavior at its pinned ELF address, including all three outcomes. -/
def result_statement : Prop :=
  ∀ (s : MachineData) (buf spill : List UInt8) (R : DataMem → Prop),
    spill.length = 8 →
    s.regs.X1 = UInt64.ofNat buf.length →
    buf.length ≤ s.regs.X2.toNat → s.regs.X2.toNat < 2 ^ 63 →
    s.regs.X0.toNat + buf.length ≤ 2 ^ 64 →
    s.regs.SP.toNat % 16 = 0 → s.regs.SP.toNat + 16 ≤ 2 ^ 64 →
    s.regs.X30.toNat % 4 = 0 →
    (Eq (spill.At (s.regs.SP.toBitVec + 8)) ⋆ Eq (buf.At s.regs.X0.toBitVec) ⋆ R) s.dmem →
    Eventually (step1 Code.executable) (Post s buf R) ⟨s, 0x8d090⟩

end Uvarint.Arm64
