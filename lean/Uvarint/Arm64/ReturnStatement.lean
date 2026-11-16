module
public import Uvarint.Arm64.Program
public import Kraken.AArch64.OmniSemantics

@[expose] public section

namespace Uvarint.Arm64

/-- Each RET branches through the specified register and keeps every register and memory byte unchanged. -/
def return_statement (e : Executable) (r : XReg) : Prop :=
  ∀ (s : MachineData) (pc : Int64),
    pc ∈ [0x8d0fc, 0x8d114, 0x8d120, 0x8d12c] →
    Eventually (step1 e)
      (fun st => st.pc = Int64.ofBitVec (s.regs.getXReg r).toBitVec ∧ st.data = s) ⟨s, pc⟩

end Uvarint.Arm64
