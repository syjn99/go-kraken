import Machine.Amd64.Step
import Uvarint.Amd64.Statements

/-!
# The three early returns of `encoding/binary.Uvarint`

Directive indices of `Uvarint.Code.uvarint`:
- 32 to 34: `xor %eax,%eax`, `mov $-0xa,%rbx`, `ret` (overflow after 10 bytes).
- 45 to 48: label, `xor %eax,%eax`, `mov $-0xb,%rbx`, `ret` (overflow after 11 bytes).
- 49 to 52: label, `xor %eax,%eax`, `xor %ebx,%ebx`, `ret` (buffer too small).

The loop does not write memory. Thus each path ends with the memory of the loop.
-/

open Machine Uvarint.Code
variable [Host]

namespace Uvarint

/-- The memory after the first instruction: the return address at `rsp`,
the spill slot that holds the buffer pointer `p`, the buffer and the frame `R`. -/
def Decode.loopMemory (ra p rsp : UInt64) (buf : List UInt8) (R : DataMem → Prop) : DataMem → Prop :=
  Eq ((Int.toBytes 8 ra.toBitVec.toInt).At rsp.toBitVec)
    ⋆ Eq ((Int.toBytes 8 p.toBitVec.toInt).At (rsp.toBitVec + 8)) ⋆ Eq (buf.At p.toBitVec) ⋆ R

/-- The conclusion of `Decode.result_statement`, for the entry values `p` (rax), `rsp`, `rbp` and `r14`. -/
def Decode.finalCondition (ra p rsp rbp r14 : UInt64) (buf : List UInt8) (R : DataMem → Prop)
    (st : MachineState) : Prop :=
  st.pc = Int64.ofBitVec ra.toBitVec
    ∧ (st.data.regs.rax, st.data.regs.rbx) = (decode buf).machineForm
    ∧ st.data.regs.rsp = rsp + 8 ∧ st.data.regs.rbp = rbp ∧ st.data.regs.r14 = r14
    ∧ Decode.loopMemory ra p rsp buf R st.data.dmem

omit [Host] in
/-- `xor %eax,%eax` gives zero. -/
theorem xor_self_zero (x : UInt64) :
    ({ toBitVec := BitVec.zeroExtend 64 (BitVec.extractLsb' 0 32 x.toBitVec ^^^ BitVec.extractLsb' 0 32 x.toBitVec) }
      : UInt64) = 0 := by
  apply UInt64.toBitVec_inj.mp
  simp

/-- Directives 49 to 52: the buffer ends before the value ends. -/
theorem Decode.exit_incomplete (k : Nat) (hk : uvarint.IsInfixAt Host.prog k)
    (ra p rsp rbp r14 : UInt64) (buf : List UInt8) (R : DataMem → Prop)
    (rax rbx rcx rdx rsi rdi r8 r9 r10 r11 r12 r13 r15 : UInt64) (zmms : RegZmms) (flags : StatusFlags)
    (mem : DataMem) (hm : Decode.loopMemory ra p rsp buf R mem) (hdec : decode buf = .incomplete) :
    Eventually (step1 Host.exe) (Decode.finalCondition ra p rsp rbp r14 buf R)
      ⟨⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩,
        Host.addrOf (k + 49)⟩ := by
  step_directive hk uvarint 49
  step_directive hk uvarint 50
  intro _
  step_directive hk uvarint 51
  intro _
  step_directive hk uvarint 52
  simp only [Decode.loopMemory] at hm
  apply load_step _ _ _ _ (Int.toBytes 8 ra.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  unfold_step
  apply Eventually.done
  simp only [Decode.finalCondition, Decode.loopMemory, hdec, Result.machineForm, xor_self_zero]
  refine ⟨trivial, ?_, ?_, trivial, trivial, hm⟩
  all_goals first
    | trivial
    | (apply UInt64.toBitVec_inj.mp; simp; done)
    | (simp only [Prod.mk.injEq]; constructor <;> (apply UInt64.toBitVec_inj.mp; decide))

/-- Directives 45 to 48: an eleventh byte. -/
theorem Decode.exit_overflow_eleven (k : Nat) (hk : uvarint.IsInfixAt Host.prog k)
    (ra p rsp rbp r14 : UInt64) (buf : List UInt8) (R : DataMem → Prop)
    (rax rbx rcx rdx rsi rdi r8 r9 r10 r11 r12 r13 r15 : UInt64) (zmms : RegZmms) (flags : StatusFlags)
    (mem : DataMem) (hm : Decode.loopMemory ra p rsp buf R mem) (hdec : decode buf = .overflow 11) :
    Eventually (step1 Host.exe) (Decode.finalCondition ra p rsp rbp r14 buf R)
      ⟨⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩,
        Host.addrOf (k + 45)⟩ := by
  step_directive hk uvarint 45
  step_directive hk uvarint 46
  intro _
  step_directive hk uvarint 47
  step_directive hk uvarint 48
  simp only [Decode.loopMemory] at hm
  apply load_step _ _ _ _ (Int.toBytes 8 ra.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  unfold_step
  apply Eventually.done
  simp only [Decode.finalCondition, Decode.loopMemory, hdec, Result.machineForm, xor_self_zero]
  refine ⟨trivial, ?_, ?_, trivial, trivial, hm⟩
  all_goals first
    | trivial
    | (apply UInt64.toBitVec_inj.mp; simp; done)
    | (simp only [Prod.mk.injEq]; constructor <;> (apply UInt64.toBitVec_inj.mp; decide))

/-- Directives 32 to 34: the tenth byte is larger than 1. -/
theorem Decode.exit_overflow_ten (k : Nat) (hk : uvarint.IsInfixAt Host.prog k)
    (ra p rsp rbp r14 : UInt64) (buf : List UInt8) (R : DataMem → Prop)
    (rax rbx rcx rdx rsi rdi r8 r9 r10 r11 r12 r13 r15 : UInt64) (zmms : RegZmms) (flags : StatusFlags)
    (mem : DataMem) (hm : Decode.loopMemory ra p rsp buf R mem) (hdec : decode buf = .overflow 10) :
    Eventually (step1 Host.exe) (Decode.finalCondition ra p rsp rbp r14 buf R)
      ⟨⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩,
        Host.addrOf (k + 32)⟩ := by
  step_directive hk uvarint 32
  intro _
  step_directive hk uvarint 33
  step_directive hk uvarint 34
  simp only [Decode.loopMemory] at hm
  apply load_step _ _ _ _ (Int.toBytes 8 ra.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  unfold_step
  apply Eventually.done
  simp only [Decode.finalCondition, Decode.loopMemory, hdec, Result.machineForm, xor_self_zero]
  refine ⟨trivial, ?_, ?_, trivial, trivial, hm⟩
  all_goals first
    | trivial
    | (apply UInt64.toBitVec_inj.mp; simp; done)
    | (simp only [Prod.mk.injEq]; constructor <;> (apply UInt64.toBitVec_inj.mp; decide))

end Uvarint
