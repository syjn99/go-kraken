import Machine.Amd64.CompareFlags
import Uvarint.Amd64.DecodeExits
import Uvarint.Amd64.ShiftAndMask

/-!
# The value return of `encoding/binary.Uvarint`

Directives 35 to 44 of `Uvarint.Code.uvarint`:

    L_62: mov %rcx,%rax       // i
          mov %rdx,%rcx       // 7 * i
          shl %cl,%rdi        // b << 7i
          lea 0x1(%rax),%rbx  // i + 1
          cmp $0x40,%rcx
          sbb %rax,%rax       // all ones, because 7i < 64
          and %rdi,%rax
          or %rsi,%rax        // sum | (b << 7i)
          ret
-/

open Machine Uvarint.Code
variable [Host]

namespace Uvarint

/-- Directives 39 to 44: from the shifted byte to the return. -/
theorem Decode.value_tail (k : Nat) (hk : uvarint.IsInfixAt Host.prog k)
    (ra p rsp rbp r14 : UInt64) (buf : List UInt8) (R : DataMem → Prop)
    (rax rbx rcx rdx rsi rdi r8 r9 r10 r11 r12 r13 r15 : UInt64) (zmms : RegZmms) (flags : StatusFlags)
    (mem : DataMem) (hm : Decode.loopMemory ra p rsp buf R mem)
    (i sum : Nat) (b : UInt8) (hi : i ≤ 9) (hsum : sum < 2 ^ (7 * i))
    (hrax : rax = UInt64.ofNat i) (hrcx : rcx = UInt64.ofNat (7 * i))
    (hrdi : rdi.toBitVec = BitVec.zeroExtend 64 (BitVec.zeroExtend 32 b.toBitVec) <<< (7 * i))
    (hrsi : rsi = UInt64.ofNat sum)
    (hdec : decode buf = .value (UInt64.ofNat (sum + b.toNat * 2 ^ (7 * i))) (i + 1)) :
    Eventually (step1 Host.exe) (Decode.finalCondition ra p rsp rbp r14 buf R)
      ⟨⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩,
        Host.addrOf (k + 39)⟩ := by
  subst hrax hrcx hrsi
  step_directive hk uvarint 39
  step_directive hk uvarint 40
  step_directive hk uvarint 41
  step_directive hk uvarint 42
  intro _
  step_directive hk uvarint 43
  intro _
  step_directive hk uvarint 44
  simp only [Decode.loopMemory] at hm
  apply load_step _ _ _ _ (Int.toBytes 8 ra.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  unfold_step
  apply Eventually.done
  simp only [Decode.finalCondition, Decode.loopMemory, hdec, Result.machineForm]
  have hc : ((UInt64.ofNat (7 * i)).toBitVec).toNat < (64 : BitVec 64).toNat := by
    rw [show (64 : BitVec 64).toNat = 64 from rfl]
    simp only [UInt64.toNat_toBitVec, UInt64.toNat_ofNat']
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  rw [sbb_self_after_borrow _ _ _ _ _ hc, BitVec.allOnes_and, hrdi, UInt64.toBitVec_ofNat',
    shiftLeft_or_ofNat _ _ _ hsum, zero_extend_byte_toNat]
  refine ⟨trivial, ?_, ?_, trivial, trivial, hm⟩
  · simp only [Prod.mk.injEq]
    constructor
    · rfl
    · apply UInt64.toBitVec_inj.mp
      simp only [UInt64.toBitVec_ofNat', BitVec.ofNat_add, BitVec.ofNat_eq_ofNat]
  · apply UInt64.toBitVec_inj.mp
    simp

/-- Directives 35 to 44: the value return for the last byte `b` at index `i`. -/
theorem Decode.value_path (k : Nat) (hk : uvarint.IsInfixAt Host.prog k)
    (ra p rsp rbp r14 : UInt64) (buf : List UInt8) (R : DataMem → Prop)
    (rax rbx rcx rdx rsi rdi r8 r9 r10 r11 r12 r13 r15 : UInt64) (zmms : RegZmms) (flags : StatusFlags)
    (mem : DataMem) (hm : Decode.loopMemory ra p rsp buf R mem)
    (i sum : Nat) (b : UInt8) (hi : i ≤ 9) (hsum : sum < 2 ^ (7 * i))
    (hrcx : rcx = UInt64.ofNat i) (hrdx : rdx = UInt64.ofNat (7 * i))
    (hrdi : rdi = ⟨BitVec.zeroExtend 64 (BitVec.zeroExtend 32 b.toBitVec)⟩)
    (hrsi : rsi = UInt64.ofNat sum)
    (hdec : decode buf = .value (UInt64.ofNat (sum + b.toNat * 2 ^ (7 * i))) (i + 1)) :
    Eventually (step1 Host.exe) (Decode.finalCondition ra p rsp rbp r14 buf R)
      ⟨⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩,
        Host.addrOf (k + 35)⟩ := by
  subst hrcx hrdx hrdi hrsi
  step_directive hk uvarint 35
  step_directive hk uvarint 36
  step_directive hk uvarint 37
  step_directive hk uvarint 38
  rw [shift_count i hi]
  split
  · rename_i h0
    simp only [Effects.All]
    have h7 : 7 * i = 0 := by simpa using h0
    refine Decode.value_tail k hk ra p rsp rbp r14 buf R _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hm i sum b hi hsum
      rfl rfl ?_ rfl hdec
    simp only [h7, BitVec.shiftLeft_zero]
  · intro _
    repeat' (first | split | (simp only [Effects.All]; intro _))
    all_goals
      try simp only [Effects.All]
      intros
      exact Decode.value_tail k hk ra p rsp rbp r14 buf R _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hm i sum b hi hsum
        rfl rfl rfl rfl hdec

end Uvarint
