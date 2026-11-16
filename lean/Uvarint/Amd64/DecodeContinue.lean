import Machine.Amd64.CompareFlags
import Uvarint.Amd64.ShiftAndMask
import Uvarint.Amd64.Code

/-!
# One more byte: the loop body of `encoding/binary.Uvarint`

Directives 6 to 18 of `Uvarint.Amd64.Code.uvarint`, for a byte `b` with the top bit set at index `i`:

    L_d: and $0x7f,%edi       // b & 0x7f
         mov %rcx,%r8         // i
         mov %rdx,%rcx        // 7 * i
         shl %cl,%rdi
         inc %r8              // i + 1
         lea 0x7(%rcx),%r9    // 7 * i + 7
         cmp $0x40,%rcx
         sbb %r10,%r10        // all ones, because 7i < 64
         and %r10,%rdi
         or %rdi,%rsi         // sum | ((b & 0x7f) << 7i)
         mov %r8,%rcx
         mov %r9,%rdx

The code continues at the loop head, which is directive 19. The lemmas hold for each final condition `post`.
-/

open Machine.Amd64 Uvarint.Amd64.Code
variable [Host]

namespace Uvarint.Amd64

/-- Directives 11 to 18: from the shifted payload to the loop head. -/
theorem Decode.continue_tail (k : Nat) (hk : uvarint.IsInfixAt Host.prog k) (post : MachineState → Prop)
    (rax rbx rcx rdx rsi rdi rsp rbp r8 r9 r10 r11 r12 r13 r14 r15 : UInt64) (zmms : RegZmms)
    (flags : StatusFlags) (mem : DataMem)
    (i sum : Nat) (b : UInt8) (hi : i ≤ 9) (hsum : sum < 2 ^ (7 * i))
    (hrcx : rcx = UInt64.ofNat (7 * i)) (hr8 : r8 = UInt64.ofNat i)
    (hrdi : rdi.toBitVec = BitVec.zeroExtend 64 (BitVec.extractLsb' 0 32
      (BitVec.zeroExtend 64 (BitVec.zeroExtend 32 b.toBitVec)) &&& BitVec.truncate 32 (127 : BitVec 64)) <<< (7 * i))
    (hrsi : rsi = UInt64.ofNat sum)
    (next : ∀ (rcx' rdx' rsi' rdi' r8' r9' r10' : UInt64) (flags' : StatusFlags),
      rcx' = UInt64.ofNat (i + 1) → rdx' = UInt64.ofNat (7 * (i + 1)) →
      rsi' = UInt64.ofNat (sum + b.toNat % 128 * 2 ^ (7 * i)) →
      Eventually (step1 Host.exe) post
        ⟨⟨⟨rax, rbx, rcx', rdx', rsi', rdi', rsp, rbp, r8', r9', r10', r11, r12, r13, r14, r15⟩, zmms, flags', mem⟩,
          Host.addrOf (k + 19)⟩) :
    Eventually (step1 Host.exe) post
      ⟨⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩,
        Host.addrOf (k + 11)⟩ := by
  subst hrcx hr8 hrsi
  step_directive hk uvarint 11
  step_directive hk uvarint 12
  step_directive hk uvarint 13
  step_directive hk uvarint 14
  step_directive hk uvarint 15
  intro _
  step_directive hk uvarint 16
  intro _
  step_directive hk uvarint 17
  step_directive hk uvarint 18
  have hc : ((UInt64.ofNat (7 * i)).toBitVec).toNat < (64 : BitVec 64).toNat := by
    rw [show (64 : BitVec 64).toNat = 64 from rfl]
    simp only [UInt64.toNat_toBitVec, UInt64.toNat_ofNat']
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  rw [sbb_self_after_borrow _ _ _ _ _ hc, BitVec.and_allOnes]
  apply next
  · apply UInt64.toBitVec_inj.mp
    simp only [UInt64.toBitVec_ofNat', BitVec.ofNat_add, BitVec.ofNat_eq_ofNat]
  · apply UInt64.toBitVec_inj.mp
    simp only [UInt64.toBitVec_ofNat', Nat.mul_add, BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, Nat.mul_one]
  · apply UInt64.toBitVec_inj.mp
    rw [hrdi, UInt64.toBitVec_ofNat', BitVec.or_comm, shiftLeft_or_ofNat _ _ _ hsum, low_seven_toNat]
    rfl

/-- Directives 6 to 18: one byte `b` with the top bit set, at index `i`. -/
theorem Decode.continue_path (k : Nat) (hk : uvarint.IsInfixAt Host.prog k) (post : MachineState → Prop)
    (rax rbx rcx rdx rsi rdi rsp rbp r8 r9 r10 r11 r12 r13 r14 r15 : UInt64) (zmms : RegZmms)
    (flags : StatusFlags) (mem : DataMem)
    (i sum : Nat) (b : UInt8) (hi : i ≤ 9) (hsum : sum < 2 ^ (7 * i))
    (hrcx : rcx = UInt64.ofNat i) (hrdx : rdx = UInt64.ofNat (7 * i))
    (hrdi : rdi = ⟨BitVec.zeroExtend 64 (BitVec.zeroExtend 32 b.toBitVec)⟩)
    (hrsi : rsi = UInt64.ofNat sum)
    (next : ∀ (rcx' rdx' rsi' rdi' r8' r9' r10' : UInt64) (flags' : StatusFlags),
      rcx' = UInt64.ofNat (i + 1) → rdx' = UInt64.ofNat (7 * (i + 1)) →
      rsi' = UInt64.ofNat (sum + b.toNat % 128 * 2 ^ (7 * i)) →
      Eventually (step1 Host.exe) post
        ⟨⟨⟨rax, rbx, rcx', rdx', rsi', rdi', rsp, rbp, r8', r9', r10', r11, r12, r13, r14, r15⟩, zmms, flags', mem⟩,
          Host.addrOf (k + 19)⟩) :
    Eventually (step1 Host.exe) post
      ⟨⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩,
        Host.addrOf (k + 6)⟩ := by
  subst hrcx hrdx hrdi hrsi
  step_directive hk uvarint 6
  step_directive hk uvarint 7
  intro _
  step_directive hk uvarint 8
  step_directive hk uvarint 9
  step_directive hk uvarint 10
  rw [shift_count i hi]
  split
  · rename_i h0
    simp only [Effects.All]
    have h7 : 7 * i = 0 := by simpa using h0
    refine Decode.continue_tail k hk post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ i sum b hi hsum rfl rfl ?_ rfl next
    simp only [h7, BitVec.shiftLeft_zero]
  · intro _
    repeat' (first | split | (simp only [Effects.All]; intro _))
    all_goals
      try simp only [Effects.All]
      intros
      exact Decode.continue_tail k hk post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ i sum b hi hsum rfl rfl rfl rfl next

end Uvarint.Amd64
