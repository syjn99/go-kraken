import Machine.ByteLoad
import Machine.Bytes
import Machine.CompareFlags
import Machine.Labels
import Uvarint.DecodeExits
import Uvarint.DecodeValue
import Uvarint.DecodeContinue

/-!
# The loop of `encoding/binary.Uvarint`

The loop head is directive 19 (label `L_33`):

    L_33: cmp %rcx,%rbx; jle L_87      // i ≥ len: buffer too small
          movzbl (%rax,%rcx,1),%edi    // b = buf[i]
          nop
          cmp $0xa,%rcx; je L_7d       // i = 10: overflow after 11 bytes
          cmp $0x80,%dil; jae L_d      // top bit set: one more byte
          cmp $0x9,%rcx; jne L_62      // value
          cmp $0x1,%dil; jbe L_62      // value
          ...                          // overflow after 10 bytes

The loop invariant at the loop head: rax holds the buffer pointer and rbx holds the length.
rcx holds the index `i`, rdx holds the shift `7 * i`, and rsi holds the sum `sum` of the payloads that the loop read.
The specification of the remaining bytes is `decodeFrom i sum (buf.drop i)`.
-/

open Machine Uvarint.Code

namespace Uvarint

/-- An eleventh byte is an overflow. -/
theorem decodeFrom_eleventh (sum : Nat) (b : UInt8) (rest : List UInt8) :
    decodeFrom 10 sum (b :: rest) = .overflow 11 := by
  simp [decodeFrom, maxLength]

/-- A byte without the top bit ends the value, unless it is the tenth byte and larger than 1. -/
theorem decodeFrom_last (i sum : Nat) (b : UInt8) (rest : List UInt8) (hi : i < 10) (hb : b.toNat < 128)
    (hnine : ¬(i = 9 ∧ 1 < b.toNat)) :
    decodeFrom i sum (b :: rest) = .value (UInt64.ofNat (sum + b.toNat * 2 ^ (7 * i))) (i + 1) := by
  have h1 : b < 0x80 := by rw [UInt8.lt_iff_toNat_lt]; exact hb
  have h2 : ¬(i = 10 - 1 ∧ 1 < b) := by
    rw [UInt8.lt_iff_toNat_lt]; simpa using hnine
  simp [decodeFrom, maxLength, h1, h2, show i ≠ 10 by omega]

/-- A tenth byte larger than 1 is an overflow. -/
theorem decodeFrom_tenth_large (sum : Nat) (b : UInt8) (rest : List UInt8) (hb : b.toNat < 128)
    (h1 : 1 < b.toNat) : decodeFrom 9 sum (b :: rest) = .overflow 10 := by
  have hb' : b < 0x80 := by rw [UInt8.lt_iff_toNat_lt]; exact hb
  have h1' : 1 < b := by rw [UInt8.lt_iff_toNat_lt]; exact h1
  simp [decodeFrom, maxLength, hb', h1']

/-- A byte with the top bit set adds its payload and continues with the next byte. -/
theorem decodeFrom_more (i sum : Nat) (b : UInt8) (rest : List UInt8) (hi : i < 10) (hb : 128 ≤ b.toNat) :
    decodeFrom i sum (b :: rest) = decodeFrom (i + 1) (sum + (b.toNat - 128) * 2 ^ (7 * i)) rest := by
  have hb' : ¬b < 0x80 := by rw [UInt8.lt_iff_toNat_lt]; simp; omega
  simp only [decodeFrom, maxLength, hb', show i ≠ 10 by omega, ite_false]

/-- `(UInt64.ofNat n).toBitVec.toNat = n` for `n < 2 ^ 64`. -/
theorem ofNat_toBitVec_toNat (n : Nat) (h : n < 2 ^ 64) : (UInt64.ofNat n).toBitVec.toNat = n := by
  simp only [UInt64.toNat_toBitVec, UInt64.toNat_ofNat']
  exact Nat.mod_eq_of_lt h

variable [Host]

/-- One pass of the loop from the loop head. The hypothesis `more` is the claim at the next index.
The three early returns and the value return end in the final condition. A byte with the top bit set uses `more`. -/
theorem Decode.iteration (k : Nat) (hk : uvarint.IsInfixAt Host.prog k) (hf : LabelsFresh uvarint k)
    (ra p rsp rbp r14 : UInt64) (buf : List UInt8) (R : DataMem → Prop) (hbound : buf.length < 2 ^ 63)
    (rcx rdx rsi rdi r8 r9 r10 r11 r12 r13 r15 : UInt64) (zmms : RegZmms) (flags : StatusFlags)
    (mem : DataMem) (hm : Decode.loopMemory ra p rsp buf R mem)
    (i sum : Nat) (hi : i ≤ 10) (hile : i ≤ buf.length) (hsum : sum < 2 ^ (7 * i))
    (hdec : decode buf = decodeFrom i sum (buf.drop i))
    (hrcx : rcx = UInt64.ofNat i) (hrdx : rdx = UInt64.ofNat (7 * i)) (hrsi : rsi = UInt64.ofNat sum)
    (more : i ≤ 9 → i < buf.length → ∀ (sum' : Nat) (rcx' rdx' rsi' rdi' r8' r9' r10' : UInt64) (flags' : StatusFlags),
      sum' < 2 ^ (7 * (i + 1)) → decode buf = decodeFrom (i + 1) sum' (buf.drop (i + 1)) →
      rcx' = UInt64.ofNat (i + 1) → rdx' = UInt64.ofNat (7 * (i + 1)) → rsi' = UInt64.ofNat sum' →
      Eventually (step1 Host.exe) (Decode.finalCondition ra p rsp rbp r14 buf R)
        ⟨⟨⟨p, UInt64.ofNat buf.length, rcx', rdx', rsi', rdi', rsp, rbp, r8', r9', r10', r11, r12, r13, r14, r15⟩,
          zmms, flags', mem⟩, Host.addrOf (k + 19)⟩) :
    Eventually (step1 Host.exe) (Decode.finalCondition ra p rsp rbp r14 buf R)
      ⟨⟨⟨p, UInt64.ofNat buf.length, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩,
        zmms, flags, mem⟩, Host.addrOf (k + 19)⟩ := by
  subst hrcx hrdx hrsi
  step_directive hk uvarint 19
  step_directive hk uvarint 20
  step_directive hk uvarint 21
  rw [flag_le _ _ _ _ (by rw [ofNat_toBitVec_toNat _ (by omega)]; omega)
    (by rw [ofNat_toBitVec_toNat _ (by omega)]; omega),
    ofNat_toBitVec_toNat _ (by omega), ofNat_toBitVec_toNat _ (by omega)]
  split
  · rename_i hle
    simp only [decide_eq_true_eq] at hle
    label_address hk hf uvarint 49
    simp only [Effects.All]
    apply Decode.exit_incomplete k hk ra p rsp rbp r14 buf R _ _ _ _ _ _ _ _ _ _ _ _ _ zmms _ mem hm
    rw [hdec, List.drop_eq_nil_of_le (by omega)]
    rfl
  · rename_i hlt
    simp only [decide_eq_true_eq, Nat.not_le] at hlt
    simp only [Effects.All]
    step_directive hk uvarint 22
    have hm' := hm
    simp only [Decode.loopMemory] at hm'
    apply load_byte_step _ p.toBitVec _ _ buf i _ _ (by ecancel) hlt (by omega)
      (by simp only [UInt64.toBitVec_ofNat', BitVec.mul_one])
    unfold_step
    step_directive hk uvarint 23
    step_directive hk uvarint 24
    step_directive hk uvarint 25
    rw [flag_z]
    have hdrop := List.drop_eq_getElem_cons hlt
    split
    · rename_i h10
      have h10' : i = 10 := by
        have := congrArg BitVec.toNat (of_decide_eq_true h10)
        rw [ofNat_toBitVec_toNat _ (by omega)] at this
        exact this
      label_address hk hf uvarint 45
      simp only [Effects.All]
      apply Decode.exit_overflow_eleven k hk ra p rsp rbp r14 buf R _ _ _ _ _ _ _ _ _ _ _ _ _ zmms _ mem hm
      rw [hdec, hdrop]
      subst h10'
      exact decodeFrom_eleventh _ _ _
    · rename_i h10
      have h10' : i ≠ 10 := by
        intro e; apply h10; subst e; rfl
      simp only [Effects.All]
      step_directive hk uvarint 26
      step_directive hk uvarint 27
      have h128 : (BitVec.truncate 8 (128 : BitVec 64)).toNat = 128 := by decide
      rw [flag_nc, Machine.zx8, h128, UInt8.toNat_toBitVec]
      have hbyte := buf[i].toNat_lt
      split
      · rename_i hb
        simp only [decide_eq_true_eq] at hb
        label_address hk hf uvarint 6
        simp only [Effects.All]
        refine Decode.continue_path k hk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ zmms _ mem i sum buf[i] (by omega) hsum
          rfl rfl rfl rfl ?_
        intro rcx' rdx' rsi' rdi' r8' r9' r10' flags' h1 h2 h3
        have hpow : 2 ^ (7 * (i + 1)) = 2 ^ (7 * i) * 128 := by
          rw [Nat.mul_succ, Nat.pow_add]
        have hpay : (buf[i].toNat - 128) * 2 ^ (7 * i) ≤ 127 * 2 ^ (7 * i) :=
          Nat.mul_le_mul_right _ (by omega)
        refine more (by omega) hlt (sum + (buf[i].toNat - 128) * 2 ^ (7 * i)) rcx' rdx' rsi' rdi' r8' r9' r10' flags'
          (by rw [hpow]; omega) ?_ h1 h2 ?_
        · rw [hdec, hdrop, decodeFrom_more _ _ _ _ (by omega) hb]
        · rw [h3, show buf[i].toNat % 128 = buf[i].toNat - 128 by omega]
      · rename_i hb
        simp only [decide_eq_true_eq, Nat.not_le] at hb
        simp only [Effects.All]
        step_directive hk uvarint 28
        step_directive hk uvarint 29
        rw [flag_nz]
        split
        · rename_i h9
          have h9' : i ≠ 9 := by
            intro e; subst e; simp at h9
          label_address hk hf uvarint 35
          simp only [Effects.All]
          refine Decode.value_path k hk ra p rsp rbp r14 buf R _ _ _ _ _ _ _ _ _ _ _ _ _ zmms _ mem hm i sum buf[i]
            (by omega) hsum rfl rfl rfl rfl ?_
          rw [hdec, hdrop, decodeFrom_last _ _ _ _ (by omega) hb (by omega)]
        · rename_i h9
          have h9' : i = 9 := by
            have := congrArg BitVec.toNat (of_decide_eq_true (by simpa using h9))
            rw [ofNat_toBitVec_toNat _ (by omega)] at this
            exact this
          simp only [Effects.All]
          step_directive hk uvarint 30
          step_directive hk uvarint 31
          have h1 : (BitVec.truncate 8 (1 : BitVec 64)).toNat = 1 := by decide
          rw [flag_be, Machine.zx8, h1, UInt8.toNat_toBitVec]
          split
          · rename_i hle1
            simp only [decide_eq_true_eq] at hle1
            label_address hk hf uvarint 35
            simp only [Effects.All]
            refine Decode.value_path k hk ra p rsp rbp r14 buf R _ _ _ _ _ _ _ _ _ _ _ _ _ zmms _ mem hm i sum buf[i]
              (by omega) hsum rfl rfl rfl rfl ?_
            rw [hdec, hdrop, decodeFrom_last _ _ _ _ (by omega) hb (by omega)]
          · rename_i hgt1
            simp only [decide_eq_true_eq, Nat.not_le] at hgt1
            simp only [Effects.All]
            apply Decode.exit_overflow_ten k hk ra p rsp rbp r14 buf R _ _ _ _ _ _ _ _ _ _ _ _ _ zmms _ mem hm
            rw [hdec, hdrop]
            subst h9'
            exact decodeFrom_tenth_large _ _ _ hb hgt1

/-- The loop from the loop head ends in the final condition, at each index `i ≤ 10`.
The proof is an induction on `10 - i`. -/
theorem Decode.loop (k : Nat) (hk : uvarint.IsInfixAt Host.prog k) (hf : LabelsFresh uvarint k)
    (ra p rsp rbp r14 : UInt64) (buf : List UInt8) (R : DataMem → Prop) (hbound : buf.length < 2 ^ 63)
    (r11 r12 r13 r15 : UInt64) (zmms : RegZmms) (mem : DataMem) (hm : Decode.loopMemory ra p rsp buf R mem) :
    ∀ (n i sum : Nat) (rcx rdx rsi rdi r8 r9 r10 : UInt64) (flags : StatusFlags),
      10 - i = n → i ≤ 10 → i ≤ buf.length → sum < 2 ^ (7 * i) →
      decode buf = decodeFrom i sum (buf.drop i) →
      rcx = UInt64.ofNat i → rdx = UInt64.ofNat (7 * i) → rsi = UInt64.ofNat sum →
      Eventually (step1 Host.exe) (Decode.finalCondition ra p rsp rbp r14 buf R)
        ⟨⟨⟨p, UInt64.ofNat buf.length, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩,
          zmms, flags, mem⟩, Host.addrOf (k + 19)⟩ := by
  intro n
  induction n with
  | zero =>
    intro i sum rcx rdx rsi rdi r8 r9 r10 flags hn hi hile hsum hdec hrcx hrdx hrsi
    exact Decode.iteration k hk hf ra p rsp rbp r14 buf R hbound rcx rdx rsi rdi r8 r9 r10 r11 r12 r13 r15 zmms
      flags mem hm i sum hi hile hsum hdec hrcx hrdx hrsi (fun h9 => absurd hn (by omega))
  | succ n ih =>
    intro i sum rcx rdx rsi rdi r8 r9 r10 flags hn hi hile hsum hdec hrcx hrdx hrsi
    exact Decode.iteration k hk hf ra p rsp rbp r14 buf R hbound rcx rdx rsi rdi r8 r9 r10 r11 r12 r13 r15 zmms
      flags mem hm i sum hi hile hsum hdec hrcx hrdx hrsi
      (fun _ hlt sum' rcx' rdx' rsi' rdi' r8' r9' r10' flags' hs hd h1 h2 h3 =>
        ih (i + 1) sum' rcx' rdx' rsi' rdi' r8' r9' r10' flags' (by omega) (by omega) (by omega) hs hd h1 h2 h3)

end Uvarint
