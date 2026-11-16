import Machine.Step

/-!
# Shift and byte facts of the `Uvarint` code

The loop shifts the payload of byte `i` left by `7 * i` and joins it to the sum with `or`.
These lemmas give the shift count, the payload values and the `or` as an addition.
-/

namespace Uvarint

/-- `shl %cl` with `rcx = 7 * i` and `i ≤ 9`: the masked count is `7 * i`. -/
theorem shift_count (i : Nat) (hi : i ≤ 9) :
    (BitVec.extractLsb' 0 8 (UInt64.ofNat (7 * i)).toBitVec).toNat &&& 63 = 7 * i := by
  rw [show (63 : Nat) = 2 ^ 6 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  simp only [BitVec.extractLsb'_toNat, UInt64.toNat_toBitVec, UInt64.toNat_ofNat', Nat.shiftRight_zero]
  omega

/-- `movzbl` of byte `b`: the register value is the byte value. -/
theorem zero_extend_byte_toNat (b : UInt8) :
    (BitVec.zeroExtend 64 (BitVec.zeroExtend 32 b.toBitVec)).toNat = b.toNat := by
  have := b.toNat_lt
  simp only [BitVec.toNat_setWidth, UInt8.toNat_toBitVec]
  omega

/-- `and $0x7f, %edi` after `movzbl` of byte `b`: the value is the low 7 bits of `b`. -/
theorem low_seven_toNat (b : UInt8) :
    (BitVec.zeroExtend 64 (BitVec.extractLsb' 0 32 (BitVec.zeroExtend 64 (BitVec.zeroExtend 32 b.toBitVec))
      &&& BitVec.truncate 32 (127 : BitVec 64))).toNat = b.toNat % 128 := by
  have := b.toNat_lt
  have e : (BitVec.truncate 32 (127 : BitVec 64)).toNat = 2 ^ 7 - 1 := by decide
  simp only [BitVec.toNat_setWidth, BitVec.toNat_and, BitVec.extractLsb'_toNat, UInt8.toNat_toBitVec,
    Nat.shiftRight_zero, e, Nat.and_two_pow_sub_one_eq_mod]
  omega

/-- A value shifted left by `c` and a sum below `2 ^ c` have no common bit.
So their `or` is their sum, modulo `2 ^ 64`. -/
theorem shiftLeft_or_ofNat (z : BitVec 64) (c sum : Nat) (hsum : sum < 2 ^ c) :
    (z <<< c) ||| BitVec.ofNat 64 sum = BitVec.ofNat 64 (sum + z.toNat * 2 ^ c) := by
  have hand : (z <<< c) &&& BitVec.ofNat 64 sum = 0#64 := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ofNat]
    by_cases hjc : j < c
    · simp [hjc]
    · have : sum.testBit j = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hsum (Nat.pow_le_pow_right (by omega) (by omega)))
      simp [this]
  rw [← BitVec.add_eq_or_of_and_eq_zero _ _ hand]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  rw [Nat.add_comm sum (z.toNat * 2 ^ c), Nat.add_mod (z.toNat * 2 ^ c) sum]

end Uvarint
