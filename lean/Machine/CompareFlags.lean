import Machine.Step

/-!
# Branch conditions after `cmp`

New in go-kraken. Kraken computes `cmp b, a` as the flags of `a - b`.
Each lemma turns one condition code of these flags into a comparison of the operands.
The operands are free, so the lemmas hold at every width.
-/

namespace Machine

/-- The carry flag of `cmp` is the unsigned borrow. -/
theorem sub_borrow {w : Nat} (a b : BitVec w) :
    (BitVec.unsigned (a - b) != a.unsigned - b.unsigned) = decide (a.toNat < b.toNat) := by
  rw [Bool.eq_iff_iff, bne_iff_ne, decide_eq_true_eq]
  simp only [BitVec.unsigned]
  constructor
  · intro hne
    apply Classical.byContradiction
    intro h
    apply hne
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; omega)]
    omega
  · intro hlt heq
    omega

/-- The zero flag of `cmp` is the equality of the operands. -/
theorem sub_zero_beq {w : Nat} (a b : BitVec w) : ((a - b) == BitVec.zero w) = decide (a = b) := by
  by_cases h : a = b
  · subst h; simp [BitVec.zero]
  · have : a - b ≠ 0#w := by
      intro h0
      apply h
      have := BitVec.sub_add_cancel a b
      rw [h0, BitVec.zero_add] at this
      exact this.symm
    simp [BitVec.zero, h, this]

/-- `cmp b, a; jae` (no carry) is taken when `b ≤ a` (unsigned). -/
theorem flag_nc {w : Nat} (a b : BitVec w) (af of' : Bool) :
    CondCode.nc.interp (StatusFlags.from_result (a - b)
      { cf := BitVec.unsigned (a - b) != a.unsigned - b.unsigned, af := af, of := of' })
      = decide (b.toNat ≤ a.toNat) := by
  simp only [CondCode.interp, StatusFlags.from_result, sub_borrow]
  by_cases h : b.toNat ≤ a.toNat <;> simp [h] <;> omega

/-- `cmp b, a; je` is taken when `a = b`. -/
theorem flag_z {w : Nat} (a b : BitVec w) (f : StatusFlags.from_result.Remaining) :
    CondCode.z.interp (StatusFlags.from_result (a - b) f) = decide (a = b) := by
  simp only [CondCode.interp, StatusFlags.from_result, sub_zero_beq]

/-- `cmp b, a; jne` is taken when `a ≠ b`. -/
theorem flag_nz {w : Nat} (a b : BitVec w) (f : StatusFlags.from_result.Remaining) :
    CondCode.nz.interp (StatusFlags.from_result (a - b) f) = !decide (a = b) := by
  simp only [CondCode.interp, StatusFlags.from_result, sub_zero_beq]

/-- `cmp b, a; jbe` is taken when `a ≤ b` (unsigned). -/
theorem flag_be {w : Nat} (a b : BitVec w) (af of' : Bool) :
    CondCode.be.interp (StatusFlags.from_result (a - b)
      { cf := BitVec.unsigned (a - b) != a.unsigned - b.unsigned, af := af, of := of' })
      = decide (a.toNat ≤ b.toNat) := by
  simp only [CondCode.interp, StatusFlags.from_result, sub_borrow, sub_zero_beq]
  by_cases h : a = b
  · subst h; simp
  · have : a.toNat ≠ b.toNat := fun e => h (BitVec.eq_of_toNat_eq e)
    by_cases h2 : a.toNat < b.toNat <;> simp [h, h2] <;> omega

/-- `cmp b, a; jle` for two operands below `2 ^ 63`. Here the signed order and the unsigned order agree. -/
theorem flag_le (a b : BitVec 64) (cf af : Bool) (ha : a.toNat < 2 ^ 63) (hb : b.toNat < 2 ^ 63) :
    CondCode.le.interp (StatusFlags.from_result (a - b)
      { cf := cf, af := af, of := BitVec.toInt (a - b) != a.toInt - b.toInt })
      = decide (a.toNat ≤ b.toNat) := by
  have ta : a.toInt = a.toNat := BitVec.toInt_eq_toNat_of_lt (by omega)
  have tb : b.toInt = b.toNat := BitVec.toInt_eq_toNat_of_lt (by omega)
  have hs : (a - b).toInt = (a.toNat : Int) - b.toNat := by
    rw [BitVec.toInt_sub, ta, tb]; apply Int.bmod_eq_of_le <;> omega
  simp only [CondCode.interp, StatusFlags.from_result, sub_zero_beq, hs, ta, tb, bne_self_eq_false,
    Bool.bne_false]
  by_cases h : a = b
  · subst h; simp
  · have hne : a.toNat ≠ b.toNat := fun e => h (BitVec.eq_of_toNat_eq e)
    rw [BitVec.msb_eq_decide, BitVec.toNat_sub]
    by_cases h2 : a.toNat < b.toNat
    · have : 2 ^ 63 ≤ (2 ^ 64 - b.toNat + a.toNat) % 2 ^ 64 := by
        rw [Nat.mod_eq_of_lt (by omega)]; omega
      simp [h, this]; omega
    · have : (2 ^ 64 - b.toNat + a.toNat) % 2 ^ 64 < 2 ^ 63 := by
        rw [show 2 ^ 64 - b.toNat + a.toNat = (a.toNat - b.toNat) + 2 ^ 64 by omega, Nat.add_mod_right,
          Nat.mod_eq_of_lt (by omega)]; omega
      simp [h]; omega

/-- `cmp b, a; sbb x, x` with a borrow (`a < b`, unsigned) gives all ones. Go uses it as a shift mask. -/
theorem sbb_self_after_borrow (x a b : BitVec 64) (af of' : Bool) (h : a.toNat < b.toNat) :
    x - x - BitVec.ofNat 64 (StatusFlags.from_result (a - b)
      { cf := BitVec.unsigned (a - b) != a.unsigned - b.unsigned, af := af, of := of' }).cf.toNat
      = BitVec.allOnes 64 := by
  simp only [StatusFlags.from_result, sub_borrow, h, decide_true, Bool.toNat_true, BitVec.sub_self,
    BitVec.zero_sub]
  exact BitVec.neg_one_eq_allOnes

end Machine
