-- Source: reference commit 320929dd, fv/kraken/lean/Machine/Flags.lean (only the lemmas that do not name an SSZ layout).
import Machine.Step

/-! Branch-condition lemmas stated once, so the kernel does not re-check
arithmetic on 64-bit literals at every use (`simp` + `omega` proof terms with
literals near 2^64 make the kernel report deep recursion). -/

namespace Machine

theorem toNat_add_neg8 (x : BitVec 64) (h : 8 ≤ x.toNat) : (x + -8).toNat = x.toNat - 8 := by
  rw [← BitVec.sub_eq_add_neg, BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simpa using h)]; rfl

/-- `cmp b, a; jbe` is not taken when `b < a` (unsigned). -/
theorem cmp_be_false (a b : BitVec 64) (af of' : Bool) (h : b.toNat < a.toNat) :
    CondCode.be.interp (StatusFlags.from_result (a - b)
      { cf := BitVec.unsigned (a - b) != a.unsigned - b.unsigned, af := af, of := of' }) = false := by
  have hle : b ≤ a := by rw [BitVec.le_def]; omega
  have hs : (a - b).toNat = a.toNat - b.toNat := BitVec.toNat_sub_of_le hle
  have hz : a - b ≠ 0#64 := by
    intro h0; have := congrArg BitVec.toNat h0; rw [hs] at this; simp at this; omega
  simp only [CondCode.interp, StatusFlags.from_result, BitVec.unsigned, hs]
  simp [hz]; omega

theorem toNat_add_neg4 (x : BitVec 64) (h : 4 ≤ x.toNat) : (x + -4).toNat = x.toNat - 4 := by
  rw [← BitVec.sub_eq_add_neg, BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simpa using h)]; rfl

theorem ret_slot (x : BitVec 64) : x - 8 + 8#64 = x := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.ofNat_eq_ofNat]
  omega

end Machine
