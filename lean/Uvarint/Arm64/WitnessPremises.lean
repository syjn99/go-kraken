module
public import Uvarint.Arm64.Witness

@[expose] public section

namespace Uvarint.Arm64.Witness

/-- The caller owns the input and spill. The frame owns the saved-link slot and the trailing bytes. -/
theorem witness_mem (buf : List UInt8) (hlen : buf.length < 2 ^ 32) :
    (Eq ((zeros 8).At ((initial buf).regs.SP.toBitVec + 8)) ⋆
      Eq (buf.At (initial buf).regs.X0.toBitVec) ⋆ frame buf) (initial buf).dmem := by
  have h : Eq ((block buf).At (0x10000 : BitVec 64)) (initial buf).dmem := rfl
  simp only [block] at h
  rw [Mem.At_append_sep _ _ _ (by simp [zeros]; omega),
    Mem.At_append_sep _ _ _ (by simp [zeros]; omega),
    Mem.At_append_sep _ _ _ (by simp [zeros]; omega)] at h
  simp only [List.length_replicate, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at h
  simp only [initial, frame, UInt64.toBitVec_ofNat, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at h ⊢
  simpa only [Std.ExtHashMap.sep_assoc, Std.ExtHashMap.sep_comm_l] using h

/-- These witnesses satisfy every entry premise of the complete result statement. -/
theorem premises_hold (buf : List UInt8) (hlen : buf.length < 2 ^ 32) :
    let s := initial buf
    (zeros 8).length = 8 ∧ s.regs.X1 = UInt64.ofNat buf.length ∧
    buf.length ≤ s.regs.X2.toNat ∧ s.regs.X2.toNat < 2 ^ 63 ∧
    s.regs.X0.toNat + buf.length ≤ 2 ^ 64 ∧
    s.regs.SP.toNat % 16 = 0 ∧ s.regs.SP.toNat + 16 ≤ 2 ^ 64 ∧
    s.regs.X30.toNat % 4 = 0 ∧
    (Eq ((zeros 8).At (s.regs.SP.toBitVec + 8)) ⋆ Eq (buf.At s.regs.X0.toBitVec) ⋆ frame buf) s.dmem := by
  have hn : (UInt64.ofNat buf.length).toNat = buf.length := by
    rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
  refine ⟨rfl, rfl, ?_, ?_, ?_, by change (65536 : Nat) % 16 = 0; decide, ?_, by change (262144 : Nat) % 4 = 0; decide, witness_mem buf hlen⟩
  · simp only [initial, hn]; omega
  · simp only [initial, hn]; omega
  · change 0x10010 + buf.length ≤ 2 ^ 64
    omega
  · change (65536 : Nat) + 16 ≤ 2 ^ 64
    decide

end Uvarint.Arm64.Witness
