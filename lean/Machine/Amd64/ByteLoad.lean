import Machine.Amd64.Step

/-!
# A load of one byte from inside a separate block

This file is not in the reference.
A loop that reads `buf[i]` loads one byte from the middle of the block `buf`.
The lemma splits the block around byte `i` and applies `load_step_at`.
-/

namespace Machine.Amd64

/-- The block `buf` at `p` is its first `i` bytes, its byte `i` and the rest. -/
theorem block_split_byte (buf : List UInt8) (p : BitVec 64) (i : Nat) (hi : i < buf.length)
    (hlen : buf.length ≤ 2 ^ 64) :
    Eq (buf.At p) = Eq ((buf.take i).At p) ⋆ Eq ([buf[i]].At (p + BitVec.ofNat 64 i))
      ⋆ Eq ((buf.drop (i + 1)).At (p + BitVec.ofNat 64 i + BitVec.ofNat 64 1)) := by
  have e : buf = buf.take i ++ ([buf[i]] ++ buf.drop (i + 1)) := by
    rw [List.singleton_append, List.getElem_cons_drop, List.take_append_drop]
  have l1 : (buf.take i).length = i := by simp only [List.length_take]; omega
  have s1 : (buf.take i).length + ([buf[i]] ++ buf.drop (i + 1)).length ≤ 2 ^ 64 := by
    simp only [List.length_append, List.length_take, List.length_singleton, List.length_drop]; omega
  have s2 : [buf[i]].length + (buf.drop (i + 1)).length ≤ 2 ^ 64 := by
    simp only [List.length_singleton, List.length_drop]; omega
  conv => lhs; rw [e]
  rw [Mem.At_append_sep _ _ _ s1, Mem.At_append_sep _ _ _ s2, l1, List.length_singleton, Std.ExtHashMap.sep_assoc]

/-- `Int.ofBytes` of one byte, read back at width 8, is the byte. -/
theorem ofInt_ofBytes_singleton (b : UInt8) : BitVec.ofInt 8 (Int.ofBytes [b]) = b.toBitVec := by
  apply BitVec.eq_of_toNat_eq
  simp only [Int.ofBytes, List.foldr_cons, List.foldr_nil, Int.zero_mul, Int.zero_add, BitVec.toNat_ofInt]
  have := b.toNat_lt
  simp only [UInt8.toNat_toBitVec]
  omega

/-- Load byte `i` of the block `buf` at `p`. The value is `buf[i]`, and the memory does not change. -/
theorem load_byte_step (s : MachineData) (p addr : BitVec 64) (ret : Width.W8.type → MachineData → Effects)
    (buf : List UInt8) (i : Nat) (F : DataMem → Prop) (post : MachineState → Prop)
    (H : (Eq (buf.At p) ⋆ F) s.dmem) (hi : i < buf.length) (hlen : buf.length ≤ 2 ^ 64)
    (he : addr = p + BitVec.ofNat 64 i)
    (k : (ret buf[i].toBitVec s).All post) :
    (MachineData.load s addr .W8 ret).All post := by
  rw [block_split_byte buf p i hi hlen] at H
  have H' : (Eq ([buf[i]].At (p + BitVec.ofNat 64 i))
      ⋆ (Eq ((buf.take i).At p) ⋆ Eq ((buf.drop (i + 1)).At (p + BitVec.ofNat 64 i + BitVec.ofNat 64 1)) ⋆ F))
      s.dmem := by
    simp only [Std.ExtHashMap.sep_assoc] at H ⊢
    rw [Std.ExtHashMap.sep_comm_l]
    exact H
  apply load_step_at s addr _ .W8 ret [buf[i]] _ post he H' rfl
  show (ret (BitVec.ofInt 8 (Int.ofBytes [buf[i]])) s).All post
  rw [ofInt_ofBytes_singleton]
  exact k

end Machine.Amd64
