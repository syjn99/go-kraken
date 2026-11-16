-- Source: reference commit 320929dd, fv/kraken/lean/Machine/Frame.lean (only `at_app`, not the 144-byte frame layout).
import Machine.Bytes

/-! A byte block at one address is the separating conjunction of its two parts. -/

namespace Machine

theorem at_app {a : BitVec 64} {b : BitVec 64} (l1 l2 : List UInt8) (h : b = a + BitVec.ofNat 64 l1.length)
    (hl : l1.length + l2.length ≤ 2 ^ 64) :
    Eq ((l1 ++ l2).At a) = Eq (l1.At a) ⋆ Eq (l2.At b) := by
  rw [Mem.At_append_sep _ _ _ hl, h]

end Machine
