import Uvarint.Spec

/-!
# Known answers of the specification

Each example checks `Uvarint.decode` on one fixed buffer.
The expected values come from the format, not from the definition.
-/

namespace Uvarint

/-- The empty buffer holds no complete value. -/
example : decode [] = .incomplete := by decide

/-- One byte with the top bit clear is the value itself. -/
example : decode [0x00] = .value 0 1 := by decide

example : decode [0x01] = .value 1 1 := by decide

/-- The example of the protocol buffers documentation: 300 is `AC 02`. -/
example : decode [0xAC, 0x02] = .value 300 2 := by decide

/-- A byte with the top bit set needs one more byte. -/
example : decode [0x80] = .incomplete := by decide

/-- The largest 64-bit value has ten bytes. -/
example : decode (List.replicate 9 0xFF ++ [0x01]) = .value 0xFFFFFFFFFFFFFFFF 10 := by decide

/-- The tenth byte can only be 0 or 1. The value 2 gives bit 64. -/
example : decode (List.replicate 9 0xFF ++ [0x02]) = .overflow 10 := by decide

/-- An eleventh byte is an overflow, also when that byte ends the value. -/
example : decode (List.replicate 10 0x80 ++ [0x00]) = .overflow 11 := by decide

/-- Ten bytes with the top bit set and no more bytes are an incomplete value. -/
example : decode (List.replicate 10 0x80) = .incomplete := by decide

end Uvarint
