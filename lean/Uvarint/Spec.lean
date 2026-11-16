/-!
# Specification of the unsigned variable-length integer decoder

This file is the assumed input of the pilot target. The framework does not prove it. A reviewer reads it.

The format is the base-128 encoding of protocol buffers and of Go `encoding/binary`.
Each byte holds 7 payload bits. The first byte holds the least significant bits.
A byte with the top bit set says that one more byte follows. A 64-bit value has at most 10 bytes.

The three results follow the documentation of `encoding/binary.Uvarint` (Go 1.26.10):
a value with the number of bytes read, a buffer that is too small, or a value that is larger than 64 bits.
The definition adds payload groups as natural numbers. It does not use shifts or bit operations.
-/

namespace Uvarint

/-- The result of a decode. -/
inductive Result where
  /-- The first `bytesRead` bytes hold the complete value `x`. -/
  | value (x : UInt64) (bytesRead : Nat)
  /-- The buffer ends before the last byte of the value. -/
  | incomplete
  /-- The value is larger than 64 bits. The decoder examined `bytesRead` bytes. -/
  | overflow (bytesRead : Nat)
  deriving DecidableEq, Repr

/-- The largest number of bytes of an encoded 64-bit value. -/
def maxLength : Nat := 10

/--
Decode the rest of a buffer. `index` is the number of bytes already read.
`sum` is the value of their payload groups.
-/
def decodeFrom (index : Nat) (sum : Nat) : List UInt8 → Result
  | [] => .incomplete
  | b :: rest =>
    if index = maxLength then .overflow (index + 1)
    else if b < 0x80 then
      if index = maxLength - 1 ∧ 1 < b then .overflow (index + 1)
      else .value (UInt64.ofNat (sum + b.toNat * 2 ^ (7 * index))) (index + 1)
    else decodeFrom (index + 1) (sum + (b.toNat - 128) * 2 ^ (7 * index)) rest

/-- Decode an unsigned variable-length integer from the start of `buf`. -/
def decode (buf : List UInt8) : Result := decodeFrom 0 0 buf

end Uvarint
