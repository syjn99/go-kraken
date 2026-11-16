import Machine.Labels
import Uvarint.Code
import Uvarint.Spec

/-!
# Statement of the main theorem of `encoding/binary.Uvarint` (statement only, no proof)

A later change needs a new name and a written reason. This definition stays.

    func Uvarint(buf []byte) (uint64, int) {
        var x uint64
        var s uint
        for i, b := range buf {
            if i == MaxVarintLen64 { return 0, -(i + 1) }
            if b < 0x80 {
                if i == MaxVarintLen64-1 && b > 1 { return 0, -(i + 1) }
                return x | uint64(b)<<s, i + 1
            }
            x |= uint64(b&0x7f) << s
            s += 7
        }
        return 0, 0
    }

Go register ABI: at entry, rax is the slice pointer, rbx the length and rcx the capacity.
At return, rax is the value and rbx is the number `n`.
The function is a leaf. It has no stack frame, no stack guard check and no call.
Its first instruction stores rax into the argument spill slot of the caller at `rsp + 8`.
It reads at most 11 bytes of the buffer and writes no other memory.
-/

open Machine Uvarint.Code
variable [Host]

namespace Uvarint

/-- The machine form of a result: the pair (rax, rbx) at return.
A value `x` of `n` bytes gives (`x`, `n`).
An incomplete buffer gives (0, 0).
An overflow after `n` bytes gives (0, the 64-bit two's complement of `-n`). -/
def Result.machineForm : Result → UInt64 × UInt64
  | .value x n => (x, UInt64.ofNat n)
  | .incomplete => (0, 0)
  | .overflow n => (0, UInt64.ofInt (-(n : Int)))

/-- **Main theorem of `encoding/binary.Uvarint`, all three results in one statement.**

The statement quantifies over the place `k` of the code in a host program with fresh labels.
It also quantifies over the entry state `s`, the return address `ra` and the buffer `buf`.
The old spill slot bytes `spill` and the frame `R` are free too.
Every execution from the entry returns to `ra`.
At return, (rax, rbx) is the machine form of `Uvarint.decode buf`.
`rsp` is the entry `rsp + 8`, and `rbp` and `r14` are unchanged.
The spill slot holds the entry rax. The buffer, the return address and `R` are unchanged.

Premises:
- `hk`, `hf`: the code sits at index `k`, and no label of the code occurs before index `k`.
- `hspill`: the spill slot has 8 bytes. Its old content is free.
- `h_mem`: the memory is the return address at `rsp`, the spill slot at `rsp + 8`,
  the buffer at the address in rax, and the frame `R`, all separate.
- `hlength`: rbx holds the buffer length (Go register ABI).
- `hbound`: the length is below `2 ^ 63`. A Go length is a non-negative `int`.
  The code compares the length with the index as signed numbers (`cmp %rcx,%rbx; jle`).

There is no runtime contract. The function has no call instruction. -/
def Decode.result_statement : Prop :=
  ∀ (k : Nat) (hk : uvarint.IsInfixAt Host.prog k) (hf : LabelsFresh uvarint k)
    (s : MachineData) (ra : UInt64) (buf spill : List UInt8) (hspill : spill.length = 8)
    (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (spill.At (s.regs.rsp.toBitVec + 8)) ⋆ Eq (buf.At s.regs.rax.toBitVec) ⋆ R)
    (hlength : s.regs.rbx = UInt64.ofNat buf.length) (hbound : buf.length < 2 ^ 63),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec
        ∧ (st.data.regs.rax, st.data.regs.rbx) = (decode buf).machineForm
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14
        ∧ (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq (buf.At s.regs.rax.toBitVec) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩

end Uvarint
