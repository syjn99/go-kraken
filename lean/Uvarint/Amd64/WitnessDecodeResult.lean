import Uvarint.Amd64.DecodeResult
import Uvarint.SpecKnownAnswers
import Machine.Amd64.WitnessHost

/-!
# Witnesses of `Uvarint.Amd64.Decode.result`

The host holds only the real `encoding/binary.Uvarint`, at the index 0. Its directive `i` is at `0x10000 + i`.
The memory is one block at `0x10000`. The block holds these parts:
- the return slot: rsp is `0x10000`, and the return address is 0,
- the spill slot at rsp + 8, with old bytes of value zero,
- the buffer at `0x10010`, which is the value of rax,
- 8 more bytes. The frame `R` is these 8 bytes.

`premises_hold` shows that this state satisfies each premise of the main theorem, for each buffer below `2 ^ 32` bytes.
The theorems `runs_empty`, `runs_one_byte` and `runs_maximum` apply the main theorem to three buffers.
Each theorem gives the concrete result registers.
`runs_maximum` uses the largest value, not the largest buffer.
-/

open Machine.Amd64 Machine.Amd64.Witness Uvarint.Amd64.Code

namespace Uvarint.Amd64.Witness.DecodeResult

def program : Program := uvarint

theorem program_length : program.length = 53 := by rfl

instance host : Host := mkHost program (by rw [program_length]; decide)

theorem placed_at_0 : uvarint.IsInfixAt Host.prog 0 := ⟨[], by simp [Host.prog, program]⟩

theorem labels_fresh_at_0 : LabelsFresh uvarint 0 := fun _ hi => absurd hi (Nat.not_lt_zero _)

abbrev zeros (k : Nat) : List UInt8 := List.replicate k 0

/-- The return slot with the return address 0, the spill slot, the buffer and 8 bytes of the frame. -/
def block (buf : List UInt8) : List UInt8 :=
  Int.toBytes 8 (0 : UInt64).toBitVec.toInt ++ (zeros 8 ++ (buf ++ zeros 8))

def mem (buf : List UInt8) : DataMem := (block buf).At (0x10000 : BitVec 64)

def initial_state (buf : List UInt8) (zmms : RegZmms) (flags : StatusFlags) : MachineData :=
  ⟨⟨0x10010, UInt64.ofNat buf.length, 0, 0, 0, 0, 0x10000, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, zmms, flags, mem buf⟩

/-- The frame `R` of the witness: the 8 bytes after the buffer, and no other byte. -/
def frame_rest (buf : List UInt8) : DataMem → Prop :=
  Eq ((zeros 8).At ((0x10010 : BitVec 64) + BitVec.ofNat 64 buf.length))

/-- The memory premise of the main theorem holds on the witness state. -/
theorem witness_mem (buf : List UInt8) (hlen : buf.length < 2 ^ 32) (zmms : RegZmms) (flags : StatusFlags) :
    let s := initial_state buf zmms flags
    s.dmem =⋆ Eq ((Int.toBytes 8 (0 : UInt64).toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq ((zeros 8).At (s.regs.rsp.toBitVec + 8)) ⋆ Eq (buf.At s.regs.rax.toBitVec) ⋆ frame_rest buf := by
  intro s
  have H : Eq ((block buf).At (0x10000 : BitVec 64)) (mem buf) := rfl
  simp only [block] at H
  rw [Mem.At_append_sep _ _ _ (by simp only [List.length_append, Int.toBytes_length, List.length_replicate]; omega),
    Mem.At_append_sep _ _ _ (by simp only [List.length_append, List.length_replicate]; omega),
    Mem.At_append_sep _ _ _ (by simp only [List.length_replicate]; omega)] at H
  simp only [Int.toBytes_length, List.length_replicate, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd,
    uint64_toBitVec_zero] at H
  simp only [s, initial_state, frame_rest, UInt64.toBitVec_ofNat, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd]
  simpa only [Std.ExtHashMap.sep_assoc] using H

/-- **The premises of `Decode.result_statement` are consistent.** For each buffer below `2 ^ 32` bytes,
the witness host and state satisfy each premise. -/
theorem premises_hold (buf : List UInt8) (hlen : buf.length < 2 ^ 32) (zmms : RegZmms) (flags : StatusFlags) :
    let s := initial_state buf zmms flags
    uvarint.IsInfixAt Host.prog 0 ∧ LabelsFresh uvarint 0 ∧ (zeros 8).length = 8
      ∧ (s.dmem =⋆ Eq ((Int.toBytes 8 (0 : UInt64).toBitVec.toInt).At s.regs.rsp.toBitVec)
        ⋆ Eq ((zeros 8).At (s.regs.rsp.toBitVec + 8)) ⋆ Eq (buf.At s.regs.rax.toBitVec) ⋆ frame_rest buf)
      ∧ s.regs.rbx = UInt64.ofNat buf.length ∧ buf.length < 2 ^ 63 :=
  ⟨placed_at_0, labels_fresh_at_0, rfl, witness_mem buf hlen zmms flags, rfl, by omega⟩

/-- The main theorem on the witness: the result registers are the machine form of `decode buf`. -/
theorem runs (buf : List UInt8) (hlen : buf.length < 2 ^ 32) (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec
        ∧ (st.data.regs.rax, st.data.regs.rbx) = (decode buf).machineForm ∧ st.data.regs.rsp = 0x10008)
      ⟨initial_state buf zmms flags, Host.addrOf 0⟩ :=
  eventually_weaken _ _ _ _ (fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩)
    (Decode.result 0 placed_at_0 labels_fresh_at_0 (initial_state buf zmms flags) 0 buf (zeros 8) rfl
      (frame_rest buf) (witness_mem buf hlen zmms flags) rfl (by omega))

/-- The empty buffer: rax = 0 and rbx = 0 (incomplete). -/
theorem runs_empty (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0)
      ⟨initial_state [] zmms flags, Host.addrOf 0⟩ :=
  eventually_weaken _ _ _ _ (fun _ h => by
      have e := h.2.1
      rw [show decode [] = .incomplete by decide] at e
      simp only [Result.machineForm, Prod.mk.injEq] at e
      exact ⟨h.1, e.1, e.2⟩)
    (runs [] (by decide) zmms flags)

/-- The buffer `[0x01]`: rax = 1 and rbx = 1. -/
theorem runs_one_byte (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rax = 1 ∧ st.data.regs.rbx = 1)
      ⟨initial_state [0x01] zmms flags, Host.addrOf 0⟩ :=
  eventually_weaken _ _ _ _ (fun _ h => by
      have e := h.2.1
      rw [show decode [0x01] = .value 1 1 by decide] at e
      simp only [Result.machineForm, Prod.mk.injEq] at e
      exact ⟨h.1, e.1, e.2⟩)
    (runs [0x01] (by decide) zmms flags)

/-- Ten bytes `0xFF ×9, 0x01`, the largest value: rax = 2 ^ 64 - 1 and rbx = 10. -/
theorem runs_maximum (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rax = 0xFFFFFFFFFFFFFFFF
        ∧ st.data.regs.rbx = 10)
      ⟨initial_state (List.replicate 9 0xFF ++ [0x01]) zmms flags, Host.addrOf 0⟩ :=
  eventually_weaken _ _ _ _ (fun _ h => by
      have e := h.2.1
      rw [show decode (List.replicate 9 0xFF ++ [0x01]) = .value 0xFFFFFFFFFFFFFFFF 10 by decide] at e
      simp only [Result.machineForm, Prod.mk.injEq] at e
      exact ⟨h.1, e.1, e.2⟩)
    (runs (List.replicate 9 0xFF ++ [0x01]) (by decide) zmms flags)

end Uvarint.Amd64.Witness.DecodeResult
