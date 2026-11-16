import Uvarint.Amd64.DecodeLoop

/-!
# Main theorem of `encoding/binary.Uvarint`

The entry is directives 0 to 5 of `Uvarint.Code.uvarint`:

    encoding_binary.Uvarint:
      mov %rax,0x8(%rsp)    // spill the buffer pointer
      xor %ecx,%ecx         // i = 0
      xor %edx,%edx         // shift = 0
      xor %esi,%esi         // sum = 0
      jmp L_33              // loop head

Then `Decode.loop` at the index 0 gives the conclusion.
-/

open Machine Uvarint.Code
variable [Host]

namespace Uvarint

/-- **Main theorem of `encoding/binary.Uvarint`**: the machine code returns the machine form of
`Uvarint.decode buf` for each buffer below `2 ^ 63` bytes. The statement is `Decode.result_statement`. -/
theorem Decode.result : Decode.result_statement := by
  intro k hk hf s ra buf spill hspill R h_mem hlength hbound
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hlength ⊢
  subst hlength
  step_directive hk uvarint 0
  step_directive hk uvarint 1
  apply store_step_at _ _ (rsp.toBitVec + 8) _ _ _ spill _ _ (by bv_omega) (by ecancel) (by exact hspill)
  intro m1 H1
  simp only [Width.bytes, Width.bits] at H1
  unfold_step
  step_directive hk uvarint 2
  intro _
  step_directive hk uvarint 3
  intro _
  step_directive hk uvarint 4
  intro _
  step_directive hk uvarint 5
  label_address hk hf uvarint 19
  have hm : Decode.loopMemory ra rax rsp buf R m1 := by
    simp only [Decode.loopMemory]
    ecancel
  exact Decode.loop k hk hf ra rax rsp rbp r14 buf R hbound r11 r12 r13 r15 zmms m1 hm 10 0 0 _ _ _ _ _ _ _ _
    rfl (by omega) (by omega) (by decide) rfl (by rw [xor_self_zero]; rfl) (by rw [xor_self_zero]; rfl)
    (by rw [xor_self_zero]; rfl)

end Uvarint
