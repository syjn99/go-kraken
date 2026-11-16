encoding_binary.Uvarint:
  mov %rax,0x8(%rsp)
  xor %ecx,%ecx
  xor %edx,%edx
  xor %esi,%esi
  jmp L_encoding_binary.Uvarint_33
L_encoding_binary.Uvarint_d:
  and $0x7f,%edi
  mov %rcx,%r8
  mov %rdx,%rcx
  shl %cl,%rdi
  inc %r8
  lea 0x7(%rcx),%r9
  cmp $0x40,%rcx
  sbb %r10,%r10
  and %r10,%rdi
  or %rdi,%rsi
  mov %r8,%rcx
  mov %r9,%rdx
L_encoding_binary.Uvarint_33:
  cmp %rcx,%rbx
  jle L_encoding_binary.Uvarint_87
  movzbl (%rax,%rcx,1),%edi
  nop
  cmp $0xa,%rcx
  je L_encoding_binary.Uvarint_7d
  cmp $0x80,%dil
  jae L_encoding_binary.Uvarint_d
  cmp $0x9,%rcx
  jne L_encoding_binary.Uvarint_62
  cmp $0x1,%dil
  jbe L_encoding_binary.Uvarint_62
  xor %eax,%eax
  mov $-0xa,%rbx
  retq
L_encoding_binary.Uvarint_62:
  mov %rcx,%rax
  mov %rdx,%rcx
  shl %cl,%rdi
  lea 0x1(%rax),%rbx
  cmp $0x40,%rcx
  sbb %rax,%rax
  and %rdi,%rax
  or %rsi,%rax
  retq
L_encoding_binary.Uvarint_7d:
  xor %eax,%eax
  mov $-0xb,%rbx
  retq
L_encoding_binary.Uvarint_87:
  xor %eax,%eax
  xor %ebx,%ebx
  retq
