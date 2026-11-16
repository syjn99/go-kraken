encoding_binary.Uvarint:
  str x0, [sp,#8]
  mov x2, xzr
  mov x3, xzr
  mov x4, xzr
  b L_encoding_binary.Uvarint_34
L_encoding_binary.Uvarint_14:
  and x5, x5, #0x7f
  lsl x5, x5, x3
  add x2, x2, #0x1
  add x6, x3, #0x7
  cmp x3, #0x40
  csel x5, x5, xzr, cc
  orr x4, x4, x5
  mov x3, x6
L_encoding_binary.Uvarint_34:
  cmp x1, x2
  b.le L_encoding_binary.Uvarint_94
  ldrb w5, [x0,x2]
  cmp x2, #0xa
  b.eq L_encoding_binary.Uvarint_88
  mov x6, x5
  cmp w6, #0x80
  b.cs L_encoding_binary.Uvarint_14
  cmp x2, #0x9
  b.ne L_encoding_binary.Uvarint_70
  cmp w6, #0x1
  b.ls L_encoding_binary.Uvarint_70
  mov x0, xzr
  mov x1, #0xfffffffffffffff6
  ret
L_encoding_binary.Uvarint_70:
  lsl x5, x5, x3
  add x1, x2, #0x1
  cmp x3, #0x40
  csel x2, x5, xzr, cc
  orr x0, x4, x2
  ret
L_encoding_binary.Uvarint_88:
  mov x0, xzr
  mov x1, #0xfffffffffffffff5
  ret
L_encoding_binary.Uvarint_94:
  mov x0, xzr
  mov x1, xzr
  ret
