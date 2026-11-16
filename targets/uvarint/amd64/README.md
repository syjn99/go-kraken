# AMD64 Uvarint verification

The target uses Go 1.26.10, linux/amd64, and GOAMD64=v1.
The manifest is `manifest.json`, the artifacts use `build/`, and negative cases use `tests/negative-cases.json`.
Both architectures use the same source package and main package.

## Inputs and calling convention

The slice pointer uses rax, and its length uses rbx.
The function stores the pointer in the caller spill at rsp + 8.
The statement owns the return-address slot, the eight-byte spill, and the complete input buffer as separate regions.
The predicate R describes the remaining memory.
The buffer length must be below `2 ^ 63`.
The result uses rax for the value and rbx for the signed byte count.
RET reads the return address from the stack and increases rsp by eight.
The statement preserves rbp, r14, the input buffer, the return-address slot, and R.

## Instruction inspection

The converted function has 47 instructions, 140 bytes, six labels, and four returns.
It has no stack growth path, runtime call, data reference, or write barrier path.
The assembly is `build/norm/encoding_binary.Uvarint.S`.
The executable and symbol listing use the same names as ARM64: `build/target` and `build/target.nm`.

## Verified parts and tests

The main theorem is `Uvarint.Amd64.Decode.result`.
Its statement is `Uvarint.Amd64.Decode.result_statement`.
The theorem covers normal, incomplete, and overflow outcomes, termination, and the stated memory frame.
The witnesses prove consistent premises for buffers shorter than `2 ^ 32` bytes.
The negative cases check unchanged controls, code mutations, and statement mutations.
The differential script selects this architecture with its required `amd64` argument.
Both architectures share `Uvarint.Spec` and `Uvarint.SpecKnownAnswers`.

## Unfinished obligations

The statement does not cover vector registers, arithmetic flags, or every general register.
It does not establish the Go requirement that X15 holds zero at return.
`FINDINGS.md` records these limits and the validation commands.
