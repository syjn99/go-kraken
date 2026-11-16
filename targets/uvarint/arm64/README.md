# ARM64 Uvarint attempt

The build and byte linkage pass for Go 1.26.10, linux/arm64, GOARM64=v8.0.
The complete result statement has no proof yet.
`FINDINGS.md` records the unfinished obligations and the validation results.

## Inputs and calling convention

The manifest is `../manifest-arm64.json`.
The artifacts are in `../build-arm64/`.
Both architectures use the same source package and main package.
The Go image, Kraken commit, and Lean version remain pinned.

The pinned image contains the calling convention in `/usr/local/go/src/cmd/compile/abi-internal.md`, section `arm64 architecture`.
Go ABIInternal means the internal Go calling convention.
The slice arguments use x0 for the pointer, x1 for the length, and x2 for the capacity.
The results use x0 for the value and x1 for the signed byte count.
The return address uses x30, the link register.
RET branches through x30 and keeps sp unchanged.

The statement requires these entry conditions:

- The buffer length equals x1 and does not exceed x2.
- The capacity is below `2 ^ 63`.
- The buffer address plus its length does not exceed `2 ^ 64`.
- The stack pointer has 16-byte alignment, and `sp + 16` does not exceed `2 ^ 64`.
- The return address has four-byte alignment.
- The caller owns eight spill bytes at `sp + 8` and the complete input buffer.
- The spill and input regions are separate. The predicate R describes every other memory byte.

The conclusion requires termination, the specified results, unchanged sp, and unchanged x7 through x30.
The spill contains the entry pointer. The complete input and R remain unchanged.
The statement does not claim preservation of the arithmetic flags.
Kraken does not model ARM64 floating-point or vector registers in this machine state.
The statement therefore does not cover their preservation.

The executable uses the ELF entry address `0x8d090`, four-byte instructions, and zero-byte labels.
This statement concerns the function alone at that address.
A placement theorem for an arbitrary host remains unfinished.

## Instruction inspection

The function has 40 instructions, 160 bytes, six labels, and four returns.
The offset is relative to `0x8d090`.
The converter generates each instruction and each label from Go objdump.
The table lists every emitted instruction. The artifact holds the complete label names.

| Offset | Instruction | Effect |
| --- | --- | --- |
| 00 | `str x0, [sp,#8]` | Store the input pointer in the caller spill |
| 04 | `mov x2, xzr` | Clear the index |
| 08 | `mov x3, xzr` | Clear the shift count |
| 0c | `mov x4, xzr` | Clear the accumulator |
| 10 | `b L_34` | Enter the loop |
| 14 | `and x5, x5, #0x7f` | Keep seven payload bits |
| 18 | `lsl x5, x5, x3` | Shift the payload |
| 1c | `add x2, x2, #0x1` | Increase the index |
| 20 | `add x6, x3, #0x7` | Calculate the next shift count |
| 24 | `cmp x3, #0x40` | Check the Go shift bound |
| 28 | `csel x5, x5, xzr, cc` | Clear an excessive shift result |
| 2c | `orr x4, x4, x5` | Accumulate payload bits |
| 30 | `mov x3, x6` | Set the next shift count |
| 34 | `cmp x1, x2` | Compare the signed length and index |
| 38 | `b.le L_94` | Select the incomplete return |
| 3c | `ldrb w5, [x0,x2]` | Read one input byte |
| 40 | `cmp x2, #0xa` | Check the eleventh-byte index |
| 44 | `b.eq L_88` | Select overflow after eleven bytes |
| 48 | `mov x6, x5` | Copy the byte |
| 4c | `cmp w6, #0x80` | Test the continuation bit |
| 50 | `b.cs L_14` | Continue the loop |
| 54 | `cmp x2, #0x9` | Check the tenth-byte index |
| 58 | `b.ne L_70` | Select a normal return |
| 5c | `cmp w6, #0x1` | Check the final payload bound |
| 60 | `b.ls L_70` | Select a normal tenth-byte return |
| 64 | `mov x0, xzr` | Clear the overflow value |
| 68 | `mov x1, #0xfffffffffffffff6` | Return negative ten |
| 6c | `ret` | Branch through x30 |
| 70 | `lsl x5, x5, x3` | Shift the final payload |
| 74 | `add x1, x2, #0x1` | Return the consumed byte count |
| 78 | `cmp x3, #0x40` | Check the Go shift bound |
| 7c | `csel x2, x5, xzr, cc` | Clear an excessive shift result |
| 80 | `orr x0, x4, x2` | Return the decoded value |
| 84 | `ret` | Branch through x30 |
| 88 | `mov x0, xzr` | Clear the overflow value |
| 8c | `mov x1, #0xfffffffffffffff5` | Return negative eleven |
| 90 | `ret` | Branch through x30 |
| 94 | `mov x0, xzr` | Clear the incomplete value |
| 98 | `mov x1, xzr` | Return a zero count |
| 9c | `ret` | Branch through x30 |

The function has no stack adjustment, stack guard, runtime call, indirect call, data reference, or write barrier.
The only store addresses `sp + 8`.
The only load reads `buffer[index]`.
The eleventh-byte path performs that load before it returns overflow.

## Verified parts and tests

`Uvarint.Arm64.returns` proves all four RET sites against the converted program.
It proves that RET keeps the complete machine data unchanged and branches through x30.
`Witness.premises_hold` proves consistent entry premises for each buffer shorter than `2 ^ 32` bytes.
`Machine.Arm64.run_sound` proves that a successful bounded interpreter run implies Kraken termination.
`Witness.check_sound` connects the Boolean state check to that termination statement.
These theorems do not prove that each input makes the Boolean check succeed.

`SelfTest.lean` executes the converted instructions in Kraken for the shared known-answer table.
It checks all memory bytes, x7 through x30, sp, the result registers, and return to `0x40000` within 256 steps.
This runtime test is separate from the Lean kernel proofs.
It does not execute the target ELF.
The Go differential run compiles a separate comparison program for the selected architecture and compares its output with the specification. It does not execute either target ELF.

## Reproduce the unfinished proofs

Run these commands from `lean/`.
Both commands currently exit with 1. Their errors identify unfinished proof obligations. Neither command passes.

```sh
lake env lean ../targets/uvarint/arm64/attempts/Result.lean
lake env lean ../targets/uvarint/arm64/attempts/KernelWitness.lean
```

`Result.lean` retains the complete statement and separates normal, incomplete, and overflow outcomes.
It stops at the entry spill obligation in each outcome.
`KernelWitness.lean` attempts closed execution proofs for empty, normal, and overflow inputs.
`decide +kernel` cannot reduce the interpreter and memory operations to a Boolean answer.
These files remain outside the Lake library directories. They contain no admitted proof.
