# Findings

Each finding gives its place, its effect and its state.
The commands that check the present state are in `README.md`.
The Git history records the fixed defects.

## The uvarint target

### Inputs that the theorem does not cover

`Uvarint.Decode.result` covers each path of the compiled function from the entry to each of its four returns.
The function has no stack growth path, no write barrier path and no call.
These items stay outside the theorem:

- A buffer length of `2 ^ 63` or more. The code compares the length as a signed number. A Go slice length is a non-negative `int`.
- The entry state. The statement takes the Go register calling convention as given: `rax` is the pointer and `rbx` is the length. No check reads this convention from the ELF.
- The memory layout of the caller. The buffer, the return address slot and the spill slot must be separate regions. The premise owns the whole buffer, not only the bytes that the code reads.
- The callers. The theorem is about the function at its own symbol. It does not cover a caller that has an inline copy of the function.

### Items that the conclusion does not state

The conclusion gives `rax`, `rbx`, `rsp`, `rbp`, `r14` and the memory at the return.
It does not state the vector registers, the flags or the other general registers.
The Go register calling convention requires that `X15` holds zero at the return.
The statement does not show that the function keeps `X15`.
State: open. A change needs a new statement with a new name.

### The overflow result also covers a long encoding

Place: `lean/Uvarint/Spec.lean`, the constructor `Result.overflow`.
The specification follows the Go rule: an eleventh byte gives an overflow.
Thus ten bytes `0x80` and then `0x00` give `overflow 11`, but the value of these bytes is zero.
Go `binary.Uvarint` gives the same result.
Effect: `overflow` is the Go rejection of a value that is too large or of an encoding that is too long.
It does not always mean that the value is larger than 64 bits.
State: the docstring now says this. The definition did not change.

### The witnesses

Place: `lean/Uvarint/WitnessDecodeResult.lean`.
`premises_hold` shows that one concrete state satisfies all premises, for each buffer that is shorter than `2 ^ 32` bytes.
It does not show a witness for a longer buffer. The main theorem accepts lengths up to `2 ^ 63`.
The theorems `runs_empty`, `runs_one_byte` and `runs_maximum` give the program counter and the result registers in concrete form.
They do not state the final memory again. The main theorem states it.
State: open.

### No execution on an x86-64 processor

The build ran on an arm64 host and compiled for amd64.
This project did not run its ELF on an x86-64 processor.
The Kraken repository has tests that compare each instruction with an x86-64 host or with Intel SDE (`Kraken/X64/Test/asm_tests.py`).
This project did not run these tests.
The differential run executes Go on the architecture of the container.
State: open.

### The Kraken machine model

Place: `Kraken/X64/OmniSemantics.lean` and `Kraken/X64/Semantics.lean` of the pinned Kraken commit.
`Effects.All` accepts each request for read, write or execute access without a check of permissions.
`MachineData` keeps the data memory apart from the program.
The witness puts the code and the stack at the same address `0x10000`, which is valid in this model.
Effect: a theorem is about this model. It does not show the permissions of a process or the place of the code in its memory.
State: a limit of the trusted model.

## Tools

### The negative cases can only find a mismatch by its name

Place: `tools/negative.py`.
A code mutant renames the program constant in the copied modules.
If a case does not copy a module that names the program, the first error can be a mismatch of the two program constants.
The runner gives that error the class `mixed_programs`, which is not a pass.
It finds the mismatch from the names in the first error message only.
State: open.

### The negative test runner on macOS

Place: `tools/negative.py`, `tools/memory_limit.py`.
The reference runner works only on Linux, because it reads `/proc`.
Without `/proc`, these tools read the process table from `ps` and the session from `os.getsid`.
On macOS, the memory limit counts the full resident size, which includes shared file pages. On Linux, it counts anonymous pages.
The Linux path did not run on this repository.
State: open.

### The link check self-test skips cases on a target without data

Place: `tools/link_check.py --selftest`.
Four of the thirteen mutated inputs need a data file or an operand relative to `rip`. The uvarint link set has neither.
Effect: on this target, the self-test does not show that the data checks and the global offset check fail on a wrong input.
State: open until a target has a data item.

### No data extractor, and no build of a Go module source

Place: `tools/build_target.sh`.
The script stops with exit status 2 when `data_items` is not empty, or when the source kind is a Go module.
The manifest format has both fields. The data extractor of the reference has item tables that are specific to SSZ.
State: open until a target needs them.

### The tools do not compare the manifest lists with the code

Place: `tools/link_check.py`.
No tool compares `runtime_callees` with the call targets of the converted code.
No tool compares `data_items` with the data files.
State: open.

### Machine lemmas without a user

Place: `lean/Machine/`.
Some lemmas and macros have no user in the pilot proofs, for example `zx16`, `zx32`, `sep_true`, `shift_left64`, `address_equation` and `witness_split`.
They came from the reference with the modules that the pilot uses.
State: open. Remove them, or keep them for the next target.

### Build warnings

- `lean/Uvarint/Statements.lean` gives six warnings about unused variables, for the named premises of the statement. The reference form has the same names.
- A file that imports Kraken without a `module` header gives a warning about the module system.

State: open. Neither warning changes a proof.

## Stages that the pilot did not use

- Runtime contracts and their models. The function has no call. The contracts stay in the reference.
- Data items and a data include command.
- The stack guard branch and the write barrier branch.
- Proof generation.
