# Findings

Each finding gives its place, its effect and its state.
The commands that check the present state are in `README.md`.
The Git history records the fixed defects.

## The AMD64 uvarint target

### Inputs that the theorem does not cover

`Uvarint.Amd64.Decode.result` covers each path of the compiled function from the entry to each of its four returns.
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

Place: `lean/Uvarint/Amd64/WitnessDecodeResult.lean`.
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

## The ARM64 uvarint attempt

The pinned Kraken commit already supplies the ARM64 parser, semantics, separation lemmas, examples, and native tests.
This attempt changes neither Kraken nor the toolchain.
The parser accepts all 40 generated instructions. There is no unsupported instruction in this target.
The instruction inventory and calling convention are in `targets/uvarint/arm64/README.md`.

### Implemented and verified parts

- Two ARM64 builds produce ELF hash `ac68b01b768d9f954ccf65a3dae8f3a13f7cd77ac07b409ce0af98f182b7bbaa`.
- Go objdump, ELF bytes, and independent LLVM decoding agree for all 160 bytes.
- Clang reassembly produces exactly the same bytes for every instruction.
- The function has no stack growth, runtime call, data reference, or write barrier path.
- `Uvarint.Arm64.returns` proves that all four RET sites branch through x30 and preserve the complete machine data.
- `Witness.premises_hold` proves consistent entry premises for every buffer shorter than `2 ^ 32` bytes.
- The bounded interpreter and its state checker have soundness proofs.
- Runtime model tests cover nine shared known answers, complete memory, preserved registers, and a 256-step termination bound.

The runtime model tests do not execute the ELF and do not prove the full result theorem.
The differential tests compare Go with the specification. They do not execute either target ELF.

### Unfinished proof obligations

`Uvarint.Arm64.Decode.result_statement` remains unchanged in strength and has no result theorem.
Commit `f707438` records that statement before ARM64 proof work.
Commit `c82e5ea` records the concrete execution definitions before their proofs.
Commit `02a0bd3` records the four-return statement before its proof.

The statement includes termination, all three outcomes, explicit size bounds, preserved registers, and unchanged input and frame memory.
The first generic proof attempt stops at the entry STR in each outcome.
It must connect the owned spill bytes to `store_sep` and discharge the SP alignment condition.
The loop still needs an invariant for index, shift, accumulator, input ownership, and the unchanged frame.
The proof must connect signed CMP/B.LE, byte loads, LSL/CSEL, and both overflow branches to `decodeFrom`.
A host-placement theorem remains unfinished. The current statement fixes the standalone ELF address.
The Kraken state does not model vector registers, so this statement does not prove their preservation.

Closed kernel calculations also failed for empty, normal, and overflow executions.
The exact error is `Tactic decide failed to reduce`, followed by `Reduction got stuck at` the bounded interpreter call.
A smaller probe also fails to reduce `Mem.loadInt (Witness.initial []).dmem 65544 8 = some 0`.
The recursive executable traversal uses well-founded recursion. The proof must rewrite its equation lemmas instead of evaluating its definition.
The return proof succeeds with `withAddresses.eq_1`, `withAddresses.eq_2`, and the corresponding interpreter equations.
The concrete execution proof also needs separation-memory rewrites for the initial store and indexed loads.
These repository proofs remain unfinished. Kraken supplies the required instruction semantics.

Commit `d54bd4d` retains the failed proof sources. The current checkout removes those sources.
Their errors and required lemmas remain documented here. No admitted theorem enters the build.
ARM64 theorem mutants currently cover RET behavior. Full-result mutants remain unavailable until that result theorem exists.
Timeouts, memory failures, and unfinished proofs are not passes.

### Required loop lemmas

The remaining proof needs these repository lemmas:

| Obligation | Required relation |
| --- | --- |
| Entry store | Own the eight spill bytes, prove stack alignment, and apply `store_sep` |
| Indexed load | Read `buf[i]` from the owned input region and keep the input and R unchanged |
| Signed loop test | For bounded lengths and indices, B.LE selects exactly `length ≤ index` |
| Payload shift | For `i ≤ 9`, the count `7 * i` is below 64 and CSEL keeps the shifted payload |
| Accumulator | The bitwise OR equals the specification sum modulo `2 ^ 64` |
| Iteration | Increase the index, retain `decodeFrom`, keep memory, and decrease the remaining iteration bound |
| Returns | Connect normal, incomplete, tenth-byte overflow, and eleventh-byte overflow values to the full postcondition |

The code loads the eleventh byte before it detects overflow, so that load also needs owned memory.
No proof may replace complete buffer ownership or the unchanged R conclusion with a weaker condition.

### Differential execution architecture

Docker rejected a second platform pull for the pinned image with `cannot overwrite digest sha256:670bb5aa5349ae03b8516764718486f4f16399134bdc9acd0c46a23f043ab05c`.
The differential script now uses the existing pinned compiler image for both target architectures.
It sets GOOS and GOARCH for the comparison binary and checks the resulting Go build information.
It then executes that binary. The current Docker environment executes the AMD64 binary from the ARM64 compiler container.
The compiler itself remains Go 1.26.10 on linux/arm64.

### Model validation limits

Both target ELFs pass one Docker smoke execution. Each returns `(47, 1)` for its executable path.
This single input does not check every function input.
Kraken's native instruction suite cannot start because `krakenrunner_aarch64` is not built.
The environment also lacks `qemu-aarch64` and `qemu-aarch64-static`, which the suite requires.
It does not change the trusted separation of code memory and data memory.
It assumes the Go calling convention from the pinned compiler documentation.

### Architecture declarations in the axioms gate

Kraken generates some instruction equations lazily in the importing module.
The two architecture environments can therefore report the same declaration name with different types.
An initial combined dump failed its duplicate-name check.
The gate now scopes each record with its importing module and checks every scoped record.
The hand-list check still requires every original declaration name.
A repeated scoped record or any forbidden axiom still fails the gate.
The self-test checks both clean scoped names and a forbidden axiom behind a scoped name.

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

- `lean/Uvarint/Amd64/Statements.lean` gives six warnings about unused variables, for the named premises of the statement. The reference form has the same names.
- A file that imports Kraken without a `module` header gives a warning about the module system.

State: open. Neither warning changes a proof.

## Stages that the pilot did not use

- Runtime contracts and their models. The function has no call. The contracts stay in the reference.
- Data items and a data include command.
- The stack guard branch and the write barrier branch.
- Proof generation.

## Validation commands for the current directory layout

Run these commands from the repository root.
The commands with parentheses select `lean/` before they start Lake.
All Go comparison runs use the pinned image and Go 1.26.10.

| Command | Result |
| --- | --- |
| `sh tools/build_target.sh targets/uvarint/amd64/manifest.json` | Exit 0. Two identical builds. Existing AMD64 artifacts retain their hashes |
| `sh tools/build_target.sh targets/uvarint/arm64/manifest.json` | Exit 0. Two identical ARM64 builds |
| `python3 -I -B tools/link_check.py targets/uvarint/amd64/build` | Exit 0. 47 instructions, 140 bytes |
| `python3 -I -B tools/link_check.py targets/uvarint/arm64/build` | Exit 0. 40 instructions, 160 exact reassembly bytes |
| `python3 -I -B tools/link_check.py --selftest targets/uvarint/amd64/build` | Exit 0. Expected mutations fail and the unchanged control passes |
| `python3 -I -B tools/link_check.py --selftest targets/uvarint/arm64/build` | Exit 0. Expected mutations fail and the unchanged control passes |
| `(cd lean && lake build Machine Uvarint)` | Exit 0. All 124 build jobs complete |
| `(cd lean && lake build --no-build Machine Uvarint)` | Exit 0. The built libraries are current |
| `python3 -I -B tools/axioms_gate.py run /private/tmp/go-kraken-symmetry-gate.json /private/tmp/go-kraken-symmetry-dump.tsv` | Exit 0. 1262 scoped declarations, 1098 theorems, 13 hand-list names, and no forbidden axioms |
| `python3 -I -B tools/axioms_gate.py --selftest` | Exit 0. Scoped records and forbidden-axiom cases pass |
| `python3 -I -B tools/negative.py --check-cases targets/uvarint/amd64/tests/negative-cases.json` | Exit 0. Twelve valid cases |
| `python3 -I -B tools/negative.py --check-cases targets/uvarint/arm64/tests/negative-cases.json` | Exit 0. Three valid cases |
| `python3 -I -B tools/negative.py targets/uvarint/amd64/tests/negative-cases.json /private/tmp/go-kraken-symmetry-negative-amd64 /private/tmp/go-kraken-symmetry-negative-amd64.json` | Exit 0. Five controls and seven mutants pass |
| `python3 -I -B tools/negative.py targets/uvarint/arm64/tests/negative-cases.json /private/tmp/go-kraken-symmetry-negative-arm64 /private/tmp/go-kraken-symmetry-negative-arm64.json` | Exit 0. One control and two return mutants pass |
| `python3 -I -B tools/negative.py --selftest` | Exit 0 |
| `python3 -I -B tools/negative.py --selftest-timeout` | Exit 0. The intentional timeout leaves no child process |
| `(cd lean && lake env lean --run ../targets/uvarint/arm64/tests/SelfTest.lean)` | Exit 0. Nine known answers pass the complete state checks |
| `sh targets/uvarint/differential/run.sh /private/tmp/go-kraken-symmetry-differential-amd64 amd64` | Exit 0. Go and the specification agree on all 795 inputs |
| `sh targets/uvarint/differential/run.sh /private/tmp/go-kraken-symmetry-differential-arm64 arm64` | Exit 0. Go and the specification agree on all 795 inputs |
| `python3 -I -B lean/.lake/packages/Kraken/Kraken/AArch64/Test/asm_tests.py lean/.lake/packages/Kraken/Kraken/AArch64/Test/asm` | Exit 1. The native runner is not built. QEMU is also unavailable |
| `git diff d54bd4d --exit-code -- lean/lake-manifest.json lean/lean-toolchain` | Exit 0. Dependency pins remain unchanged |

A temporary comment in each architecture assembly file makes `lake build --no-build Machine Uvarint` exit with 3.
Restoring each file makes the same command exit with 0.
The probe changes only an assembly comment and restores the complete original file before it checks freshness again.

The link self-tests skip data and global-reference cases because this target has neither input.
The ARM64 link self-test also skips padding because its function has no padding instruction.
The model, negative, and differential runs complete without a resource timeout or a memory-limit stop.
The historical failed proof attempts remain unfinished. Their nonzero exits are not passes.

The failed sources in commit `d54bd4d` report the following errors.
The full-result attempt retains three case goals:

```text
Result.lean:12:50: error: unsolved goals
case value
case incomplete
case overflow
```

The concrete kernel attempts report these errors:

```text
KernelWitness.lean:16:2: error: Tactic `decide` failed to reduce
KernelWitness.lean:21:2: error: Tactic `decide` failed to reduce
KernelWitness.lean:27:2: error: Tactic `decide` failed to reduce
Reduction got stuck at
```

The Docker smoke commands also exit with 0 and print `47 1`:

```sh
docker run --rm --network none --memory 4g -v "$PWD/targets/uvarint/arm64/build:/out:ro" golang:1.26.10@sha256:670bb5aa5349ae03b8516764718486f4f16399134bdc9acd0c46a23f043ab05c /out/target
docker run --rm --network none --memory 4g -v "$PWD/targets/uvarint/amd64/build:/out:ro" golang:1.26.10@sha256:670bb5aa5349ae03b8516764718486f4f16399134bdc9acd0c46a23f043ab05c /out/target
```

## Symmetric architecture paths

Both architectures use `targets/uvarint/<arch>/manifest.json`, `build/`, `tests/`, and `README.md`.
The binaries use `build/target`, and the symbol listings use `build/target.nm`.
Both manifests refer to the shared Go package through `main_package: ../main`.
The differential script requires an architecture and reads that architecture manifest.

Machine declarations use `Machine.Amd64` or `Machine.Arm64`.
Target declarations use `Uvarint.Amd64` or `Uvarint.Arm64`.
The main statement names are `Uvarint.Amd64.Decode.result_statement` and `Uvarint.Arm64.Decode.result_statement`.
These name changes preserve the statement assumptions and conclusions.
The include commands and axiom-list filenames also name both architectures explicitly.

A byte comparison with the previous paths preserves both executables, disassembly files, symbol listings, assembly files, and link reports.
The manifests change their relative source paths and Lean constant names.
Only their manifest-hash lines change in the build identifiers.
The current checkout removes the failed proof sources because builds and tests do not need them.
Git history retains those sources. The remaining ARM64 proof obligations remain open.

The final checks cover these properties:

- Both architecture roots contain the same names: `README.md`, `manifest.json`, `build`, and `tests`.
- Both build directories contain the same artifact names.
- Both main statement bodies match their previous versions exactly after removal of the definition name.
- An incorrect architecture directory or target name stops manifest validation before Docker starts.
- Both assembly inputs invalidate Lake freshness after a temporary comment change. Restoration returns exit 0.
- The differential command rejects a missing or unsupported architecture with exit 2.
