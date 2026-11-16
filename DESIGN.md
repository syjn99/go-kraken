# Design: machine-code proofs for Go functions on Kraken

This framework proves that AMD64 Go machine code agrees with a Lean specification.
The ARM64 extension supplies checked infrastructure and partial proofs. Its complete Uvarint theorem remains unfinished.
Kraken supplies separate instruction models for both architectures.
The method comes from the directory `fv/kraken` of the repository `syjn99/methodical-ssz`.
That directory applies the method to generated SSZ code.
SSZ (Simple Serialize) is the serialization format of the Ethereum consensus layer.
This document gives the stages of the method and the items that a new target must supply.
A target is one set of Go functions in one compiled binary.

The reference for the method is commit `320929dd` of the branch `fv-restructure` of `syjn99/methodical-ssz`.
In this document, the reference is that commit.
A path that starts with `fv/kraken/` is a path in the reference.
The framework does not use the reference at build time.

## Architecture separation

Machine modules use `Machine/Amd64` and `Machine/Arm64`.
Target modules use `Uvarint/Amd64` and `Uvarint/Arm64`.
The specification, known-answer table, and Go source remain shared.
The project has no generic backend interface.
Kraken declares architecture types at the root, so a Lean module must not import both instruction models.
The axioms gate imports each repository module in a separate process and combines their declaration records.

Both architectures use `targets/<name>/<arch>/manifest.json`, `build/`, and `tests/`.
Both build directories use `target` and `target.nm`.
Machine definitions use `Machine.<Arch>`, and target definitions use `Uvarint.<Arch>`.
Architecture-specific axiom lists use the suffix `-amd64` or `-arm64`.
Lake tracks both assembly directories as inputs.
The ARM64 converter handles four-byte instruction words and signed PC-relative branch offsets.
The ARM64 link check requires exact reassembly bytes. It permits no alternate encoding or padding exception.

The ARM64 statement uses the standalone function at its pinned ELF address.
An arbitrary-host placement theorem and the complete loop proof remain unfinished.
Read `targets/uvarint/arm64/README.md` for the instruction inventory, calling convention, and proof limits.

## Scope

The framework starts from two inputs that exist before the work starts:

- The Go source of the functions.
- A Lean specification of the functions, with the proofs about the specification itself.

The framework covers the path from the Go source to a theorem that connects the machine code to that specification.
It does not write the specification, and it does not prove properties of the specification.

The method fits a function with these properties:

- The function is sequential. Kraken has no model of goroutines, channels or locks.
- The function has no call through an interface or a closure. The target of each call is a symbol.
- The function calls few runtime functions. Each runtime function needs a contract. The section "Runtime contracts and their models" gives the contracts.
- Kraken can parse each instruction of the compiled code.
- The specification is short.

Good candidates are codecs, checksums, integer and bit operations, and the bounds checks of parsers.
Network code, concurrent data structures and code that uses reflection are outside the scope.

## What a theorem says

A theorem is about the exact instruction sequence of one compiled function in one ELF file.
ELF is the file format of the binary.
The Go source is not the object of the proof, and the Go compiler is not evidence.

Each theorem depends on three pinned sources:

| Source | Pinned items |
| --- | --- |
| Specification | The Lean module and definition, and the commit of its library |
| Target | The Go source, the Go version, the build flags and the sha256 of the ELF |
| Semantics | The Kraken commit and the Lean toolchain |

If one source changes, build the theorems again against the new pin.
Until then, no check covers them.
A proof about one ELF does not apply to a different ELF.

The proofs assume these items and do not prove them:

- The Lean kernel.
- The Kraken model of each instruction. This project did not run the Kraken tests that compare instructions with an x86-64 host or Intel SDE (`Kraken/X64/Test/asm_tests.py` in the Kraken repository). This project did not run its ELF on an x86-64 processor.
- The Kraken machine itself. It does not check read, write or execute permissions. It keeps the code apart from the data memory. A theorem is about this model, not about a process of an operating system.
- The specification.
- The converter that writes the assembly text, and the Lean command that reads it. The link check compares the text with the ELF.
- The runtime contracts.
- The Go memory layout of each type that a statement names. It comes from the Go size rules, not from the ELF.

## Stages

Each stage has four parts: what it does, what is generic, what a target supplies, and what is specific to SSZ in the reference.

### Pinned build

The build compiles a small Go `main` package that keeps the target functions in the ELF.
It runs in a Docker container without a network, with one Go version and one set of flags.
It builds the ELF two times and compares the two sha256 values.
It writes the ELF, the disassembly of the target functions, the symbol listing and a file of build identifiers.
The sha256 of the ELF binds all later results.

- Generic: the build script `tools/build_target.sh`. It reads all its inputs from the manifest.
- Target supplies: the manifest and the `main` package. The `main` package must stop the compiler from an inline expansion or a removal of the functions.
- Specific to SSZ: the generator run, the generator pin, the type inventory and the Prysm tree (`fv/kraken/gen/prysm-gen.sh`, `prysm-elf.sh`, `keepalive.py`).

### ELF to Kraken program

The converter selects AMD64 or ARM64 from the manifest architecture.
It changes the disassembly of each function into one labeled assembly file.
A jump target becomes a label.
An address relative to `rip` becomes a symbol with an offset.
The terms `include_amd64_code "<file>"` and `include_arm64_code "<file>"` select the corresponding Kraken parser.
Each term gives a `Program` constant.
No person writes an instruction, a byte or an address by hand.

A data item of the ELF is, for example, a constant table or a string.
The reference has a data file for each data item and a Lean command that reads it.
This repository does not have that command or a data extractor yet.

The assembly files are Lake inputs of the library that reads them.
Thus a changed file makes Lake build the proofs again.

- Generic: `tools/convert_objdump.py` and the Lean command in `lean/Machine/Amd64/Include.lean`.
- Target supplies: the function symbols in the manifest, and one `Code` module that includes them.
- Specific to SSZ: the item tables of the link scripts (`fv/kraken/gen/checks/*link.py`) and the data module of the Prysm link set.

If the Kraken parser rejects an instruction, stop the work on that function.
Record the instruction and the error text as a finding.
Do not change Kraken.

### Link check

The link check shows that the text that Lean reads is the code and the data of the pinned ELF.
It compares the ELF, the disassembly and the symbol listing with the sha256 pins of the build.
It compares the disassembly bytes with the ELF bytes.
A second decoder must find the same instruction boundaries.
The check requires a label for each jump target that the text names.
It assembles the converted text again and compares the result with the ELF bytes.
It checks that each label has one definition, and that each global label names a symbol of the ELF.
It checks each data file against the ELF bytes.
It writes one result file with a sha256 line for each input and one hash over the whole result.
A self-test changes copies of the inputs, and each changed copy must fail.

The check does not read the Lean sources.
A reader checks in the statement that a theorem uses the included constants.

- Generic: `tools/link_check.py`.
- Target supplies: no item other than the manifest.
- Specific to SSZ: no part of the check itself.

### Runtime contracts and their models

A compiled Go function can call the Go runtime, for example to get memory or to copy bytes.
The framework does not prove the compiled runtime.
A contract is a Lean hypothesis that describes one runtime function at its label.
It states the argument registers, the size range, the stack window that the callee can use, the heap that it owns, and the frame.
Its conclusion gives the result, the kept registers and the unchanged frame.
A theorem names each contract that it uses as an explicit premise.

A contract can be contradictory, and then a theorem that uses it says nothing.
A runtime model is a small assembly program with a proof that it satisfies the contract.
The witness uses the model to show that the premises can be true together.
The model is not the real runtime. It only shows that the contract is consistent.

The Go compiler can put two more paths into a function:

- The stack growth path. The function entry compares the stack pointer with a guard and can call `runtime.morestack`. The compiler can omit this check for a function with a small frame or no frame.
- The write barrier path. A store of a pointer to the heap can branch to the garbage collector.

Find these paths in the disassembly of each function.
The reference excludes both paths with premises and lists them as not proved.
A new target does the same, and its list of paths not proved names them.

- Generic: the contracts of `runtime.makeslice`, `runtime.newobject`, `runtime.growslice`, `runtime.memmove` and `runtime.convT64`, and their models (`fv/kraken/lean/Runtime/`).
- Target supplies: the list of runtime functions that its code calls. For each runtime function that the framework does not have, the target supplies a contract and a model.
- Specific to SSZ: the `fmt.Errorf` contracts for the format strings of the SSZ library, and the witness allocators that read Prysm type words.

After the specification, the contracts of the runtime functions are the largest cost of a new target.
A known limit of the reference: the `growslice` contract gives no lower bound on the remaining heap.
Thus the reference does not prove a state after a second slice growth.

### Main theorem and witness

The statement is a `def` of type `Prop`.
Commit the statement before the proof.
Never weaken a statement to make a proof close.
A proof that does not close is a result. Report it.

A statement has these parts:

- Placement: the function is at an index of a host program, and no label of the function occurs before that index.
- Entry state: the argument registers follow the Go register calling convention.
- Memory: each region is separate and has its owner. The regions are the return address, the stack slots, the inputs, the outputs, the heap and the frame.
- The frame `R` is all other memory. The conclusion keeps it unchanged.
- Sizes: each size has an explicit range.
- Contracts: one premise for each runtime function that the code calls.
- Conclusion: each execution gets to the return address. The conclusion gives the result registers, the stack pointer after the return and the preserved registers. The final memory names each region again. It does not end with an unspecified remainder.

The specification function gives the result registers and the output memory.
If the specification has more than one outcome, each outcome needs a theorem, or one theorem covers all outcomes.

A witness is one concrete machine state that satisfies all premises of the main theorem.
It builds a concrete host program from the converted function and the runtime models.
Without a witness, the premises can be contradictory.
For an input of variable length, the witnesses cover the empty input, one element and the maximum.

- Generic: the statement rules, the witness host builder and its tactics (`lean/Machine/Amd64/WitnessHost.lean`).
- Target supplies: the statements, the mapping from specification values to registers and memory, and the witnesses.
- Specific to SSZ: the `Desc` type descriptions of EthLib, the Go value predicates of Prysm types, and the three theorem forms of a decoder. These forms are accept, reject and reject completeness.

### Proof layers

The proofs have three layers.
A lower layer does not import a higher layer.

| Layer | Content | Owner |
| --- | --- | --- |
| Machine lemmas | Step lemmas for one instruction, tactics, bytes, labels and flags | Framework (`lean/Machine/`) |
| Code-pattern lemmas | A lemma for a code form that the Go compiler emits in many places, stated once for each size or count | Framework when two targets use it, else the target |
| Target proofs | The proofs of the statements of one target | Target (`lean/<Target>/`) |

Examples of code patterns in the reference are the stack guard branch, a bounded copy loop and a load of an integer of fixed width.
The reference keeps its patterns in `fv/kraken/lean/Codec/`.
Many of them import SSZ type modules.
Do not copy that library.
Move a pattern into the framework only when a second target needs it.

Split a long straight-line proof into segments over the memory regions that each segment touches.
Give a loop an invariant lemma that holds for each iteration count in the size range.

- Generic: `lean/Machine/`.
- Target supplies: its proofs, and its patterns until a second target shares them.
- Specific to SSZ: `fv/kraken/lean/Codec/` and `fv/kraken/lean/Prysm/`.

### Proof generation

A generator writes Lean proof text from a converted assembly file and a description of the target.
A generator is not trusted.
Lean checks each proof that it writes.
A separate check examines the statement of a generated theorem: Lean proves that it is equal to a statement form that a person wrote.
A generated file must be equal to the output of its generator.

Generation is useful only when one code form occurs many times.
Generated SSZ code has that property.
Go code that a person wrote usually does not have it.
Thus the framework has no generator now.
Add a generator when a target has at least three functions with the same code form.

- Generic: two rules and one check. The generator is not trusted. A separate check examines each generated statement. A regeneration check compares each generated file with its generator output.
- Target supplies: no item, until it has a repeated code form.
- Specific to SSZ: `fv/kraken/gen/generator/` and the statement forms in `fv/kraken/lean/Codec/Kind/`.

### Checks

| Check | Decision | Tool |
| --- | --- | --- |
| Build | The Lean kernel accepts each proof | `lake build`, then `lake build --no-build` |
| Axioms gate | Each declaration uses only `propext`, `Classical.choice` and `Quot.sound` | `tools/axioms_gate.py` |
| Negative cases | A mutant of one instruction or of the statement fails inside its designated theorem. An unchanged control passes | `tools/negative.py` |
| Link check | The included code and data are the bytes of the pinned ELF | `tools/link_check.py` |
| Regeneration | The pinned build gives the same ELF sha256 again | `tools/build_target.sh` |
| Differential run | The Go function and the Lean specification give the same results on a list of inputs | A script of the target |

A timeout or a stop for lack of memory is a result. It is never a pass.
Report a check that did not run as not run.

A code mutant changes one instruction in a copy of the assembly file.
The runner renames the program constant in the copy of the theorem module.
The case field `inline` copies the modules between the code module and the theorem module into the same file.
Then no imported lemma or separate statement names the original program.
A first error that names both programs is never a pass.

The differential run compiles Go for the selected architecture and executes that comparison program in Docker.
It does not execute either target ELF.
It checks the specification against the Go behavior before the proof starts.
It is not evidence for a theorem.

- Generic: the axioms gate, the negative test runner, the link check and the build script.
- Target supplies: the negative cases, and the inputs of the differential run.
- Specific to SSZ: the `Desc` checker, the statement drift tool of the reference, and the proof inventory.

## The interface of a target

### Manifest

One manifest holds the build inputs for each target architecture.
Each architecture manifest uses `targets/<name>/<arch>/manifest.json`.
Its directory name must match GOARCH, and its parent directory must match the target name.
The main package path is relative to that architecture directory.

| Field | Content |
| --- | --- |
| `schema` | The format identifier `go-kraken.target/1` |
| `name` | The directory name of the target |
| `source` | The origin of the Go source: the Go standard library with a package path, or a Go module with a version and its `go.sum` hash |
| `go` | The Go version, the Docker image with its digest, the environment, the build flags and the build tags |
| `main_package` | The directory of the `main` package that keeps the functions in the ELF |
| `functions` | For each function: the ELF symbol and the name of its Lean program constant |
| `runtime_callees` | The symbols of the runtime functions that the code calls and that have a contract |
| `data_items` | For each data item: an identifier, the ELF symbol and the kind (bytes, address only, or pointer words) |

The build writes the pins that it calculates into `targets/<name>/build/build-ids.txt`.
These pins are the ELF sha256 and the hashes of the listings.
Read a pin from the file that holds it.
Do not copy a pin into other files.

### Lean obligations

A target supplies these modules in `lean/<Target>/`.
The names follow the role names of the reference (`fv/kraken/lean/README.md`), without the SSZ roles.

| Module | Obligation |
| --- | --- |
| `Spec` | The specification, or an import of it. The header names its source and commit |
| `Code` | One program constant for each function of the manifest, made with the architecture include command |
| `Data` | One definition for each data item of the manifest. Not necessary when the list is empty |
| `Statements` | The main statements, and the mapping from specification values to registers and memory |
| Proof modules | One theorem for each statement |
| `Witness...` | One witness for each main theorem |

A target also supplies these items outside Lean:

- A negative case file. For each main theorem, it has at least one control, one code mutant and one statement mutant.
- The inputs of the differential run.
- A list of the paths that its theorems do not cover, in its findings file.

These checks apply to a function: its theorems, its witness, its negative cases, the link check and the axioms gate.
Mark a function as finished only when all these checks pass.
Never write "complete" for a function that has a path in its list of paths not proved.

## Directory layout

```text
<repository root>
  README.md, DESIGN.md, FINDINGS.md
  tools/
    axioms-lists/uvarint-amd64.lean
    axioms-lists/uvarint-arm64.lean
  lean/
    Machine/Amd64/, Machine/Arm64/
    Uvarint/Amd64/, Uvarint/Arm64/
    Uvarint/Spec.lean, Uvarint/SpecKnownAnswers.lean
  targets/uvarint/
    main/, differential/
    amd64/
      README.md, manifest.json, build/, tests/
    arm64/
      README.md, manifest.json, build/, tests/
```

One Lake project holds the generic library and each target library.
The reference has the same form, and one project needs only one copy of Kraken.

The table gives each generic part and its source in the reference.
"Extracted" means that the part is in this repository.
"Listed" means that the part stays in the reference until a target needs it.

| Part | Source in the reference | State |
| --- | --- | --- |
| Build script | `fv/kraken/link/build.sh`, `fv/kraken/gen/prysm-elf.sh` (as a model) | Extracted as `tools/build_target.sh` |
| Converter | `fv/kraken/link/convert_objdump.py` | Extracted |
| Link check | `fv/kraken/link/check.py` | Extracted as `tools/link_check.py` |
| Data extractor and data include command | `fv/kraken/link/data.py`, `fv/kraken/gen/checks/link_set.py`, `fv/kraken/lean/Machine/Include.lean` | Listed. Their item tables are specific to SSZ |
| Machine lemmas, include command, witness host | `fv/kraken/lean/Machine/` | Extracted |
| Runtime contracts and models | `fv/kraken/lean/Runtime/` | Listed. The pilot has no runtime call |
| Stack guard branch lemmas and frame lemmas | `fv/kraken/lean/Machine/Flags.lean`, `fv/kraken/lean/Machine/Frame.lean`, `fv/kraken/lean/Codec/` (`lea_cmp_be_false`) | Listed. The pilot has no stack guard and no frame |
| Segment and loop lemmas | `fv/kraken/lean/Codec/Segment/` | Listed. Many of them import SSZ type modules |
| Axioms gate | `fv/kraken/gen/checks/axioms_gate.py` | Extracted |
| Negative test runner | `fv/kraken/gen/checks/negative.py` | Extracted, with the case field `inline` added |
| Proof generator and statement forms | `fv/kraken/gen/generator/`, `fv/kraken/lean/Codec/Kind/` | Listed. The section "Proof generation" gives the reason |
| Statement drift check | `.claude/skills/maintaining-methodical-fv/scripts/decl_drift.py` | Listed |

## The pilot target

The pilot is the function `encoding/binary.Uvarint` of the Go 1.26.10 standard library.
It decodes an unsigned integer of variable length from a byte slice.

These are the reasons for this choice:

- It is a real library function that many programs use, for example protocol buffer decoders.
- Its specification is short and has three outcomes: a value, a buffer that is too small, and an overflow.
- Its compiled code is 140 bytes. It has a loop, three error returns and a shift by a variable count.
- It is a leaf function. It has no stack frame, no stack guard, no runtime call and no data item. Thus the pilot can get to a theorem without a contract, and each stage up to the proof runs.
- A probe build showed no instruction that the Kraken parser does not know.

The pilot does not use the contract stage or the data stage.
The next target must use them.
A good next function is `encoding/binary.AppendUvarint`, which calls `runtime.growslice`.

The specification `lean/Uvarint/Spec.lean` adds payload groups as natural numbers.
The compiled code uses shifts and a bitwise or.
Thus the proof has real content: it is not a comparison of two copies of one text.

The checks in `README.md` give the state of the pilot.
`FINDINGS.md` gives the stops and their causes.

## Rules

These rules come from `fv/AGENTS.md` and `fv/README.md` of the reference.
They apply to this framework.

- Do not use `sorry`, `admit`, a new `axiom`, `native_decide` or `bv_decide`.
- Do not change Kraken or the Lean toolchain. Record a missing instruction as a finding.
- Write the statement before the proof. Do not weaken it.
- Supply a witness for each main theorem.
- Take expected values from an independent source. Do not make them with the code under check.
- Run one heavy Lean build at a time.
- A status is a result that a check calculates. Do not write a status by hand.
