# Design: machine-code proofs for Go functions on Kraken

This framework proves that the x86-64 machine code of a Go function agrees with a Lean specification.
Kraken is a Lean 4 model of x86-64 instructions.
The method comes from the project `fv/kraken` of this repository, which applies it to generated SSZ code.
SSZ (Simple Serialize) is the serialization format of the Ethereum consensus layer.
This document gives the stages of the method, and what a new target must supply.
A target is one set of Go functions in one compiled binary.

The reference for the method is commit `320929dd` of the branch `fv-restructure` (`syjn99/methodical-ssz`).
A path that starts with `fv/kraken/` is a path of that commit.
The framework does not depend on these paths at build time.

## 1. Scope

The framework starts from two inputs that exist before the work starts.

- The Go source of the functions.
- A Lean specification of the functions, with the proofs about the specification itself.

The framework covers the path from the Go source to a theorem that connects the machine code to that specification.
It does not write the specification, and it does not prove properties of the specification.

The method fits a function with these properties.

- The function is sequential. Kraken has no model of goroutines, channels or locks.
- The function has no call through an interface or a closure. The target of each call is a symbol.
- The function calls few runtime functions. Each runtime function needs a contract (section 3.4).
- The compiled code uses only instructions that Kraken can parse.
- The specification is short.

Good candidates are codecs, checksums, integer and bit operations, and the bounds checks of parsers.
Network code, concurrent data structures and code that uses reflection are outside the scope.

## 2. What a theorem says

A theorem is about the exact instruction sequence of one compiled function in one ELF file.
ELF is the file format of the binary.
The Go source is not the object of the proof, and the Go compiler is not evidence.

Each theorem depends on three pinned sources.

| Source | What is pinned |
| --- | --- |
| Specification | The Lean module and definition, and the commit of its library |
| Target | The Go source, the Go version, the build flags and the sha256 of the ELF |
| Semantics | The Kraken commit and the Lean toolchain |

If one source changes, the theorems are unchecked until they build again against the new pin.
A proof about one ELF does not transfer to another ELF.

The proofs assume these items and do not prove them.

- The Lean kernel and the Kraken model of each instruction. No test compares Kraken with a real CPU.
- The specification.
- The converter that writes assembly text and the Lean command that reads it. The link check compares the text with the ELF.
- The runtime contracts (section 3.4).
- The Go memory layout of each type that a statement names. It comes from the Go size rules, not from the ELF.

## 3. Stages

Each stage has four parts: what it does, what is generic, what a target supplies, and what is specific to SSZ in `fv/kraken`.

### 3.1 Pinned build

The build compiles a small Go `main` package that keeps the target functions in the ELF.
It runs in a Docker container without a network, with one Go version and one set of flags.
It builds two times and compares the sha256 values.
It writes the ELF, the disassembly of the target functions, the symbol listing and a file of build identifiers.
The sha256 of the ELF binds all later results.

- Generic: the build script `tools/build_target.sh`. It reads everything from the manifest.
- Target supplies: the manifest and the `main` package. The `main` package must stop the compiler from inlining or removing the functions.
- Specific to SSZ: the generator run, the generator pin, the type inventory and the Prysm tree (`fv/kraken/gen/prysm-gen.sh`, `prysm-elf.sh`, `keepalive.py`).

### 3.2 ELF to Kraken program

The converter changes the disassembly of each function into one labeled assembly file.
A jump target becomes a label, and an address relative to `rip` becomes a symbol with an offset.
The Lean term `include_x64_code "<file>"` parses the file with the Kraken parser and gives a `Program` constant.
A data item of the ELF (for example a constant table or a string) becomes a data file.
A Lean command reads the data file and defines its bytes and its address.
No instruction, byte or address is written by hand.

The assembly files and the data files are Lake inputs of the library that reads them.
Thus a changed file makes Lake build the proofs again.

- Generic: `tools/convert_objdump.py` and the Lean commands in `lean/Machine/Include.lean`.
- Target supplies: the function symbols and the data items in the manifest, and one `Code` module that includes them.
- Specific to SSZ: the item tables of the link scripts (`fv/kraken/gen/checks/*link.py`) and the data module of the Prysm link set.

If the Kraken parser rejects an instruction, the work on that function stops.
Record the instruction and the error text as a finding. Do not change Kraken.

### 3.3 Link check

The link check shows that the text that Lean reads is the code and the data of the pinned ELF.
It compares the disassembly bytes with the ELF bytes, and a second decoder must find the same instruction boundaries.
It assembles the converted text again and compares the result with the ELF bytes.
It checks that each label is defined once, and that each global label names a symbol of the ELF.
It checks each data file against the ELF bytes.
It writes one result file with a sha256 line for each input and one hash over the whole result.
A self-test changes copies of the inputs, and each changed copy must fail.

The check does not read the Lean sources.
A reader confirms from the statement that a theorem uses the included constants.

- Generic: `tools/link_check.py`.
- Target supplies: nothing more than the manifest.
- Specific to SSZ: nothing in the check itself.

### 3.4 Runtime contracts and their models

A compiled Go function can call the Go runtime, for example to allocate memory or to copy bytes.
The framework does not prove the compiled runtime.
A contract is a Lean hypothesis that describes one runtime function at its label.
It states the argument registers, the size range, the stack window that the callee can use, the heap that it owns, and the frame.
Its conclusion gives the result, the kept registers and the unchanged frame.
A theorem names each contract that it uses as an explicit premise.

A contract can be contradictory, and then a theorem that uses it says nothing.
A runtime model is a small assembly program with a proof that it satisfies the contract.
The witness (section 3.5) uses the model to show that the premises can hold together.
The model is not the real runtime. It only shows that the contract is consistent.

Two paths are in every Go function that has a stack frame or stores a pointer.

- The stack growth path: the function entry compares the stack pointer with a guard and can call `runtime.morestack`.
- The write barrier path: a pointer store can branch to the garbage collector.

The reference excludes both paths by premises and lists them as not proved.
A new target does the same, and its list of paths not proved names them.

- Generic: the contracts of `runtime.makeslice`, `runtime.newobject`, `runtime.growslice`, `runtime.memmove` and `runtime.convT64`, and their models (`fv/kraken/lean/Runtime/`).
- Target supplies: the list of runtime functions that its code calls, and a contract and a model for each one that the framework does not have.
- Specific to SSZ: the `fmt.Errorf` contracts for the format strings of the SSZ library, and the witness-only allocators that read Prysm type words.

The contract of a runtime function is the largest cost of a new target, after the specification.
Known limit of the reference: the `growslice` contract gives no lower bound on the remaining heap.
Thus a state after a second slice growth is not proved there.

### 3.5 Main theorem and witness

The statement is a `def` of type `Prop`. Commit it before the proof.
Never weaken a statement to make a proof close. A proof that does not close is a result, and it is reported.

A statement has these parts.

- Placement: the function sits at an index of a host program, and no label of the function occurs before it.
- Entry state: the argument registers follow the Go register calling convention.
- Memory: each region is a separate fragment with its owner. The regions are the return address, the stack slots, the inputs, the outputs, the heap and the frame.
- The frame `R` is all other memory. The conclusion keeps it unchanged.
- Sizes: each size has an explicit range.
- Contracts: one premise for each runtime function that the code calls.
- Conclusion: every execution reaches the return address, with the result registers, the stack pointer after the return and the preserved registers.
  The final memory names each fragment again. It does not end with an unspecified remainder.

The result registers and the output memory are stated with the specification function.
If the specification has several outcomes, each outcome needs a theorem, or one theorem covers all of them.

A witness is one concrete machine state that satisfies all premises of the main theorem.
It builds a concrete host program from the converted function and the runtime models.
Without a witness, the premises can be contradictory.
For an input of variable length, the witnesses cover the empty input, one element and the maximum.

- Generic: the statement rules, the witness host builder and its tactics (`lean/Machine/WitnessHost.lean`, `WitnessSplit.lean`).
- Target supplies: the statements, the mapping from specification values to registers and memory, and the witnesses.
- Specific to SSZ: the `Desc` type descriptions of EthLib, the three theorem forms of a decoder (accept, reject, reject completeness), and the Go value predicates of Prysm types.

### 3.6 Proof layers

The proofs have three layers. A lower layer does not import a higher one.

| Layer | Content | Owner |
| --- | --- | --- |
| Machine lemmas | One-instruction step lemmas and tactics, stack frame, bytes, labels and flags | Framework (`lean/Machine/`) |
| Code-pattern lemmas | A lemma for a code form that the Go compiler emits in many places, stated once for any size or count | Framework when two targets use it, else the target |
| Target proofs | The proofs of the statements of one target | Target (`lean/<Target>/`) |

Examples of code patterns in the reference are the stack guard branch, a bounded copy loop and a fixed-width integer load.
The reference keeps its patterns in `fv/kraken/lean/Codec/`. Many of them import SSZ type modules.
Do not copy that library. Move a pattern into the framework only when a second target needs it.

A long straight-line proof is split into segments over the memory fragments that each segment touches.
A loop gets an invariant lemma that is stated for any iteration count in the size range.

- Generic: `lean/Machine/`.
- Target supplies: its proofs, and its patterns until a second target shares them.
- Specific to SSZ: `fv/kraken/lean/Codec/` and `fv/kraken/lean/Prysm/`.

### 3.7 Proof generation

A generator writes Lean proof text from a converted assembly file and a description of the target.
A generator is not trusted. Lean checks each proof that it writes.
The statement of a generated theorem is checked separately: Lean proves that it is equal to a hand-written statement form.
A generated file must be equal to the output of its generator.

Generation is useful only when one code form occurs many times.
Generated SSZ code has that property. Hand-written Go code usually does not.
Thus the framework has no generator now.
Add one when a target has at least three functions with the same code form.

- Generic: the two rules above (untrusted generator, separate statement check) and the regeneration check.
- Target supplies: nothing, until it has a repeated code form.
- Specific to SSZ: `fv/kraken/gen/generator/` and the statement forms in `fv/kraken/lean/Codec/Kind/`.

### 3.8 Checks

| Check | What it decides | Tool |
| --- | --- | --- |
| Build | The Lean kernel accepts each proof | `lake build`, then `lake build --no-build` |
| Axioms gate | Each declaration uses only `propext`, `Classical.choice` and `Quot.sound` | `tools/axioms_gate.py` |
| Negative cases | A mutant of one instruction or of the statement fails inside its designated theorem. An unchanged control passes | `tools/negative.py` |
| Link check | The included code and data are the bytes of the pinned ELF | `tools/link_check.py` |
| Regeneration | The pinned build gives the same ELF sha256 again. A generated file is equal to its generator output | `tools/build_target.sh` |
| Differential run | The Go function and the Lean specification give the same results on a list of inputs | A script of the target |

A timeout or an out-of-memory stop is a result. It is never a pass.
A check that did not run is reported as not run.

The differential run executes Go on the host. It does not execute the amd64 machine code.
It checks the specification against the Go behavior before the proof starts.
It is not evidence for a theorem.

- Generic: the axioms gate, the negative test runner, the link check and the build script.
- Target supplies: the negative cases, and the inputs of the differential run.
- Specific to SSZ: the `Desc` checker, the statement drift tool of the project skill, and the proof inventory.

## 4. The interface of a target

### 4.1 Manifest

One JSON file, `targets/<name>/manifest.json`, holds all inputs of the build and the link stages.

| Field | Content |
| --- | --- |
| `schema` | The format identifier `go-kraken.target/1` |
| `name` | The directory name of the target |
| `source` | Where the Go source comes from: the Go standard library with a package path, or a Go module with a version and its `go.sum` hash |
| `go` | The Go version, the Docker image with its digest, the environment, the build flags and the build tags |
| `main_package` | The directory of the `main` package that keeps the functions in the ELF |
| `functions` | For each function: the ELF symbol and the name of its Lean program constant |
| `runtime_callees` | The symbols of the runtime functions that the code calls and that have a contract |
| `data_items` | For each data item: an identifier, the ELF symbol and the kind (bytes, address only, or pointer words) |

The build writes the pins that it computes (the ELF sha256 and the listing hashes) into `targets/<name>/build/build-ids.txt`.
Read a pin from the file that holds it. Do not copy it into other files.

### 4.2 Lean obligations

A target supplies these modules in `lean/<Target>/`.
The names follow the role names of the reference (`fv/kraken/lean/README.md`, section 8), without the SSZ roles.

| Module | Obligation |
| --- | --- |
| `Spec` | The specification, or an import of it. The header names its source and commit |
| `Code` | One program constant for each function of the manifest, made with `include_x64_code` |
| `Data` | One definition for each data item of the manifest. Not necessary when the list is empty |
| `Statements` | The main statements, and the mapping from specification values to registers and memory |
| Proof modules | One theorem for each statement |
| `Witness...` | One witness for each main theorem |

A target also supplies these items outside Lean.

- A negative case file: at least one control, one code mutant and one statement mutant for each main theorem.
- The inputs of the differential run.
- A list of the paths that its theorems do not cover, in its findings file.

A function is done only when its theorems, its witness, its negative cases, the link check and the axioms gate all pass.
Never write "complete" for a function that has a path in its list of paths not proved.

## 5. Directory layout

```text
go-kraken/
  DESIGN.md              this document
  README.md              the commands that work
  FINDINGS.md            findings, stops and paths not proved
  tools/                 build, conversion, link check, axioms gate, negative test runner
  lean/                  one Lake project
    Machine/             machine lemmas, include commands, witness host (generic)
    Uvarint/             the pilot target
  targets/
    uvarint/
      manifest.json
      main/              the main package of the build
      build/             build identifiers, disassembly, symbol listing, converted code, link result
```

One Lake project holds the generic library and each target library.
The reference has the same form, and one project needs only one copy of Kraken.

The table gives each generic part and its source in the reference.
"Extracted" means that the part is in this tree. "Listed" means that it stays in the reference until a target needs it.

| Part | Source in the reference | State |
| --- | --- | --- |
| Build script | `fv/kraken/link/build.sh`, `fv/kraken/gen/prysm-elf.sh` (as a model) | Extracted as `tools/build_target.sh` |
| Converter | `fv/kraken/link/convert_objdump.py` | Extracted |
| Link check | `fv/kraken/link/check.py` | Extracted as `tools/link_check.py` |
| Data extractor | `fv/kraken/link/data.py`, `fv/kraken/gen/checks/link_set.py` | Listed. Their item tables are specific to SSZ |
| Machine lemmas, include commands, witness host | `fv/kraken/lean/Machine/` | Extracted |
| Runtime contracts and models | `fv/kraken/lean/Runtime/` | Listed. The pilot has no runtime call |
| Stack guard branch lemmas | `fv/kraken/lean/Machine/Flags.lean`, `fv/kraken/lean/Codec/` (`lea_cmp_be_false`) | Listed. The pilot has no stack guard |
| Segment and loop lemmas | `fv/kraken/lean/Codec/Segment/` | Listed. Many of them import SSZ type modules |
| Axioms gate | `fv/kraken/gen/checks/axioms_gate.py` | Extracted |
| Negative test runner | `fv/kraken/gen/checks/negative.py` | Extracted |
| Proof generator and statement forms | `fv/kraken/gen/generator/`, `fv/kraken/lean/Codec/Kind/` | Listed. See section 3.7 |
| Statement drift check | `.claude/skills/maintaining-methodical-fv/scripts/decl_drift.py` | Listed |

## 6. The pilot target

The pilot is the function `encoding/binary.Uvarint` of the Go 1.26.10 standard library.
It decodes an unsigned integer of variable length from a byte slice.

Reasons for this choice:

- It is a real library function that many programs use, for example protocol buffer decoders.
- Its specification is short and has three outcomes: a value, a buffer that is too small, and an overflow.
- Its compiled code is 140 bytes and has a loop, three error returns and a shift by a variable count.
- It is a leaf function. It has no stack frame, no stack guard, no runtime call and no data item.
  Thus the pilot can reach a theorem without a contract, and each stage up to the proof runs.
- A probe build showed no instruction that the Kraken parser does not know.

The pilot does not exercise the contract stage or the data stage.
The next target must do that.
A good next function is `encoding/binary.AppendUvarint`, which calls `runtime.growslice`.

The specification `lean/Uvarint/Spec.lean` adds payload groups as natural numbers.
The compiled code uses shifts and a bitwise or.
Thus the proof has real content: it is not a comparison of two copies of one text.

The state of the pilot is the result of the checks in `README.md`.
Stops and their causes are in `FINDINGS.md`.

## 7. Rules

The rules of `fv/AGENTS.md` and `fv/README.md` of the reference apply to this framework.
The most important ones are these.

- Do not use `sorry`, `admit`, a new `axiom`, `native_decide` or `bv_decide`.
- Do not change Kraken or the Lean toolchain. Record a missing instruction as a finding.
- Write the statement before the proof. Do not weaken it.
- Supply a witness for each main theorem.
- Take expected values from an independent source. Do not make them with the code under check.
- Run one heavy Lean build at a time.
- A status is a result that a check computes. Do not write a status by hand.
