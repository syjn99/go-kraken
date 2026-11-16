# Findings

Each finding gives its place, its effect and its state.
The commands that check the present state are in `README.md`.

## 1. The uvarint target

### Paths that the theorem does not cover

`Uvarint.Decode.result` covers each path of the compiled function from the entry to each of its four returns.
The function has no stack growth path, no write barrier path and no call.
These items stay outside the theorem.

- A buffer length of `2 ^ 63` or more. The code compares the length as a signed number. A Go slice length is a non-negative `int`.
- The entry state. The statement takes the Go register calling convention as given: `rax` is the pointer and `rbx` is the length.
  No check reads this convention from the ELF.
- The callers. The theorem is about the function at its own symbol. A caller that has an inlined copy is not covered.

### Witnesses state the result registers only

Place: `lean/Uvarint/WitnessDecodeResult.lean`.
The theorems `runs_empty`, `runs_one_byte` and `runs_maximum` give the program counter and the result registers in concrete form.
They do not state the final memory again. The main theorem states it.
State: open.

### Nothing ran on x86-64 hardware

The build ran on an arm64 host and cross-compiled to amd64.
No test ran the ELF, and no test compares Kraken with a real CPU.
The differential run executes Go on the architecture of the container.
State: open.

## 2. Tools

### A code mutant cannot have a theorem with a separate statement as its target

Place: `tools/negative.py`, with `lean/Uvarint/DecodeResult.lean`.
The runner renames the program constant in the copy of the module of the theorem.
The statement of `Uvarint.Decode.result` is the definition `Decode.result_statement` in another module, and it names the original constant.
Thus a control with a code definition fails for that theorem, and a code mutant fails with the same error as the control.
The runner gives that mutant the class `inside`, which is a pass. The pass says nothing about the mutated instruction.
Effect: no negative case changes an instruction of the entry (directives 0 to 5), because only the main theorem runs them.
The case file has code mutants only for lemmas that write their statement in the theorem itself.
State: open. A fix needs a runner that also renames the constant in a copy of the statement module.

### The negative test runner read `/proc`

Place: `tools/negative.py`, `tools/memory_limit.py`.
The reference runner works only on Linux. On macOS each case ended with an exception, and each control failed.
State: fixed in this tree. Without `/proc`, the tools read the process table from `ps` and the session from `os.getsid`.
On macOS the memory cap counts the full resident size, which includes shared file pages. On Linux it counts anonymous pages.
The Linux path did not run on this tree.

### The link check self-test skips cases on a target without data

Place: `tools/link_check.py --selftest`.
Four of the eleven mutated inputs need a data file or an operand relative to `rip`. The uvarint link set has neither.
Effect: the self-test does not show on this target that the data checks and the global offset check fail on a wrong input.
State: open until a target has a data item.

### No data extractor, and no build of a Go module source

Place: `tools/build_target.sh`.
The script stops with exit 2 when `data_items` is not empty, or when the source kind is a Go module.
The manifest format has both fields. The reference data extractor has item tables that are specific to SSZ.
State: open until a target needs them.

### The manifest lists are not compared with the code

Place: `tools/link_check.py`.
No tool compares `runtime_callees` with the call targets of the converted code.
No tool compares `data_items` with the data files.
State: open.

### Build warnings

- `lean/Uvarint/Statements.lean` gives six unused-variable warnings for the named premises of the statement. The reference form has the same names.
- A file that imports Kraken without a `module` header gives a warning about the module system.

State: open. Neither warning changes a proof.

## 3. Stages that the pilot did not exercise

- Runtime contracts and their models. The function has no call. The contracts stay in the reference (`DESIGN.md`, section 5).
- Data items and the data include command.
- The stack guard branch and the write barrier branch.
- Proof generation.
