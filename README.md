# go-kraken: machine-code proofs for Go functions

This repository proves that compiled AMD64 Go functions agree with Lean specifications.
It also contains an unfinished ARM64 verification attempt.
Kraken supplies separate AMD64 and ARM64 instruction models.
The design is in `DESIGN.md`.
The findings and the limits are in `FINDINGS.md`.

The only target is `uvarint`.
This target is the function `encoding/binary.Uvarint` of the Go 1.26.10 standard library.
The AMD64 main theorem is `Uvarint.Amd64.Decode.result` in `lean/Uvarint/Amd64/DecodeResult.lean`.
Its statement is `Uvarint.Amd64.Decode.result_statement` in `lean/Uvarint/Amd64/Statements.lean`.

The ARM64 build, parser probe, byte linkage, return theorem, and concrete model tests pass.
The complete ARM64 result statement remains unproved.
Read the [AMD64 notes](targets/uvarint/amd64/README.md) and [ARM64 notes](targets/uvarint/arm64/README.md) for calling conventions and proof limits.
`Machine/Amd64` and `Machine/Arm64` contain separate machine modules.
`Uvarint/Amd64` and `Uvarint/Arm64` contain separate target modules.
Both architectures share `Uvarint.Spec`, `Uvarint.SpecKnownAnswers`, and the Go main package.

## Directory structure

Use `amd64` or `arm64` for `<arch>` in target paths.
Use `Amd64` or `Arm64` for the corresponding Lean namespace.

```text
targets/uvarint/
  main/                      shared Go entry point
  differential/              shared Go and specification comparison
  amd64/
    README.md
    manifest.json
    build/                   target, target.nm, target.objdump, build-ids.txt, RESULT, norm/
    tests/negative-cases.json
  arm64/
    README.md
    manifest.json
    build/                   the same artifact names
    tests/negative-cases.json
    tests/SelfTest.lean       ARM64 model execution checks
```

Machine definitions use `Machine.<Arch>` and target definitions use `Uvarint.<Arch>`.
The input commands are `include_amd64_code` and `include_arm64_code`.
The axiom lists are `tools/axioms-lists/uvarint-amd64.lean` and `uvarint-arm64.lean`.
Each architecture keeps its actual proof and test modules. No empty counterpart files exist.

## Pinned versions

Read each pin from the file that holds it.

| Pin | File |
| --- | --- |
| Go version, Docker image, build flags, function list | `targets/uvarint/<arch>/manifest.json` |
| ELF sha256 and the hashes of the listings | `targets/uvarint/<arch>/build/build-ids.txt` |
| Kraken commit | `lean/lakefile.toml` and `lean/lake-manifest.json` |
| Lean toolchain | `lean/lean-toolchain` |

## Commands

Run the commands from the repository root, unless a command starts with `cd`.
`<scratch>` is a directory outside the repository.
Run one heavy Lean build at a time.
Before a build, examine the running builds with `pgrep -lx lake`.

### Build the ELF again and convert it

This command needs Docker and Python.

```sh
sh tools/build_target.sh targets/uvarint/amd64/manifest.json
sh tools/build_target.sh targets/uvarint/arm64/manifest.json
```

The script builds the ELF two times and compares the two sha256 values.
After each run, `git status` must show no change under that architecture build directory.
Git does not track either ELF.
Both architectures use `build/target`, `build/target.nm`, and the same artifact names.
The directory move preserves the ELF, disassembly, symbol listing, and assembly bytes.
Manifest hashes change because the relative source paths and Lean names change.

### Link check

This check needs the ELF, `clang` and `llvm-objdump`.

```sh
python3 -I -B tools/link_check.py targets/uvarint/amd64/build
python3 -I -B tools/link_check.py --selftest targets/uvarint/amd64/build
python3 -I -B tools/link_check.py targets/uvarint/arm64/build
python3 -I -B tools/link_check.py --selftest targets/uvarint/arm64/build
```

The check writes `RESULT` inside the selected architecture build directory.
After the run, `git status` must show no change of that file.

### Lean build

On the first run, Lake gets Kraken at the pinned commit.

```sh
(cd lean && lake build Machine Uvarint)
(cd lean && lake build --no-build Machine Uvarint)
```

The second command must exit with 0.
The command `lake env lean` does not check that the build is current.

### Axioms gate

This check needs a current build.

```sh
python3 -I -B tools/axioms_gate.py run <scratch>/gate.json <scratch>/dump.tsv
python3 -I -B tools/axioms_gate.py --selftest
```

The gate examines each declaration of each library of `lean/lakefile.toml`.
It also checks that the dump holds each name of the hand lists in `tools/axioms-lists/`.

### Negative cases

This check needs a current build.

```sh
python3 -I -B tools/negative.py --check-cases targets/uvarint/amd64/tests/negative-cases.json
python3 -I -B tools/negative.py targets/uvarint/amd64/tests/negative-cases.json <scratch>/negative-work <scratch>/negative-result.json
python3 -I -B tools/negative.py --check-cases targets/uvarint/arm64/tests/negative-cases.json
python3 -I -B tools/negative.py targets/uvarint/arm64/tests/negative-cases.json <scratch>/negative-arm64 <scratch>/negative-arm64.json
python3 -I -B tools/negative.py --selftest
python3 -I -B tools/negative.py --selftest-timeout
```

ARM64 negative cases currently cover the return theorem, not the unfinished result statement.
A mutant passes only when Lean reports an error inside the designated theorem.
A control passes only when Lean reports no error.

### Differential run

This run needs Docker and a current build of `Uvarint.Spec`.

```sh
sh targets/uvarint/differential/run.sh <scratch>/differential-amd64 amd64
sh targets/uvarint/differential/run.sh <scratch>/differential-arm64 arm64
```

The run compares the Go function with the Lean specification on a fixed list of inputs.
The required architecture selects the compiled Go comparison program.
The compiler container keeps the pinned image and its native architecture.
The run checks the binary build information for the Go version and target architecture.
Execution needs container support for that architecture, including emulation when necessary.
It does not execute either target ELF.

### ARM64 concrete model test

Run this command from `lean/`, after the library build.

```sh
lake env lean --run ../targets/uvarint/arm64/tests/SelfTest.lean
```

This test checks the shared known answers against the converted code in Kraken.
It checks termination within 256 steps, complete memory, and preserved general registers.
It does not prove the complete ARM64 result statement.

## Add a target

1. Write `targets/<name>/<arch>/manifest.json` and the shared `main` package. The design gives the fields in the section "Manifest".
2. Run `tools/build_target.sh` and the link check.
3. Add a library `<Name>` with the glob `<Name>.+` to `lean/lakefile.toml`. Add the directory of the converted code as an `input_dir`.
4. Write the Lean modules of the design section "Lean obligations". Commit the statements before the proofs.
5. Add a hand list to `tools/axioms-lists/` and a negative case file to the target directory.
