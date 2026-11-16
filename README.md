# go-kraken: machine-code proofs for Go functions

This repository proves that compiled AMD64 Go functions agree with Lean specifications.
It also contains an unfinished ARM64 verification attempt.
Kraken supplies separate AMD64 and ARM64 instruction models.
The design is in `DESIGN.md`.
The findings and the limits are in `FINDINGS.md`.

The only target is `uvarint`.
This target is the function `encoding/binary.Uvarint` of the Go 1.26.10 standard library.
The AMD64 main theorem is `Uvarint.Decode.result` in `lean/Uvarint/Amd64/DecodeResult.lean`.
Its statement is `Uvarint.Decode.result_statement` in `lean/Uvarint/Amd64/Statements.lean`.

The ARM64 build, parser probe, byte linkage, return theorem, and concrete model tests pass.
The complete ARM64 result statement remains unproved.
Read [the ARM64 architecture notes](targets/uvarint/arm64/README.md) for its calling convention and unfinished obligations.
`Machine/Amd64` and `Machine/Arm64` contain separate machine modules.
`Uvarint/Amd64` and `Uvarint/Arm64` contain separate target modules.
Both architectures share `Uvarint.Spec`, `Uvarint.SpecKnownAnswers`, and the Go main package.

## Pinned versions

Read each pin from the file that holds it.

| Pin | File |
| --- | --- |
| Go version, Docker image, build flags, function list | `targets/uvarint/manifest.json` |
| ELF sha256 and the hashes of the listings | `targets/uvarint/build/build-ids.txt` |
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
sh tools/build_target.sh targets/uvarint/manifest.json
sh tools/build_target.sh targets/uvarint/manifest-arm64.json
```

The script builds the ELF two times and compares the two sha256 values.
After the run, `git status` must show no change under `targets/uvarint/build/`.
Git does not track either ELF.
ARM64 artifacts use `targets/uvarint/build-arm64/` and the ELF name `target-arm64`.
AMD64 artifacts retain their original paths and hashes.

### Link check

This check needs the ELF, `clang` and `llvm-objdump`.

```sh
python3 -I -B tools/link_check.py targets/uvarint/build
python3 -I -B tools/link_check.py --selftest targets/uvarint/build
python3 -I -B tools/link_check.py targets/uvarint/build-arm64
python3 -I -B tools/link_check.py --selftest targets/uvarint/build-arm64
```

The check writes `targets/uvarint/build/RESULT`.
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
python3 -I -B tools/negative.py --check-cases targets/uvarint/negative-cases.json
python3 -I -B tools/negative.py targets/uvarint/negative-cases.json <scratch>/negative-work <scratch>/negative-result.json
python3 -I -B tools/negative.py --check-cases targets/uvarint/negative-cases-arm64.json
python3 -I -B tools/negative.py targets/uvarint/negative-cases-arm64.json <scratch>/negative-arm64 <scratch>/negative-arm64.json
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
The optional architecture selects the compiled Go comparison program.
The compiler container keeps the pinned image and its native architecture.
The run checks the binary build information for the Go version and target architecture.
Execution needs container support for that architecture, including emulation when necessary.
It does not execute either target ELF.

### ARM64 concrete model test

Run this command from `lean/`, after the library build.

```sh
lake env lean --run ../targets/uvarint/arm64/SelfTest.lean
```

This test checks the shared known answers against the converted code in Kraken.
It checks termination within 256 steps, complete memory, and preserved general registers.
It does not prove the complete ARM64 result statement.

## Add a target

1. Write `targets/<name>/manifest.json` and the `main` package. The design gives the fields in the section "Manifest".
2. Run `tools/build_target.sh` and the link check.
3. Add a library `<Name>` with the glob `<Name>.+` to `lean/lakefile.toml`. Add the directory of the converted code as an `input_dir`.
4. Write the Lean modules of the design section "Lean obligations". Commit the statements before the proofs.
5. Add a hand list to `tools/axioms-lists/` and a negative case file to the target directory.
