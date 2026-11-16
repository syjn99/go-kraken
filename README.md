# go-kraken: machine-code proofs for Go functions

This directory holds a framework that proves that the x86-64 machine code of a Go function agrees with a Lean specification.
Kraken is a Lean 4 model of x86-64 instructions.
The design is in `DESIGN.md`. The findings and the limits are in `FINDINGS.md`.

The only target is `uvarint`: the function `encoding/binary.Uvarint` of the Go 1.26.10 standard library.
Its main theorem is `Uvarint.Decode.result` in `lean/Uvarint/DecodeResult.lean`.
Its statement is `Uvarint.Decode.result_statement` in `lean/Uvarint/Statements.lean`.

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
Run one heavy Lean build at a time. Check with `pgrep -lx lake` before a build.

**Build the ELF again and convert it.** Needs Docker and Python.

```sh
sh go-kraken/tools/build_target.sh go-kraken/targets/uvarint/manifest.json
```

The script builds two times and compares the sha256 values.
After the run, `git status` must show no change under `targets/uvarint/build/`.
The ELF `targets/uvarint/build/target-amd64` is not tracked.

**Link check.** Needs the ELF, `clang` and `llvm-objdump`.

```sh
python3 -I -B go-kraken/tools/link_check.py go-kraken/targets/uvarint/build
python3 -I -B go-kraken/tools/link_check.py --selftest go-kraken/targets/uvarint/build
```

**Lean build.** Lake fetches Kraken at the pinned commit on the first run.

```sh
cd go-kraken/lean && lake build Machine Uvarint
cd go-kraken/lean && lake build --no-build Machine Uvarint
```

The second command must exit 0. `lake env lean` does not check that the build is current.

**Axioms gate.** Needs a built tree.

```sh
python3 -I -B go-kraken/tools/axioms_gate.py run <scratch>/gate.json <scratch>/dump.tsv
python3 -I -B go-kraken/tools/axioms_gate.py --selftest
```

The gate covers each declaration of each library of `lean/lakefile.toml`.
It also checks that each name of the hand lists in `tools/axioms-lists/` is in the dump.

**Negative cases.** Needs a built tree.

```sh
python3 -I -B go-kraken/tools/negative.py --check-cases go-kraken/targets/uvarint/negative-cases.json
python3 -I -B go-kraken/tools/negative.py go-kraken/targets/uvarint/negative-cases.json <scratch>/negative-work <scratch>/negative-result.json
python3 -I -B go-kraken/tools/negative.py --selftest
```

A mutant passes only when Lean reports an error inside the designated theorem.
A control passes only when Lean reports no error.

**Differential run.** Needs Docker and a built `Uvarint.Spec`.

```sh
sh go-kraken/targets/uvarint/differential/run.sh <scratch>/differential
```

The run compares the Go function with the Lean specification on a fixed list of inputs.
It runs Go on the architecture of the container. It does not run the amd64 machine code.

## Add a target

1. Write `targets/<name>/manifest.json` and the `main` package (`DESIGN.md`, section 4.1).
2. Run `tools/build_target.sh` and the link check.
3. Add a library `<Name>` with the glob `<Name>.+` to `lean/lakefile.toml`, with the converted code directory as an `input_dir`.
4. Supply the Lean modules of `DESIGN.md`, section 4.2. Commit the statements before the proofs.
5. Add a hand list to `tools/axioms-lists/` and a negative case file to the target directory.
