# Agent Guide

This repository proves that compiled Go functions agree with Lean specifications under the Kraken machine model.
A target is a set of functions in one compiled binary.

## Start

- Read `README.md` for commands, `DESIGN.md` for proof requirements, and `FINDINGS.md` for limits.
- Read the relevant specification, statements, assembly, proofs, and callers before editing.
- Read version pins from target manifests, `lean/lakefile.toml`, `lean/lake-manifest.json`, and `lean/lean-toolchain`.
- Keep changes within the requested task.
- Reuse existing helpers before adding abstractions or dependencies.

## Proof Integrity

- Write and commit each main statement before its proof, as `DESIGN.md` requires.
- Do not strengthen premises or weaken conclusions to make a proof succeed.
- In main statements, do not assume the execution property that the conclusion claims.
- If a statement must change, use a new name and explain the changed guarantee.
- State register conventions, size bounds, memory ownership, preserved state, and runtime contracts explicitly.
- Connect each machine-code theorem to the included program constant.
- Prove termination and the specified memory preservation conditions.
- Provide a concrete state that satisfies each main theorem's premises.
- Check statement meaning separately from proof acceptance and the axioms gate.
- Do not use `sorry`, `admit`, new axioms, `native_decide`, or `bv_decide`.
- Do not expand the axiom allowlist to bypass a failed check.
- Take expected test values from independent sources.
- If a proof fails, record the exact obligation and cause in `FINDINGS.md`.

## Architecture and Dependencies

- Keep shared specifications independent of Kraken and architecture-specific modules.
- Keep machine helpers independent of target proofs.
- Keep architecture-specific machine helpers, statements, proofs, and artifacts separate.
- Do not make one architecture depend on another.
- Share a helper only when its types, assumptions, and semantics support each intended user.
- Keep executable test backends outside the proof dependency graph.
- When adding or moving modules, update imports, Lake configuration, declaration lists, and affected checks.
- Register included assembly files as Lake inputs.

## Generated Files and Versions

- Regenerate assembly, build identifiers, and link results with their tools.
- Do not edit generated instructions or hashes to make a proof succeed.
- Run mutation checks on separate copies of their inputs.
- Do not edit dependencies under `.lake/packages`.
- Do not change Kraken or the Lean toolchain.
- If Kraken does not support an instruction, record the instruction and error in `FINDINGS.md`.
- Keep each architecture's binary and proof artifacts distinguishable.
- Do not transfer a verification claim to a different binary, specification, architecture, or machine model.

## Validation

- Use the exact check commands in `README.md`.
- During development, build the affected modules first.
- Before reporting completion, build all affected libraries and check freshness with `lake build --no-build`.
- Run the axioms gate after Lean changes.
- When changing a specification, run known-answer checks and the differential comparison.
- When changing build or conversion tools, run reproducible builds and link checks.
- When changing main statements or instruction proofs, run the relevant mutation checks and unchanged controls.
- When changing check tools, run their self-tests.
- When changing architecture support, check both the existing architecture and the new architecture.
- Treat timeouts, memory failures, and skipped checks as distinct results, never as passes.
- Do not claim that differential tests execute the target binary unless they actually do.
- Do not claim hardware validation from a proof about the Kraken model.

## Proof Performance

- Run one heavy Lean build at a time.
- Avoid concurrent builds that write to shared dependency artifacts.
- If a proof is slow, inspect the failing goal and expensive step first.
- Narrow unnecessary unfolding and automation before increasing resource limits.
- Split repeated or large arguments into focused helper lemmas.
- If a resource limit must change, record the reason and measurements before and after the change.
- Do not disable checks or linters to hide a failure.

## Documentation and Reports

- Use ASD-STE100 style for documents and agent instructions.
- State the result first and use active voice, simple tenses, and consistent terms.
- Define a technical term at its first use.
- Use at most 20 words per instruction sentence and 25 per description sentence.
- Put conditions before commands and use one instruction per sentence.
- Do not use contractions, semicolons, em dashes, or filler.
- Preserve hypotheses, quantifiers, bounds, uncertainty, and requirement strength when editing prose.
- Update documentation when commands, module paths, or verification scope change.
- Keep source migration history in commit messages instead of repeated provenance comments.
- Report what changed, exact check commands and results, skipped checks, and remaining obligations.
- Claim success only when a check or inspected source establishes it.
- Keep known limits in `FINDINGS.md` and command details in `README.md`.
