# Product Requirements Document: Otter Rust Port

## Summary
Port the legacy Otter 3.3 first-order theorem prover from C to a safe, maintainable Rust codebase while preserving behaviour across the bundled example suite and preparing the project for future enhancements.

## Goals
- Provide a drop-in Rust binary that matches Otter's command-line interface and outputs for existing `.in` files.
- Replace C data structures (`types.h`, `macros.h`) with idiomatic Rust equivalents without FFI glue.
- Establish automated regression testing using `_wb/otter-examples` to ensure parity with the historical results.
- Maintain developer ergonomics with Cargo-based workflows, modular architecture, and comprehensive documentation.

## Non-Goals
- Changing or extending inference rules beyond the C implementation.
- Rewriting example inputs or outputs except for format normalisation (e.g., timestamps).
- Supporting external integrations beyond those shipped with Otter 3.3 (e.g., third-party foreign functions) in the initial release.

## Personas
- **Research Developer**: Runs automated proofs, expects deterministic outputs and clear failure diagnostics.
- **Project Maintainer**: Contributes code, needs modular structure, tests, and documentation to onboard quickly.
- **CI/CD Pipeline**: Executes regression tests for every change, must detect behavioural deviations reliably.

## Requirements
1. **Parity Harness**
   - Discover legacy examples and capture golden outputs from the C binaries (#PARITY-1).
   - Provide a Rust regression runner that executes the new prover against the examples and diffs outputs (#PARITY-2).

2. **Core Infrastructure**
   - Implement symbol tables, terms, literals, clauses, and global state in Rust (#CORE-1).
   - Port configuration parsing and option handling (`options.c`, `io.c`, `header.h` flags/params) (#CORE-2).
   - Recreate logging/timing behaviour with feature flags (#CORE-3).

3. **Inference Engine**
   - Port clause indexing, selection, and weighting logic (`clause.c`, `index.c`, `weight.c`) (#ENGINE-1).
   - Implement unification, paramodulation, resolution, demodulation, and related inference routines (#ENGINE-2).
   - Rebuild splitting, hot list, and linked inference support (#ENGINE-3).

4. **Binary & Tooling**
   - Replace `main.c` with a Rust CLI that mirrors argument handling (#CLI-1).
   - Port auxiliary tools (e.g., `formed`) where applicable (#CLI-2).
   - Provide documentation and developer guides for running benchmarks and regression suites (#CLI-3).

## Milestones
1. **M1: Foundations (Week 1-2)**
   - Rust scaffolding for data structures and configuration completed.
   - Regression suite enumerates examples and records current C outputs.

2. **M2: Parsing & Clause Lifecycle (Week 3-5)**
   - Input parsing and clause construction run fully in Rust.
   - Basic clauses can be read, transformed, and emitted.

3. **M3: Inference Core (Week 6-10)**
   - Resolution, unification, demodulation, and indexing modules ported.
   - Majority of regression examples pass in Rust with minimal diffs.

4. **M4: Full Parity (Week 11-12)**
   - CLI parity and auxiliary tooling complete.
   - All automated tests pass; documentation published.

## Success Metrics
- 100% of regression examples pass with acceptable output diffs (timestamp/format tolerances defined).
- `cargo test` and regression runner complete under a target runtime budget (<15 minutes).
- Code coverage for core modules exceeds 80% via unit and integration tests.

## Risks & Mitigations
- **Complex global state translation**: Address by designing explicit Rust structs/modules to replace global arrays and by incremental refactors.
- **Output divergence**: Normalise non-semantic differences (timestamps, whitespace) and use structured comparisons.
- **Resource constraints**: Prioritise modules based on dependency graph from `proto.h`; implement continuous benchmarks to detect performance regressions.

## Open Questions
- How should legacy foreign function hooks be represented in Rust (plug-in trait vs. static registry)?
- Should we retain legacy command scripts (`Run_group`, `Run_all`) or replace them with Rust-based drivers?
- What minimum Rust version and edition will we officially support beyond the current default?

