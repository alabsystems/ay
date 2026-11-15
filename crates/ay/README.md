# `ay` command-line solver

This crate builds AY's unified command-line interface. Library crates provide
the SAT, SMT, CHC, optimization, proof, benchmark, and parser components; this
crate selects those paths, applies resource limits, and renders their results.

Build the public CLI with:

```bash
targo --unverified build --release --locked -p ay --features cli --bin ay   # Trust toolchain
cargo build --release --locked -p ay --features cli --bin ay                # stock Rust
```

Run `ay commands`, `ay <command> --help`, and `ay --features` for the behavior
of the binary you built. The root [`README`](../../README.md) gives supported
examples and certificate-checking commands; [`LIMITATIONS`](../../LIMITATIONS.md)
states the trust and coverage boundary.

Proof emission and AY's in-process rechecking are path- and format-specific.
Treat a result as independently certified only when the documented artifact is
emitted and accepted by its named external checker. `--rigor certified`
(legacy `--self-check`) is the fail-closed mode for workflows that require
it; `--rigor strict` (legacy `--strict-proofs`) adds AY's strict proof checker
and downgrades a terminal trust-backed `unsat` it cannot prove to `unknown`.
