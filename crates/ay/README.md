# `ay` command-line solver

This crate builds AY's unified command-line interface. Library crates provide
the SAT, SMT, CHC, optimization, proof, benchmark, and parser components; this
crate selects those paths, applies resource limits, and renders their results.

Build the public CLI with:

```bash
cargo build --release --locked -p ay --features cli --bin ay
```

Run `ay --help`, `ay <command> --help`, and `ay --features` for the behavior of
the binary you built. The root [`README`](../../README.md) gives supported
examples and certificate-checking commands; [`LIMITATIONS`](../../LIMITATIONS.md)
states the trust and coverage boundary.

Proof emission and AY's in-process rechecking are path- and format-specific.
Treat a result as independently certified only when the documented artifact is
emitted and accepted by its named external checker. `--strict-proofs` and
`--self-check` provide fail-closed modes for workflows that require them.
