# Contributing

## Build

```bash
cargo build --release --locked -p ay --features cli --bin ay
```

A current stable Rust toolchain is the only requirement.

## Test

Start with the narrowest check that covers your change, then broaden:

```bash
cargo fmt --check --all
cargo check --workspace --all-targets
cargo test -p <crate>          # e.g. -p ay-sat, -p ay-dpll
cargo check -p ay --features cli
```

Public CI checks the complete workspace under every public feature; exercises
SAT, SMT, CHC, LRAT, proof replay, PB model admission, and approximate BCP; and
smoke-tests the README's CLI and Alethe path. Please still run the narrowest
relevant checks locally before sending a change. Solver changes should also be
checked against a reference solver and, where possible, a proof or model
checker.

CI downloads a checksum-pinned Carcara release and independently replays the
quick-start Alethe certificate. Solver or proof changes should still use the
narrowest relevant checker tests locally before the full CI gate.

## Licensing

AY is Apache-2.0. Contributions are accepted under the same terms
(inbound = outbound): by submitting a change you agree it is licensed under
Apache-2.0. There is no CLA.

## Reporting

Bugs, questions, and feature requests go through GitHub Issues — see
[`SUPPORT.md`](SUPPORT.md). Suspected vulnerabilities go through the private
process in [`SECURITY.md`](SECURITY.md), not public issues.
