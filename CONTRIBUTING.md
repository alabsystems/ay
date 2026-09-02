# Contributing

## Build

```bash
cargo build --release --locked -p ay --features cli --bin ay
```

A current stable Rust toolchain is the only requirement. That is a statement
about this published snapshot, whose `rust-toolchain.toml` pins stock stable
Rust; publication installs that pin, so no consumer or contributor needs a
verifying compiler to build, test, or patch AY. ALab's development tree pins
the Trust verifying compiler as its default instead (verification on, in an
advisory policy), which is why some in-tree notes talk about proof obligations
that plain stable Rust never emits.

## Test

Start with the narrowest check that covers your change, then broaden:

```bash
cargo fmt --check --all
cargo check --workspace --all-targets
cargo test -p <crate>          # e.g. -p ay-sat, -p ay-dpll
cargo check -p ay --features cli
```

AY deliberately has no hosted GitHub Actions workflow. Maintainers run the
checked-in local solver gate and the full public-export check instead:

```bash
cargo run --locked -p ay --features cli -- gate solver
publish/publish.sh check ay --check
```

The publication command builds an allowlisted export, runs fail-closed content
guards, and checks the pinned, locked public workspace in an isolated Cargo
environment. Run the narrowest relevant checks first; solver changes should
also be checked against a reference solver and, where possible, a proof or
model checker.

## Licensing

AY is Apache-2.0. Contributions are accepted under the same terms
(inbound = outbound): by submitting a change you agree it is licensed under
Apache-2.0. There is no CLA.

## Reporting

Bugs, questions, and feature requests go through GitHub Issues — see
[`SUPPORT.md`](SUPPORT.md). Suspected vulnerabilities go through the private
process in [`SECURITY.md`](SECURITY.md), not public issues.
