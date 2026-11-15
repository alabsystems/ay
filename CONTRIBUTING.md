# Contributing

## Build

AY builds with ALab's Trust compiler, which `rust-toolchain.toml` pins; the
[README](README.md#build) says how to install it. `targo` is the spelling for
every command (`targo --unverified test`, `targo fmt`, `targo tippy`).

```bash
targo --unverified build --release --locked -p ay --features cli --bin ay
```

## Test

Start with the narrowest check that covers your change, then broaden:

```bash
targo fmt --check --all
targo --unverified check --workspace --all-targets
targo --unverified test -p <crate>          # e.g. -p ay-sat, -p ay-dpll
targo --unverified check -p ay --features cli
```

AY has no hosted GitHub Actions workflow. Ordinary changes use the native
landing command after focused checks:

```bash
targo --unverified run --locked -p ay --features cli -- gate land
```

Publication validation is separate: run `pub check` when preparing a public
release. It checks the allowlisted export and the pinned public workspace.
Solver changes also need a discriminating regression and comparison against a
reference solver or independent proof/model checker. Do not rerun unrelated
benchmark campaigns or legacy script suites to land a local change.

## Licensing

AY is Apache-2.0. Contributions are accepted under the same terms
(inbound = outbound): by submitting a change you agree it is licensed under
Apache-2.0. There is no CLA.

## Reporting

Bugs, questions, and feature requests go through GitHub Issues — see
[`SUPPORT.md`](SUPPORT.md). Suspected vulnerabilities go through the private
process in [`SECURITY.md`](SECURITY.md), not public issues.
