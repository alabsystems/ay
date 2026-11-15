# Fake VeriPB checkers

Five binaries that are **not** proof checkers but that every unsound gate this
repo has shipped would have accepted. They exist so "our gates reject fake
checkers" is a thing you can *run*, not a thing we assert.

Each one impersonates VeriPB well enough to get past the cheap defences: they
all answer `--version` with `veripb 3.0.2`, so the version half of
`ci/veripb.pin` waves them through, and they all print a well-formed `s ...`
verdict line on stdout.

| script | behaviour | which gate used to accept it |
| --- | --- | --- |
| `verdict-then-exit1.sh` | delegates to a **real** checker, prints its verdict verbatim, then exits 1 | every gate that asserts on the verdict text and documents "exit status is not a gate" — including the Rust resolver's self-test, which never looked at exit codes at all |
| `silent-exit0.sh` | prints nothing, exits 0 | any gate asserting `ExitStatus::success()`; the shell gates' `grep '^s '` produced an empty verdict, and `case "" in "s VERIFIED"*)` fell through to *fail*, but `scripts/pb_cert_coverage.sh`'s `*VERIFIED*` glob and several `--verify`-style CLI paths did not |
| `always-unsat.sh` | prints `s VERIFIED UNSATISFIABLE`, exits 0, whatever the input | every `case "$verdict" in "s VERIFIED"*)` gate, on a **satisfiable** instance |
| `parrot.sh` | reads the `conclusion` line out of the proof file and echoes back the matching verdict, exits 0 | every gate: it "confirms" exactly what the caller hoped for, so prefix tests, exact-conclusion tests and status/conclusion cross-checks *all* pass. Only a probe with a proof whose stated conclusion is a lie catches it |
| `comment-verified.sh` | **refuses** the proof — `s NOT VERIFIED` — with the accepting words in a `c` comment above it, exits 0 | any gate deciding acceptance by scanning stdout for a *substring*. `veripb_runner::verify_unsat` did exactly that (`stdout.contains("VERIFIED UNSATISFIABLE")`), so this fake's **refusal** was read as a verification. Note that `s NOT VERIFIED UNSATISFIABLE` carries the same substring on the verdict line itself: a comment is only the cheapest carrier |

`verdict-then-exit1.sh` needs a real checker to delegate to:

```sh
AY_FAKE_VERIPB_DELEGATE=/path/to/real/veripb ci/fake-checkers/verdict-then-exit1.sh --opb f.opb p.pbp
```

## Running the demonstration

```sh
scripts/ci/veripb_fake_checker_gate.sh
```

That script points every gate at each fake in turn and **fails if any of them
passes**. It also runs a control case: the real checker must still pass every
gate, because a suite that rejects everything is as useless as one that accepts
everything.

Surfaces covered:

| surface | how it rejects a fake |
| --- | --- |
| `scripts/cert_ci.sh` | `veripb_require_self_test` before any class is checked |
| `scripts/ci/pb_certified_gate.sh` | phase 2 self-test, then per-row exact-conclusion matching |
| `scripts/pb_cert_coverage.sh` | self-test before a single row is scored |
| `scripts/lib/veripb_verdict.sh` | the six-probe battery itself |
| `ay-pb-dev certify-unsat --veripb` | `veripb_runner::self_test` in `cert_config`, before the campaign: four probes run through `verify_unsat` itself. Reading the verdict structurally is NOT enough here and never was — `always-unsat.sh` and `parrot.sh` print a *well-formed* `s VERIFIED UNSATISFIABLE` and exit 0, and both drove this command to `VERIFICATION CAMPAIGN: 1/1 VERIFIED_UNSATISFIABLE`, exit 0 (measured). The sha256 pin fixes WHICH bytes ran, not what they do |
| `ay submission preflight pb-comp-verify --require-veripb` | positive probe **and** counter-probe in `resolve_working_veripb` |
| `ay_test_support::veripb` (every checker-backed Rust test) | `require_checker` self-tests the resolved binary once, and panics on failure — `AY_VERIPB_OPTIONAL` excuses an ABSENT checker, never a fake one |

The Rust half of the demonstration is
`crates/ay-pb/tests/veripb_fake_checker_gate.rs` (whose
`certify_unsat_cannot_obtain_a_checker_without_self_testing_it` pins that the
`certify-unsat` self-test stays wired, and that `CertifyConfig` has exactly one
construction site so no certify-* subcommand can bypass it),
`crates/ay-pb-core/src/veripb_runner.rs`'s own
`self_test_rejects_every_committed_fake_checker` (the behavioural battery for
that surface; needs `--features dev-tools`, and needs no real checker), plus
`submission_preflight_pb_comp_verify_policy_veripb_rejects_every_committed_fake`
in `crates/ay/tests/group_cli/submission_generate.rs`.
