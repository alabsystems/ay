# proof-fixtures — known-answer test cases for the proof harness

These are not benchmarks. They are **calibration weights for the instrument.**

Proof checking is how this project decides whether it is making progress. If the
harness lies, every number derived from it is worthless — and it has lied three
times, each time in the same direction: reporting success while having measured
nothing.

| # | defect | what it printed |
|---|--------|-----------------|
| 1 | `check_proofs.sh` wrote **relative** paths into the work-cell `ln -sf`; every symlink dangled and AY read nothing | `RESULT: PASS`, over **zero** checked proofs |
| 2 | `check_proofs.sh` recorded carcara's **first stderr line**, which is a `[WARN]`, not the `[ERROR]` | correct verdict, **fictional cause** — two instances were filed under an "assume-after-step" defect class that does not exist |
| 3 | `soundness_sweep.py` scanned only **stdout**, but `(:reason-unknown …)` prints to **stderr** | `DEFINITE_BUT_UNDECIDED` could physically fire only via `rc == 124` |

Every one was found by accident, late, after conclusions had been drawn. The
answer is not vigilance, it is fixtures whose correct classification is known in
advance, so a harness that stops measuring is caught by its own test suite.

Run the suite:

```
scripts/selftest_proof_harness.py                   # 0 = the instrument works
scripts/selftest_proof_harness.py --seed-fault all  # prove it can go red
```

A fourth instance of defect 1 was found **by these fixtures' measurement guard**
on 2026-08-02: the absolutize fix had only ever been applied to the `.jsonl`
selection reader, so `check_proofs.sh benchmarks/…/ALIA/piVC` (a relative
directory) still dangled all 41 symlinks. See `c01`-vs-relative-path coverage in
`selftest_proof_harness.py::test_relative_corpus`.

---

## How a fixture works

Each fixture is **one self-contained `.smt2` file**: a legal SMT-LIB problem
(carcara, z3 and cvc5 all read it) carrying `;` comment directives.

`benchmarks/proof-fixtures/fake_ay.py` is a deterministic stand-in for the `ay`
binary. It reads those directives and does exactly what they say — prints a
given answer, exits with a given code, writes a given canned Alethe proof. The
self-test then runs the **real** `scripts/check_proofs.sh` and
`scripts/soundness_sweep.py` with `--ay` / `AY_BIN` pointed at the stub.

Only the *solver* is faked. Work-cell symlinking, answer parsing, carcara
invocation, reason extraction, counters, guards and exit codes are all the
production code paths.

This is what lets the suite cover classifications real AY cannot produce on
demand — "emits a proof carcara cannot parse", "answers `sat` on an unsat
instance" — and to do so in about a second, deterministically.

### Directives read by the stub

```
; AY-ANSWER: unsat            what to print on stdout (omit ⇒ print nothing)
; AY-STDERR: (:reason-unknown "…")   an extra stderr line
; AY-RC: 124                  process exit code (default 0)
; AY-PROOF-BEGIN              start of the canned Alethe proof
;| (assume h1 p)              proof body, one line per `;|`
; AY-PROOF-END
```

The proof is **embedded**, not kept in a sibling file, because the harness hands
the solver a symlink inside a scratch cell — anything resolved relative to the
argument would be defeated by exactly the bug class these fixtures exist to
catch.

### Directives read by the self-test

```
; EXPECT-CHECK-VERDICT: invalid          check_proofs.sh classification
; EXPECT-CHECK-REASON-CONTAINS: and_neg
; EXPECT-CHECK-REASON-EXCLUDES: appears after
; EXPECT-CHECK-REASON-IS-EMPTY: 1
; EXPECT-CHECK-WARN-CONTAINS: appears after
; EXPECT-SWEEP: clean | flagged-unconfirmed | confirmed-wrong
; EXPECT-SWEEP-FLAGS: CONTRADICTS_STATUS
```

---

## `checker/` — one per classification `check_proofs.sh` can emit

| fixture | expected | why it exists |
|---|---|---|
| `c01_valid_resolution` | `valid` | the only outcome that counts as a pass |
| `c02_holey_hole_step` | `holey` | `hole` is the honest escape hatch; must never be reported as `valid` **or** as `invalid` |
| `c03_invalid_unknown_rule` | `invalid`, reason ⊃ `unknown rule` | the original 2026-07-30 defect (`:rule dt_distinct`) |
| `c04_invalid_parse_error` | `invalid`, reason ⊃ `parser error` | the S2 class: a `declare-fun` leaking into the proof. An unparseable artifact is `invalid`, not `checker-error` |
| `c05_invalid_warn_masks_error` | `invalid`, reason ⊃ `and_neg`, reason ⊅ `appears after` | **defect 2.** carcara emits `[WARN]` before `[ERROR]`; the reason must name the rule that failed |
| `c06_valid_with_warning` | `valid`, reason **empty**, warning kept | the over-correction guard: "treat any stderr as a failure" would break this. Warnings are recorded, never promoted |
| `c07_unsat_no_proof` | `no-proof` | unsat with no certificate is a gap, not a lie — fatal only under `--require-proof` |
| `c08_wrong_answer_sat` | `WRONG-ANSWER` | AY contradicting a declared `:status` is a hard failure, never bucketed with "unknown/timeout" |
| `c09_not_unsat_unknown` | `unknown` | a legitimate non-answer, and **not** the same thing as `no-answer` |

The set deliberately contains bad proofs, so a *healthy* harness exits **1** on
this directory (real defects found) — never 0, and never 3 (measurement broken).

## `sweep/` — one per classification `soundness_sweep.py` can emit

| fixture | expected | why it exists |
|---|---|---|
| `s01_clean` | not flagged | AY agrees with the header and reports no doubt |
| `s02_contradicts_status_confirmed` | `CONFIRMED-WRONG` | a real wrong answer: AY says `sat` on a genuinely unsat problem, z3 and cvc5 agree against it |
| `s03_definite_but_undecided_stderr` | flagged, `unconfirmed` | **defect 3.** The `(:reason-unknown …)` admission is on **stderr** with `rc 0`, so this fires *only* through the stderr scan |
| `s04_definite_but_undecided_rc124` | flagged, `unconfirmed` | the other arm — clean stderr, timeout exit code |
| `s05_bad_header_unconfirmed` | flagged, `unconfirmed` | the header is **wrong** and AY is right. Without this fixture the whole z3/cvc5 cross-check could be deleted and the suite would still pass |

## `guard/` — "did we actually measure anything?"

| directory | trips | rule |
|---|---|---|
| `nothing_checked/` | guard 1 | every instance answers `unknown`: each outcome legitimate, but **0 proofs reached carcara**, so the run says nothing about proof emission |
| `no_answer/` | guards 1 + 2 | AY prints nothing at all — the dangling-symlink signature |
| `mixed_no_answer/` | guard 2 only | one healthy instance keeps guard 1 quiet, so the no-answer **rate** is tested on its own |

Both guards exit **3**, distinct from the 1 that means "AY emitted a bad proof",
so a caller can tell *"this is a defect"* from *"this number is not evidence"*.

**Why a rate, and why 20%?** `sat` / `unsat` / `unknown` / `timeout` are printed
*outcomes* and are all fine. `no-answer` is the *absence* of an outcome — a
crash, an unreadable input, a broken work cell. A healthy run sits at ~0%; the
collapse that printed PASS was at 100%. 20% is an order of magnitude above
healthy and far below any collapse, and being a rate it does not fail a
1000-instance sweep over one crashed instance. Tunable with
`--max-no-answer-pct` (`0` makes any no-answer fatal); `--allow-nothing-checked`
overrides guard 1 when emptiness is the thing being probed.

## Provenance — *what* did it measure?

The guards answer "did we measure anything?". A fourth incident, 2026-08-02,
showed that is only half the question.

An A/B of `check_proofs.sh` itself was run from a **copy** of the script in a
scratch dir. `$AY` defaults to `<script dir>/../target/release/ay`, so the copy
silently re-pointed it at a month-old frozen `ay` that happened to be sitting
there. The two arms disagreed — `invalid` vs `holey` — and the disagreement was
read as an effect of the change under test. It was a different solver.

Nothing in the record could have revealed that: it held verdicts and no
identity. So `--report-tsv` now opens with `#` provenance lines —

```
# ay        /path/to/ay
# ay-build  ay 0.5.0+build.6427.153665fb9…@2026-08-02T19:15:10Z
# carcara   carcara 1.1.0 [git main 9a352ee]  /path/to/carcara
# corpus    /path/to/corpus
# started   2026-08-02T…Z
```

— and the summary prints `measured-with <stamp>` even under `--quiet`, which
suppresses the banner. `selftest_proof_harness.py` asserts the record names the
binary **actually used**, not the repo default; `--seed-fault
provenance-stripped` proves that assertion has teeth. Readers must skip leading
`#` lines (`read_tsv()` in the self-test does).

## `selections/checker.jsonl`

The `.jsonl` input path, used to exercise `--bench-root` both ways: with the
right root it must measure (2 proofs reach carcara), with a bogus one it must
exit 2 rather than report a clean run over zero instances.

---

## Adding a fixture

1. Write one `.smt2` with the `AY-*` directives for the stub and the
   `EXPECT-*` directives for the assertion.
2. **Probe carcara by hand first** (`carcara check proof.alethe problem.smt2`)
   and paste the verdict you actually observed. Every verdict in this directory
   was measured, not predicted — two diagnoses in this campaign were confidently
   wrong because they were reasoned rather than tested.
3. Re-run the self-test.
4. If the fixture guards against a specific regression, add a matching entry to
   `FAULTS` in `scripts/selftest_proof_harness.py` and confirm
   `--seed-fault <name>` reports `caught`. A fixture nothing can break is not
   protecting anything.

Seeded-fault anchors must match **exactly once** in the target script. The
first `relative-symlink` fault matched the explanatory *comment* that quotes the
same line, so the defect was never applied and the suite was reported as having
no teeth; `--seed-fault` now refuses an ambiguous anchor.
