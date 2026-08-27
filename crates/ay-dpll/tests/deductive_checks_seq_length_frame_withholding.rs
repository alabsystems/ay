// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! PUBLICATION pin: a BV-LIA bridged length frame must never be DECIDED and
//! then WITHHELD.
//!
//! REGRESSION PINNED: `d02df7059` ("fix(cert): the BV-LIA original-rebuild
//! scope dropped scalar sorted roots"). On these queries the original-rebuild
//! lane could not re-ground a step the solver had genuinely derived, the
//! strict presentation was withheld, and a correct refutation was published as
//! `unknown` — which for the consumer is a lost obligation, not a slow one.
//!
//! POSTURE — READ `solve()` BEFORE CHANGING ANYTHING HERE. The fixtures are
//! byte-exact `to_smtlib2()` captures and carry the option set deductive-checks sends.
//! One production option is NOT in that dump and is re-installed by `solve()`:
//! the 30 s nominal solve wall. Replaying without it is not a conservative
//! substitution — it runs under ay's 300 s `DEFAULT_SAFETY_DEADLINE`, i.e. a
//! MORE permissive posture than production, and it costs ~5.5x more wall time
//! (≈95 s vs ≈18 s for the whole file) for a strictly WEAKER discriminator.
//!
//! MEASURED. ay `284248ce1` (HEAD) vs `6e80d4bf5` (`d02df7059^`), dev profile,
//! interleaved arms, 9 observations per arm: 3 whole-file runs at box load
//! 24-30, 3 at load 61-71, and 3 sequential passes (one fixture per process,
//! `--exact --test-threads=1`).
//!
//! | fixture                   | withheld at `6e80d4bf5` | at `284248ce1` (HEAD) |
//! |---------------------------|-------------------------|-----------------------|
//! | `a032_q-i2b-sos_decb4f6a` | 9/9                     | unsat, 13.6-17.1 s    |
//! | `a032_q-i2b-sos_62a76f32` | 9/9                     | unsat, 13.4-17.6 s    |
//! | `a032_q-i2b-sos_56dd8934` | 8/9                     | unsat, 13.6-17.5 s    |
//! | `a032_q-i2b-sos_e28ec85a` | 8/9                     | unsat, 15.3-17.8 s    |
//! | `a032_q-i2b-sos_f9704f86` | 4/9                     | unsat, 14.3-17.7 s    |
//! | `a032_q-i2b-sos_8e73a521` | 1/9                     | unsat, 14.0-17.4 s    |
//!
//! Every withholding above is `unknown (SelfCheckRejected)` — DECIDED, then
//! refused. At HEAD the class never withholds and never times out: every
//! observation is `unsat`, worst 17.8 s against the 30 s wall.
//!
//! WHY SIX PINS AND NOT ONE. At `6e80d4bf5` the withholding is deterministic as
//! a SET and not as a membership: all six are in the withholding class, but
//! only `decb4f6a` and `62a76f32` withhold in 9/9, and which of the others go
//! with them shifts with scheduling — `f9704f86` withholds under low-load
//! parallelism and publishes under high-load parallelism; `8e73a521` does
//! nearly the reverse. So any single fixture is a flaky pin and the family is
//! not, which is also why the failure message names the fixture rather than a
//! count. The FILE is red in 9/9.
//!
//! THERE IS NO GREEN CONTROL INSIDE THIS FAMILY, and an earlier draft of this
//! file was wrong to call `f9704f86` one. That reading came from replaying
//! WITHOUT the production wall, where `f9704f86` gets through; under the wall
//! it withholds in 4 of 9 observations. The whole `a032_q-i2b-sos` class
//! regressed. The class control is
//! `named_false_terminated_frames_publish_unsat` — same capture, same
//! `:named`-core machinery, `unsat` at BOTH revisions in 9/9 — so a red pin
//! above still localises to the withholding lane rather than to the fixture
//! loader or the core machinery.
//!
//! WHOLE-FILE RUNS, 3 per arm per load band, every run in a band identical:
//!
//! * `284248ce1` (HEAD): ok, 8 passed / 0 failed — 16.65 / 17.44 / 18.60 s at
//!   load 24-30, and 17.52 / 17.88 / 18.42 s at load 61-71. A separate probe
//!   under 28 CPU spinners: ok 8/8 in 17.79 s and 17.24 s. The cost is
//!   budget-driven, not compute-driven, so it does not move with load — which
//!   is what makes a 30 s wall a safe place to stand (~1.7x headroom at load
//!   71).
//! * `6e80d4bf5` (`d02df7059^`): FAILED in every run — 5, 5, 4 of 8 at load
//!   24-30 and 4, 4, 4 at load 61-71, plus red in all 3 sequential passes.
//!
//! WHAT THIS FILE GOES RED ON. Three things, and only the first is the pinned
//! regression:
//!
//! 1. a verdict DECIDED and then WITHHELD (`DECIDED_THEN_WITHHELD` below) —
//!    the publication regression `d02df7059` fixed;
//! 2. an answer never reached (`NEVER_REACHED_AN_ANSWER`) — a COST failure
//!    inside the 30 s wall, given its own message so it cannot be misread as
//!    (1). Measured headroom at HEAD is ~1.7x and load-independent;
//! 3. any other non-`unsat`, via the trailing `assert_eq!`. This INCLUDES
//!    `unknown (Incomplete)`, i.e. a COMPLETENESS loss on this family. That is
//!    intended, and is stated here rather than denied: two sibling
//!    `a032_q-i2b-sos` queries from the same capture did go `unsat` ->
//!    `Incomplete` inside this very window, so the case is live. A refutation
//!    ay stops being able to reach is as lost to deductive-checks as one it reaches
//!    and withholds; what the two-branch split buys is that the reader is told
//!    WHICH happened.
//!
//! WHY NOTHING IN ay's OWN SUITE SAW THIS. The shape is
//! `(Array (_ BitVec 64) (_ BitVec 32))` carrier + `:produce-unsat-cores` with
//! EVERY assertion `:named` + an `int2bv` STORE INDEX inside a three-deep
//! `store` chain that a `forall` reads back. Across `crates/ay-dpll/tests`,
//! `set_produce_unsat_cores` appears in three files, all `Logic::QfLia` over
//! `Sort::Int`; the intersection of cores with arrays or quantifiers is empty;
//! and `int2bv` is used as a store index nowhere at all.
//!
//! COST, AND WHAT WAS TRIED. ≈18 s for the whole file in parallel (≈92 s
//! sequential), against a 30 s production wall. Two axes of reduction were
//! tried. STRUCTURAL, on the fixtures: dropping the second length frame, or
//! the ground `select` instances, makes the query answer `unsat` at
//! `6e80d4bf5` too — it destroys the discrimination — and only the
//! literal-`true` assertions can go, which saves nothing. OPTIONS, on the
//! harness: installing deductive-checks's own 30 s wall (`solve()`) cut the file from
//! ≈95 s to ≈17 s and made it discriminate on MORE fixtures, not fewer. That
//! is the whole of the reduction available; the remaining ~14 s per fixture is
//! what the query costs.
#![allow(clippy::panic)]

use std::path::PathBuf;
use std::time::Instant;

use ay_dpll::Executor;
use ay_frontend::parse;
use ntest::timeout;

/// `UnknownReason` spellings that mean **ay DECIDED this query and then refused
/// to publish the decision**.
///
/// Both are ay's own words. `SelfCheckRejected`: "AY *did* reach `sat` or
/// `unsat`, its own model evaluator or strict refutation checker refused to
/// certify it". `ProofTrusted`: "AY reached `unsat` and refused to stand behind
/// it ... the same class of fact as `SelfCheckRejected`". `InternalError` is
/// documented as "Internal executor error (e.g., model validation failure)",
/// which is the same shape: a verdict computed and then dropped.
///
/// Deliberately NOT including `Incomplete`: that means ay never decided, which
/// is a different (and older) gap — see the module doc's `Incomplete` note.
///
/// These strings are matched against `format!("{r:?}")` of
/// `Executor::unknown_reason() -> Option<UnknownReason>`, so every entry must
/// be an actual `UnknownReason` variant. It is not enough for a name to exist
/// somewhere in ay: this list previously carried `ModelNotValidated` (a
/// `SolveDecisionProfileModelConsumerReason`) and `SolveDeadline` (an
/// `UnknownOrigin`), neither of which can ever appear here, so two of its five
/// entries were dead.
const DECIDED_THEN_WITHHELD: &[&str] = &["SelfCheckRejected", "ProofTrusted", "InternalError"];

/// `UnknownReason` spellings that mean **ay never reached an answer**.
///
/// Per the enum's own doc, every variant other than `SelfCheckRejected` /
/// `ProofTrusted` is in this class. These get a DIFFERENT message: an expired
/// budget is a cost problem, not a publication regression, and printing "was
/// DECIDED and then WITHHELD" for a deadline expiry sends the reader hunting a
/// regression that did not occur.
const NEVER_REACHED_AN_ANSWER: &[&str] =
    &["Timeout", "ResourceLimit", "MemoryLimit", "Interrupted"];

fn fixture(name: &str) -> String {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/deductive_checks_seq_length_frame")
        .join(name);
    std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()))
}

/// Solve one captured query in deductive-checks's posture.
///
/// The fixture text is byte-exact and carries the option set deductive-checks's
/// `to_smtlib2()` dump serialises. One option is NOT in that dump, and it has
/// to be re-installed here: deductive-checks drives every one of these queries through
/// `Solver::set_timeout(DEFAULT_SOLVER_NOMINAL_TIMEOUT_MS = 30_000)`
/// (deductive-checks-core `encoder/mod.rs` `with_limits`, constant at
/// `encoder/verification/timeout.rs`), and `Solver::to_smtlib2()` does not
/// serialise the timeout. A bare replay therefore runs under ay's 300 s
/// `DEFAULT_SAFETY_DEADLINE` instead — a MORE permissive posture than
/// production, not a conservative one — and lets the `:produce-unsat-cores`
/// deletion scan burn a ~90 s wall-clock shrink budget on a query it has
/// ALREADY decided. `(set-option :timeout 30000)` installs the deadline
/// "via the same mechanism as `set_timeout`" (ay `executor.rs`, `:timeout`
/// handling), leaves the fixtures untouched, cuts the file's cost ~5.5x, and
/// DISCRIMINATES BETTER — see the module doc's measured table.
fn solve(name: &str) -> (String, Option<String>, f64) {
    let script = format!("(set-option :timeout 30000)\n{}", fixture(name));
    let commands = parse(&script).unwrap_or_else(|e| panic!("parse {name}: {e}"));
    let mut executor = Executor::new();
    let started = Instant::now();
    let outputs = executor
        .execute_all(&commands)
        .unwrap_or_else(|e| panic!("execute {name}: {e}"));
    let elapsed = started.elapsed().as_secs_f64();
    let verdict = outputs
        .iter()
        .find(|line| matches!(line.trim(), "sat" | "unsat" | "unknown"))
        .cloned()
        .unwrap_or_else(|| "<no verdict>".into());
    let reason = executor.unknown_reason().map(|r| format!("{r:?}"));
    (verdict, reason, elapsed)
}

/// The assertion every pin below shares.
fn assert_not_withheld(name: &str) {
    let (verdict, reason, elapsed) = solve(name);
    eprintln!("{name}: {verdict} ({reason:?}) in {elapsed:.2}s");
    let matches_class = |class: &[&str]| {
        verdict == "unknown"
            && reason
                .as_deref()
                .is_some_and(|r| class.iter().any(|w| r.contains(w)))
    };
    assert!(
        !matches_class(DECIDED_THEN_WITHHELD),
        "{name} was DECIDED and then WITHHELD ({reason:?}) — for the consumer \
         that is not a slow answer, it is a refutation that stops counting as \
         proved. This is the publication regression this file pins. Solved in \
         {elapsed:.2}s."
    );
    assert!(
        !matches_class(NEVER_REACHED_AN_ANSWER),
        "{name} never reached an answer ({reason:?}) in {elapsed:.2}s. This is \
         a COST failure inside the 30 s production wall, not a publication \
         regression — do not read it as one. Expected ~16-18s at a healthy \
         revision; check box load and the deletion-scan budget before \
         suspecting the certification lane."
    );
    assert_eq!(
        verdict, "unsat",
        "{name} is a refutable length-frame obligation and must be published \
         `unsat`; got {verdict} ({reason:?}) in {elapsed:.2}s"
    );
}

/// PIN — BV64 carrier, goal `1 <= len` on the FIRST length frame.
#[test]
#[timeout(120_000)]
fn bv64_first_frame_length_bound_publishes_unsat() {
    assert_not_withheld("a032_q-i2b-sos_56dd8934.smt2");
}

/// PIN — BV64 carrier, goal on the SECOND length frame.
#[test]
#[timeout(120_000)]
fn bv64_second_frame_length_bound_publishes_unsat() {
    assert_not_withheld("a032_q-i2b-sos_decb4f6a.smt2");
}

/// PIN — BV64 carrier, second frame, distinct element values.
#[test]
#[timeout(120_000)]
fn bv64_second_frame_alternate_elements_publishes_unsat() {
    assert_not_withheld("a032_q-i2b-sos_62a76f32.smt2");
}

/// PIN — BV64 carrier, first frame, distinct element values.
#[test]
#[timeout(120_000)]
fn bv64_first_frame_alternate_elements_publishes_unsat() {
    assert_not_withheld("a032_q-i2b-sos_e28ec85a.smt2");
}

/// PIN — BV32 carrier (the 32-bit pointer-width lowering), second frame.
#[test]
#[timeout(120_000)]
fn bv32_second_frame_length_bound_publishes_unsat() {
    assert_not_withheld("a032_q-i2b-sos_8e73a521.smt2");
}

/// PIN — BV32 carrier, first frame. NOT a control: under the production wall
/// this fixture withholds at `6e80d4bf5` in 4 of 9 observations. An earlier
/// draft called it a class control on the strength of a no-wall replay; the
/// module doc records why that was wrong.
#[test]
#[timeout(120_000)]
fn bv32_first_frame_length_bound_publishes_unsat() {
    assert_not_withheld("a032_q-i2b-sos_f9704f86.smt2");
}

/// CLASS CONTROL. The `(assert (! false :named dnN))` terminator — a
/// preprocessing-time refutation delivered THROUGH the named-core machinery.
/// 120 of the 284 captured production calls end this way and ay has no other
/// test for it. Sub-second, and `unsat` at BOTH revisions in 9/9 observations,
/// so it separates "the withholding lane regressed" from "the fixture loader
/// or the named-core path broke". It is the control this family has; the
/// `a032_q-i2b-sos` fixtures above all regressed together.
#[test]
#[timeout(120_000)]
fn named_false_terminated_frames_publish_unsat() {
    for name in [
        "a032_q-i2b-false-sos_16a9cf2b.smt2",
        "a032_q-i2b-false-sos_26abd260.smt2",
        "a032_q-i2b-false-sos_cc8e2b0a.smt2",
        "a032_q-i2b-false-sos_e57b31a0.smt2",
    ] {
        assert_not_withheld(name);
    }
}

/// WRONG-FACT TWINS — the no-over-acceptance direction.
///
/// Two more captured queries from the same suite, and the same
/// BV-indexed-carrier + `int2bv` length-bridge posture, but SATISFIABLE: they
/// ask `5 <= len` of a frame whose length is 1. Whatever else changes on this
/// lane, they must never come back `unsat` — that would be a false refutation
/// of a true fact, which in deductive-checks is a false VERIFY.
///
/// They are also the cheapest statement of a SEPARATE, still-open gap: at every
/// revision measured here ay answers them `unknown (Incomplete)` rather than
/// `sat`, so deductive-checks loses the COUNTEREXAMPLE on this class. That is a
/// completeness gap, not a soundness one, and it is deliberately not asserted
/// on: this test forbids only the unsound direction.
#[test]
#[timeout(120_000)]
fn satisfiable_length_bound_twins_are_never_refuted() {
    for name in ["a005_i2b_dda81e46.smt2", "a005_i2b_7336f5b4.smt2"] {
        let (verdict, reason, elapsed) = solve(name);
        eprintln!("twin {name}: {verdict} ({reason:?}) in {elapsed:.2}s");
        assert_ne!(
            verdict, "unsat",
            "{name} asks `5 <= 1`, whose negation is satisfiable; refuting it \
             would be a false refutation. got {verdict} ({reason:?}) in {elapsed:.2}s"
        );
    }
}
