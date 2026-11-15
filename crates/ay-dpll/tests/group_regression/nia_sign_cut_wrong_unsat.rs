// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Wrong-UNSAT regression: an NIA refutation must never rest on a model guess
//! (#nia-sign-cut-soundness).
//!
//! On main `b1c1f8f201` (2026-09-21) these four satisfiable QF_NIA problems
//! (z3 5.1.0 `sat`, hand-checkable models in each banner) were answered
//! `unsat` in BOTH postures. The NIA refinement loop asserts a sign cut
//! (`z >= 0` from the current LRA model value) and an integer-rounding pin
//! (`z = round(model(z))`) into a tentative LIA scope as bounds whose reason
//! is the VARIABLE TERM — a heuristic that steers the LP, never a theorem —
//! and the LIA's side checks (`check_modular_for_var`, the direct-enumeration
//! box, the Diophantine fixed-variable fold) read those bounds as facts and
//! returned the whole asserted set as a conflict, which the loop then
//! published as "Only exact lemmas were used. UNSAT is genuine."
//!
//! Fixed in the LIA: its verdict-producing reads use JUSTIFIED bounds only
//! and its `check()` refuses to publish a conflict citing a non-live literal
//! (`ay-lia/src/justified_bounds.rs`), so a bound whose reason is a term can
//! never reach a refutation. The NIA counts every guess in scope and, in
//! debug builds under `--debug nia`, re-derives an UNSAT observed with one in
//! force in a guess-free scope as an audit (`ay-nia/src/check_loop.rs`); a
//! `Sat` is claimed only for a point the exact evaluator does not refute, so
//! the `sat` these files deserve survives the executor's model gate
//! (`ay-nia/src/bounded_enum.rs`). Theory-level pins live in
//! `ay-nia/src/sign_cut_soundness_tests.rs`; this pin exercises the executor
//! pipeline the wrong verdict actually went through. Corpus-free.
//!
//! `unknown` would be a completeness loss, reported but not wrong; `unsat`
//! is the regression. The last pin is the SAT side of the same change: a
//! branch-and-bound split the loop requests on a STALE tableau point must not
//! send the split loop walking.

use std::time::Duration;

use ay_dpll::Executor;
use ay_frontend::parse;
use ntest::timeout;

/// `benchmarks/smt/wrong-verdict/sat_nia_sign_cut_1.smt2`
/// (z3 model x = -23, y = -46, z = -15).
const SAT_NIA_SIGN_CUT_1: &str = r#"
(set-logic QF_NIA)
(set-info :status sat)
(declare-const x Int)
(declare-const y Int)
(declare-const z Int)
(assert (= (* 2 x) y))
(assert (= (* 3 z) (+ y 1)))
(assert (>= y (- 2000)))
(assert (<= y 1))
(assert (>= (* x z) 1))
(assert (<= (* x z) 400))
(check-sat)"#;

/// `benchmarks/smt/wrong-verdict/sat_nia_sign_cut_2.smt2`
/// (z3 model x = -1, w = -2, z = -7).
const SAT_NIA_SIGN_CUT_2: &str = r#"
(set-logic QF_NIA)
(set-info :status sat)
(declare-const x Int)
(declare-const z Int)
(declare-const w Int)
(assert (= (* 3 w) (+ z 1)))
(assert (= (+ (* 2 x) z) (- 9)))
(assert (<= z 1))
(assert (>= z (- 2000)))
(assert (>= (* x z) 1))
(assert (<= (* x z) 400))
(check-sat)"#;

/// `benchmarks/smt/wrong-verdict/sat_nia_sign_cut_3.smt2`
/// (z3 model w = -13, x = -7, z = -40): contradictory sign guesses `x >= 0`
/// and `x <= 0` accumulated in one tentative scope pinned `x = 0`.
const SAT_NIA_SIGN_CUT_3: &str = r#"
(set-logic QF_NIA)
(set-info :status sat)
(declare-const x Int)
(declare-const z Int)
(declare-const w Int)
(assert (= (* 3 w) (+ z 1)))
(assert (= (- (* 5 x) (* 2 z)) 45))
(assert (<= x 1))
(assert (>= z (- 2000)))
(assert (>= (* x z) 1))
(assert (<= (* x z) 400))
(check-sat)"#;

/// `benchmarks/smt/wrong-verdict/sat_nia_sign_cut_4.smt2`
/// (z3 model w = -8, x = -1, z = -25): the sign cut alone suffices.
const SAT_NIA_SIGN_CUT_4: &str = r#"
(set-logic QF_NIA)
(set-info :status sat)
(declare-const x Int)
(declare-const z Int)
(declare-const w Int)
(assert (= (* 3 w) (+ z 1)))
(assert (= (- (* 5 x) (* 2 z)) 45))
(assert (<= x 1))
(assert (>= x (- 1000)))
(assert (>= (* x z) 1))
(assert (<= (* x z) 400))
(check-sat)"#;

fn solve(input: &str, shed_proof_cycle: bool) -> String {
    let commands = parse(input).unwrap_or_else(|err| panic!("parse failed: {err}"));
    let mut exec = Executor::new();
    // `--z3-mode` / `--no-proof` posture when set; the batteries-on default
    // otherwise. The wrong verdict fired in both.
    exec.set_competition_mode(shed_proof_cycle);
    exec.set_timeout(Some(Duration::from_secs(30)));
    exec.set_memory_limit(Some(8 << 30));
    let outputs = exec
        .execute_all(&commands)
        .unwrap_or_else(|err| panic!("execution failed: {err}"));
    outputs.last().cloned().unwrap_or_default()
}

fn assert_never_unsat(name: &str, input: &str) {
    for shed in [false, true] {
        let verdict = solve(input, shed);
        assert_ne!(
            verdict, "unsat",
            "{name} (shed_proof_cycle={shed}) declares :status sat and z3 5.1.0 answers sat; \
             a refutation here rests on a model guess"
        );
    }
}

#[test]
#[timeout(180_000)]
fn sat_nia_sign_cut_1_is_never_unsat() {
    assert_never_unsat("sat_nia_sign_cut_1", SAT_NIA_SIGN_CUT_1);
}

#[test]
#[timeout(180_000)]
fn sat_nia_sign_cut_2_is_never_unsat() {
    assert_never_unsat("sat_nia_sign_cut_2", SAT_NIA_SIGN_CUT_2);
}

#[test]
#[timeout(180_000)]
fn sat_nia_sign_cut_3_is_never_unsat() {
    assert_never_unsat("sat_nia_sign_cut_3", SAT_NIA_SIGN_CUT_3);
}

#[test]
#[timeout(180_000)]
fn sat_nia_sign_cut_4_is_never_unsat() {
    assert_never_unsat("sat_nia_sign_cut_4", SAT_NIA_SIGN_CUT_4);
}

/// `~/ay-bench/signfuzz/p066.smt2` (z3 5.1.0 `sat`; main decides it in
/// 0.05 s through the clausal local search). The first cut of the SAT-side
/// fix asked for a branch-and-bound split on the refinement's stalled
/// tableau point BEFORE reading that point against the variable's bounds:
/// after the factor split's branches the tableau sat at `y = 1/170` under an
/// asserted `y <= 0`, the split `y <= 0 ∨ y >= 1` re-asserted a literal
/// already in force, the branch instance was the same problem again, and
/// the split loop walked to the 30 s deadline (`unknown`, 1,940 identical
/// splits in the trace). A split is requested only for a value inside the
/// variable's current bounds, where both branches are new information.
const SIGNFUZZ_P066: &str = r#"
(set-logic QF_NIA)
(set-info :status sat)
(declare-const x Int)
(declare-const y Int)
(declare-const z Int)
(declare-const w Int)
(assert (<= (* y x z) (- 60)))
(assert (= (* y w x) (- 100)))
(assert (= (+ x z) (- 2)))
(check-sat)"#;

#[test]
#[timeout(180_000)]
fn signfuzz_p066_stalled_split_does_not_walk() {
    for shed in [false, true] {
        let verdict = solve(SIGNFUZZ_P066, shed);
        assert_eq!(
            verdict, "sat",
            "signfuzz p066 (shed_proof_cycle={shed}) is sat on main in 0.05 s; anything else \
             here is the split loop walking on a stale point"
        );
    }
}
