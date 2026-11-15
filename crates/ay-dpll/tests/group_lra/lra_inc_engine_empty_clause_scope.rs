// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression: the incremental QF_LRA engine lane (`#lra-inc-engine`) and a
//! refuted persistent SAT solver (`repros/empty-clause-scope-2026-09-23/`).
//!
//! * `ATTACH_REFUTATION`: the lane's state-preserving incremental reset
//!   attaches the clauses asserted since the last check-sat; `(= c 6)`
//!   contradicts the level-0 bound `c < 5/4`, which refutes the clause
//!   database during the attach. The solve went on into BCP anyway (`BUG:
//!   propagate_bcp_unsafe called with has_empty_clause=true` from the CLI):
//!   all 17 `corpus/lra_bcp_*` scripts on ay 387b3c1cf, debug build, in both
//!   postures.
//! * `RETRACTED_BASE_REFUTATION`: `(or p q) (not p) (not q)` is refuted
//!   while one scope is live, so `pop()` retracts the refutation and the next
//!   solve has to derive it again. The incremental reset resumed from the
//!   level-0 trail that had already consumed the conflict, and the attach had
//!   stopped at the first falsified clause while recording the rest as
//!   attached, so the SAT core returned an assignment violating `(or p q)`:
//!   `BUG [#8078]: BCP missed conflict!` in debug; in release the finalize
//!   check turned it into `unknown` (`FINALIZE_SAT_FAIL`) and the lane fell
//!   back to the standalone solver. Nine `corpus/lra_finalize_*` scripts trip
//!   the debug assertion on 387b3c1cf (`--competition`). The tenth,
//!   `lra_finalize_seed3028.smt2`, is where the fallback did not rescue the
//!   verdict: the solver's `FINALIZE_SAT_FAIL` count is sticky, so its last
//!   check-sat, `unsat` at depth 0, was downgraded to `unknown` in debug and
//!   release builds of 387b3c1cf, in both postures.
//!
//! Apart from that script the published verdicts were right in release, so
//! the other replays fail before the fix only in a debug build; the
//! SAT-level contract is pinned in release by ay-sat
//! `group_incremental/empty_clause_scope_lifecycle.rs`. Every `sat` here is
//! checked against its model and every `unsat` against a fresh
//! non-incremental solve (`common::incremental_script`).

use crate::common::incremental_script::{empty_clause_scope_corpus, run_checking_models};
use ay_dpll::Executor;
use ntest::timeout;

fn verdicts(smt: &str, competition: bool) -> Vec<String> {
    run_checking_models(smt, |exec: &mut Executor| {
        exec.set_competition_mode(competition);
    })
}

/// ddmin of fuzz script `QF_LRA_5`.
const ATTACH_REFUTATION: &str = r#"
(set-logic QF_LRA)
(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (and (< (* (- 2) (* (- 1) c)) (/ 5 2)) (and (>= (+ (* (- 1) c) (+ a (- 1))) (+ a (* (- 1) b))) (not (<= (+ (+ (/ -3 3) c) c) (- 2))))))
(push 1)
(pop 1)
(check-sat)
(assert (= c (* 2 (+ 3 0))))
(check-sat)
"#;

/// ddmin of generated script `QF_LRA_193`.
const RETRACTED_BASE_REFUTATION: &str = r#"
(set-logic QF_LRA)
(declare-const a Real)
(declare-const c Real)
(declare-const p Bool)
(declare-const q Bool)
(assert (> c (* (- 2) (+ 5 a))))
(assert (or p q))
(assert (not p))
(assert (not q))
(push 1)
(check-sat)
(pop 1)
(check-sat)
"#;

/// The retraction shape across several scopes, with satisfiable check-sats
/// before the contradiction.
const RETRACTED_BASE_REFUTATION_DEEP: &str = r#"
(set-logic QF_LRA)
(declare-const a Real)
(declare-const c Real)
(declare-const p Bool)
(declare-const q Bool)
(assert (> c (* (- 2) (+ 5 a))))
(assert (or p q))
(check-sat)
(push 1)
(assert (< c 0))
(check-sat)
(pop 1)
(assert (not p))
(assert (not q))
(push 1)
(push 1)
(check-sat)
(pop 1)
(check-sat)
(pop 1)
(check-sat)
(push 1)
(check-sat)
(pop 1)
(check-sat)
"#;

#[test]
#[timeout(60_000)]
fn lra_inc_engine_attach_refutation_is_unsat() {
    for competition in [false, true] {
        assert_eq!(
            verdicts(ATTACH_REFUTATION, competition),
            ["sat", "unsat"],
            "competition={competition}"
        );
    }
}

#[test]
#[timeout(60_000)]
fn lra_inc_engine_retracted_base_refutation_is_derived_again() {
    for competition in [false, true] {
        assert_eq!(
            verdicts(RETRACTED_BASE_REFUTATION, competition),
            ["unsat", "unsat"],
            "competition={competition}"
        );
    }
}

#[test]
#[timeout(60_000)]
fn lra_inc_engine_retracted_base_refutation_is_derived_again_across_scopes() {
    for competition in [false, true] {
        assert_eq!(
            verdicts(RETRACTED_BASE_REFUTATION_DEEP, competition),
            ["sat", "sat", "unsat", "unsat", "unsat", "unsat", "unsat"],
            "competition={competition}"
        );
    }
}

/// Replay every corpus script with the given name prefix in both postures:
/// complete, posture-independent verdicts, each `sat` model-checked and each
/// `unsat` re-derived by a fresh non-incremental solve.
fn replay_corpus(prefix: &str, expected_scripts: usize) {
    let scripts = empty_clause_scope_corpus(prefix);
    assert_eq!(scripts.len(), expected_scripts, "the `{prefix}` fuzz hits");
    for (name, smt) in &scripts {
        let check_sats = smt.matches("(check-sat)").count();
        let mut per_posture: Vec<Vec<String>> = Vec::new();
        for competition in [false, true] {
            let answers = verdicts(smt, competition);
            assert_eq!(
                answers.len(),
                check_sats,
                "{name} (competition={competition}) must answer every check-sat"
            );
            assert!(
                !answers.iter().any(|answer| answer == "unknown"),
                "{name} (competition={competition}): {answers:?}"
            );
            per_posture.push(answers);
        }
        assert_eq!(per_posture[0], per_posture[1], "{name}: postures disagree");
    }
}

#[test]
#[timeout(300_000)]
fn lra_inc_engine_bcp_fuzz_hits_replay() {
    replay_corpus("lra_bcp_", 17);
}

#[test]
#[timeout(300_000)]
fn lra_inc_engine_finalize_fuzz_hits_replay() {
    replay_corpus("lra_finalize_", 10);
}
