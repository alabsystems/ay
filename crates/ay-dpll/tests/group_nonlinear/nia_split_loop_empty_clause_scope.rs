// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression: the incremental QF_NIA split loop found its persistent SAT
//! solver already refuted before a round's `solve()` and tripped
//!
//! ```text
//! BUG: persistent SAT solver has_empty_clause=true BEFORE solve() in split
//! loop iteration 0. Scope depth: 2, active scopes: 2.
//! ```
//!
//! In a debug build the panic turned that check-sat's correct `unsat`, and
//! every later check-sat of the script, into `unknown`. Measured on ay
//! 387b3c1cf (debug CLI, `--competition`): all 15 random QF_NIA push/pop
//! scripts in `repros/empty-clause-scope-2026-09-23/corpus/nia_split_loop_*`
//! trip it (2 of them in the default posture). Two shapes:
//!
//! * `STALE_DEPTH`: in the proof-free posture, a level-0 conflict kept the
//!   scope depth an earlier, already-retracted refutation had left behind
//!   (`empty_clause_scope_depth == 0` was its first-occurrence test, and
//!   `pop()` never reset the field). A refutation derived in the split loop's
//!   private frame at depth 2 was recorded at depth 1, so the frame's own
//!   `pop()` did not retract it. Fixed in ay-sat: every raise of the flag
//!   records the depth it happens at, and every retraction resets it.
//! * `BASE_LEVEL`: a refutation derived with no scope live is permanent by
//!   design (`ay_sat::Solver::pop`); the next check-sat entered the split loop
//!   with it and the assertion, which forbade any refutation, fired on a
//!   correct state. It now rejects only a refutation recorded at the loop's
//!   own frame depth or deeper.
//!
//! In the proof-free posture only a level-0 conflict raises the flag, and no
//! clause guarded by a live scope's selector can be falsified at level 0,
//! where that selector is never false (it enters the search only as an
//! assumption). The surviving flags changed no published verdict: on
//! 387b3c1cf (release CLI, both postures) every check-sat of these scripts
//! agrees with a fresh non-incremental solve of its live assertions, so the
//! replays below fail before the fix only in a debug build.
//! Every replay here makes that comparison for each `unsat` and checks each
//! `sat` against its model (`common::incremental_script`), which is what a
//! release build can observe; the flag's lifecycle itself is pinned at the
//! SAT level, in release too, by ay-sat
//! `group_incremental/empty_clause_scope_lifecycle.rs`.

use crate::common::incremental_script::{empty_clause_scope_corpus, run_checking_models};
use ay_dpll::Executor;
use ntest::timeout;

#[derive(Clone, Copy, Debug)]
enum Posture {
    /// `Executor::new()` defaults.
    Default,
    /// Proof production on, as the `ay` CLI runs a file by default.
    Proofs,
    /// The proof-shedding `--competition` posture.
    Competition,
}

const POSTURES: [Posture; 3] = [Posture::Default, Posture::Proofs, Posture::Competition];

fn verdicts(smt: &str, posture: Posture) -> Vec<String> {
    run_checking_models(smt, |exec: &mut Executor| match posture {
        Posture::Default => {}
        Posture::Proofs => exec.set_produce_proofs(true),
        Posture::Competition => exec.set_competition_mode(true),
    })
}

/// ddmin of fuzz script `QF_NIA_3`: the second assertion is false, so every
/// check-sat is `unsat`. The refutation of check-sat 2 is derived at depth 2
/// (one user scope, one private frame).
const STALE_DEPTH: &str = r#"
(set-logic QF_NIA)
(declare-const a Int)
(declare-const b Int)
(declare-const c Int)
(assert (>= (* 0 (+ b c)) (- (* c a) c)))
(assert (not (> (* 0 0) (- 6))))
(check-sat)
(push 1)
(check-sat)
(check-sat)
"#;

/// ddmin of fuzz script `QF_NIA_0`: the first assertion is false. The first
/// check-sat refutes the solver at depth 0; the second enters the NIA split
/// loop with that permanent refutation.
const BASE_LEVEL: &str = r#"
(set-logic QF_NIA)
(declare-const a Int)
(declare-const b Int)
(assert (< (- 2) (- 4)))
(check-sat)
(assert (< (+ (* b a) (* a a)) (- 3)))
(check-sat)
"#;

/// The stale-depth shape with satisfiable check-sats around it: popping the
/// refuting scope must restore `sat`, and deeper refutations must not outlive
/// their scopes either. 387b3c1cf already answers this one correctly; it pins
/// the retraction contract end to end rather than reproducing the defect.
const STALE_DEPTH_WITH_SAT_BASE: &str = r#"
(set-logic QF_NIA)
(declare-const a Int)
(declare-const b Int)
(declare-const c Int)
(assert (>= (* 0 (+ b c)) (- (* c a) c)))
(check-sat)
(push 1)
(assert (not (> (* 0 0) (- 6))))
(check-sat)
(pop 1)
(check-sat)
(push 1)
(push 1)
(assert (not (> (* 0 0) (- 6))))
(check-sat)
(push 1)
(check-sat)
(pop 1)
(check-sat)
(pop 1)
(check-sat)
(pop 1)
(check-sat)
"#;

#[test]
#[timeout(60_000)]
fn nia_split_loop_refutation_does_not_outlive_its_scope() {
    for posture in POSTURES {
        assert_eq!(
            verdicts(STALE_DEPTH, posture),
            ["unsat", "unsat", "unsat"],
            "{posture:?} posture"
        );
    }
}

#[test]
#[timeout(60_000)]
fn nia_split_loop_accepts_a_base_level_refutation() {
    for posture in POSTURES {
        assert_eq!(
            verdicts(BASE_LEVEL, posture),
            ["unsat", "unsat"],
            "{posture:?} posture"
        );
    }
}

#[test]
#[timeout(60_000)]
fn nia_split_loop_scoped_refutations_retract_on_pop() {
    for posture in POSTURES {
        assert_eq!(
            verdicts(STALE_DEPTH_WITH_SAT_BASE, posture),
            ["sat", "unsat", "sat", "unsat", "unsat", "unsat", "sat", "sat"],
            "{posture:?} posture"
        );
    }
}

/// Every QF_NIA fuzz hit replays to a complete, posture-independent verdict
/// sequence, with each `sat` model-checked and each `unsat` re-derived by a
/// fresh non-incremental solve.
#[test]
#[timeout(300_000)]
fn nia_split_loop_fuzz_hits_replay_in_every_posture() {
    let scripts = empty_clause_scope_corpus("nia_split_loop_");
    assert_eq!(scripts.len(), 15, "the 15 QF_NIA fuzz hits");
    for (name, smt) in &scripts {
        let check_sats = smt.matches("(check-sat)").count();
        let mut per_posture: Vec<Vec<String>> = Vec::new();
        for posture in POSTURES {
            let answers = verdicts(smt, posture);
            assert_eq!(
                answers.len(),
                check_sats,
                "{name} ({posture:?} posture) must answer every check-sat"
            );
            assert!(
                !answers.iter().any(|answer| answer == "unknown"),
                "{name} ({posture:?} posture): {answers:?}"
            );
            per_posture.push(answers);
        }
        assert!(
            per_posture.windows(2).all(|pair| pair[0] == pair[1]),
            "{name}: postures disagree {per_posture:?}"
        );
    }
}
