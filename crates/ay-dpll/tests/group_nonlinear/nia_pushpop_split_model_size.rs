// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression: the incremental QF_NIA split loop stored a SAT model whose
//! `term_to_var` named variables the model did not contain, tripping
//! `model_helpers.rs` `solve_and_store_model_full`:
//!
//! ```text
//! term_to_var contains index 17 but model has only 14 vars
//! ```
//!
//! First seen as a compiler_consumer ICE (2026-09-08,
//! `compiler_consumer-ice-2026-09-08T13_00_35-78600.txt`, compiler_consumer 10f221fbe pinning ay
//! b5ea9bba3): ay-chc's PDR executor backend drove `solve_nia` ->
//! `solve_nia_inner` -> the lazy split arm's `pipeline_store_sat_model!` on a
//! model-checker-consumer worker thread while Trust verified clean-mathverse.
//!
//! Root cause (the same defect as the 2026-09-18 incremental QF_LRA false
//! `unsat`, fixed in bd8c45923): the split loop seeded its fresh SAT-variable
//! cursor as `user_num_vars() + scope_depth()`. `Solver::push()` mints each
//! scope selector through `new_var_internal` (no `user_num_vars` advance) and
//! `pop()` never frees it, so once a session has popped scopes the seed points
//! INTO the selector range below `total_num_vars()`. A split atom minted there
//! aliases a live or dead selector; `ensure_num_vars` is then a no-op, so
//! `user_num_vars` (the length every returned SAT model is truncated to) never
//! grows to cover it. When the aliased value happens to agree with the theory
//! the round is SAT and the stored `term_to_var` points past the model's end;
//! when it does not (both disequality atoms on TRUE selectors) the round is a
//! false `unsat`. `split_incremental::fresh_sat_var_floor` now floors every
//! minting site at `total_num_vars()`.
//!
//! The scripts below were found by differential fuzzing of ay 25e6683cf (the
//! parent of bd8c45923) and shrunk by line-level delta debugging; on that
//! revision the proof-producing run (the `ay` CLI's default, which
//! synthesizes an Alethe sidecar) panics with
//! `term_to_var contains index 8 but model has only 6 vars` inside
//! `solve_nia_inner`, the exact frame chain of the compiler_consumer ICE. Every
//! `check-sat` is satisfiable (e.g. a=0, b=1, c=0).

use crate::common::incremental_script::run_checking_models;
use ay_dpll::Executor;
use ntest::timeout;

/// The executor postures the split loop runs under.
#[derive(Clone, Copy, Debug)]
enum Posture {
    /// `Executor::new()` defaults.
    Default,
    /// Proof production on, as the `ay` CLI runs a file by default (it
    /// synthesizes an Alethe sidecar). Measured on 25e6683cf: this is the
    /// posture in which the pre-fix split loop stored the short model for
    /// these scripts. The default and competition postures answered `sat`
    /// with a covering model there, in debug builds too, so for these scripts
    /// they are model-checked pins that cannot observe that defect.
    Proofs,
    /// The proof-shedding `--competition` posture.
    Competition,
}

/// The verdicts of `smt` under `posture`, each `sat` checked against the model
/// it comes with and each `unsat` against a fresh non-incremental solve
/// (`common::incremental_script`). The short model itself is invisible to
/// both checks (the constants' values come from the theory and are right):
/// a debug build trips the #4714 coverage assertion on it (the panic quoted
/// above), and a release build answers `unknown`, because
/// `solve_and_store_model_full` refuses a model that does not cover a
/// Tseitin-mapped variable.
fn verdicts(smt: &str, posture: Posture) -> Vec<String> {
    run_checking_models(smt, |exec: &mut Executor| match posture {
        Posture::Default => {}
        Posture::Proofs => exec.set_produce_proofs(true),
        Posture::Competition => exec.set_competition_mode(true),
    })
}

/// Shrunk from a fuzz hit: two empty nested scopes before the first
/// `check-sat` and two more before the second leave dead selectors above
/// `user_num_vars`; `(not (= a b))` then forces a disequality split whose
/// atoms the pre-fix seed minted onto those selectors.
const MIN_NIA_EMPTY_SCOPES: &str = r#"
(set-logic QF_NIA)
(declare-const a Int)
(declare-const b Int)
(declare-const c Int)
(assert (<= b 5))
(push 1)
(pop 1)
(assert (not (= a b)))
(push 1)
(push 1)
(pop 1)
(pop 1)
(assert (<= (* b c) 4))
(check-sat)
(push 1)
(push 1)
(pop 1)
(pop 1)
(check-sat)
"#;

#[test]
#[timeout(30_000)]
fn nia_split_atoms_after_popped_scopes_proof_posture() {
    assert_eq!(
        verdicts(MIN_NIA_EMPTY_SCOPES, Posture::Proofs),
        ["sat", "sat"]
    );
}

#[test]
#[timeout(30_000)]
fn nia_split_atoms_after_popped_scopes_default_posture() {
    assert_eq!(
        verdicts(MIN_NIA_EMPTY_SCOPES, Posture::Default),
        ["sat", "sat"]
    );
}

#[test]
#[timeout(30_000)]
fn nia_split_atoms_after_popped_scopes_competition_posture() {
    assert_eq!(
        verdicts(MIN_NIA_EMPTY_SCOPES, Posture::Competition),
        ["sat", "sat"]
    );
}

/// The same shape with many more popped scopes between the two check-sats:
/// the cursor must clear every dead selector, not just the first few, and
/// each round's stored model must cover every split atom it names.
#[test]
#[timeout(60_000)]
fn nia_split_atoms_after_many_popped_scopes() {
    let mut smt = String::from(
        "(set-logic QF_NIA)\n(declare-const a Int)\n(declare-const b Int)\n\
         (declare-const c Int)\n(assert (<= b 5))\n(push 1)\n(pop 1)\n\
         (assert (not (= a b)))\n(push 1)\n(push 1)\n(pop 1)\n(pop 1)\n\
         (assert (<= (* b c) 4))\n(check-sat)\n",
    );
    for _ in 0..12 {
        smt.push_str("(push 1)\n(push 1)\n(pop 1)\n(pop 1)\n(check-sat)\n");
    }
    let expected = vec!["sat".to_owned(); 13];
    for posture in [Posture::Proofs, Posture::Default, Posture::Competition] {
        assert_eq!(verdicts(&smt, posture), expected, "{posture:?} posture");
    }
}

/// Found by fuzzing random push/pop scripts, each satisfiable by construction
/// (a=0, b=1, c=0), on 387b3c1cf with bd8c45923's source reverted, and shrunk
/// by line-level delta debugging. There the proof posture computes a false
/// `unsat` for the second check-sat; its mandatory strict certification
/// rejects it (`SelfCheckRejected`), so the check-sat answers `unknown`. That
/// is a verdict, so this pin fails with the defect reverted even without the
/// model-coverage store. The default and competition postures answered every
/// check-sat of 150 such scripts correctly there; they are pinned for
/// agreement.
const MIN_NIA_WITHHELD_FALSE_UNSAT: &str = r#"
(set-logic QF_NIA)
(declare-const a Int)
(declare-const b Int)
(declare-const c Int)
(assert (not (= a b)))
(assert (>= a 0))
(push 1)
(assert (<= (* c c) 1))
(check-sat)
(pop 1)
(push 1)
(push 1)
(pop 1)
(pop 1)
(push 1)
(assert (<= (* c c) 1))
(check-sat)
"#;

#[test]
#[timeout(30_000)]
fn nia_split_atoms_after_popped_scopes_no_false_unsat() {
    for posture in [Posture::Proofs, Posture::Default, Posture::Competition] {
        assert_eq!(
            verdicts(MIN_NIA_WITHHELD_FALSE_UNSAT, posture),
            ["sat", "sat"],
            "{posture:?} posture"
        );
    }
}
