// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A transitivity step whose printed chain is broken only by the spelling of a
//! closed bit-vector term.
//!
//! AY folds `(concat #x0 #x4)` to `#x04` while elaborating, then prints the
//! assertion `(= lo (concat #x0 #x4))` in its authored spelling so the
//! `assume` matches the premise. Its transitivity step `lo = hi` therefore
//! printed as the links `lo = (concat #x0 #x4)` and `hi = #x04`, which pinned
//! carcara refuses as a broken chain, so the printer shipped the step as a
//! `hole` and two corpus rows were published `holey`
//! (`model_checker_consumer_quantified_counterexample/wide_key136_truncated_pin_unsat`,
//! `model_checker_consumer_nested_residual/vec_alias_conflict_unsat`; never trust-free
//! `valid` at any measured history point from 353a5f37a to ad60a0707). The
//! closed-value planner proves supported links with `evaluate`, lifted
//! through `cong` under function symbols. Operators pinned carcara 1.1.0
//! (git 9a352ee) evaluates wrongly (`bvsub`, `extract`, every signed operation;
//! see `ay_core::pinned_carcara::evaluate`) remain excluded from that planner.
//! A complete source-bound BV derivation can prove the whole query without
//! evaluating the closed operator. These integration tests require that
//! complete document to pass the maintained guard and default Carcara;
//! direct planner units retain the operator-exclusion contract.

use super::{
    carcara_verdict_without_allowances, required_carcara_for_corpus, solve_unsat_and_get_proof,
    workspace_root, CarcaraVerdict,
};
use ntest::timeout;

fn chain_problem(low: &str, high: &str) -> String {
    format!(
        "(set-logic ALL)\n\
         (declare-const t (Array (_ BitVec 8) (_ BitVec 8)))\n\
         (declare-const lo (_ BitVec 8))\n\
         (declare-const hi (_ BitVec 8))\n\
         (assert (= lo {low}))\n\
         (assert (= hi {high}))\n\
         (assert (distinct (select t lo) (select t hi)))\n\
         (check-sat)\n"
    )
}

fn corpus_row(relative: &str) -> String {
    let path = workspace_root().join("benchmarks/smt").join(relative);
    std::fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("read {}: {e}", path.display()))
        .lines()
        .filter(|line| line.trim() != "(exit)")
        .collect::<Vec<_>>()
        .join("\n")
}

#[test]
#[timeout(60_000)]
fn a_closed_spelling_link_is_proved_not_holed() {
    let carcara = required_carcara_for_corpus();
    // All original questions stay fixed; any complete checked derivation
    // must verify independently against those exact authored premises.
    for (label, low, high) in [
        ("closed_concat_link", "(concat #x0 #x4)", "#x04"),
        ("closed_bvadd_link", "(bvadd #x03 #x01)", "#x04"),
        (
            "closed_two_spellings_link",
            "(bvadd #x03 #x01)",
            "(concat #x0 #x4)",
        ),
    ] {
        let problem = chain_problem(low, high);
        let proof = solve_unsat_and_get_proof(&problem, label);
        assert!(
            !proof.contains(":rule hole") && !proof.contains(":rule trust"),
            "{label}: the chain must be closed with checked steps:\n{proof}"
        );
        let carcara = &carcara;
        assert_eq!(
            carcara_verdict_without_allowances(carcara, label, &problem, &proof),
            CarcaraVerdict::Valid,
            "{label}: pinned carcara must verify the complete query proof trust-free"
        );
        assert_ne!(
            carcara_verdict_without_allowances(carcara, label, &chain_problem(low, "#x05"), &proof),
            CarcaraVerdict::Valid,
            "{label}: the checked proof must not refute the changed satisfiable problem"
        );
    }
}

/// Exclusion from the closed-value `evaluate` planner does not prevent a
/// complete checked derivation of the same whole query.
#[test]
#[timeout(60_000)]
fn excluded_evaluate_operators_have_complete_checked_query_proofs() {
    let carcara = required_carcara_for_corpus();
    for (label, low) in [
        // carcara 1.1.0 evaluates this to #xfc (it reads #xff as 1, #xfb as 5).
        ("closed_bvsub_link", "(bvsub #xff #xfb)"),
        // Bit 7 is clear, so carcara happens to get this value right: the
        // case pins that the operator is excluded as a whole.
        ("closed_extract_link", "((_ extract 7 0) #x0104)"),
    ] {
        let problem = chain_problem(low, "#x04");
        let proof = solve_unsat_and_get_proof(&problem, label);
        assert!(
            !proof.contains(":rule evaluate"),
            "{label}: the bridge never evaluates this operator:\n{proof}"
        );
        assert!(
            !proof.contains(":rule hole") && !proof.contains(":rule trust"),
            "{label}: the whole query needs a complete checked proof:\n{proof}"
        );
        let carcara = &carcara;
        assert_eq!(
            carcara_verdict_without_allowances(carcara, label, &problem, &proof),
            CarcaraVerdict::Valid,
            "{label}: pinned carcara must verify the complete proof without allowances"
        );
        assert_ne!(
            carcara_verdict_without_allowances(carcara, label, &chain_problem(low, "#x05"), &proof),
            CarcaraVerdict::Valid,
            "{label}: the checked proof must not refute the changed satisfiable problem"
        );
    }
}

#[test]
#[timeout(60_000)]
fn the_repaired_corpus_rows_are_trust_free_valid() {
    let carcara = required_carcara_for_corpus();
    for (label, relative) in [
        (
            "closed_spelling_wide_key136",
            "model_checker_consumer_quantified_counterexample/wide_key136_truncated_pin_unsat.smt2",
        ),
        (
            "closed_spelling_vec_alias",
            "model_checker_consumer_nested_residual/vec_alias_conflict_unsat.smt2",
        ),
    ] {
        let problem = corpus_row(relative);
        let proof = solve_unsat_and_get_proof(&problem, label);
        assert!(
            !proof.contains(":rule hole") && !proof.contains(":rule trust"),
            "{label}: no unchecked step:\n{proof}"
        );
        assert!(
            proof.contains(":rule evaluate)") && proof.contains(".gb.et (cl "),
            "{label}: the chain is closed by the checked closed-spelling bridge:\n{proof}"
        );
        let carcara = &carcara;
        assert_eq!(
            carcara_verdict_without_allowances(carcara, label, &problem, &proof),
            CarcaraVerdict::Valid,
            "{label}: the corpus document must verify trust-free"
        );
    }
}
