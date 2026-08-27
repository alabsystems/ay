// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Coverage for the STORE-OVER-STORE half of the rewritten-assertion bridge
//! LANE.
//!
//! `ay-proof`'s `array_store_overwrite_tests` /
//! `array_store_overwrite_negative_tests` own the MINTER's bar: an independent
//! bounded array-model evaluator that shares no code with it re-checks every
//! accept, exhaustive sweeps over a bounded index/element alphabet, adversarial
//! negatives that each name a concrete falsifying assignment and CHECK it, and
//! a 14-entry guard mutation ledger. This file owns the LANE — which leaves it
//! now reaches, which it still refuses, and what the spliced proof looks like.
//!
//! Split out of `rewritten_assertion_bridge_array_tests.rs` so each file stays
//! inside the repository's 500-line ceiling.
//!
//! **Every fixture is a REAL SOLVE of a COMPLETE problem**, for the reason the
//! sibling test file records: with a truncated fixture a guard mutation can
//! come back green because a backstop reverted the rewrite for an unrelated
//! reason.

use ay_core::{ProofStep, Symbol, TermData, TermId, TheoryLemmaKind};

use super::tests::{premiseless_equality_trust_leaves, solve};

/// GUARD MUTATION LEDGER for the store-over-store LANE — every guard deleted or
/// weakened, the NAMED test observed FAILING, the guard restored. The 14-entry
/// ledger for the MINTER and for the checker sub-schema lives in `ay-proof`'s
/// `array_store_overwrite_negative_tests.rs`; its two honest negatives are
/// recorded there rather than hidden.
///
/// | guard | named test |
/// |---|---|
/// | all three writes share ONE index term (`array_store_overwrite.rs`) | `every_store_overwrite_leaf_writes_one_index_term` |
/// | `recognize_array_theory_lemma == ArrayRowChain` at mint time | `array_store_overwrite::negative_tests::*` |
/// | Guard 7: the leaf strict-checks before entering the pool | `guard_seven_refuses_a_forged_different_index_overwrite` |
/// | the emission-time recognizer re-check | `every_store_overwrite_leaf_writes_one_index_term` |
/// | the walk only follows a SAME-index definition | `array_store_overwrite::tests::a_definition_at_a_different_index_mints_nothing` |
/// | the instance cap | `array_store_overwrite::tests::the_instance_count_is_capped` |
const STORE_OVERWRITE_GUARD_MUTATION_LEDGER: () = ();

#[test]
fn the_store_overwrite_guard_mutation_ledger_exists() {
    let () = STORE_OVERWRITE_GUARD_MUTATION_LEDGER;
}

/// The STORE-OVER-STORE class, as a complete problem.
///
/// `mk_store` collapses `(store (store a1 i0 e1) i0 e2)` to `(store a1 i0 e2)`
/// while `VariableSubstitution` is inlining, so connecting the authored chain
/// to the asserted one needs the array EQUALITY
/// `(= (store (store a1 i0 e1) i0 e2) (store a1 i0 e2))`. That equality is now
/// minted by `ay_proof::plan_store_overwrite_instances` and certified by the
/// row-chain validator's sub-schema (J).
///
/// This fixture pinned "left alone" before the store-over-store lane existed;
/// it is RE-AIMED at the property it was protecting — the leaf is only ever
/// replaced by a DERIVATION the strict gate re-validates — which the assertions
/// below now pin directly. The fail-closed half moved to `ROW2_FOLD`.
const STORE_OVER_STORE: &str = r#"
    (set-logic QF_AX)
    (declare-sort Index 0)
    (declare-sort Element 0)
    (declare-fun a1 () (Array Index Element))
    (declare-fun a2 () (Array Index Element))
    (declare-fun a3 () (Array Index Element))
    (declare-fun i0 () Index)
    (declare-fun i1 () Index)
    (declare-fun e1 () Element)
    (declare-fun e2 () Element)
    (declare-fun e3 () Element)
    (assert (= a2 (store a1 i0 e1)))
    (assert (= a3 (store a2 i0 e2)))
    (assert (= e3 (select a3 i1)))
    (assert (not (= e3 (select (store a1 i0 e2) i1))))
    (check-sat)
"#;

/// A rewritten assertion whose fold this lane does NOT model — MEASURED, on
/// this fixture, to leave a premiseless `trust` leaf at HEAD.
///
/// `mk_select` looks THROUGH a store at a provably distinct CONSTANT index
/// (`select(store(a, 0, e), 1) -> select(a, 1)`), so the asserted rewrite needs
/// read-over-write-NEGATIVE. The only ROW2 schema `ay-proof` accepts carries
/// the index equality as a clause literal (`matches_row2_conditional`), which
/// this lane has nothing to discharge; nothing here may mint a unit for it.
const ROW2_FOLD: &str = r#"
    (set-logic QF_AUFLIA)
    (declare-sort Element 0)
    (declare-fun a1 () (Array Int Element))
    (declare-fun a2 () (Array Int Element))
    (declare-fun e1 () Element)
    (declare-fun e2 () Element)
    (declare-fun e3 () Element)
    (assert (= a2 (store a1 0 e1)))
    (assert (= e2 (select a2 1)))
    (assert (= e3 (select a1 1)))
    (assert (not (= e2 e3)))
    (check-sat)
"#;

/// Every `ArrayRowChain` theory lemma the finished proof carries.
fn store_overwrite_leaves(proof: &ay_core::Proof) -> Vec<Vec<TermId>> {
    proof
        .steps
        .iter()
        .filter_map(|step| match step {
            ProofStep::TheoryLemma {
                kind: TheoryLemmaKind::ArrayRowChain,
                clause,
                farkas,
                lia,
                ..
            } => {
                assert!(farkas.is_none(), "an axiom leaf carries no Farkas payload");
                assert!(lia.is_none(), "an axiom leaf carries no LIA payload");
                Some(clause.clone())
            }
            _ => None,
        })
        .collect()
}

/// byte-identical `trust` step.
///
/// `mk_select` looking THROUGH a store at a distinct constant index erases a
/// node just as store-over-store does, and nothing in this lane mints an
/// instance for it. The leaf must survive untouched and no store-over-store
/// leaf may be spliced in.
#[test]
fn a_fold_this_lane_does_not_model_keeps_its_trust_step() {
    let exec = solve(ROW2_FOLD);
    let proof = exec
        .last_proof
        .as_ref()
        .expect("the solve produced a proof");
    assert!(
        premiseless_equality_trust_leaves(&exec, proof) >= 1,
        "the read-over-write-negative rewrite is NOT derivable here and must be left alone"
    );
    assert!(
        store_overwrite_leaves(proof).is_empty(),
        "no store-over-store instance may be spliced in for a fold this lane does not model"
    );
}

/// The STORE-OVER-STORE residual the sibling pass left behind is now DERIVED by
/// the solve itself.
#[test]
fn the_store_over_store_residual_is_derived_by_the_solve_itself() {
    let exec = solve(STORE_OVER_STORE);
    let proof = exec
        .last_proof
        .as_ref()
        .expect("the solve produced a proof");
    assert_eq!(
        premiseless_equality_trust_leaves(&exec, proof),
        0,
        "the store-over-store rewrite must not survive as a premiseless trust step"
    );
    assert_eq!(
        store_overwrite_leaves(proof).len(),
        1,
        "exactly one store-over-store axiom instance is needed"
    );
}

/// Every store-over-store leaf the lane emits writes ONE index term in all
/// three of its stores, and repeats the written value on both sides. This is
/// the soundness property of the whole mechanism, checked on the SPLICED proof
/// rather than on the minter.
#[test]
fn every_store_overwrite_leaf_writes_one_index_term() {
    let exec = solve(STORE_OVER_STORE);
    let proof = exec
        .last_proof
        .as_ref()
        .expect("the solve produced a proof");
    let leaves = store_overwrite_leaves(proof);
    assert!(!leaves.is_empty(), "the fixture must exercise the lane");
    for clause in leaves {
        assert_eq!(clause.len(), 1, "an axiom leaf is a unit clause");
        // The checker's OWN classifier must call it the row-chain kind.
        assert_eq!(
            ay_proof::recognize_array_theory_lemma(&exec.ctx.terms, &clause),
            Some(TheoryLemmaKind::ArrayRowChain),
            "an emitted store-over-store leaf must be the row-chain schema"
        );
        let TermData::App(Symbol::Named(name), sides) = exec.ctx.terms.get(clause[0]) else {
            panic!("an axiom leaf is a binary `=` application");
        };
        assert_eq!(name, "=");
        let TermData::App(Symbol::Named(outer), overwrite) = exec.ctx.terms.get(sides[0]) else {
            panic!("the overwrite side is an application");
        };
        assert_eq!(outer, "store");
        let TermData::App(Symbol::Named(inner), shadowed) = exec.ctx.terms.get(overwrite[0]) else {
            panic!("the overwrite side writes over a store");
        };
        assert_eq!(inner, "store");
        let TermData::App(Symbol::Named(folded_head), folded) = exec.ctx.terms.get(sides[1]) else {
            panic!("the folded side is an application");
        };
        assert_eq!(folded_head, "store");
        assert_eq!(
            overwrite[1], shadowed[1],
            "the outer write must be at the SHADOWED write's own index — a different \
             index is not a fold at all"
        );
        assert_eq!(
            overwrite[1], folded[1],
            "the folded side must write at that SAME index term"
        );
        assert_eq!(
            overwrite[2], folded[2],
            "both sides must write the SAME value"
        );
        assert_eq!(
            shadowed[0], folded[0],
            "the folded side must be built over the SHADOWED write's own base"
        );
    }
}

/// Guard 7 for the store-over-store leaf: a hand-forged DIFFERENT-index
/// instance — the one that is not valid at all — is refused by the same call
/// the pool uses, and the honest instance is accepted.
#[test]
fn guard_seven_refuses_a_forged_different_index_overwrite() {
    let mut exec = solve(STORE_OVER_STORE);
    let index_sort = ay_core::Sort::Uninterpreted("Index".to_string());
    let element_sort = ay_core::Sort::Uninterpreted("Element".to_string());
    let array_sort = ay_core::Sort::Array(Box::new(ay_core::ArraySort::new(
        index_sort.clone(),
        element_sort.clone(),
    )));
    let terms = &mut exec.ctx.terms;
    let base = terms.mk_var("a1", array_sort.clone());
    let at = terms.mk_var("i0", index_sort.clone());
    let other = terms.mk_var("i_other", index_sort);
    let shadowed_value = terms.mk_var("e1", element_sort.clone());
    let value = terms.mk_var("e2", element_sort);
    let shadowed = terms.mk_app(
        Symbol::named("store"),
        vec![base, at, shadowed_value],
        array_sort.clone(),
    );
    let forged_overwrite = terms.mk_app(
        Symbol::named("store"),
        vec![shadowed, other, value],
        array_sort.clone(),
    );
    let forged_folded = terms.mk_app(Symbol::named("store"), vec![base, other, value], array_sort);
    let forged = terms.mk_app(
        Symbol::named("="),
        vec![forged_overwrite, forged_folded],
        ay_core::Sort::Bool,
    );
    assert!(
        !exec.store_overwrite_axiom_leaf_strict_checks(forged),
        "Guard 7 must refuse a store-over-store at a DIFFERENT index"
    );
    let honest = ay_proof::mint_store_overwrite_axiom(&mut exec.ctx.terms, shadowed, value)
        .expect("the same-index instance mints");
    assert!(
        exec.store_overwrite_axiom_leaf_strict_checks(honest),
        "Guard 7 must accept the same-index instance"
    );
}

/// The wire: the store-over-store fragment prints, its own leaf falls through
/// to the honest `hole` (Carcara has no store-overwrite rule), and the rest of
/// the fragment prints as real Alethe rules. The `trust` step it replaces is
/// GONE — the trade is one `hole` for one `trust`, and only the `hole` keeps
/// the document checkable-as-holey.
#[test]
fn the_store_overwrite_leaf_prints_on_the_wire() {
    let exec = solve(STORE_OVER_STORE);
    let proof = exec
        .last_proof
        .as_ref()
        .expect("the solve produced a proof");
    let document =
        ay_proof::try_export_alethe(proof, &exec.ctx.terms).expect("the proof must render");
    assert!(
        !document.contains(":rule trust"),
        "no trust step may survive:\n{document}"
    );
    assert!(
        document.contains("(= (store (store a1 i0 e1) i0 e2) (store a1 i0 e2))) :rule hole)"),
        "the store-over-store leaf must print as the honest hole with its own raw \
         overwrite term:\n{document}"
    );
    assert!(
        document.contains(":rule th_resolution"),
        "each cited hypothesis is discharged by th_resolution:\n{document}"
    );
    assert!(
        document.contains(":rule eq_congruent"),
        "the closure step that reaches the axiom's node is a congruence:\n{document}"
    );
}
