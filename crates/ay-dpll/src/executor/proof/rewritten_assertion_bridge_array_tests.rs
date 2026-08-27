// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Coverage for the ARRAY half of the rewritten-assertion bridge LANE.
//!
//! `ay-proof`'s `array_row_axiom_tests` / `array_row_axiom_negative_tests` own
//! the MINTER's bar: an independent array-model evaluator that shares no code
//! with it re-checks every accept, exhaustive sweeps over a bounded
//! index/element alphabet, and adversarial negatives that each name a concrete
//! falsifying assignment and CHECK it. This file owns the LANE — which leaves
//! it now reaches, which it still refuses, and what the spliced proof looks
//! like.
//!
//! **Every fixture is a REAL SOLVE of a COMPLETE problem**, for the reason the
//! sibling test file records: with a truncated fixture a guard mutation can
//! come back green because a backstop reverted the rewrite for an unrelated
//! reason.

use ay_core::{ProofStep, Symbol, TermData, TermId, TheoryLemmaKind};

use super::tests::{premiseless_equality_trust_leaves, solve};

/// The MEASURED head of the read-over-write residual, as a complete problem.
///
/// `VariableSubstitution` inlines `a_260` into `(= e_261 (select a_260 i0))`;
/// `mk_select` then folds the read-over-write at the store's own index and the
/// solver asserts `(= e_259 e_261)`, which is not an authored assertion. The
/// corpus carries this exact rewrite on the QF_AX `swap_*` family — measured on
/// `swap_t1_np_sf_ai_00005_005` as `(= e_259 e_261)` and `(= e_277 e_281)`.
const READ_OVER_WRITE: &str = r#"
    (set-logic QF_AX)
    (declare-sort Index 0)
    (declare-sort Element 0)
    (declare-fun a_258 () (Array Index Element))
    (declare-fun a_260 () (Array Index Element))
    (declare-fun i0 () Index)
    (declare-fun e_259 () Element)
    (declare-fun e_261 () Element)
    (assert (= a_260 (store a_258 i0 e_259)))
    (assert (= e_261 (select a_260 i0)))
    (assert (not (= e_259 e_261)))
    (check-sat)
"#;

/// Every `ArraySelectStore` theory lemma the finished proof carries.
fn array_axiom_leaves(proof: &ay_core::Proof) -> Vec<Vec<TermId>> {
    proof
        .steps
        .iter()
        .filter_map(|step| match step {
            ProofStep::TheoryLemma {
                kind: TheoryLemmaKind::ArraySelectStore { index_eq: true },
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

// ===== the class this pass closes =====

/// The whole point: the read-over-write residual is gone from the SOLVE's own
/// finished proof, and it is gone because the lane derived it.
#[test]
fn the_read_over_write_residual_is_derived_by_the_solve_itself() {
    let exec = solve(READ_OVER_WRITE);
    let proof = exec
        .last_proof
        .as_ref()
        .expect("the solve produced a proof");
    assert_eq!(
        premiseless_equality_trust_leaves(&exec, proof),
        0,
        "the read-over-write rewrite must not survive as a premiseless trust step"
    );
    assert_eq!(
        array_axiom_leaves(proof).len(),
        1,
        "exactly one read-over-write axiom instance is needed"
    );
}

/// Every axiom leaf the lane emits reads the store at the store's OWN index
/// term. This is the soundness property of the whole mechanism, checked on the
/// spliced proof rather than on the minter.
#[test]
fn every_axiom_leaf_reads_the_store_at_its_own_index() {
    let exec = solve(READ_OVER_WRITE);
    let proof = exec
        .last_proof
        .as_ref()
        .expect("the solve produced a proof");
    let leaves = array_axiom_leaves(proof);
    assert!(!leaves.is_empty(), "the fixture must exercise the lane");
    for clause in leaves {
        assert_eq!(clause.len(), 1, "an axiom leaf is a unit clause");
        // The checker's OWN recognizer must call it the index-EQUAL schema.
        assert_eq!(
            ay_proof::recognize_array_select_store(&exec.ctx.terms, &clause),
            Some(true),
            "an emitted axiom leaf must be the index-EQUAL read-over-write schema"
        );
        // And, structurally: store index and read index are the SAME term.
        let TermData::App(Symbol::Named(name), sides) = exec.ctx.terms.get(clause[0]) else {
            panic!("an axiom leaf is a binary `=` application");
        };
        assert_eq!(name, "=");
        let TermData::App(Symbol::Named(head), read) = exec.ctx.terms.get(sides[0]) else {
            panic!("the select side is an application");
        };
        assert_eq!(head, "select");
        let TermData::App(Symbol::Named(inner), stored) = exec.ctx.terms.get(read[0]) else {
            panic!("the select reads a store");
        };
        assert_eq!(inner, "store");
        assert_eq!(
            stored[1], read[1],
            "the read index must BE the store index — a different-index read is only \
             sound with a disequality, which this lane never has"
        );
        assert_eq!(stored[2], sides[1], "the value side is the stored value");
    }
}

/// The finished proof CERTIFIES under the untouched mandatory gate.
#[test]
fn the_derived_proof_certifies_under_the_untouched_strict_gate() {
    let exec = solve(READ_OVER_WRITE);
    let proof = exec
        .last_proof
        .as_ref()
        .expect("the solve produced a proof");
    exec.check_proof_strict_with_datatypes(proof)
        .expect("the spliced proof must certify");
}

/// The wire: the fragment prints, and the axiom leaf prints as a real array
/// rule rather than as a `trust` step.
#[test]
fn the_array_axiom_prints_on_the_wire() {
    let exec = solve(READ_OVER_WRITE);
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
        !document.contains(":rule hole"),
        "the axiom must not be traded for a hole:\n{document}"
    );
    // EXACT wire text: the leaf lowers to Carcara's own read-over-write rule.
    assert!(
        document.contains(
            "(step t2 (cl (= (select (store a_258 i0 e_259) i0) e_259)) :rule arrays_idx)"
        ),
        "the axiom leaf must print as Carcara's `arrays_idx` with its own raw read:\n{document}"
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

// ===== fail-closed =====

/// A rewritten assertion whose fold this lane does NOT model keeps its

/// An axiom instance is never an `assume`, so the assumption scope is exactly
/// what it was: every `Assume` in the finished proof is still an authored
/// assertion.
#[test]
fn the_axiom_never_widens_the_assumption_scope() {
    let exec = solve(READ_OVER_WRITE);
    let scope: Vec<TermId> = exec.complete_problem_assertions_for_strict_proof();
    let proof = exec
        .last_proof
        .as_ref()
        .expect("the solve produced a proof")
        .clone();
    for step in &proof.steps {
        let ProofStep::Assume(term) = step else {
            continue;
        };
        assert!(
            scope.contains(term),
            "the lane assumed a term outside the strict scope"
        );
    }
}

// ===== guards =====

/// Guard 7: the leaf the lane would emit is replayed by the UNTOUCHED strict
/// checker before it may enter the pool. A hand-forged different-index
/// instance — the unsound one — is refused by that same call.
#[test]
fn guard_seven_refuses_a_forged_different_index_instance() {
    let mut exec = solve(READ_OVER_WRITE);
    let index_sort = ay_core::Sort::Uninterpreted("Index".to_string());
    let element_sort = ay_core::Sort::Uninterpreted("Element".to_string());
    let array_sort = ay_core::Sort::Array(Box::new(ay_core::ArraySort::new(
        index_sort.clone(),
        element_sort.clone(),
    )));
    let terms = &mut exec.ctx.terms;
    let base = terms.mk_var("a_258", array_sort.clone());
    let at = terms.mk_var("i0", index_sort.clone());
    let other = terms.mk_var("i_other", index_sort);
    let value = terms.mk_var("e_259", element_sort.clone());
    let stored = terms.mk_app(Symbol::named("store"), vec![base, at, value], array_sort);
    let read = terms.mk_app(Symbol::named("select"), vec![stored, other], element_sort);
    let forged = terms.mk_app(Symbol::named("="), vec![read, value], ay_core::Sort::Bool);

    assert!(
        !exec.row1_axiom_leaf_strict_checks(forged),
        "Guard 7 must refuse a read-over-write at a DIFFERENT index"
    );
    let honest =
        ay_proof::mint_row1_axiom(&mut exec.ctx.terms, stored).expect("the store yields one");
    assert!(
        exec.row1_axiom_leaf_strict_checks(honest),
        "Guard 7 must accept the index-EQUAL instance"
    );
}

/// GUARD MUTATION LEDGER — every guard deleted or weakened, the NAMED test
/// observed FAILING, the guard restored. Honest negatives are recorded in the
/// pass write-up rather than hidden.
///
/// | guard | named test |
/// |---|---|
/// | the read index IS the store index (`array_row_axiom.rs`) | `every_axiom_leaf_reads_the_store_at_its_own_index` |
/// | `recognize_array_select_store == Some(true)` at mint time | `array_row_axiom::negative_tests::*` |
/// | Guard 7: the leaf strict-checks before entering the pool | `guard_seven_refuses_a_forged_different_index_instance` |
/// | the emission-time recognizer re-check | `every_axiom_leaf_reads_the_store_at_its_own_index` |
/// | `well_sorted_store_parts` re-derives every sort relation | `array_row_axiom::negative_tests::a_store_whose_operands_do_not_match_the_array_sort_is_declined` |
/// | the instance cap | `array_row_axiom::tests::the_instance_count_is_capped` |
const ARRAY_GUARD_MUTATION_LEDGER: () = ();

#[test]
fn the_array_guard_mutation_ledger_exists() {
    let () = ARRAY_GUARD_MUTATION_LEDGER;
}
