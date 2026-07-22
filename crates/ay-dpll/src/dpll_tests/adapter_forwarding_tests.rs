// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Direct unit tests for adapter forwarding of TheorySolver trait methods.
//!
//! These tests verify that combined solvers (TheoryCombiner, StringsLiaSolver, etc.)
//! correctly forward `generate_bound_axiom_terms()`, `sort_atom_index()`, and
//! `suggest_phase()` to their inner theory solvers.
//!
//! Why these tests exist: integration tests that only check SAT/UNSAT results
//! CANNOT detect missing forwarding for performance methods like bound axiom
//! generation. The trait defaults return empty/no-op, so the solver produces
//! correct but slower results. Only direct invocation tests catch the gap.
//! See P1:126 commit for analysis.
//!
//! ACTIVATION: A Worker must add `mod adapter_forwarding_tests;` to
//! dpll_tests/mod.rs to compile and run these tests.

use ay_core::{Sort, TermStore, TheorySolver};
use num_bigint::BigInt;

use crate::combined_solvers::combiner::TheoryCombiner;
use crate::combined_solvers::StringsLiaSolver;
use crate::combined_solvers::UfSeqLiaSolver;

/// Verify that TheoryCombiner::uf_lia.generate_bound_axiom_terms() returns non-empty
/// when bound atoms are registered. This test would FAIL if the forwarding
/// to the inner LIA solver were removed (trait default returns empty Vec).
#[test]
fn test_uflia_generate_bound_axiom_terms_forwards_to_lia() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let three = terms.mk_int(BigInt::from(3));
    let seven = terms.mk_int(BigInt::from(7));

    let ge3 = terms.mk_ge(x, three); // x >= 3
    let ge7 = terms.mk_ge(x, seven); // x >= 7

    let mut solver = TheoryCombiner::uf_lia(&terms);
    solver.register_atom(ge3);
    solver.register_atom(ge7);
    solver.sort_atom_index();

    let axioms = solver.generate_bound_axiom_terms();
    assert!(
        !axioms.is_empty(),
        "TheoryCombiner::uf_lia must forward generate_bound_axiom_terms to LIA; \
         got empty Vec (trait default). Two lower bounds on same Int variable \
         should produce at least one bound ordering axiom."
    );
}

/// Verify that TheoryCombiner::auf_lia.generate_bound_axiom_terms() returns non-empty
/// when bound atoms are registered. Same forwarding check for AUFLIA via combiner.
#[test]
fn test_auflia_generate_bound_axiom_terms_forwards_to_lia() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let three = terms.mk_int(BigInt::from(3));
    let seven = terms.mk_int(BigInt::from(7));

    let ge3 = terms.mk_ge(x, three); // x >= 3
    let ge7 = terms.mk_ge(x, seven); // x >= 7

    let mut solver = TheoryCombiner::auf_lia(&terms);
    solver.register_atom(ge3);
    solver.register_atom(ge7);
    solver.sort_atom_index();

    let axioms = solver.generate_bound_axiom_terms();
    assert!(
        !axioms.is_empty(),
        "TheoryCombiner::auf_lia must forward generate_bound_axiom_terms to LIA; \
         got empty Vec (trait default). Two lower bounds on same Int variable \
         should produce at least one bound ordering axiom."
    );
}

/// Verify that suggest_phase forwards through TheoryCombiner::uf_lia to LIA, comparing
/// combiner result against a standalone LiaSolver. If forwarding is missing,
/// the combiner returns None (trait default) while standalone returns non-None.
/// (P1:130 strengthened: previous version discarded the return value.)
#[test]
fn test_uflia_suggest_phase_forwards_to_lia() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let three = terms.mk_int(BigInt::from(3));
    let ge3 = terms.mk_ge(x, three);

    let mut combiner = TheoryCombiner::uf_lia(&terms);
    combiner.register_atom(ge3);
    let mut standalone = ay_lia::LiaSolver::new(&terms);
    standalone.register_atom(ge3);

    let combiner_phase = combiner.suggest_phase(ge3);
    let standalone_phase = standalone.suggest_phase(ge3);
    assert_eq!(
        combiner_phase, standalone_phase,
        "TheoryCombiner::uf_lia.suggest_phase must match standalone LIA; \
         combiner={combiner_phase:?}, standalone={standalone_phase:?}"
    );
    // Guard: if standalone returns None, this test cannot detect missing forwarding.
    // x >= 3 with model x=0 evaluates to -3 <= 0, so LRA returns Some(true).
    assert!(
        standalone_phase.is_some(),
        "BUG: standalone LiaSolver returned None for suggest_phase(x >= 3); \
         this test cannot detect missing forwarding. Investigate LIA/LRA suggest_phase."
    );
}

/// Verify that StringsLiaSolver.generate_bound_axiom_terms() returns non-empty
/// when bound atoms are registered. Without forwarding, the trait default
/// returns an empty Vec and QF_SLIA problems miss bound ordering axioms.
#[test]
fn test_strings_lia_generate_bound_axiom_terms_forwards_to_lia() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let three = terms.mk_int(BigInt::from(3));
    let seven = terms.mk_int(BigInt::from(7));

    let ge3 = terms.mk_ge(x, three); // x >= 3
    let ge7 = terms.mk_ge(x, seven); // x >= 7

    let mut solver = StringsLiaSolver::new(&terms);
    solver.register_atom(ge3);
    solver.register_atom(ge7);
    solver.sort_atom_index();

    let axioms = solver.generate_bound_axiom_terms();
    assert!(
        !axioms.is_empty(),
        "StringsLiaSolver must forward generate_bound_axiom_terms to LIA; \
         got empty Vec (trait default). Two lower bounds on same Int variable \
         should produce at least one bound ordering axiom."
    );
}

/// Verify that UfSeqLiaSolver.generate_bound_axiom_terms() returns non-empty
/// when bound atoms are registered. Without forwarding, QF_SEQLIA problems
/// miss bound ordering axioms.
#[test]
fn test_uf_seq_lia_generate_bound_axiom_terms_forwards_to_lia() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let three = terms.mk_int(BigInt::from(3));
    let seven = terms.mk_int(BigInt::from(7));

    let ge3 = terms.mk_ge(x, three); // x >= 3
    let ge7 = terms.mk_ge(x, seven); // x >= 7

    let mut solver = UfSeqLiaSolver::new(&terms);
    solver.register_atom(ge3);
    solver.register_atom(ge7);
    solver.sort_atom_index();

    let axioms = solver.generate_bound_axiom_terms();
    assert!(
        !axioms.is_empty(),
        "UfSeqLiaSolver must forward generate_bound_axiom_terms to LIA; \
         got empty Vec (trait default). Two lower bounds on same Int variable \
         should produce at least one bound ordering axiom."
    );
}

/// Verify that StringsLiaSolver.suggest_phase() forwards to LIA, comparing
/// adapter result against standalone LiaSolver. (P1:130 strengthened.)
#[test]
fn test_strings_lia_suggest_phase_forwards_to_lia() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let three = terms.mk_int(BigInt::from(3));
    let ge3 = terms.mk_ge(x, three);

    let mut adapter = StringsLiaSolver::new(&terms);
    adapter.register_atom(ge3);
    let mut standalone = ay_lia::LiaSolver::new(&terms);
    standalone.register_atom(ge3);

    let adapter_phase = adapter.suggest_phase(ge3);
    let standalone_phase = standalone.suggest_phase(ge3);
    assert_eq!(
        adapter_phase, standalone_phase,
        "StringsLiaSolver.suggest_phase must match standalone LIA; \
         adapter={adapter_phase:?}, standalone={standalone_phase:?}"
    );
    assert!(
        standalone_phase.is_some(),
        "BUG: standalone LiaSolver returned None for suggest_phase(x >= 3); \
         test cannot detect missing forwarding"
    );
}

/// Verify that UfSeqLiaSolver.suggest_phase() forwards to LIA, comparing
/// adapter result against standalone LiaSolver. (P1:130 strengthened.)
#[test]
fn test_uf_seq_lia_suggest_phase_forwards_to_lia() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let three = terms.mk_int(BigInt::from(3));
    let ge3 = terms.mk_ge(x, three);

    let mut adapter = UfSeqLiaSolver::new(&terms);
    adapter.register_atom(ge3);
    let mut standalone = ay_lia::LiaSolver::new(&terms);
    standalone.register_atom(ge3);

    let adapter_phase = adapter.suggest_phase(ge3);
    let standalone_phase = standalone.suggest_phase(ge3);
    assert_eq!(
        adapter_phase, standalone_phase,
        "UfSeqLiaSolver.suggest_phase must match standalone LIA; \
         adapter={adapter_phase:?}, standalone={standalone_phase:?}"
    );
    assert!(
        standalone_phase.is_some(),
        "BUG: standalone LiaSolver returned None for suggest_phase(x >= 3); \
         test cannot detect missing forwarding"
    );
}

/// Verify that StringsLiaSolver.supports_theory_aware_branching() forwards to LIA.
/// LIMITATION (P1:130): LRA currently returns false, same as trait default.
/// This comparison test is structurally correct but cannot distinguish forwarding
/// from non-forwarding while both return false. It becomes meaningful if LRA
/// re-enables theory-aware branching (returns true). The generate_bound_axiom_terms
/// and suggest_phase tests above provide stronger forwarding evidence.
#[test]
fn test_strings_lia_supports_theory_aware_branching() {
    let terms = TermStore::new();
    let adapter = StringsLiaSolver::new(&terms);
    let standalone = ay_lia::LiaSolver::new(&terms);
    assert_eq!(
        adapter.supports_theory_aware_branching(),
        standalone.supports_theory_aware_branching(),
        "StringsLiaSolver must forward supports_theory_aware_branching to LIA"
    );
}

/// Verify that UfSeqLiaSolver.supports_theory_aware_branching() forwards to LIA.
/// LIMITATION (P1:130): same as above — currently vacuous while LRA returns false.
#[test]
fn test_uf_seq_lia_supports_theory_aware_branching() {
    let terms = TermStore::new();
    let adapter = UfSeqLiaSolver::new(&terms);
    let standalone = ay_lia::LiaSolver::new(&terms);
    assert_eq!(
        adapter.supports_theory_aware_branching(),
        standalone.supports_theory_aware_branching(),
        "UfSeqLiaSolver must forward supports_theory_aware_branching to LIA"
    );
}
