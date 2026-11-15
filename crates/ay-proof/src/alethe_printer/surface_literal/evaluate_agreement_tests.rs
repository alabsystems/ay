// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The `evaluate` lowering reads an alternate spelling of the SAME bit-vector
//! literal as the identity, and nothing wider: a changed value, a changed
//! width, a folded compound spelling, or any other surface difference still
//! withholds the step (the printer then refuses it as "evaluate conclusion
//! changed under surface rewriting").

use super::*;
use crate::evaluate_step_lowering_supported;
use num_bigint::BigInt;

/// `(= (= left right) false)`, the closer the instance-seeded closure emits
/// for two distinct constant endpoints.
fn refuted_equality(terms: &mut TermStore, left: TermId, right: TermId) -> [TermId; 1] {
    let equality = terms.mk_app(Symbol::named("="), [left, right], Sort::Bool);
    let falsity = terms.false_term();
    [terms.mk_app(Symbol::named("="), [equality, falsity], Sort::Bool)]
}

fn spelled(entries: &[(TermId, &str)]) -> HashMap<TermId, String> {
    entries
        .iter()
        .map(|&(term, surface)| (term, surface.to_string()))
        .collect()
}

#[test]
fn evaluate_admits_an_alternate_spelling_of_the_same_literal() {
    let mut terms = TermStore::new();
    let one = terms.mk_bitvec(BigInt::from(1), 1);
    let zero = terms.mk_bitvec(BigInt::from(0), 1);
    let clause = refuted_equality(&mut terms, one, zero);
    let respelled = spelled(&[(one, "(_ bv1 1)"), (zero, "(_ bv0 1)")]);
    assert!(evaluate_step_lowering_supported(
        &terms,
        &clause,
        Some(&respelled)
    ));
    // Counterfactual pin: the shared classifier every other promotion reads
    // (including the byte-guarded LIA `evaluate` printer) is unchanged.
    assert_eq!(
        clause_surface_agreement(&terms, &clause, Some(&respelled)),
        ClauseSurfaceAgreement::Divergent
    );

    // The same literal below an otherwise identical application.
    let k = terms.mk_var("k", Sort::bitvec(64));
    let sixty_five = terms.mk_bitvec(BigInt::from(65), 64);
    let guard = terms.mk_app(Symbol::named("bvult"), [k, sixty_five], Sort::Bool);
    let truth = terms.true_term();
    let clause = [terms.mk_app(Symbol::named("="), [guard, truth], Sort::Bool)];
    let respelled = spelled(&[(guard, "(bvult k (_ bv65 64))")]);
    assert!(evaluate_step_lowering_supported(
        &terms,
        &clause,
        Some(&respelled)
    ));
}

#[test]
fn evaluate_still_refuses_every_other_surface_change() {
    let mut terms = TermStore::new();
    let one = terms.mk_bitvec(BigInt::from(1), 1);
    let zero = terms.mk_bitvec(BigInt::from(0), 1);
    let clause = refuted_equality(&mut terms, one, zero);
    // A different VALUE would print `(= (= #b0 #b0) false)`: a false step.
    let changed_value = spelled(&[(one, "(_ bv0 1)")]);
    assert!(!evaluate_step_lowering_supported(
        &terms,
        &clause,
        Some(&changed_value)
    ));

    let sixty_five = terms.mk_bitvec(BigInt::from(65), 64);
    let sixty_four = terms.mk_bitvec(BigInt::from(64), 64);
    let clause = refuted_equality(&mut terms, sixty_five, sixty_four);
    // A different WIDTH is a different constant to the checker.
    let changed_width = spelled(&[(sixty_five, "(_ bv65 72)")]);
    assert!(!evaluate_step_lowering_supported(
        &terms,
        &clause,
        Some(&changed_width)
    ));

    // A folded compound spelling needs evaluation, not parser identity.
    let wide = terms.mk_bitvec(BigInt::from(1) << 128, 136);
    let wide_zero = terms.mk_bitvec(BigInt::from(0), 136);
    let clause = refuted_equality(&mut terms, wide, wide_zero);
    let folded = spelled(&[(wide, "(concat (_ bv1 8) (_ bv0 128))")]);
    assert!(!evaluate_step_lowering_supported(
        &terms,
        &clause,
        Some(&folded)
    ));

    // A changed operand beside an admitted literal respelling.
    let k = terms.mk_var("k", Sort::bitvec(64));
    let guard = terms.mk_app(Symbol::named("bvult"), [k, sixty_five], Sort::Bool);
    let truth = terms.true_term();
    let clause = [terms.mk_app(Symbol::named("="), [guard, truth], Sort::Bool)];
    let changed_operand = spelled(&[(guard, "(bvult j (_ bv65 64))")]);
    assert!(!evaluate_step_lowering_supported(
        &terms,
        &clause,
        Some(&changed_operand)
    ));
}
