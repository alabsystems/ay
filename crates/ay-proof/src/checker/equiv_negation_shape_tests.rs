// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `equiv_*` must accept an operand that is itself a negation.
//!
//! `clause_matches_expected`'s `ExpectedLit::Not(t)` arm tested
//! `strip_not(lit) == Some(t)` — a purely syntactic check. When the equivalence
//! operand `t` is itself `(not X)`, that demands the clause literal be
//! `(not (not X))`.
//!
//! **No emitter can ever satisfy that.** `TermStore` collapses double negation:
//! `mk_not`, `negate_term` and the canonicalizer's `neg()` all return `X` for
//! `(not (not X))`, so the term the checker was asking for cannot be
//! constructed. Every `equiv_pos1`/`equiv_neg1` step over a negated operand was
//! therefore rejected as "clause shape does not match equality", and the
//! surrounding `unsat` was published as `unknown`.
//!
//! The fix uses `matches_negation_of_term`, which already sits in the same file
//! and already opens with exactly the `strip_not` test it replaces — so the
//! change is strictly ADDITIVE: everything accepted before is still accepted.
//! It is also not a novel grant of trust: `matches_negation_of_term` is what
//! `resolution.rs` uses for PIVOT matching (lines 210/217/219), the most
//! soundness-critical comparison in the checker.
//!
//! The rejecting-direction tests below are the ones that matter — a shape check
//! that accepts everything would be worthless, so each fix here ships with a
//! case proving the rule still refuses a clause that is genuinely wrong.

use crate::checker::*;
use ay_core::{AletheRule, ProofId, ProofStep, Sort, Symbol, TermId, TermStore};

fn eq(terms: &mut TermStore, lhs: TermId, rhs: TermId) -> TermId {
    terms.mk_app(Symbol::named("="), vec![lhs, rhs], Sort::Bool)
}

fn boolvar(terms: &mut TermStore, name: &str) -> TermId {
    terms.mk_var(name, Sort::Bool)
}

fn validate(
    terms: &TermStore,
    rule: AletheRule,
    clause: Vec<TermId>,
) -> Result<(), ProofCheckError> {
    let step = ProofStep::Step {
        rule,
        clause,
        premises: vec![],
        args: vec![],
    };
    let mut derived: Vec<Option<Vec<TermId>>> = vec![];
    validate_step(terms, &mut derived, ProofId(0), &step, true, None)
}

/// `equiv_pos1` over `(= a (not b))`.
///
/// Shape: `(cl (not (= a (not b))) a (not (not b)))`. The third literal cannot
/// be built as `(not (not b))` — the store folds it to `b` — so the clause AY
/// actually emits is `(cl (not (= a (not b))) a b)`. That is the correct
/// clause, and the checker must accept it.
#[test]
fn equiv_pos1_accepts_a_negated_right_operand() {
    let mut terms = TermStore::new();
    let a = boolvar(&mut terms, "a");
    let b = boolvar(&mut terms, "b");
    let not_b = terms.mk_not(b);
    let equality = eq(&mut terms, a, not_b);
    let not_eq = terms.mk_not(equality);

    // `mk_not` collapses the double negation: this IS `b`.
    let third = terms.mk_not(not_b);
    assert_eq!(
        third, b,
        "precondition: TermStore must collapse (not (not b)) to b — if this \
         ever changes, the defect this file pins no longer exists in this form"
    );

    validate(&terms, AletheRule::EquivPos1, vec![not_eq, a, third]).expect(
        "equiv_pos1 over a negated operand must be accepted: the checker was \
         demanding a literal `(not (not b))` that TermStore cannot construct",
    );
}

/// `equiv_neg1` over `(= (not a) b)` — both expected literals are negations.
#[test]
fn equiv_neg1_accepts_a_negated_left_operand() {
    let mut terms = TermStore::new();
    let a = boolvar(&mut terms, "a");
    let b = boolvar(&mut terms, "b");
    let not_a = terms.mk_not(a);
    let equality = eq(&mut terms, not_a, b);

    let neg_first = terms.mk_not(not_a); // == a
    let neg_second = terms.mk_not(b);
    assert_eq!(neg_first, a, "precondition: (not (not a)) folds to a");

    validate(
        &terms,
        AletheRule::EquivNeg1,
        vec![equality, neg_first, neg_second],
    )
    .expect("equiv_neg1 over a negated operand must be accepted");
}

/// REJECTING DIRECTION. A clause whose literals are NOT the rule's shape must
/// still be refused — the fix must not turn the check into a rubber stamp.
#[test]
fn equiv_pos1_still_rejects_an_unrelated_third_literal() {
    let mut terms = TermStore::new();
    let a = boolvar(&mut terms, "a");
    let b = boolvar(&mut terms, "b");
    let c = boolvar(&mut terms, "c");
    let not_b = terms.mk_not(b);
    let equality = eq(&mut terms, a, not_b);
    let not_eq = terms.mk_not(equality);

    // `c` is neither `b` nor the negation of `(not b)`.
    validate(&terms, AletheRule::EquivPos1, vec![not_eq, a, c])
        .expect_err("equiv_pos1 must reject a clause with an unrelated literal");
}

/// REJECTING DIRECTION. Wrong POLARITY on the operand must stay rejected:
/// `(cl (not (= a b)) a b)` is not `equiv_pos1` (the third literal should be
/// `(not b)`), and accepting it would be unsound.
#[test]
fn equiv_pos1_still_rejects_wrong_polarity() {
    let mut terms = TermStore::new();
    let a = boolvar(&mut terms, "a");
    let b = boolvar(&mut terms, "b");
    let equality = eq(&mut terms, a, b);
    let not_eq = terms.mk_not(equality);

    validate(&terms, AletheRule::EquivPos1, vec![not_eq, a, b]).expect_err(
        "equiv_pos1 must reject a positive `b` where `(not b)` is required — \
         this is the soundness content of the rule",
    );
}

/// REJECTING DIRECTION. Length must still be enforced.
#[test]
fn equiv_pos1_still_rejects_a_short_clause() {
    let mut terms = TermStore::new();
    let a = boolvar(&mut terms, "a");
    let b = boolvar(&mut terms, "b");
    let not_b = terms.mk_not(b);
    let equality = eq(&mut terms, a, not_b);
    let not_eq = terms.mk_not(equality);

    validate(&terms, AletheRule::EquivPos1, vec![not_eq, a])
        .expect_err("equiv_pos1 must reject a 2-literal clause");
}

/// CONTROL: the ordinary, non-negated case keeps working unchanged.
#[test]
fn equiv_pos1_plain_operands_unchanged() {
    let mut terms = TermStore::new();
    let a = boolvar(&mut terms, "a");
    let b = boolvar(&mut terms, "b");
    let equality = eq(&mut terms, a, b);
    let not_eq = terms.mk_not(equality);
    let not_b = terms.mk_not(b);

    validate(&terms, AletheRule::EquivPos1, vec![not_eq, a, not_b])
        .expect("the plain equiv_pos1 shape must still be accepted");
}
