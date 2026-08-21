// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Shape tests for the fresh-definition bound recognizer.
//!
//! This half decides only the LOCAL shape. The properties that make the step
//! sound — freshness, one definiens per symbol, no introduced symbol inside a
//! definiens — are whole-proof and are tested in `ay-proof`'s
//! `checker/fresh_def_tests.rs`, which is also where the adversarial negatives
//! naming a falsifying assignment live for those.
//!
//! The one condition that IS local and IS load-bearing for soundness is SORT:
//! the whole argument is "assign `d` the value of `lin`", and that assignment
//! must exist. Its adversarial negative names its falsifying assignment here.

use num_bigint::BigInt;

use super::fresh_def_bound::{recognize_fresh_def_bound, FreshDefBoundShapeError};
use crate::proof_validation::FreshDefBoundSide;
use crate::{Sort, TermId, TermStore};

/// Which guard in `recognize_fresh_def_bound` each adversarial test defends.
/// Every entry was checked by DELETING the guard, running the named test,
/// observing the failure, and restoring the guard.
const SHAPE_GUARD_MUTATION_LEDGER: &[(&str, &str)] = &[
    (
        "recognize_fresh_def_bound: `premise_count != 0`",
        "rejects_a_bound_that_carries_premises",
    ),
    (
        "recognize_fresh_def_bound: exactly one `:args` term",
        "rejects_a_bound_that_names_no_symbol",
    ),
    (
        "recognize_fresh_def_bound: exactly one clause literal",
        "rejects_a_multi_literal_clause",
    ),
    (
        "recognize_fresh_def_bound: `<=` head with arity 2",
        "rejects_an_equality_instead_of_a_bound",
    ),
    (
        "recognize_fresh_def_bound: definiendum is `TermData::Var`",
        "rejects_a_compound_definiendum",
    ),
    (
        "recognize_fresh_def_bound: EXACTLY one operand is the definiendum",
        "rejects_a_bound_whose_symbol_is_on_neither_side",
    ),
    (
        "recognize_fresh_def_bound: `sort(d) == sort(lin)`",
        "rejects_an_int_symbol_defined_by_a_real_term_satisfied_at_one_half",
    ),
];

#[test]
fn shape_guard_mutation_ledger_names_a_test_per_guard() {
    assert_eq!(
        SHAPE_GUARD_MUTATION_LEDGER.len(),
        7,
        "every guard in the shape recognizer must name the test that defends it",
    );
    for (guard, test) in SHAPE_GUARD_MUTATION_LEDGER {
        assert!(!guard.is_empty() && !test.is_empty());
    }
}

struct Fixture {
    terms: TermStore,
    d: TermId,
    x: TermId,
    y: TermId,
}

fn fixture() -> Fixture {
    let mut terms = TermStore::new();
    let d = terms.mk_var("__ay_eqdv!1".to_string(), Sort::Int);
    let x = terms.mk_var("x".to_string(), Sort::Int);
    let y = terms.mk_var("y".to_string(), Sort::Int);
    Fixture { terms, d, x, y }
}

/// `x - y`, the shape `EqDiffVar` actually builds for `(= x y)`.
fn diff(terms: &mut TermStore, x: TermId, y: TermId) -> TermId {
    let neg_y = terms.mk_neg(y);
    terms.mk_add(vec![x, neg_y])
}

#[test]
fn accepts_the_upper_bound_of_a_definitional_pair() {
    let mut f = fixture();
    let lin = diff(&mut f.terms, f.x, f.y);
    let atom = f.terms.mk_le(f.d, lin);
    let shape = recognize_fresh_def_bound(&f.terms, &[atom], 0, &[f.d])
        .expect("`(<= d (x - y))` with `:args (d)` is the shape this rule is for");
    assert_eq!(shape.definiendum, f.d);
    assert_eq!(shape.definiens, lin);
    assert_eq!(shape.side, FreshDefBoundSide::Upper);
    assert_eq!(shape.atom, atom);
}

#[test]
fn accepts_the_lower_bound_of_a_definitional_pair() {
    let mut f = fixture();
    let lin = diff(&mut f.terms, f.x, f.y);
    // `mk_ge(d, lin)` canonicalizes to `(<= lin d)`, which is what reaches the
    // proof; the recognizer must see the definiendum on the RIGHT.
    let atom = f.terms.mk_ge(f.d, lin);
    let shape = recognize_fresh_def_bound(&f.terms, &[atom], 0, &[f.d])
        .expect("`(>= d lin)` canonicalizes to `(<= lin d)` and is equally a definitional bound");
    assert_eq!(shape.definiendum, f.d);
    assert_eq!(shape.definiens, lin);
    assert_eq!(shape.side, FreshDefBoundSide::Lower);
}

#[test]
fn accepts_a_constant_definiens() {
    // `(= x y)` folds to `(= d 0)`, whose equality lowering is the pair
    // `(<= d 0)` / `(<= 0 d)`. A constant is a perfectly good definiens:
    // `d := 0` is an assignment like any other.
    let mut f = fixture();
    let zero = f.terms.mk_int(BigInt::from(0));
    let atom = f.terms.mk_le(f.d, zero);
    let shape = recognize_fresh_def_bound(&f.terms, &[atom], 0, &[f.d])
        .expect("a ground definiens is still a definiens");
    assert_eq!(shape.definiens, zero);
}

#[test]
fn rejects_a_bound_that_carries_premises() {
    // A step with premises is an INFERENCE, and this rule proves nothing from
    // anything — admitting one would let `(<= d lin)` be presented as though
    // it followed from the cited steps. Falsifying witness for the underlying
    // claim: with `d` genuinely constrained by a premise, `d = lin + 1`
    // satisfies every premise and refutes the conclusion.
    let mut f = fixture();
    let lin = diff(&mut f.terms, f.x, f.y);
    let atom = f.terms.mk_le(f.d, lin);
    assert_eq!(
        recognize_fresh_def_bound(&f.terms, &[atom], 1, &[f.d]),
        Err(FreshDefBoundShapeError::HasPremises)
    );
}

#[test]
fn rejects_a_bound_that_names_no_symbol() {
    // Without `:args` the checker would have to GUESS which operand is being
    // defined. For `(<= a b)` with both sides atomic that guess decides which
    // of two symbols is claimed fresh, so it is not a guess a soundness gate
    // may make.
    let mut f = fixture();
    let atom = f.terms.mk_le(f.d, f.x);
    assert_eq!(
        recognize_fresh_def_bound(&f.terms, &[atom], 0, &[]),
        Err(FreshDefBoundShapeError::ArgArity(0))
    );
    assert_eq!(
        recognize_fresh_def_bound(&f.terms, &[atom], 0, &[f.d, f.x]),
        Err(FreshDefBoundShapeError::ArgArity(2))
    );
}

#[test]
fn rejects_a_multi_literal_clause() {
    // A wider clause is a disjunction, and a disjunction containing a
    // definitional bound is NOT satisfied by `d := lin` — the other disjuncts
    // are unconstrained. Falsifying witness for `(cl (<= d lin) (<= 0 x))`
    // read as a definition: at `x = -1` the second disjunct is false, so the
    // clause carries content beyond the definition.
    let mut f = fixture();
    let lin = diff(&mut f.terms, f.x, f.y);
    let atom = f.terms.mk_le(f.d, lin);
    let zero = f.terms.mk_int(BigInt::from(0));
    let other = f.terms.mk_le(zero, f.x);
    assert_eq!(
        recognize_fresh_def_bound(&f.terms, &[atom, other], 0, &[f.d]),
        Err(FreshDefBoundShapeError::ClauseArity(2))
    );
    assert_eq!(
        recognize_fresh_def_bound(&f.terms, &[], 0, &[f.d]),
        Err(FreshDefBoundShapeError::ClauseArity(0))
    );
}

#[test]
fn rejects_an_equality_instead_of_a_bound() {
    // `(= d lin)` is a unit equality, and downstream `VariableSubstitution`
    // inlines those — the pass emits the inequality PAIR precisely so it is
    // not inlined. Admitting the equality spelling here would also admit any
    // other binary predicate the head happened to be.
    let mut f = fixture();
    let lin = diff(&mut f.terms, f.x, f.y);
    let atom = f.terms.mk_eq(f.d, lin);
    assert_eq!(
        recognize_fresh_def_bound(&f.terms, &[atom], 0, &[f.d]),
        Err(FreshDefBoundShapeError::NotBinaryLe)
    );
}

#[test]
fn rejects_a_compound_definiendum() {
    // Freshness is a property of a SYMBOL. `(f a)` is not a symbol: bounding
    // it constrains `f` at one point, and no reinterpretation of a fresh
    // symbol can arrange that. Falsifying witness: with `f` the identity and
    // `a = 5`, `(<= (f a) 0)` is false, yet a "definition" reading would take
    // it for free.
    let mut f = fixture();
    let app = f
        .terms
        .mk_app(crate::Symbol::Named("g".to_string()), vec![f.x], Sort::Int);
    let zero = f.terms.mk_int(BigInt::from(0));
    let atom = f.terms.mk_le(app, zero);
    assert_eq!(
        recognize_fresh_def_bound(&f.terms, &[atom], 0, &[app]),
        Err(FreshDefBoundShapeError::DefiniendumNotVariable)
    );
}

#[test]
fn rejects_a_bound_whose_symbol_is_on_neither_side() {
    // The declared symbol must actually be what the bound is about. Otherwise
    // `(<= x y)` — an ordinary constraint on two authored variables — could be
    // waved through by naming an unrelated fresh `d` in `:args`. Falsifying
    // assignment: `x = 1, y = 0` refutes `(<= x y)`, and no choice of `d`
    // repairs it.
    let mut f = fixture();
    let atom = f.terms.mk_le(f.x, f.y);
    assert_eq!(
        recognize_fresh_def_bound(&f.terms, &[atom], 0, &[f.d]),
        Err(FreshDefBoundShapeError::DefiniendumNotAnOperand)
    );
}

#[test]
fn rejects_an_int_symbol_defined_by_a_real_term_satisfied_at_one_half() {
    // SORT is the local half of the soundness argument. `d : Int` with
    // `lin : Real` forces `lin` to be an INTEGER, which is a genuine
    // constraint on the problem's own variables — this is the same
    // integrality asymmetry that makes `2q ∈ [1,1]` unsatisfiable over ℤ and
    // satisfiable at `q = 1/2` over ℚ.
    //
    // FALSIFYING ASSIGNMENT: take `r : Real` with `r = 1/2`, the only
    // constraint on `r`. That problem is satisfiable. Adding `(<= d r)` and
    // `(<= r d)` for an Int `d` demands an integer in `[1/2, 1/2]`, so the
    // extended problem is UNSAT — the extension is not conservative.
    let mut f = fixture();
    let r = f.terms.mk_var("r".to_string(), Sort::Real);
    // `mk_le` debug-asserts matching sorts, so a mixed-sort `<=` can only be
    // built the way a FORGED or deserialized proof would present one: as a raw
    // application. That is exactly the input this guard exists for.
    let atom = f.terms.mk_app(
        crate::Symbol::Named("<=".to_string()),
        vec![f.d, r],
        Sort::Bool,
    );
    assert_eq!(
        recognize_fresh_def_bound(&f.terms, &[atom], 0, &[f.d]),
        Err(FreshDefBoundShapeError::SortMismatch(Sort::Int, Sort::Real))
    );
}

#[test]
fn accepts_a_real_symbol_defined_by_a_real_term() {
    // The guard is sort EQUALITY, not "Int only": a Real symbol defined by a
    // Real term admits `d := lin` exactly as an Int one does.
    let mut f = fixture();
    let d_real = f.terms.mk_var("__ay_eqdv!2".to_string(), Sort::Real);
    let r = f.terms.mk_var("r".to_string(), Sort::Real);
    let s = f.terms.mk_var("s".to_string(), Sort::Real);
    let lin = f.terms.mk_add(vec![r, s]);
    let atom = f.terms.mk_le(d_real, lin);
    let shape = recognize_fresh_def_bound(&f.terms, &[atom], 0, &[d_real])
        .expect("matching Real sorts admit `d := lin` just as Int sorts do");
    assert_eq!(shape.definiens, lin);
}
