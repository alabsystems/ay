// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Shape tests for the fresh-definition EQUALITY recognizer.
//!
//! This half decides only the LOCAL shape. The properties that make the step
//! sound — freshness, one definiens per symbol, no introduced symbol inside a
//! definiens — are whole-proof and are tested in `ay-proof`'s
//! `checker/fresh_def_tests.rs`, which is also where the adversarial negatives
//! naming a falsifying assignment live for those.
//!
//! Two conditions ARE local and ARE load-bearing for soundness, and each has
//! its adversarial negative here with the falsifying assignment named:
//!
//! * SORT — the whole argument is "assign `d` the value of `expr`", and that
//!   assignment must exist.
//! * EXACTLY ONE OPERAND IS THE DEFINIENDUM — `mk_eq` canonicalises operands by
//!   `TermId` order, so the term itself says nothing about which side is the
//!   defined symbol. The `:args` term is the only source of that, and a step
//!   whose `:args` symbol is on NEITHER side would let an ordinary equation
//!   between two problem terms through.

use num_bigint::BigInt;

use super::fresh_def_eq::{recognize_fresh_def_eq, FreshDefEqShapeError};
use crate::{Sort, Symbol, TermId, TermStore};

/// Which guard in `recognize_fresh_def_eq` each adversarial test defends.
/// Every entry was checked by DELETING the guard, running the named test,
/// observing the failure, and restoring the guard.
const SHAPE_GUARD_MUTATION_LEDGER: &[(&str, &str)] = &[
    (
        "recognize_fresh_def_eq: `premise_count != 0`",
        "rejects_an_equality_that_carries_premises",
    ),
    (
        "recognize_fresh_def_eq: exactly one `:args` term",
        "rejects_an_equality_that_names_no_symbol",
    ),
    (
        "recognize_fresh_def_eq: exactly one clause literal",
        "rejects_a_multi_literal_clause",
    ),
    (
        "recognize_fresh_def_eq: `=` head with arity 2",
        "rejects_a_bound_instead_of_an_equality",
    ),
    (
        "recognize_fresh_def_eq: `=` head with arity 2 (the ARITY half)",
        "rejects_an_n_ary_equality",
    ),
    (
        "recognize_fresh_def_eq: definiendum is `TermData::Var`",
        "rejects_a_compound_definiendum",
    ),
    (
        "recognize_fresh_def_eq: EXACTLY one operand is the definiendum",
        "rejects_an_equality_whose_symbol_is_on_neither_side",
    ),
    (
        "recognize_fresh_def_eq: `sort(d) == sort(expr)`",
        "rejects_an_int_symbol_defined_by_a_real_term_satisfied_at_one_half",
    ),
];

#[test]
fn shape_guard_mutation_ledger_names_a_test_per_guard() {
    assert_eq!(
        SHAPE_GUARD_MUTATION_LEDGER.len(),
        8,
        "every guard in the shape recognizer must name the test that defends it",
    );
    for (guard, test) in SHAPE_GUARD_MUTATION_LEDGER {
        assert!(!guard.is_empty() && !test.is_empty());
    }
}

struct Fixture {
    terms: TermStore,
    /// The fresh Boolean proxy `purify_bool_args` actually mints.
    p: TermId,
    /// A fresh Int symbol, for the sort tests.
    d: TermId,
    x: TermId,
    y: TermId,
    g: TermId,
}

fn fixture() -> Fixture {
    let mut terms = TermStore::new();
    let p = terms.mk_var("boolarg_7".to_string(), Sort::Bool);
    let d = terms.mk_var("__ay_def!1".to_string(), Sort::Int);
    let x = terms.mk_var("x".to_string(), Sort::Int);
    let y = terms.mk_var("y".to_string(), Sort::Int);
    let g = terms.mk_var("g".to_string(), Sort::Bool);
    Fixture {
        terms,
        p,
        d,
        x,
        y,
        g,
    }
}

impl Fixture {
    /// `(and g (<= x y))`, a compound Boolean argument of the kind
    /// `purify_bool_args` purifies.
    fn compound_bool(&mut self) -> TermId {
        let le = self.terms.mk_le(self.x, self.y);
        self.terms.mk_and(vec![self.g, le])
    }
}

// ---------------------------------------------------------------------------
// Accepts
// ---------------------------------------------------------------------------

#[test]
fn accepts_the_boolean_proxy_definition_the_corpus_actually_carries() {
    let mut f = fixture();
    let body = f.compound_bool();
    let atom = f.terms.mk_eq(f.p, body);
    let shape = recognize_fresh_def_eq(&f.terms, &[atom], 0, &[f.p])
        .expect("`(= p (and g (<= x y)))` with `:args (p)` is the shape this rule is for");
    assert_eq!(shape.definiendum, f.p);
    assert_eq!(shape.definiens, body);
    assert_eq!(shape.atom, atom);
}

#[test]
fn the_operand_order_in_the_term_is_irrelevant_because_mk_eq_canonicalises() {
    // `mk_eq` orders its operands by `TermId`, so `(= p body)` and
    // `(= body p)` are the SAME interned term. There is therefore no
    // symmetry-orientation question at all, and the `:args` term is the only
    // thing that says which side is the definiendum.
    let mut f = fixture();
    let body = f.compound_bool();
    let forward = f.terms.mk_eq(f.p, body);
    let backward = f.terms.mk_eq(body, f.p);
    assert_eq!(forward, backward, "mk_eq must canonicalise operand order");
    let a = recognize_fresh_def_eq(&f.terms, &[forward], 0, &[f.p]).expect("forward");
    let b = recognize_fresh_def_eq(&f.terms, &[backward], 0, &[f.p]).expect("backward");
    assert_eq!(a, b);
}

#[test]
fn accepts_a_definition_at_a_non_arithmetic_sort() {
    // The whole reason this is a SIBLING rule rather than a widening of
    // `fresh_def_bound`: `<=` cannot even be written at an Array sort.
    let mut terms = TermStore::new();
    let element = Sort::Int;
    let array = Sort::array(Sort::Int, element);
    let a = terms.mk_var("a".to_string(), array.clone());
    let d = terms.mk_var("__ay_def!9".to_string(), array);
    let i = terms.mk_var("i".to_string(), Sort::Int);
    let v = terms.mk_var("v".to_string(), Sort::Int);
    let store = terms.mk_store(a, i, v);
    let atom = terms.mk_eq(d, store);
    let shape = recognize_fresh_def_eq(&terms, &[atom], 0, &[d])
        .expect("an array-sorted definitional equality is in scope");
    assert_eq!(shape.definiendum, d);
    assert_eq!(shape.definiens, store);
}

#[test]
fn accepts_a_definiens_that_is_itself_an_atomic_variable() {
    // `(= d x)` with `d` fresh is a legitimate definition `d := x`; both
    // operands are variables and the `:args` term disambiguates. Whether `x`
    // is fresh too is a WHOLE-PROOF question this recognizer does not decide.
    let mut f = fixture();
    let atom = f.terms.mk_eq(f.d, f.x);
    let shape =
        recognize_fresh_def_eq(&f.terms, &[atom], 0, &[f.d]).expect("`d := x` is a definition");
    assert_eq!(shape.definiendum, f.d);
    assert_eq!(shape.definiens, f.x);
}

// ---------------------------------------------------------------------------
// Adversarial negatives
// ---------------------------------------------------------------------------

#[test]
fn rejects_an_equality_that_carries_premises() {
    // A definition is derived from NOTHING. A step with premises is an
    // inference, and relabelling it would drop the premises its consumer
    // references — the conclusion would then be asserted rather than derived.
    let mut f = fixture();
    let body = f.compound_bool();
    let atom = f.terms.mk_eq(f.p, body);
    assert_eq!(
        recognize_fresh_def_eq(&f.terms, &[atom], 1, &[f.p]),
        Err(FreshDefEqShapeError::HasPremises)
    );
}

#[test]
fn rejects_an_equality_that_names_no_symbol() {
    let mut f = fixture();
    let body = f.compound_bool();
    let atom = f.terms.mk_eq(f.p, body);
    assert_eq!(
        recognize_fresh_def_eq(&f.terms, &[atom], 0, &[]),
        Err(FreshDefEqShapeError::ArgArity(0))
    );
    assert_eq!(
        recognize_fresh_def_eq(&f.terms, &[atom], 0, &[f.p, f.g]),
        Err(FreshDefEqShapeError::ArgArity(2))
    );
}

#[test]
fn rejects_a_multi_literal_clause() {
    // A wider clause is a DISJUNCTION. `(cl (= p b) (= q c))` asserts only that
    // one of the two definitions holds, which is not a definition of either.
    let mut f = fixture();
    let body = f.compound_bool();
    let atom = f.terms.mk_eq(f.p, body);
    let other = f.terms.mk_le(f.x, f.y);
    assert_eq!(
        recognize_fresh_def_eq(&f.terms, &[atom, other], 0, &[f.p]),
        Err(FreshDefEqShapeError::ClauseArity(2))
    );
    assert_eq!(
        recognize_fresh_def_eq(&f.terms, &[], 0, &[f.p]),
        Err(FreshDefEqShapeError::ClauseArity(0))
    );
}

#[test]
fn rejects_a_bound_instead_of_an_equality() {
    // The sibling rule's shape must not be admitted here: the two carry
    // different obligations at the wire and the checker dispatches on the rule.
    let mut f = fixture();
    let atom = f.terms.mk_le(f.d, f.x);
    assert_eq!(
        recognize_fresh_def_eq(&f.terms, &[atom], 0, &[f.d]),
        Err(FreshDefEqShapeError::NotBinaryEq)
    );
}

#[test]
fn rejects_an_n_ary_equality() {
    // FALSIFYING ASSIGNMENT. `mk_eq` never builds this, but a clause is an
    // arbitrary interned term. `(= d x y)` read as `d := x` would leave `y`
    // unaccounted: the extension would also force `x = y`, which is FALSE at
    // `x = 0, y = 1` — a constraint on the problem's own variables.
    let mut f = fixture();
    let atom = f
        .terms
        .mk_app(Symbol::named("="), vec![f.d, f.x, f.y], Sort::Bool);
    assert_eq!(
        recognize_fresh_def_eq(&f.terms, &[atom], 0, &[f.d]),
        Err(FreshDefEqShapeError::NotBinaryEq)
    );
}

#[test]
fn rejects_a_compound_definiendum() {
    // FALSIFYING ASSIGNMENT. `(= (f i) e)` with a fresh `f` is NOT covered by
    // this rule's argument: two such steps at arguments the model equates
    // conflict, so `d := expr` is not a well-defined assignment. Only an
    // atomic symbol is in scope.
    let mut terms = TermStore::new();
    let i = terms.mk_var("i".to_string(), Sort::Int);
    let e = terms.mk_var("e".to_string(), Sort::Int);
    let app = terms.mk_app(Symbol::named("f"), vec![i], Sort::Int);
    let atom = terms.mk_eq(app, e);
    assert_eq!(
        recognize_fresh_def_eq(&terms, &[atom], 0, &[app]),
        Err(FreshDefEqShapeError::DefiniendumNotVariable)
    );
}

#[test]
fn rejects_an_equality_whose_symbol_is_on_neither_side() {
    // REQUIRED NEGATIVE, and the one this rule needs most: because `mk_eq`
    // canonicalises operand order, the `:args` term is the ONLY statement of
    // which operand is defined. Without this guard `(= x y)` would be
    // certifiable as a "definition of `d`".
    //
    // FALSIFYING ASSIGNMENT. Problem `A = {}`, satisfied by anything. The
    // "extension" `{ x = y }` is refuted at `x = 1, y = 0`, so `A ∪ P` is a
    // strictly stronger set and a refutation of it says nothing about `A`.
    let mut f = fixture();
    let atom = f.terms.mk_eq(f.x, f.y);
    assert_eq!(
        recognize_fresh_def_eq(&f.terms, &[atom], 0, &[f.d]),
        Err(FreshDefEqShapeError::DefiniendumNotAnOperand)
    );
}

#[test]
fn rejects_a_reflexive_equality_that_declares_both_operands() {
    // `(= d d)` declares nothing; `mk_eq` folds it to `true`, so the atom is
    // not even an `=` application. Both paths are refusals; pin the reachable
    // one so a future `mk_eq` change cannot silently open a hole.
    let mut f = fixture();
    let atom = f.terms.mk_eq(f.d, f.d);
    assert!(matches!(
        recognize_fresh_def_eq(&f.terms, &[atom], 0, &[f.d]),
        Err(FreshDefEqShapeError::NotBinaryEq)
    ));
}

#[test]
fn rejects_an_int_symbol_defined_by_a_real_term_satisfied_at_one_half() {
    // REQUIRED NEGATIVE: SORT.
    //
    // FALSIFYING ASSIGNMENT. Problem `A = { r = 1/2 }` over a Real `r`,
    // satisfied at `r = 1/2`. The "definition" `d := r` for an INTEGER `d`
    // forces `r` to be an integer, so `A ∪ P` is UNSAT: the extension
    // constrains the problem's OWN variable. The assignment `d := r` the
    // soundness argument names does not exist.
    let mut f = fixture();
    let r = f.terms.mk_var("r".to_string(), Sort::Real);
    let atom = f.terms.mk_app(Symbol::named("="), vec![f.d, r], Sort::Bool);
    assert_eq!(
        recognize_fresh_def_eq(&f.terms, &[atom], 0, &[f.d]),
        Err(FreshDefEqShapeError::SortMismatch(Sort::Int, Sort::Real))
    );
}

#[test]
fn the_error_display_is_specific_enough_to_diagnose() {
    let mut f = fixture();
    let atom = f.terms.mk_eq(f.x, f.y);
    let rendered = recognize_fresh_def_eq(&f.terms, &[atom], 0, &[f.d])
        .expect_err("neither operand is the declared symbol")
        .to_string();
    assert!(rendered.contains("EXACTLY one"), "{rendered}");
    let zero = f.terms.mk_int(BigInt::from(0));
    let bound = f.terms.mk_le(f.d, zero);
    let rendered = recognize_fresh_def_eq(&f.terms, &[bound], 0, &[f.d])
        .expect_err("a bound is not an equality")
        .to_string();
    assert!(rendered.contains("binary `=`"), "{rendered}");
}
