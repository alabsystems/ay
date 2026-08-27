// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Soundness tests for the fresh-definition EQUALITY form.
//!
//! The sibling `fresh_def_tests.rs` covers the `<=` form. What is NEW here and
//! has to be defended on its own:
//!
//! * the equality's own local shape (`ay-core`'s `fresh_def_eq_tests.rs` owns
//!   that half; this file exercises it only through the registry);
//! * the CROSS-RULE conditions — a symbol defined by `fresh_def_eq` and
//!   bounded by `fresh_def_bound` has TWO definitions, and the two rules share
//!   one registry precisely so that is caught;
//! * that the argument still names a WITNESS: `d := expr`.
//!
//! Every adversarial negative names a concrete falsifying assignment AND
//! CHECKS it, with [`Evaluator`] — a plain-`i64`/`bool` interpreter that shares
//! no code with the registry (no `recognize_*`, no `FreshDefRegistry`, no
//! `ProofStep`). "Checks it" means both halves are asserted: the ORIGINAL
//! problem is SATISFIED at the named point, and NO value of the introduced
//! symbols satisfies the extension there — so the "definition" would refute a
//! satisfiable problem.

use ay_core::{AletheRule, Proof, ProofStep, Sort, TermId, TermStore};
use num_bigint::BigInt;

use super::{fixture, push_bound, Fixture, FreshDefRegistry};

#[path = "fresh_def_eq_negative_tests.rs"]
mod negatives;
#[path = "fresh_def_eq_sweep_tests.rs"]
mod sweeps;

/// Which whole-proof guard each adversarial test in THIS file defends.
/// Every entry was checked by DELETING or WEAKENING the guard, running the
/// named test, observing the failure, and restoring the guard.
const EQ_GUARD_MUTATION_LEDGER: &[(&str, &str)] = &[
    (
        "collect_bindings: `FreshDefEq` steps are collected at all",
        "rejects_two_different_equality_definitions_of_the_same_symbol",
    ),
    (
        "collect_bindings: ONE map shared by both rules (SINGLE DEFINIENS across rules)",
        "rejects_a_symbol_defined_by_an_equality_and_bounded_by_a_different_term",
    ),
    (
        "verify_fresh_and_independent: `constrained` from `problem_assertions`",
        "rejects_an_equality_over_a_symbol_the_problem_constrains",
    ),
    (
        "verify_fresh_and_independent: `constrained` from the proof's `assume` leaves",
        "rejects_an_equality_over_a_symbol_an_assume_constrains",
    ),
    (
        "verify_fresh_and_independent: `definiens_names` membership (self)",
        "rejects_an_equality_whose_symbol_occurs_in_its_own_definiens",
    ),
    (
        "verify_fresh_and_independent: `definiens_names` membership (cycle)",
        "rejects_a_two_symbol_equality_cycle",
    ),
    (
        "recognize_fresh_def_eq: `sort(d) == sort(expr)`, reached through the registry",
        "rejects_an_int_symbol_defined_by_a_real_term",
    ),
    (
        "validate_introduction: the step's name must have a vetted binding",
        "rejects_an_equality_with_no_registry_binding",
    ),
    (
        "validate_introduction: the step's definiens must match the recorded one",
        "rejects_an_equality_rebound_to_a_different_definiens",
    ),
    (
        "recognize_fresh_definition: the rule must BE a fresh-definition rule",
        "the_dispatcher_refuses_a_rule_that_is_not_a_fresh_definition_rule",
    ),
    (
        "collect_bindings + validate_introduction: only the two rules contribute a binding",
        "a_non_fresh_definition_rule_is_refused_by_the_dispatcher",
    ),
];

#[test]
fn eq_guard_mutation_ledger_names_a_test_per_guard() {
    assert_eq!(
        EQ_GUARD_MUTATION_LEDGER.len(),
        11,
        "every guard this file defends must name its test",
    );
    for (guard, test) in EQ_GUARD_MUTATION_LEDGER {
        assert!(!guard.is_empty() && !test.is_empty());
    }
}

/// Append `(cl (= d expr))` with `:args (d)`.
pub(super) fn push_eq(proof: &mut Proof, terms: &mut TermStore, d: TermId, expr: TermId) {
    let atom = terms.mk_eq(d, expr);
    proof.add_step(ProofStep::Step {
        rule: AletheRule::FreshDefEq,
        clause: vec![atom],
        premises: Vec::new(),
        args: vec![d],
    });
}

// ---------------------------------------------------------------------------
// The independent evaluator. No registry code, no recognizers, no proof types.
// ---------------------------------------------------------------------------

/// A value in the tiny fragment these tests build.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Val {
    Int(i64),
    Bool(bool),
}

impl Val {
    fn int(self) -> i64 {
        match self {
            Self::Int(v) => v,
            Self::Bool(_) => panic!("expected an Int value"),
        }
    }

    fn bool(self) -> bool {
        match self {
            Self::Bool(v) => v,
            Self::Int(_) => panic!("expected a Bool value"),
        }
    }
}

/// A plain interpreter over `(name -> value)`. Deliberately hand-written and
/// total on the fragment these tests construct; anything else panics loudly
/// rather than silently returning a default that could hide a disagreement.
pub(super) struct Evaluator<'a> {
    terms: &'a TermStore,
    bindings: Vec<(String, Val)>,
}

impl<'a> Evaluator<'a> {
    pub(super) fn new(terms: &'a TermStore) -> Self {
        Self {
            terms,
            bindings: Vec::new(),
        }
    }

    pub(super) fn with_int(mut self, name: &str, value: i64) -> Self {
        self.bindings.push((name.to_string(), Val::Int(value)));
        self
    }

    pub(super) fn with_bool(mut self, name: &str, value: bool) -> Self {
        self.bindings.push((name.to_string(), Val::Bool(value)));
        self
    }

    fn lookup(&self, name: &str) -> Val {
        self.bindings
            .iter()
            .rev()
            .find(|(n, _)| n == name)
            .unwrap_or_else(|| panic!("no value bound for `{name}`"))
            .1
    }

    pub(super) fn holds(&self, term: TermId) -> bool {
        self.eval(term).bool()
    }

    #[allow(clippy::too_many_lines)]
    pub(super) fn eval(&self, term: TermId) -> Val {
        use ay_core::term::TermData;
        match self.terms.get(term) {
            TermData::Var(name, _) => self.lookup(name),
            TermData::Const(ay_core::Constant::Int(value)) => {
                Val::Int(i64::try_from(value.clone()).expect("test constants fit in i64"))
            }
            TermData::Const(ay_core::Constant::Bool(value)) => Val::Bool(*value),
            TermData::Const(_) => {
                panic!("unsupported constant in the evaluator's fragment")
            }
            TermData::Not(inner) => Val::Bool(!self.eval(*inner).bool()),
            TermData::App(sym, args) => {
                let name = sym.name().to_string();
                match name.as_str() {
                    "+" => Val::Int(args.iter().map(|&a| self.eval(a).int()).sum()),
                    "*" => Val::Int(args.iter().map(|&a| self.eval(a).int()).product()),
                    "-" if args.len() == 1 => Val::Int(-self.eval(args[0]).int()),
                    "-" => Val::Int(
                        args.iter()
                            .skip(1)
                            .fold(self.eval(args[0]).int(), |acc, &a| acc - self.eval(a).int()),
                    ),
                    "<=" => {
                        assert_eq!(args.len(), 2);
                        Val::Bool(self.eval(args[0]).int() <= self.eval(args[1]).int())
                    }
                    "<" => {
                        assert_eq!(args.len(), 2);
                        Val::Bool(self.eval(args[0]).int() < self.eval(args[1]).int())
                    }
                    "=" => {
                        assert_eq!(args.len(), 2);
                        Val::Bool(self.eval(args[0]) == self.eval(args[1]))
                    }
                    "and" => Val::Bool(args.iter().all(|&a| self.eval(a).bool())),
                    "or" => Val::Bool(args.iter().any(|&a| self.eval(a).bool())),
                    "not" => {
                        assert_eq!(args.len(), 1);
                        Val::Bool(!self.eval(args[0]).bool())
                    }
                    other => panic!("unsupported operator `{other}` in the evaluator's fragment"),
                }
            }
            other => panic!("unsupported term {other:?} in the evaluator's fragment"),
        }
    }
}

/// The two halves an adversarial negative has to establish, both CHECKED.
///
/// 1. the ORIGINAL problem holds at the named point (so it is satisfiable);
/// 2. no value of the introduced symbols, over `range`, satisfies every atom of
///    the "extension" there (so the extension is refutable from nothing).
pub(super) fn assert_extension_refutes_a_satisfiable_problem(
    terms: &TermStore,
    authored: &[TermId],
    point: &[(&str, i64)],
    bools: &[(&str, bool)],
    introduced: &[&str],
    extension: &[TermId],
    range: std::ops::RangeInclusive<i64>,
) {
    let base = |extra: &[(&str, i64)]| {
        let mut ev = Evaluator::new(terms);
        for &(name, value) in point {
            ev = ev.with_int(name, value);
        }
        for &(name, value) in bools {
            ev = ev.with_bool(name, value);
        }
        for &(name, value) in extra {
            ev = ev.with_int(name, value);
        }
        ev
    };
    // `point` is the COMPLETE named assignment, including the introduced
    // symbols — a model interprets the whole signature, and when the defect
    // being demonstrated is "the problem constrains `d`" the authored half is
    // only satisfiable at the value the problem forces.
    for &assertion in authored {
        assert!(
            base(&[]).holds(assertion),
            "the named assignment must SATISFY the authored problem, or the negative proves nothing"
        );
    }
    assert!(
        !introduced.is_empty() && introduced.len() <= 2,
        "this helper enumerates one or two introduced symbols"
    );
    for first in range.clone() {
        let seconds: Vec<i64> = if introduced.len() == 2 {
            range.clone().collect()
        } else {
            vec![0]
        };
        for second in seconds {
            let mut extra = vec![(introduced[0], first)];
            if introduced.len() == 2 {
                extra.push((introduced[1], second));
            }
            let ev = base(&extra);
            assert!(
                !extension.iter().all(|&atom| ev.holds(atom)),
                "the extension must be UNSATISFIABLE at the named point, but \
                 {introduced:?} = ({first}, {second}) satisfies every atom"
            );
        }
    }
}

impl Fixture {
    /// A fresh Boolean proxy of the kind `purify_bool_args` mints.
    pub(super) fn proxy(&mut self, n: u32) -> TermId {
        self.terms.mk_var(format!("boolarg_{n}"), Sort::Bool)
    }
}

// ---------------------------------------------------------------------------
// Accepts — each names the witness `d := expr` that makes it conservative.
// ---------------------------------------------------------------------------

#[test]
fn accepts_the_boolean_proxy_definition_the_corpus_carries() {
    // The measured production shape: `purify_bool_args` mints `p` and asserts
    // `(= p (and g (<= x y)))`. WITNESS: any model extends by
    // `p := (g ∧ x ≤ y)^M`, and the CHECK below evaluates that witness at a
    // point rather than merely asserting it exists.
    let mut f = fixture();
    let p = f.proxy(7);
    let g = f.terms.mk_var("g".to_string(), Sort::Bool);
    let le = f.terms.mk_le(f.x, f.y);
    let body = f.terms.mk_and(vec![g, le]);
    let zero = f.int(0);
    let authored = f.terms.mk_le(zero, f.x);
    let mut proof = Proof::new();
    proof.add_assume(authored, None);
    push_eq(&mut proof, &mut f.terms, p, body);
    let registry = FreshDefRegistry::collect(&proof, &f.terms, Some(&[authored]))
        .expect("a fresh Boolean proxy definition is a conservative extension");
    assert_eq!(registry.len(), 1);

    // The witness, checked with the independent evaluator at 3x3 points.
    let atom = f.terms.mk_eq(p, body);
    for x in 0..3 {
        for y in -1..2 {
            for g_value in [false, true] {
                let witness = g_value && x <= y;
                let ev = Evaluator::new(&f.terms)
                    .with_int("x", x)
                    .with_int("y", y)
                    .with_bool("g", g_value)
                    .with_bool("boolarg_7", witness);
                assert!(ev.holds(authored) == (0 <= x));
                assert!(
                    ev.holds(atom),
                    "`p := body` must satisfy the definition at ({x}, {y}, {g_value})"
                );
            }
        }
    }
}

#[test]
fn accepts_an_equality_and_a_bound_that_agree_on_one_definiens() {
    // The two rules may BOTH speak about one symbol as long as they name the
    // SAME definiens. WITNESS: `d := x - y` satisfies `d = x - y`,
    // `d <= x - y` and `x - y <= d` alike.
    let mut f = fixture();
    let d = f.fresh(1);
    let lin = f.diff();
    let zero = f.int(0);
    let authored = f.terms.mk_le(zero, f.x);
    let mut proof = Proof::new();
    proof.add_assume(authored, None);
    push_eq(&mut proof, &mut f.terms, d, lin);
    push_bound(&mut proof, &mut f.terms, d, lin, false);
    push_bound(&mut proof, &mut f.terms, d, lin, true);
    let registry = FreshDefRegistry::collect(&proof, &f.terms, Some(&[authored]))
        .expect("one definiens named by both rules is still ONE definition");
    assert_eq!(registry.len(), 1);
}

#[test]
fn accepts_two_independent_equality_definitions() {
    // WITNESS: `d1 := x - y` and `d2 := 0`, chosen SIMULTANEOUSLY because
    // neither definiens mentions an introduced symbol.
    let mut f = fixture();
    let d1 = f.fresh(1);
    let d2 = f.fresh(2);
    let lin = f.diff();
    let zero = f.int(0);
    let authored = f.terms.mk_le(zero, f.x);
    let mut proof = Proof::new();
    proof.add_assume(authored, None);
    push_eq(&mut proof, &mut f.terms, d1, lin);
    push_eq(&mut proof, &mut f.terms, d2, zero);
    let registry = FreshDefRegistry::collect(&proof, &f.terms, Some(&[authored]))
        .expect("independent definitions admit a simultaneous assignment");
    assert_eq!(registry.len(), 2);
}

#[test]
fn accepts_a_repeated_identical_equality() {
    // Proof reconstruction can reach the same leaf twice. An identical repeat
    // is the same definition, not a second one.
    let mut f = fixture();
    let d = f.fresh(1);
    let lin = f.diff();
    let mut proof = Proof::new();
    push_eq(&mut proof, &mut f.terms, d, lin);
    push_eq(&mut proof, &mut f.terms, d, lin);
    FreshDefRegistry::collect(&proof, &f.terms, Some(&[]))
        .expect("an identical repeat is not a second definition");
}

#[test]
fn the_evaluator_disagrees_with_nothing_it_is_asked_about() {
    // The evaluator is the independent half of every negative above, so pin
    // that it actually computes what it claims — otherwise a negative could
    // "pass" because the evaluator returns the wrong thing.
    let mut f = fixture();
    let one = f.int(1);
    let sum = f.terms.mk_add(vec![f.x, one]);
    let atom = f.terms.mk_le(sum, f.y);
    let ev = Evaluator::new(&f.terms).with_int("x", 2).with_int("y", 3);
    assert!(ev.holds(atom), "3 <= 3");
    let ev = Evaluator::new(&f.terms).with_int("x", 3).with_int("y", 3);
    assert!(!ev.holds(atom), "4 <= 3 is false");
    let eq = f.terms.mk_eq(f.x, f.y);
    let ev = Evaluator::new(&f.terms).with_int("x", 4).with_int("y", 4);
    assert!(ev.holds(eq));
    let neg = f.terms.mk_neg(f.x);
    let big = f.terms.mk_int(BigInt::from(-7));
    let ev = Evaluator::new(&f.terms).with_int("x", 5).with_int("y", 0);
    assert_eq!(ev.eval(neg), Val::Int(-5));
    assert_eq!(ev.eval(big), Val::Int(-7));
}
