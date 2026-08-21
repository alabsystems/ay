// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Soundness tests for the fresh-definition provenance registry.
//!
//! Organized as the soundness argument is:
//!
//! * `accepts_*` pin the shapes the rule is FOR, each with the witness
//!   assignment (`d := lin`) that makes the extension conservative;
//! * `rejects_*` are adversarial negatives, and EVERY ONE names the concrete
//!   satisfying assignment of a problem that the "extension" would refute — so
//!   a future loosening cannot be argued to be harmless;
//! * the `sweeps` child module enumerates a bounded configuration box
//!   exhaustively and re-evaluates every ACCEPT at every point of an integer
//!   box using a plain-`i64` evaluator that shares no code with the registry;
//! * `GUARD_MUTATION_LEDGER` records, per guard, the test that fails when the
//!   guard is deleted.

use ay_core::{AletheRule, Proof, ProofStep, Sort, TermId, TermStore};
use num_bigint::BigInt;

use super::fresh_def::FreshDefRegistry;
use super::ProofCheckError;

#[path = "fresh_def_strict_tests.rs"]
mod strict;
#[path = "fresh_def_sweep_tests.rs"]
mod sweeps;

/// Which whole-proof guard in `FreshDefRegistry` each adversarial test defends.
/// Every entry was checked by DELETING the guard, running the named test,
/// observing the failure, and restoring the guard.
const GUARD_MUTATION_LEDGER: &[(&str, &str)] = &[
    (
        "collect_bindings: a second, DIFFERENT definiens for one name",
        "rejects_two_different_definitions_of_the_same_symbol",
    ),
    (
        "validate_bound: the step's definiens must match the recorded one",
        "rejects_a_bound_rebound_to_a_different_definiens",
    ),
    (
        "verify_fresh_and_independent: `definiens_names` membership",
        "rejects_a_symbol_that_occurs_inside_its_own_definiens",
    ),
    (
        "verify_fresh_and_independent: `constrained` from `problem_assertions`",
        "rejects_a_symbol_the_problem_also_constrains",
    ),
    (
        "verify_fresh_and_independent: `constrained` from the proof's `assume` leaves",
        "rejects_a_symbol_an_assume_also_constrains",
    ),
    (
        "validate_bound: the step's name must have a vetted binding",
        "rejects_a_bound_with_no_registry_binding",
    ),
    (
        "validate_step_with_datatypes: strict mode requires a registry at all",
        "strict_mode_rejects_a_fresh_def_bound_without_a_registry",
    ),
];

#[test]
fn guard_mutation_ledger_names_a_test_per_guard() {
    assert_eq!(
        GUARD_MUTATION_LEDGER.len(),
        7,
        "every whole-proof guard must name the test that defends it",
    );
    for (guard, test) in GUARD_MUTATION_LEDGER {
        assert!(!guard.is_empty() && !test.is_empty());
    }
}

pub(super) struct Fixture {
    pub(super) terms: TermStore,
    pub(super) x: TermId,
    pub(super) y: TermId,
}

pub(super) fn fixture() -> Fixture {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x".to_string(), Sort::Int);
    let y = terms.mk_var("y".to_string(), Sort::Int);
    Fixture { terms, x, y }
}

impl Fixture {
    pub(super) fn fresh(&mut self, n: u32) -> TermId {
        self.terms.mk_var(format!("__ay_eqdv!{n}"), Sort::Int)
    }

    pub(super) fn int(&mut self, value: i64) -> TermId {
        self.terms.mk_int(BigInt::from(value))
    }

    /// `x - y`, the row `EqDiffVar` builds for `(= x y)`.
    pub(super) fn diff(&mut self) -> TermId {
        let neg_y = self.terms.mk_neg(self.y);
        self.terms.mk_add(vec![self.x, neg_y])
    }
}

/// Append `(cl (<= d lin))` (or `(<= lin d)` when `lower`).
pub(super) fn push_bound(
    proof: &mut Proof,
    terms: &mut TermStore,
    d: TermId,
    lin: TermId,
    lower: bool,
) {
    let atom = if lower {
        terms.mk_le(lin, d)
    } else {
        terms.mk_le(d, lin)
    };
    proof.add_step(ProofStep::Step {
        rule: AletheRule::FreshDefBound,
        clause: vec![atom],
        premises: Vec::new(),
        args: vec![d],
    });
}

pub(super) fn reason(error: &ProofCheckError) -> String {
    match error {
        ProofCheckError::InvalidTheoryLemma { reason, .. } => reason.clone(),
        other => panic!("expected InvalidTheoryLemma, got {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// Accepts
// ---------------------------------------------------------------------------

#[test]
fn accepts_the_complete_definitional_pair() {
    // WITNESS: any model of the problem extends by `d := x - y`, which
    // satisfies BOTH `d <= x - y` and `x - y <= d`.
    let mut f = fixture();
    let d = f.fresh(1);
    let lin = f.diff();
    let mut proof = Proof::new();
    let zero = f.int(0);
    let authored = f.terms.mk_le(zero, f.x);
    proof.add_assume(authored, None);
    push_bound(&mut proof, &mut f.terms, d, lin, false);
    push_bound(&mut proof, &mut f.terms, d, lin, true);
    let registry = FreshDefRegistry::collect(&proof, &f.terms, Some(&[authored]))
        .expect("a complete definitional pair over a fresh symbol is conservative");
    assert_eq!(registry.len(), 1);
}

#[test]
fn accepts_a_single_direction() {
    // The refutation used only the upper bound. WITNESS: `d := x - y` still
    // satisfies `d <= x - y`, so the one-sided extension is conservative too.
    // Requiring both directions would be a completeness restriction with no
    // soundness content — and on `dillig12_m` it would decline 102 of 130
    // (proof, symbol) groups.
    let mut f = fixture();
    let d = f.fresh(1);
    let lin = f.diff();
    let mut proof = Proof::new();
    let zero = f.int(0);
    let authored = f.terms.mk_le(zero, f.x);
    proof.add_assume(authored, None);
    push_bound(&mut proof, &mut f.terms, d, lin, false);
    let registry = FreshDefRegistry::collect(&proof, &f.terms, Some(&[authored]))
        .expect("one bound of a definition over a fresh symbol is still conservative");
    assert_eq!(registry.len(), 1);
}

#[test]
fn accepts_two_independent_symbols() {
    // WITNESS: `d1 := x - y`, `d2 := 0`, chosen simultaneously because neither
    // definiens mentions an introduced symbol.
    let mut f = fixture();
    let d1 = f.fresh(1);
    let d2 = f.fresh(2);
    let lin = f.diff();
    let zero = f.int(0);
    let mut proof = Proof::new();
    let authored = f.terms.mk_le(zero, f.x);
    proof.add_assume(authored, None);
    push_bound(&mut proof, &mut f.terms, d1, lin, false);
    push_bound(&mut proof, &mut f.terms, d1, lin, true);
    push_bound(&mut proof, &mut f.terms, d2, zero, false);
    push_bound(&mut proof, &mut f.terms, d2, zero, true);
    let registry = FreshDefRegistry::collect(&proof, &f.terms, Some(&[authored]))
        .expect("independent definitions admit a simultaneous assignment");
    assert_eq!(registry.len(), 2);
}

#[test]
fn accepts_a_repeated_identical_bound() {
    // The same leaf can be reached twice by proof reconstruction. Identical
    // repeats are not a second definition.
    let mut f = fixture();
    let d = f.fresh(1);
    let lin = f.diff();
    let mut proof = Proof::new();
    push_bound(&mut proof, &mut f.terms, d, lin, false);
    push_bound(&mut proof, &mut f.terms, d, lin, false);
    FreshDefRegistry::collect(&proof, &f.terms, Some(&[]))
        .expect("an identical repeat is the same definition, not a second one");
}

#[test]
fn accepts_a_symbol_absent_from_the_assumes_but_present_in_no_problem() {
    // The registry is built with `None` on the proof-surgery revert gate. That
    // must NOT fail closed: turning a rescuable `trust` rejection into a hard
    // `InvalidTheoryLemma` one is strictly worse than leaving it alone. The
    // freshness the argument needs — no introduced symbol in any `assume` — is
    // still decided, from the proof itself.
    let mut f = fixture();
    let d = f.fresh(1);
    let lin = f.diff();
    let mut proof = Proof::new();
    let zero = f.int(0);
    let authored = f.terms.mk_le(zero, f.x);
    proof.add_assume(authored, None);
    push_bound(&mut proof, &mut f.terms, d, lin, false);
    FreshDefRegistry::collect(&proof, &f.terms, None)
        .expect("`None` problem assertions still decide freshness against the assumes");
}

// ---------------------------------------------------------------------------
// Adversarial negatives — each names a satisfying assignment of a problem the
// "extension" would refute.
// ---------------------------------------------------------------------------

#[test]
fn rejects_a_symbol_the_problem_also_constrains() {
    // REQUIRED NEGATIVE: `d` NOT fresh, occurring in the AUTHORED problem.
    //
    // FALSIFYING ASSIGNMENT. Problem `A = { d = 5 }`, satisfied by `d = 5`.
    // The "definition" `d := 0` adds `d <= 0` and `0 <= d`, so `A ∪ P` forces
    // `5 = d = 0` and is UNSAT. A refutation of `A ∪ P` would therefore
    // publish UNSAT for a SATISFIABLE problem.
    let mut f = fixture();
    let d = f.fresh(1);
    let five = f.int(5);
    let zero = f.int(0);
    let authored = f.terms.mk_eq(d, five);
    let mut proof = Proof::new();
    push_bound(&mut proof, &mut f.terms, d, zero, false);
    push_bound(&mut proof, &mut f.terms, d, zero, true);
    let error = FreshDefRegistry::collect(&proof, &f.terms, Some(&[authored]))
        .expect_err("a symbol the problem constrains is not fresh");
    assert!(reason(&error).contains("NOT fresh"), "{error:?}");
}

#[test]
fn rejects_a_symbol_an_assume_also_constrains() {
    // The same defect reached through the proof rather than the problem: the
    // caller may pass `None`, so the proof's own `assume` leaves have to be a
    // freshness source in their own right.
    //
    // FALSIFYING ASSIGNMENT: identical to the test above with `d = 5` assumed
    // instead of asserted — satisfied at `d = 5`, refuted by `d := 0`.
    let mut f = fixture();
    let d = f.fresh(1);
    let five = f.int(5);
    let zero = f.int(0);
    let assumed = f.terms.mk_eq(d, five);
    let mut proof = Proof::new();
    proof.add_assume(assumed, None);
    push_bound(&mut proof, &mut f.terms, d, zero, false);
    push_bound(&mut proof, &mut f.terms, d, zero, true);
    let error = FreshDefRegistry::collect(&proof, &f.terms, None)
        .expect_err("a symbol an assume constrains is not fresh");
    assert!(reason(&error).contains("NOT fresh"), "{error:?}");
}

#[test]
fn rejects_two_different_definitions_of_the_same_symbol() {
    // REQUIRED NEGATIVE: two different pairs defining the same `d`.
    //
    // FALSIFYING ASSIGNMENT. Problem `A = { 0 <= x }`, satisfied at `x = 0`.
    // Defining `d := x` AND `d := x + 1` forces `x = d = x + 1`, so `A ∪ P` is
    // UNSAT: no value of `d` satisfies both pairs at any `x`.
    let mut f = fixture();
    let d = f.fresh(1);
    let one = f.int(1);
    let x_plus_one = f.terms.mk_add(vec![f.x, one]);
    let zero = f.int(0);
    let authored = f.terms.mk_le(zero, f.x);
    let mut proof = Proof::new();
    proof.add_assume(authored, None);
    push_bound(&mut proof, &mut f.terms, d, f.x, false);
    push_bound(&mut proof, &mut f.terms, d, f.x, true);
    push_bound(&mut proof, &mut f.terms, d, x_plus_one, false);
    push_bound(&mut proof, &mut f.terms, d, x_plus_one, true);
    let error = FreshDefRegistry::collect(&proof, &f.terms, Some(&[authored]))
        .expect_err("two definientia for one symbol equate them");
    assert!(reason(&error).contains("SECOND definiens"), "{error:?}");
}

#[test]
fn rejects_an_incomplete_pair_whose_two_directions_disagree() {
    // REQUIRED NEGATIVE: "only one direction of the pair present" — in the
    // form where that is actually unsound. One direction ALONE is
    // conservative (`accepts_a_single_direction` proves it, with its witness);
    // what is not conservative is an upper bound by one term and a lower bound
    // by a DIFFERENT one, i.e. a pair that is not a definition at all.
    //
    // FALSIFYING ASSIGNMENT. Problem `A = { 0 <= x }`, satisfied at `x = 0`.
    // The bounds `d <= 0` and `1 <= d` give `1 <= d <= 0`, which is UNSAT for
    // every `x` — so the empty clause follows from NOTHING the problem said.
    let mut f = fixture();
    let d = f.fresh(1);
    let zero = f.int(0);
    let one = f.int(1);
    let authored = f.terms.mk_le(zero, f.x);
    let mut proof = Proof::new();
    proof.add_assume(authored, None);
    push_bound(&mut proof, &mut f.terms, d, zero, false);
    push_bound(&mut proof, &mut f.terms, d, one, true);
    let error = FreshDefRegistry::collect(&proof, &f.terms, Some(&[authored]))
        .expect_err("an upper bound by one term and a lower bound by another is not a definition");
    assert!(reason(&error).contains("SECOND definiens"), "{error:?}");
}

#[test]
fn rejects_a_symbol_that_occurs_inside_its_own_definiens() {
    // REQUIRED NEGATIVE: `d` occurring inside `lin`.
    //
    // FALSIFYING ASSIGNMENT. Problem `A = { 0 <= x }`, satisfied at `x = 0`.
    // The "definition" `d := d + 1` adds `d <= d + 1` and `d + 1 <= d`; the
    // second is false for EVERY integer `d`, so `A ∪ P` is UNSAT and a
    // refutation of it says nothing about `A`.
    let mut f = fixture();
    let d = f.fresh(1);
    let one = f.int(1);
    let d_plus_one = f.terms.mk_add(vec![d, one]);
    let zero = f.int(0);
    let authored = f.terms.mk_le(zero, f.x);
    let mut proof = Proof::new();
    proof.add_assume(authored, None);
    push_bound(&mut proof, &mut f.terms, d, d_plus_one, false);
    push_bound(&mut proof, &mut f.terms, d, d_plus_one, true);
    let error = FreshDefRegistry::collect(&proof, &f.terms, Some(&[authored]))
        .expect_err("a self-referential definition is not a definition");
    assert!(reason(&error).contains("inside a definiens"), "{error:?}");
}

#[test]
fn rejects_a_two_symbol_definition_cycle() {
    // Checking only DIRECT self-reference misses this. The registry's guard is
    // "no introduced symbol occurs in ANY definiens", which is strictly
    // stronger than acyclicity and needs no graph algorithm.
    //
    // FALSIFYING ASSIGNMENT. Problem `A = { 0 <= x }`, satisfied at `x = 0`.
    // `d1 := d2 + 1` and `d2 := d1 + 1` force `d1 = d2 + 1 = d1 + 2`, UNSAT
    // for every `x`.
    let mut f = fixture();
    let d1 = f.fresh(1);
    let d2 = f.fresh(2);
    let one = f.int(1);
    let d2_plus_one = f.terms.mk_add(vec![d2, one]);
    let d1_plus_one = f.terms.mk_add(vec![d1, one]);
    let zero = f.int(0);
    let authored = f.terms.mk_le(zero, f.x);
    let mut proof = Proof::new();
    proof.add_assume(authored, None);
    push_bound(&mut proof, &mut f.terms, d1, d2_plus_one, false);
    push_bound(&mut proof, &mut f.terms, d1, d2_plus_one, true);
    push_bound(&mut proof, &mut f.terms, d2, d1_plus_one, false);
    push_bound(&mut proof, &mut f.terms, d2, d1_plus_one, true);
    let error = FreshDefRegistry::collect(&proof, &f.terms, Some(&[authored]))
        .expect_err("mutually recursive definitions need not admit any assignment");
    assert!(reason(&error).contains("inside a definiens"), "{error:?}");
}

#[test]
fn rejects_two_same_named_symbols_at_different_sorts() {
    // `mk_var` keys on (name, sort), so one NAME can carry two `TermId`s. The
    // registry keys on the name — the freshness question is about the symbol —
    // so it must refuse to bind one name to two different terms.
    //
    // FALSIFYING ASSIGNMENT. Whatever the sorts, a checker that bound the name
    // once and then validated the other `TermId` against it would be checking
    // a definition it never verified; the reachable defect is the same as
    // `rejects_two_different_definitions_of_the_same_symbol`.
    let mut f = fixture();
    let d_int = f.fresh(1);
    let d_real = f.terms.mk_var("__ay_eqdv!1".to_string(), Sort::Real);
    let r = f.terms.mk_var("r".to_string(), Sort::Real);
    let s = f.terms.mk_var("s".to_string(), Sort::Real);
    let real_lin = f.terms.mk_add(vec![r, s]);
    let lin = f.diff();
    let mut proof = Proof::new();
    push_bound(&mut proof, &mut f.terms, d_int, lin, false);
    push_bound(&mut proof, &mut f.terms, d_real, real_lin, false);
    let error = FreshDefRegistry::collect(&proof, &f.terms, Some(&[]))
        .expect_err("one NAME may carry only one definition");
    assert!(reason(&error).contains("SECOND definiens"), "{error:?}");
}

#[test]
fn rejects_a_bound_with_no_registry_binding() {
    // `validate_bound` must consult the registry rather than re-deciding the
    // shape locally: a step the whole-proof pass never saw has had none of the
    // conditions checked.
    let mut f = fixture();
    let d = f.fresh(1);
    let lin = f.diff();
    let empty = FreshDefRegistry::default();
    let atom = f.terms.mk_le(d, lin);
    let error = empty
        .validate_bound(&f.terms, ay_core::ProofId(0), &[atom], &[], &[d])
        .expect_err("an unbound symbol has had no condition checked");
    assert!(
        reason(&error).contains("no vetted whole-proof binding"),
        "{error:?}"
    );
}

#[test]
fn rejects_a_bound_rebound_to_a_different_definiens() {
    // Belt-and-braces: even with a registry in hand, the per-step check must
    // confirm the definiens, not just the name.
    let mut f = fixture();
    let d = f.fresh(1);
    let lin = f.diff();
    let zero = f.int(0);
    let mut proof = Proof::new();
    push_bound(&mut proof, &mut f.terms, d, lin, false);
    let registry =
        FreshDefRegistry::collect(&proof, &f.terms, Some(&[])).expect("the single bound is fine");
    let other = f.terms.mk_le(d, zero);
    let error = registry
        .validate_bound(&f.terms, ay_core::ProofId(0), &[other], &[], &[d])
        .expect_err("the recorded definiens is `x - y`, not `0`");
    assert!(reason(&error).contains("different definiens"), "{error:?}");
}
