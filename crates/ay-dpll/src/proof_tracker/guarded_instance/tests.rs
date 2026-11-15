// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A guarded-instance derivation is exactly what the strict checker
//! re-derives: `forall_inst` of the universal at the recorded values, closed
//! guards discharged by `evaluate`, and nothing else. Every forged instance
//! (a value outside the guard range, a term that is not an instance, an open,
//! signed or nested guard) is refused before a step is emitted, and a
//! tampered `forall_inst` is refused by the checker itself.

use super::*;
use num_bigint::BigInt;

const BINDER: &str = "guarded_instance_i";

struct Fixture {
    terms: TermStore,
    forall: TermId,
    constant: TermId,
}

fn bv(terms: &mut TermStore, value: u32) -> TermId {
    terms.mk_bitvec(BigInt::from(value), 8)
}

fn app_f(terms: &mut TermStore, arg: TermId) -> TermId {
    terms.mk_app(Symbol::named("guarded_instance_f"), [arg], Sort::bitvec(8))
}

fn raw_eq(terms: &mut TermStore, a: TermId, b: TermId) -> TermId {
    terms.mk_app(Symbol::named("="), [a, b], Sort::Bool)
}

/// `(forall ((i (_ BitVec 8))) (or (= (f i) c) (not G)))`, the internal
/// shape of `(=> G (= (f i) c))`, built raw; `guard` builds `G` from `i`.
fn with_guard(guard: impl Fn(&mut TermStore, TermId) -> TermId) -> Fixture {
    let mut terms = TermStore::new();
    let i = terms.mk_var(BINDER, Sort::bitvec(8));
    let constant = terms.mk_var("guarded_instance_c", Sort::bitvec(8));
    let head = app_f(&mut terms, i);
    let equality = raw_eq(&mut terms, head, constant);
    let atom = guard(&mut terms, i);
    let not_guard = terms.mk_not_raw(atom);
    let body = terms.mk_app(Symbol::named("or"), [equality, not_guard], Sort::Bool);
    let forall = terms.mk_forall(vec![(BINDER.to_string(), Sort::bitvec(8))], body);
    Fixture {
        terms,
        forall,
        constant,
    }
}

/// The guard `(op i #x09)`.
fn guarded(op: &'static str) -> Fixture {
    with_guard(move |terms, i| {
        let bound = bv(terms, 9);
        terms.mk_app(Symbol::named(op), [i, bound], Sort::Bool)
    })
}

impl Fixture {
    /// `(= (f value) c)`, or its swap.
    fn equality_at(&mut self, value: u32, swapped: bool) -> (TermId, TermId) {
        let value = bv(&mut self.terms, value);
        let head = app_f(&mut self.terms, value);
        let equality = if swapped {
            raw_eq(&mut self.terms, self.constant, head)
        } else {
            raw_eq(&mut self.terms, head, self.constant)
        };
        (value, equality)
    }

    fn plan(&mut self, value: TermId, target: TermId) -> Option<GuardedInstance> {
        GuardedInstance::plan(&mut self.terms, self.forall, &[value], target)
    }
}

/// Close the derived unit `derived` of `target` against an assumed `(not
/// target)` and strict-check the whole refutation over `{forall, (not
/// target)}`.
fn closes_strictly(
    fixture: &mut Fixture,
    mut tracker: ProofTracker,
    target: TermId,
    derived: ProofId,
) -> Proof {
    let not_target = fixture.terms.mk_not_raw(target);
    let refuted = tracker
        .add_assumption(not_target, None)
        .expect("tracking enabled");
    tracker
        .proof
        .add_resolution(Vec::new(), target, derived, refuted);
    let proof = tracker.take_proof();
    let quality = ay_proof::check_proof_strict_with_context(
        &proof,
        &fixture.terms,
        None,
        None,
        Some(&[fixture.forall, not_target]),
    )
    .expect("a guarded-instance derivation must pass the strict checker");
    assert!(quality.is_complete());
    assert_eq!(quality.trust_count, 0);
    proof
}

fn enabled() -> ProofTracker {
    let mut tracker = ProofTracker::new();
    tracker.enable();
    tracker
}

fn rule_count(proof: &Proof, wanted: &AletheRule) -> usize {
    proof
        .steps
        .iter()
        .filter(|step| matches!(step, ProofStep::Step { rule, .. } if rule == wanted))
        .count()
}

#[test]
fn closed_guard_instance_is_derived_and_strict_checked() {
    let mut fixture = guarded("bvult");
    let (four, target) = fixture.equality_at(4, false);
    let plan = fixture.plan(four, target).expect("a closed guard plans");
    assert_eq!(plan.target, target);
    let mut tracker = enabled();
    let derived = tracker
        .add_forall_guarded_instance_assertion(&mut fixture.terms, &plan)
        .expect("the planned instance derives");
    assert_eq!(
        tracker.add_assumption(target, None),
        Some(derived),
        "assuming the asserted instance must reuse its derivation"
    );
    let proof = closes_strictly(&mut fixture, tracker, target, derived);
    assert_eq!(rule_count(&proof, &AletheRule::ForallInst), 1);
    assert_eq!(rule_count(&proof, &AletheRule::Evaluate), 1);
    assert!(proof.steps.iter().any(|step| matches!(
        step,
        ProofStep::Step { rule: AletheRule::ForallInst, args, .. } if args == &[four]
    )));
}

#[test]
fn swapped_equality_is_derived_through_symm() {
    let mut fixture = guarded("bvule");
    let (four, target) = fixture.equality_at(4, true);
    let plan = fixture
        .plan(four, target)
        .expect("a swapped disjunct plans");
    let mut tracker = enabled();
    let derived = tracker
        .add_forall_guarded_instance_assertion(&mut fixture.terms, &plan)
        .expect("the planned instance derives");
    let proof = closes_strictly(&mut fixture, tracker, target, derived);
    assert_eq!(rule_count(&proof, &AletheRule::Symm), 1);
}

#[test]
fn unguarded_instance_goes_through_the_ematching_entry() {
    let mut terms = TermStore::new();
    let i = terms.mk_var(BINDER, Sort::bitvec(8));
    let constant = terms.mk_var("guarded_instance_c", Sort::bitvec(8));
    let head = app_f(&mut terms, i);
    let body = raw_eq(&mut terms, head, constant);
    let forall = terms.mk_forall(vec![(BINDER.to_string(), Sort::bitvec(8))], body);
    let mut fixture = Fixture {
        terms,
        forall,
        constant,
    };
    let (seven, target) = fixture.equality_at(7, true);
    let plan = fixture
        .plan(seven, target)
        .expect("the swapped instance plans");
    let mut tracker = enabled();
    let derived = tracker
        .add_forall_guarded_instance_assertion(&mut fixture.terms, &plan)
        .expect("the planned instance derives");
    let proof = closes_strictly(&mut fixture, tracker, target, derived);
    assert_eq!(rule_count(&proof, &AletheRule::ForallInst), 1);
    assert_eq!(rule_count(&proof, &AletheRule::Evaluate), 0);
}

#[test]
fn forged_instances_are_refused_before_any_step() {
    // Outside the guard range: `(bvult #x0c #x09)` is false, so the instance
    // at #x0c says nothing about `(f #x0c)`.
    let mut fixture = guarded("bvult");
    let (twelve, outside) = fixture.equality_at(12, false);
    assert!(fixture.plan(twelve, outside).is_none());
    // Not the instance at the recorded value.
    let (four, _) = fixture.equality_at(4, false);
    let (_, other) = fixture.equality_at(5, false);
    assert!(fixture.plan(four, other).is_none());
    // Wrong arity and wrong sort.
    let (_, target) = fixture.equality_at(4, false);
    assert!(GuardedInstance::plan(&mut fixture.terms, fixture.forall, &[], target).is_none());
    let int_four = fixture.terms.mk_int(BigInt::from(4));
    assert!(fixture.plan(int_four, target).is_none());
    // A signed guard (pinned carcara misevaluates signed operands).
    let mut signed = guarded("bvslt");
    let (signed_four, signed_target) = signed.equality_at(4, false);
    assert!(signed.plan(signed_four, signed_target).is_none());

    // A plan forged past `plan` (the equality claimed to be the whole
    // instance) is still refused: the unguarded entry re-derives the
    // substitution before it emits a step.
    let forged = GuardedInstance {
        quantified: fixture.forall,
        values: vec![four],
        instance: target,
        target,
        kept: target,
        guards: Vec::new(),
        conclusion: ConclusionBridge::Exact,
    };
    let mut tracker = enabled();
    assert!(tracker
        .add_forall_guarded_instance_assertion(&mut fixture.terms, &forged)
        .is_none());
    assert_eq!(tracker.num_steps(), 0);
}

#[test]
fn open_and_nested_guards_are_refused() {
    let open = with_guard(|terms, i| {
        let symbolic = terms.mk_var("guarded_instance_k", Sort::bitvec(8));
        terms.mk_app(Symbol::named("bvult"), [i, symbolic], Sort::Bool)
    });
    let nested = with_guard(|terms, i| {
        let one = bv(terms, 1);
        let top = bv(terms, 0xfe);
        let difference = terms.mk_app(Symbol::named("bvsub"), [i, one], Sort::bitvec(8));
        raw_eq(terms, difference, top)
    });
    for mut fixture in [open, nested] {
        let (value, target) = fixture.equality_at(0xff, false);
        assert!(
            fixture.plan(value, target).is_none(),
            "a guard that is not a comparison over literals must not be evaluated"
        );
    }
}

#[test]
fn tampered_forall_inst_is_refused_by_the_strict_checker() {
    let mut fixture = guarded("bvult");
    let (four, target) = fixture.equality_at(4, false);
    let plan = fixture.plan(four, target).expect("a closed guard plans");
    let mut tracker = enabled();
    let derived = tracker
        .add_forall_guarded_instance_assertion(&mut fixture.terms, &plan)
        .expect("the planned instance derives");
    let not_target = fixture.terms.mk_not_raw(target);
    let refuted = tracker.add_assumption(not_target, None).expect("enabled");
    tracker
        .proof
        .add_resolution(Vec::new(), target, derived, refuted);
    let mut proof = tracker.take_proof();
    let five = bv(&mut fixture.terms, 5);
    for step in &mut proof.steps {
        if let ProofStep::Step {
            rule: AletheRule::ForallInst,
            args,
            ..
        } = step
        {
            *args = vec![five];
        }
    }
    assert!(
        ay_proof::check_proof_strict_with_context(
            &proof,
            &fixture.terms,
            None,
            None,
            Some(&[fixture.forall, not_target]),
        )
        .is_err(),
        "a forall_inst whose conclusion is not the instance at its arguments must be refused"
    );
}

#[test]
fn conjunction_needs_every_conjunct_derived() {
    let mut fixture = guarded("bvult");
    let (three, at_three) = fixture.equality_at(3, false);
    let (four, at_four) = fixture.equality_at(4, false);
    let (_, at_five) = fixture.equality_at(5, false);
    let both = fixture
        .terms
        .mk_app(Symbol::named("and"), [at_three, at_four], Sort::Bool);
    let with_underived =
        fixture
            .terms
            .mk_app(Symbol::named("and"), [at_three, at_five], Sort::Bool);
    let mut tracker = enabled();
    for (value, target) in [(three, at_three), (four, at_four)] {
        let plan = fixture.plan(value, target).expect("plans");
        tracker
            .add_forall_guarded_instance_assertion(&mut fixture.terms, &plan)
            .expect("derives");
    }
    let before = tracker.num_steps();
    assert!(tracker
        .add_conjunction_of_derived_units(&mut fixture.terms, with_underived)
        .is_none());
    assert_eq!(
        tracker.num_steps(),
        before,
        "a declined conjunction emits nothing"
    );
    let derived = tracker
        .add_conjunction_of_derived_units(&mut fixture.terms, both)
        .expect("both conjuncts are derived");
    assert_eq!(tracker.add_assumption(both, None), Some(derived));
    let proof = closes_strictly(&mut fixture, tracker, both, derived);
    assert_eq!(rule_count(&proof, &AletheRule::AndNeg), 1);
}

#[test]
fn disabled_tracking_derives_nothing() {
    let mut fixture = guarded("bvult");
    let (four, target) = fixture.equality_at(4, false);
    let plan = fixture.plan(four, target).expect("plans");
    let mut tracker = ProofTracker::new();
    assert!(tracker
        .add_forall_guarded_instance_assertion(&mut fixture.terms, &plan)
        .is_none());
    assert_eq!(tracker.num_steps(), 0);
}

#[test]
fn closed_integer_box_derives_folded_linear_bound() {
    let mut terms = TermStore::new();
    let x = terms.mk_var(BINDER, Sort::Int);
    let a = terms.mk_var("guarded_instance_a", Sort::Int);
    let zero = terms.mk_int(0.into());
    let endpoint = terms.mk_int(100.into());
    let coefficient = terms.mk_int((-5).into());
    let offset = terms.mk_int(4.into());
    let lo = terms.mk_app(Symbol::named("<="), [zero, x], Sort::Bool);
    let hi = terms.mk_app(Symbol::named("<="), [x, endpoint], Sort::Bool);
    let guard = terms.mk_app(Symbol::named("and"), [lo, hi], Sort::Bool);
    let product = terms.mk_app(Symbol::named("*"), [coefficient, x], Sort::Int);
    let sum = terms.mk_app(Symbol::named("+"), [product, offset], Sort::Int);
    let bound = terms.mk_app(Symbol::named("<="), [a, sum], Sort::Bool);
    let not_guard = terms.mk_not_raw(guard);
    let body = terms.mk_app(Symbol::named("or"), [bound, not_guard], Sort::Bool);
    let forall = terms.mk_forall(vec![(BINDER.to_string(), Sort::Int)], body);
    let folded = terms.mk_int((-496).into());
    let target = terms.mk_app(Symbol::named("<="), [a, folded], Sort::Bool);
    let too_strong = terms.mk_int((-497).into());
    let invalid = terms.mk_app(Symbol::named("<="), [a, too_strong], Sort::Bool);
    let outside = terms.mk_int(101.into());
    assert!(GuardedInstance::plan(&mut terms, forall, &[endpoint], invalid).is_none());
    assert!(GuardedInstance::plan(&mut terms, forall, &[outside], target).is_none());
    let plan = GuardedInstance::plan(&mut terms, forall, &[endpoint], target)
        .expect("closed box and arithmetic implication derive the endpoint bound");
    let mut tracker = enabled();
    let derived = tracker
        .add_forall_guarded_instance_assertion(&mut terms, &plan)
        .expect("tracked instance derives");
    let mut fixture = Fixture {
        terms,
        forall,
        constant: a,
    };
    let proof = closes_strictly(&mut fixture, tracker, target, derived);
    assert_eq!(rule_count(&proof, &AletheRule::ForallInst), 1);
}
