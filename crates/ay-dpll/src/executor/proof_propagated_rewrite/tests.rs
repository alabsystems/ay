// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Direct planner tests for the L3 replay extensions (#ppp-l3): and-headed
//! conjunct elimination and Bool `(= x true/false)` folds.
//!
//! Every GREEN case closes the planned chain into a full refutation and runs
//! the UNTOUCHED strict checker over it — the planner carries no authority of
//! its own, so the checker re-deriving every step is the actual assertion.
//! Every NEGATIVE case is guard-removal-proven: it forges exactly the record
//! shape a removed guard would admit and asserts the plan DECLINES.

use super::*;
use ay_core::kani_compat::DetHashMap;

struct Fixture {
    terms: TermStore,
    problem_set: HashSet<TermId>,
    problem_roots: Vec<TermId>,
    record_by_after: HashMap<TermId, (TermId, u32)>,
    entry_by_expr: HashMap<TermId, (TermId, TermId, u32)>,
}

impl Fixture {
    fn new(problem_roots: Vec<TermId>, terms: TermStore) -> Self {
        Self {
            terms,
            problem_set: problem_roots.iter().copied().collect(),
            problem_roots,
            record_by_after: HashMap::default(),
            entry_by_expr: HashMap::default(),
        }
    }

    fn record(&mut self, before: TermId, after: TermId, stamp: u32) {
        self.record_by_after.insert(after, (before, stamp));
    }

    fn entry(&mut self, expr: TermId, value: TermId, source: TermId, stamp: u32) {
        self.entry_by_expr.insert(expr, (value, source, stamp));
    }

    /// Plan `(cl target)`; on success return the chain and conclusion.
    fn plan(&mut self, target: TermId) -> Option<(Proof, ProofId)> {
        let mut cx = PlanCx::new(
            &self.problem_set,
            &self.problem_roots,
            &self.record_by_after,
            &self.entry_by_expr,
            &[],
            false,
        );
        let mut planner = PropagationChainPlanner {
            terms: &mut self.terms,
        };
        let conclusion = planner.plan_derive_clause(&mut cx, target)?;
        Some((cx.chain, conclusion))
    }

    /// Close a planned `(cl target)` chain into a refutation and run the
    /// untouched strict checker over the whole proof.
    fn assert_plan_is_strictly_checkable(&mut self, target: TermId) {
        let (mut chain, conclusion) = self
            .plan(target)
            .expect("planner must derive the recorded rewrite");
        let negated = self.terms.mk_not_raw(target);
        let counter = chain.add_assume(negated, None);
        chain.add_resolution(Vec::new(), target, conclusion, counter);
        let quality = ay_proof::check_proof_strict(&chain, &self.terms)
            .expect("every planned step must re-derive under the strict checker");
        assert_eq!(
            quality.trust_count, 0,
            "planned chains must be trust-free: {quality}"
        );
    }
}

fn bool_fun(terms: &mut TermStore, name: &str, arg: i64) -> TermId {
    let arg = terms.mk_int(num_bigint::BigInt::from(arg));
    terms.mk_app(Symbol::named(name), [arg], Sort::Bool)
}

// ---- and-headed conjunct elimination (#ppp-l3) ----

/// GREEN: `(and a b c)` with `b` folded to `true` collapses to `(and a c)`;
/// the bridge derives the surviving conjunction and the strict checker
/// re-derives every step.
#[test]
fn and_elimination_derives_surviving_conjunction() {
    let mut terms = TermStore::new();
    let a = bool_fun(&mut terms, "pa", 0);
    let b = bool_fun(&mut terms, "pb", 0);
    let c = bool_fun(&mut terms, "pc", 0);
    let true_term = terms.true_term();
    let before = terms.mk_app(Symbol::named("and"), [a, b, c], Sort::Bool);
    let b_def = terms.mk_app(Symbol::named("="), [b, true_term], Sort::Bool);
    let after = terms.mk_and(vec![a, true_term, c]);
    assert_ne!(after, before, "fixture must actually eliminate a conjunct");

    let mut fixture = Fixture::new(vec![before, b_def], terms);
    fixture.entry(b, true_term, b_def, 1);
    fixture.record(before, after, 1);
    fixture.assert_plan_is_strictly_checkable(after);
}

/// GREEN: all but one conjunct fold to `true`; the single-survivor collapse
/// resolves through the nested and-path.
#[test]
fn and_elimination_derives_single_survivor() {
    let mut terms = TermStore::new();
    let a = bool_fun(&mut terms, "pa", 0);
    let b = bool_fun(&mut terms, "pb", 0);
    let true_term = terms.true_term();
    let before = terms.mk_app(Symbol::named("and"), [a, b], Sort::Bool);
    let b_def = terms.mk_app(Symbol::named("="), [b, true_term], Sort::Bool);
    let after = terms.mk_and(vec![a, true_term]);
    assert_eq!(after, a, "two-conjunct fold must collapse to the survivor");

    let mut fixture = Fixture::new(vec![before, b_def], terms);
    fixture.entry(b, true_term, b_def, 1);
    fixture.record(before, after, 1);
    fixture.assert_plan_is_strictly_checkable(after);
}

/// NEGATIVE (guard: `folded == after`): a forged record claiming a conjunct
/// vanished WITHOUT a licensing entry folding it to `true` must decline.
#[test]
fn and_elimination_declines_unlicensed_elimination() {
    let mut terms = TermStore::new();
    let a = bool_fun(&mut terms, "pa", 0);
    let b = bool_fun(&mut terms, "pb", 0);
    let c = bool_fun(&mut terms, "pc", 0);
    let before = terms.mk_app(Symbol::named("and"), [a, b, c], Sort::Bool);
    let forged_after = terms.mk_and(vec![a, c]);

    let mut fixture = Fixture::new(vec![before], terms);
    // No entry for `b`: replay leaves every conjunct unchanged.
    fixture.record(before, forged_after, 1);
    assert!(
        fixture.plan(forged_after).is_none(),
        "an elimination no entry licenses must fail the plan"
    );
}

/// NEGATIVE (guard: changed conjuncts must fold to literal `true`): an entry
/// folding a conjunct to `false` must not license the surviving-and shape —
/// the canonical rebuild is `false`, not the forged survivor set.
#[test]
fn and_elimination_declines_false_folded_conjunct() {
    let mut terms = TermStore::new();
    let a = bool_fun(&mut terms, "pa", 0);
    let b = bool_fun(&mut terms, "pb", 0);
    let c = bool_fun(&mut terms, "pc", 0);
    let false_term = terms.false_term();
    let before = terms.mk_app(Symbol::named("and"), [a, b, c], Sort::Bool);
    let b_def = terms.mk_app(Symbol::named("="), [b, false_term], Sort::Bool);
    let forged_after = terms.mk_and(vec![a, c]);

    let mut fixture = Fixture::new(vec![before, b_def], terms);
    fixture.entry(b, false_term, b_def, 1);
    fixture.record(before, forged_after, 1);
    assert!(
        fixture.plan(forged_after).is_none(),
        "a false-folded conjunct eliminates the WHOLE conjunction, not one member"
    );
}

/// NEGATIVE (guard: survivors must lie on an and-path of `before`): a forged
/// `after` smuggling a fresh conjunct must decline even though the licensed
/// elimination itself is genuine.
#[test]
fn and_elimination_declines_smuggled_survivor() {
    let mut terms = TermStore::new();
    let a = bool_fun(&mut terms, "pa", 0);
    let b = bool_fun(&mut terms, "pb", 0);
    let c = bool_fun(&mut terms, "pc", 0);
    let smuggled = bool_fun(&mut terms, "pd", 0);
    let true_term = terms.true_term();
    let before = terms.mk_app(Symbol::named("and"), [a, b, c], Sort::Bool);
    let b_def = terms.mk_app(Symbol::named("="), [b, true_term], Sort::Bool);
    let forged_after = terms.mk_and(vec![a, c, smuggled]);

    let mut fixture = Fixture::new(vec![before, b_def], terms);
    fixture.entry(b, true_term, b_def, 1);
    fixture.record(before, forged_after, 1);
    assert!(
        fixture.plan(forged_after).is_none(),
        "a survivor outside the authored conjunction must fail the plan"
    );
}

// ---- Bool (= x true/false) folds (#ppp-l3) ----

/// GREEN: `(= r (pf 0))` with the entry `(pf 0) -> true` folds to `r`; the
/// equiv-chain bridge closes `(cl (= before r))` and the record bridge
/// concludes `(cl r)` — all strict-checkable.
#[test]
fn bool_eq_true_fold_derives_bare_atom() {
    let mut terms = TermStore::new();
    let r = bool_fun(&mut terms, "pr", 0);
    let pf = bool_fun(&mut terms, "pf", 0);
    let true_term = terms.true_term();
    let before = terms.mk_app(Symbol::named("="), [r, pf], Sort::Bool);
    let pf_def = terms.mk_app(Symbol::named("="), [pf, true_term], Sort::Bool);
    assert_eq!(
        terms.mk_eq(r, true_term),
        r,
        "fixture mirrors the mk_eq fold"
    );

    let mut fixture = Fixture::new(vec![before, pf_def], terms);
    fixture.entry(pf, true_term, pf_def, 1);
    fixture.record(before, r, 1);
    fixture.assert_plan_is_strictly_checkable(r);
}

/// GREEN: the `false` polarity — `(= (pf 0) r)` with `(pf 0) -> false` folds
/// to `(not r)` (constant side FIRST exercises the swapped orientation arms).
#[test]
fn bool_eq_false_fold_derives_negated_atom() {
    let mut terms = TermStore::new();
    let r = bool_fun(&mut terms, "pr", 0);
    let pf = bool_fun(&mut terms, "pf", 0);
    let false_term = terms.false_term();
    let before = terms.mk_app(Symbol::named("="), [pf, r], Sort::Bool);
    let pf_def = terms.mk_app(Symbol::named("="), [pf, false_term], Sort::Bool);
    let after = terms.mk_not(r);

    let mut fixture = Fixture::new(vec![before, pf_def], terms);
    fixture.entry(pf, false_term, pf_def, 1);
    fixture.record(before, after, 1);
    fixture.assert_plan_is_strictly_checkable(after);
}

/// GREEN: `x` itself a negation — `(= (not q) (pf 0))` with `(pf 0) -> false`
/// folds through the double-negation collapse to `q`.
#[test]
fn bool_eq_false_fold_collapses_double_negation() {
    let mut terms = TermStore::new();
    let q = bool_fun(&mut terms, "pq", 0);
    let not_q = terms.mk_not(q);
    let pf = bool_fun(&mut terms, "pf", 0);
    let false_term = terms.false_term();
    let before = terms.mk_app(Symbol::named("="), [not_q, pf], Sort::Bool);
    let pf_def = terms.mk_app(Symbol::named("="), [pf, false_term], Sort::Bool);
    assert_eq!(
        terms.mk_eq(not_q, false_term),
        q,
        "fixture mirrors the double-negation mk_eq fold"
    );

    let mut fixture = Fixture::new(vec![before, pf_def], terms);
    fixture.entry(pf, false_term, pf_def, 1);
    fixture.record(before, q, 1);
    fixture.assert_plan_is_strictly_checkable(q);
}

/// NEGATIVE (guard: `folded == expected` polarity check): a forged record
/// claiming the TRUE fold under a FALSE entry must decline.
#[test]
fn bool_eq_fold_declines_wrong_polarity() {
    let mut terms = TermStore::new();
    let r = bool_fun(&mut terms, "pr", 0);
    let pf = bool_fun(&mut terms, "pf", 0);
    let false_term = terms.false_term();
    let before = terms.mk_app(Symbol::named("="), [r, pf], Sort::Bool);
    let pf_def = terms.mk_app(Symbol::named("="), [pf, false_term], Sort::Bool);

    let mut fixture = Fixture::new(vec![before, pf_def], terms);
    fixture.entry(pf, false_term, pf_def, 1);
    // Forged: claims the positive fold `r` although the entry value is false.
    fixture.record(before, r, 1);
    assert!(
        fixture.plan(r).is_none(),
        "a polarity-flipped fold claim must fail the plan"
    );
}

/// NEGATIVE (guard: stamp ordering): an entry harvested AFTER the recorded
/// rewrite cannot license it.
#[test]
fn bool_eq_fold_declines_future_stamp_entry() {
    let mut terms = TermStore::new();
    let r = bool_fun(&mut terms, "pr", 0);
    let pf = bool_fun(&mut terms, "pf", 0);
    let true_term = terms.true_term();
    let before = terms.mk_app(Symbol::named("="), [r, pf], Sort::Bool);
    let pf_def = terms.mk_app(Symbol::named("="), [pf, true_term], Sort::Bool);

    let mut fixture = Fixture::new(vec![before, pf_def], terms);
    fixture.entry(pf, true_term, pf_def, 5);
    fixture.record(before, r, 1);
    assert!(
        fixture.plan(r).is_none(),
        "an entry from a later stamp must not license an earlier rewrite"
    );
}

/// NEGATIVE (guard: the licensing definition must itself be derivable): the
/// same green shape with the defining equality OUTSIDE the problem set must
/// decline — the chain would otherwise assume an unauthored premise.
#[test]
fn bool_eq_fold_declines_unauthored_definition() {
    let mut terms = TermStore::new();
    let r = bool_fun(&mut terms, "pr", 0);
    let pf = bool_fun(&mut terms, "pf", 0);
    let true_term = terms.true_term();
    let before = terms.mk_app(Symbol::named("="), [r, pf], Sort::Bool);
    let pf_def = terms.mk_app(Symbol::named("="), [pf, true_term], Sort::Bool);

    // `pf_def` is NOT a problem root.
    let mut fixture = Fixture::new(vec![before], terms);
    fixture.entry(pf, true_term, pf_def, 1);
    fixture.record(before, r, 1);
    assert!(
        fixture.plan(r).is_none(),
        "a licensing definition outside the authored problem must fail the plan"
    );
}

// Deterministic-map alias sanity: the fixture relies on kani_compat maps.
#[allow(dead_code)]
fn _det_map_alias(map: DetHashMap<TermId, TermId>) -> usize {
    map.len()
}
