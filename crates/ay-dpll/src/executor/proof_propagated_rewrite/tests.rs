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

    /// Plan `(cl target)` with `target` declared a literal Boolean constant,
    /// the way `plan_propagation_candidates` does for a constant candidate.
    fn plan_with_constant_target(&mut self, target: TermId) -> Option<(Proof, ProofId)> {
        let mut cx = PlanCx::new(
            &self.problem_set,
            &self.problem_roots,
            &self.record_by_after,
            &self.entry_by_expr,
            &[],
            false,
        )
        .with_constant_target(target);
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

// ---- unit-propagation disjunct deletion (#4751) ----

/// GREEN: the shape the top-level unit-propagation pass produces — `(or a b
/// c)` with the unit `(not b)` on the stack deletes `b` and stores
/// `mk_or([a, c])`. The licensing source is the bare unit, NOT a defining
/// equality, so the plan must BUILD `(= b false)` and then re-form the
/// surviving disjunction. The strict checker re-derives every step.
#[test]
fn unit_prop_deletion_derives_reformed_disjunction() {
    let mut terms = TermStore::new();
    let a = bool_fun(&mut terms, "pa", 0);
    let b = bool_fun(&mut terms, "pb", 0);
    let c = bool_fun(&mut terms, "pc", 0);
    let false_term = terms.false_term();
    let not_b = terms.mk_not_raw(b);
    let before = terms.mk_app(Symbol::named("or"), [a, b, c], Sort::Bool);
    let after = terms.mk_or(vec![a, c]);
    assert_ne!(after, before, "fixture must actually delete a disjunct");

    let mut fixture = Fixture::new(vec![before, not_b], terms);
    fixture.entry(b, false_term, not_b, 1);
    fixture.record(before, after, 1);
    fixture.assert_plan_is_strictly_checkable(after);
}

/// GREEN: the opposite polarity — the deleted disjunct is `(not b)` and the
/// licensing unit is the bare atom `b`, so the resolution pivots on `b`.
#[test]
fn unit_prop_deletion_derives_negated_disjunct_case() {
    let mut terms = TermStore::new();
    let a = bool_fun(&mut terms, "pa", 0);
    let b = bool_fun(&mut terms, "pb", 0);
    let c = bool_fun(&mut terms, "pc", 0);
    let false_term = terms.false_term();
    let not_b = terms.mk_not_raw(b);
    let before = terms.mk_app(Symbol::named("or"), [a, not_b, c], Sort::Bool);
    let after = terms.mk_or(vec![a, c]);

    let mut fixture = Fixture::new(vec![before, b], terms);
    fixture.entry(not_b, false_term, b, 1);
    fixture.record(before, after, 1);
    fixture.assert_plan_is_strictly_checkable(after);
}

/// GREEN: the collapse case — every disjunct but one is deleted, so `after`
/// IS the survivor and the existing single-survivor path concludes it.
#[test]
fn unit_prop_deletion_derives_single_survivor() {
    let mut terms = TermStore::new();
    let a = bool_fun(&mut terms, "pa", 0);
    let b = bool_fun(&mut terms, "pb", 0);
    let false_term = terms.false_term();
    let not_b = terms.mk_not_raw(b);
    let before = terms.mk_app(Symbol::named("or"), [a, b], Sort::Bool);

    let mut fixture = Fixture::new(vec![before, not_b], terms);
    fixture.entry(b, false_term, not_b, 1);
    fixture.record(before, a, 1);
    fixture.assert_plan_is_strictly_checkable(a);
}

/// NEGATIVE (guard: the source must be the literal COMPLEMENT of the deleted
/// disjunct): an unrelated authored unit cannot license a deletion. Without
/// the complementarity check the plan would emit an `equiv_neg2` chain whose
/// resolution has no pivot.
#[test]
fn unit_prop_deletion_declines_non_complementary_source() {
    let mut terms = TermStore::new();
    let a = bool_fun(&mut terms, "pa", 0);
    let b = bool_fun(&mut terms, "pb", 0);
    let c = bool_fun(&mut terms, "pc", 0);
    let unrelated = bool_fun(&mut terms, "pd", 0);
    let false_term = terms.false_term();
    let before = terms.mk_app(Symbol::named("or"), [a, b, c], Sort::Bool);
    let after = terms.mk_or(vec![a, c]);

    let mut fixture = Fixture::new(vec![before, unrelated], terms);
    // Forged: `b` is claimed false on the authority of an unrelated unit.
    fixture.entry(b, false_term, unrelated, 1);
    fixture.record(before, after, 1);
    assert!(
        fixture.plan(after).is_none(),
        "a unit that is not the disjunct's complement must fail the plan"
    );
}

/// NEGATIVE (guard: the licensing unit must itself be derivable): the same
/// green shape with the unit OUTSIDE the problem set must decline rather
/// than assume an unauthored premise.
#[test]
fn unit_prop_deletion_declines_unauthored_unit() {
    let mut terms = TermStore::new();
    let a = bool_fun(&mut terms, "pa", 0);
    let b = bool_fun(&mut terms, "pb", 0);
    let c = bool_fun(&mut terms, "pc", 0);
    let false_term = terms.false_term();
    let not_b = terms.mk_not_raw(b);
    let before = terms.mk_app(Symbol::named("or"), [a, b, c], Sort::Bool);
    let after = terms.mk_or(vec![a, c]);

    // `not_b` is NOT a problem root.
    let mut fixture = Fixture::new(vec![before], terms);
    fixture.entry(b, false_term, not_b, 1);
    fixture.record(before, after, 1);
    assert!(
        fixture.plan(after).is_none(),
        "an unauthored licensing unit must fail the plan"
    );
}

/// NEGATIVE (guard: the survivor SET must match `after`): a forged record
/// smuggling an extra disjunct into the re-formed disjunction must decline.
#[test]
fn unit_prop_deletion_declines_smuggled_survivor() {
    let mut terms = TermStore::new();
    let a = bool_fun(&mut terms, "pa", 0);
    let b = bool_fun(&mut terms, "pb", 0);
    let c = bool_fun(&mut terms, "pc", 0);
    let smuggled = bool_fun(&mut terms, "pd", 0);
    let false_term = terms.false_term();
    let not_b = terms.mk_not_raw(b);
    let before = terms.mk_app(Symbol::named("or"), [a, b, c], Sort::Bool);
    let forged_after = terms.mk_or(vec![a, c, smuggled]);

    let mut fixture = Fixture::new(vec![before, not_b], terms);
    fixture.entry(b, false_term, not_b, 1);
    fixture.record(before, forged_after, 1);
    assert!(
        fixture.plan(forged_after).is_none(),
        "a survivor outside the authored disjunction must fail the plan"
    );
}

// ---- Euclidean-dividend substitution (#4751 `_mod_q` class) ----

/// The measured `dillig12_m` shape, built raw.
///
/// * authored `(= a (+ (* 2 q) r))` — the CHC Euclidean decomposition
///   `ChcExpr::eliminate_mod` asserts for its fresh quotient/remainder pair;
/// * authored `(= r 0)`;
/// * authored `(<= -1 (+ a -1))`;
/// * the substitution pass rewrites the last one to `(<= -1 (+ (* 2 q) -1))`
///   because it applies its map to FIXPOINT (`a` then `r`) and `mk_add` drops
///   the `0`.
fn euclidean_fixture(authorize_decomposition: bool) -> (Fixture, TermId, TermId) {
    let mut terms = TermStore::new();
    let q = terms.mk_var("q", Sort::Int);
    let r = terms.mk_var("r", Sort::Int);
    let a = terms.mk_var("a", Sort::Int);
    let two = terms.mk_int(num_bigint::BigInt::from(2));
    let zero = terms.mk_int(num_bigint::BigInt::from(0));
    let minus_one = terms.mk_int(num_bigint::BigInt::from(-1));

    let two_q = terms.mk_app(Symbol::named("*"), [two, q], Sort::Int);
    let decomposition = terms.mk_app(Symbol::named("+"), [two_q, r], Sort::Int);
    let source_a = terms.mk_app(Symbol::named("="), [a, decomposition], Sort::Bool);
    let source_r = terms.mk_app(Symbol::named("="), [r, zero], Sort::Bool);

    let before_body = terms.mk_app(Symbol::named("+"), [a, minus_one], Sort::Int);
    let before = terms.mk_app(Symbol::named("<="), [minus_one, before_body], Sort::Bool);
    let after_body = terms.mk_app(Symbol::named("+"), [two_q, minus_one], Sort::Int);
    let after = terms.mk_app(Symbol::named("<="), [minus_one, after_body], Sort::Bool);
    assert_ne!(before, after, "fixture must actually rewrite the bound");

    let roots = if authorize_decomposition {
        vec![before, source_a, source_r]
    } else {
        vec![before, source_r]
    };
    let mut fixture = Fixture::new(roots, terms);
    // A NON-CONSTANT replacement, licensed by its defining equality.
    fixture.entry(a, decomposition, source_a, 1);
    fixture.entry(r, zero, source_r, 1);
    (fixture, before, after)
}

/// GREEN: the composed entry value plus the arithmetic-identity fold derive
/// the substituted bound, and the UNTOUCHED strict checker re-derives every
/// step. Before this slice the entry arm returned `(+ (* 2 q) r)` verbatim,
/// so the bridge saw `(<= -1 (+ (+ (* 2 q) r) -1))` and declined on the
/// mismatch — the dominant decline measured on `dillig12_m`.
#[test]
fn euclidean_dividend_substitution_is_strictly_checkable() {
    let (mut fixture, before, after) = euclidean_fixture(true);
    fixture.record(before, after, 1);
    fixture.assert_plan_is_strictly_checkable(after);
}

/// NEGATIVE (guard: the replayed result must equal the RECORDED `after`).
/// A forged record claiming the same rewrite produced a different bound must
/// decline, leaving today's demotion.
#[test]
fn euclidean_dividend_substitution_declines_forged_after() {
    let (mut fixture, before, _after) = euclidean_fixture(true);
    let q = fixture.terms.mk_var("q", Sort::Int);
    let three = fixture.terms.mk_int(num_bigint::BigInt::from(3));
    let minus_one = fixture.terms.mk_int(num_bigint::BigInt::from(-1));
    let three_q = fixture
        .terms
        .mk_app(Symbol::named("*"), [three, q], Sort::Int);
    let forged_body = fixture
        .terms
        .mk_app(Symbol::named("+"), [three_q, minus_one], Sort::Int);
    let forged_after =
        fixture
            .terms
            .mk_app(Symbol::named("<="), [minus_one, forged_body], Sort::Bool);

    fixture.record(before, forged_after, 1);
    assert!(
        fixture.plan(forged_after).is_none(),
        "a recorded `after` the replay cannot reproduce must fail the plan"
    );
}

/// NEGATIVE (guard: the licensing equality must itself be derivable). The
/// same green shape with the Euclidean decomposition OUTSIDE the problem set
/// must decline rather than assume an unauthored premise — the composition
/// grants no authority the uncomposed arm did not already require.
#[test]
fn euclidean_dividend_substitution_declines_unauthored_decomposition() {
    let (mut fixture, before, after) = euclidean_fixture(false);
    fixture.record(before, after, 1);
    assert!(
        fixture.plan(after).is_none(),
        "an unauthored licensing equality must fail the plan"
    );
}

// Deterministic-map alias sanity: the fixture relies on kani_compat maps.
#[allow(dead_code)]
fn _det_map_alias(map: DetHashMap<TermId, TermId>) -> usize {
    map.len()
}

// ---- arithmetic normalization bridge (#4751) ----

/// GREEN: the QF_LIA shape the residual dillig12_m rejections came from.
/// `VariableSubstitution` substitutes `A := B` in the authored
/// `(<= 0 (+ A B))` and rebuilds through `mk_add`, which COLLECTS the like
/// terms and stores `(<= 0 (* B 2))`. Congruence alone reaches only the raw
/// `(+ B B)`; the Farkas normalization lemma closes the gap and the untouched
/// strict checker re-derives every step.
#[test]
fn arith_normalization_derives_collected_sum() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("A", Sort::Int);
    let b = terms.mk_var("B", Sort::Int);
    let zero = terms.mk_int(num_bigint::BigInt::from(0));
    let sum = terms.mk_app(Symbol::named("+"), [a, b], Sort::Int);
    let before = terms.mk_app(Symbol::named("<="), [zero, sum], Sort::Bool);
    let a_def = terms.mk_app(Symbol::named("="), [a, b], Sort::Bool);
    let collected = terms.mk_add(vec![b, b]);
    let after = terms.mk_app(Symbol::named("<="), [zero, collected], Sort::Bool);
    assert_ne!(after, before, "fixture must actually collect like terms");

    let mut fixture = Fixture::new(vec![before, a_def], terms);
    fixture.entry(a, b, a_def, 1);
    fixture.record(before, after, 1);
    fixture.assert_plan_is_strictly_checkable(after);
}

/// GREEN: the DISTRIBUTIVITY shape. `C := (+ A 2)` inside `(* C -2)` makes
/// `mk_mul` distribute, so the pass stores `(+ (* A -2) -4)` where congruence
/// reaches only `(* (+ A 2) -2)`.
#[test]
fn arith_normalization_derives_distributed_product() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("A", Sort::Int);
    let c = terms.mk_var("C", Sort::Int);
    let two = terms.mk_int(num_bigint::BigInt::from(2));
    let minus_two = terms.mk_int(num_bigint::BigInt::from(-2));
    let zero = terms.mk_int(num_bigint::BigInt::from(0));
    let product = terms.mk_app(Symbol::named("*"), [c, minus_two], Sort::Int);
    let before = terms.mk_app(Symbol::named("<="), [zero, product], Sort::Bool);
    let a_plus_two = terms.mk_add(vec![a, two]);
    let c_def = terms.mk_app(Symbol::named("="), [c, a_plus_two], Sort::Bool);
    let distributed = terms.mk_mul(vec![a_plus_two, minus_two]);
    let after = terms.mk_app(Symbol::named("<="), [zero, distributed], Sort::Bool);
    assert_ne!(after, before, "fixture must actually distribute");

    let mut fixture = Fixture::new(vec![before, c_def], terms);
    fixture.entry(c, a_plus_two, c_def, 1);
    fixture.record(before, after, 1);
    fixture.assert_plan_is_strictly_checkable(after);
}

/// NEGATIVE (guard: the record bridge's `to == after`): a forged record whose
/// `after` is not the value the substitution actually produces must decline.
/// The normalization bridge changes WHICH spelling the replay reaches, never
/// whether the reached value has to equal the recorded one.
#[test]
fn arith_normalization_declines_non_identity() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("A", Sort::Int);
    let b = terms.mk_var("B", Sort::Int);
    let three = terms.mk_int(num_bigint::BigInt::from(3));
    let zero = terms.mk_int(num_bigint::BigInt::from(0));
    let sum = terms.mk_app(Symbol::named("+"), [a, b], Sort::Int);
    let before = terms.mk_app(Symbol::named("<="), [zero, sum], Sort::Bool);
    let a_def = terms.mk_app(Symbol::named("="), [a, b], Sort::Bool);
    // `(* B 3)` is NOT `(+ B B)`.
    let forged_inner = terms.mk_mul(vec![b, three]);
    let forged_after = terms.mk_app(Symbol::named("<="), [zero, forged_inner], Sort::Bool);

    let mut fixture = Fixture::new(vec![before, a_def], terms);
    fixture.entry(a, b, a_def, 1);
    fixture.record(before, forged_after, 1);
    assert!(
        fixture.plan(forged_after).is_none(),
        "a recorded `after` that is not the substituted term's linear value must fail the plan"
    );
}

/// NEGATIVE (guard: the entry must be licensed): the same collected-sum
/// rewrite with NO licensing entry for `A` must decline — the bridge
/// normalizes spellings, it never invents the substitution itself.
#[test]
fn arith_normalization_declines_unlicensed_substitution() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("A", Sort::Int);
    let b = terms.mk_var("B", Sort::Int);
    let zero = terms.mk_int(num_bigint::BigInt::from(0));
    let sum = terms.mk_app(Symbol::named("+"), [a, b], Sort::Int);
    let before = terms.mk_app(Symbol::named("<="), [zero, sum], Sort::Bool);
    let collected = terms.mk_add(vec![b, b]);
    let after = terms.mk_app(Symbol::named("<="), [zero, collected], Sort::Bool);

    let mut fixture = Fixture::new(vec![before], terms);
    fixture.record(before, after, 1);
    assert!(
        fixture.plan(after).is_none(),
        "without a licensing entry the replay leaves the term unchanged"
    );
}

/// NEGATIVE (non-linear operands): a product of two variables is not a linear
/// polynomial, so no normalization bridge can be built for it and the plan
/// declines rather than emitting a lemma about a term the Farkas validator
/// treats as opaque.
#[test]
fn arith_normalization_declines_non_linear_product() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("A", Sort::Int);
    let b = terms.mk_var("B", Sort::Int);
    let c = terms.mk_var("C", Sort::Int);
    let zero = terms.mk_int(num_bigint::BigInt::from(0));
    let product = terms.mk_app(Symbol::named("*"), [c, b], Sort::Int);
    let before = terms.mk_app(Symbol::named("<="), [zero, product], Sort::Bool);
    let c_def = terms.mk_app(Symbol::named("="), [c, a], Sort::Bool);
    let forged_inner = terms.mk_app(Symbol::named("*"), [b, a], Sort::Int);
    let forged_after = terms.mk_app(Symbol::named("<="), [zero, forged_inner], Sort::Bool);
    if forged_after == before {
        return;
    }

    let mut fixture = Fixture::new(vec![before, c_def], terms);
    fixture.entry(c, a, c_def, 1);
    fixture.record(before, forged_after, 1);
    assert!(
        fixture.plan(forged_after).is_none(),
        "a non-linear pair must not be bridged by the linear normalization lemma"
    );
}

/// GUARD-REMOVAL PROOF for `linear_identity_holds`: the plan-time self-check
/// is the EXACT acceptance test the strict checker's `lra_farkas` validator
/// runs on the emitted lemma, so it accepts every true linear identity and
/// rejects every false or non-linear one. Dropping it would let the planner
/// splice a lemma the checker rejects, converting a fail-closed decline into
/// a hard rejection of the whole refutation.
#[test]
fn linear_identity_self_check_matches_the_strict_farkas_validator() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("A", Sort::Int);
    let b = terms.mk_var("B", Sort::Int);
    let two = terms.mk_int(num_bigint::BigInt::from(2));
    let three = terms.mk_int(num_bigint::BigInt::from(3));
    let minus_two = terms.mk_int(num_bigint::BigInt::from(-2));
    let minus_four = terms.mk_int(num_bigint::BigInt::from(-4));

    let raw_sum = terms.mk_app(Symbol::named("+"), [b, b], Sort::Int);
    let collected = terms.mk_mul(vec![b, two]);
    let true_identity = terms.mk_app(Symbol::named("="), [raw_sum, collected], Sort::Bool);
    assert!(
        PropagationChainPlanner::linear_identity_holds(&terms, true_identity),
        "(+ B B) and (* B 2) are the same linear polynomial"
    );

    let wrong = terms.mk_mul(vec![b, three]);
    let false_identity = terms.mk_app(Symbol::named("="), [raw_sum, wrong], Sort::Bool);
    assert!(
        !PropagationChainPlanner::linear_identity_holds(&terms, false_identity),
        "(+ B B) is not (* B 3)"
    );

    let mixed = terms.mk_app(Symbol::named("+"), [a, b], Sort::Int);
    let mixed_identity = terms.mk_app(Symbol::named("="), [mixed, collected], Sort::Bool);
    assert!(
        !PropagationChainPlanner::linear_identity_holds(&terms, mixed_identity),
        "(+ A B) is not (* B 2)"
    );

    let a_plus_two = terms.mk_add(vec![a, two]);
    let raw_product = terms.mk_app(Symbol::named("*"), [a_plus_two, minus_two], Sort::Int);
    let scaled = terms.mk_mul(vec![a, minus_two]);
    let distributed = terms.mk_add(vec![scaled, minus_four]);
    let distributive_identity =
        terms.mk_app(Symbol::named("="), [raw_product, distributed], Sort::Bool);
    assert!(
        PropagationChainPlanner::linear_identity_holds(&terms, distributive_identity),
        "distributivity over a constant multiplier is a linear identity"
    );

    let nonlinear_left = terms.mk_app(Symbol::named("*"), [a, b], Sort::Int);
    let nonlinear_right = terms.mk_app(Symbol::named("*"), [a, a], Sort::Int);
    let forged = terms.mk_app(
        Symbol::named("="),
        [nonlinear_left, nonlinear_right],
        Sort::Bool,
    );
    assert!(
        !PropagationChainPlanner::linear_identity_holds(&terms, forged),
        "distinct opaque non-linear products must never be bridged"
    );
}

/// GUARD-REMOVAL PROOF for the non-constant mint leg
/// (`is_recorded_defining_equality`): a `VariableSubstitution` source that is
/// NOT literally the defining equality must not seed an entry, because the
/// replay's entry arm returns that source term AS the licensing equality.
/// `find_substitution` really does harvest from `ite`-encoded equalities, so
/// this is a reachable shape, not a hypothetical one.
#[test]
fn non_constant_mint_leg_requires_a_literal_defining_equality() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let one = terms.mk_int(num_bigint::BigInt::from(1));
    let replacement = terms.mk_add(vec![y, one]);
    let forward = terms.mk_app(Symbol::named("="), [x, replacement], Sort::Bool);
    let reversed = terms.mk_app(Symbol::named("="), [replacement, x], Sort::Bool);
    let unrelated = terms.mk_app(Symbol::named("<="), [x, replacement], Sort::Bool);
    let other_value = terms.mk_app(Symbol::named("="), [x, y], Sort::Bool);

    assert!(Executor::is_recorded_defining_equality(
        &terms,
        forward,
        x,
        replacement
    ));
    assert!(Executor::is_recorded_defining_equality(
        &terms,
        reversed,
        x,
        replacement
    ));
    assert!(!Executor::is_recorded_defining_equality(
        &terms,
        unrelated,
        x,
        replacement
    ));
    assert!(!Executor::is_recorded_defining_equality(
        &terms,
        other_value,
        x,
        replacement
    ));
}

include!("tests/folding_regressions.rs");
