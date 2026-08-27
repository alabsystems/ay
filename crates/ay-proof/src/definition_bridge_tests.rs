// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Coverage for the rewritten-assertion BRIDGE planner.
//!
//! The bar, and how each layer meets it:
//!
//! 1. **Every planned step is re-validated by the UNTOUCHED strict checker.**
//!    [`bridge`] closes the planned fragment over the negation of each of its
//!    own literals and runs `check_proof_strict`. No validator is relaxed and
//!    no rule is added.
//! 2. **Every ACCEPT is re-checked by an INDEPENDENT evaluator.** The planned
//!    bridge clause must be VALID by
//!    [`crate::congruence_derivation::sweep_tests::falsifies`], which shares
//!    no code with the planner: it enumerates every quotient of the clause's
//!    sub-term set and reports one that falsifies every literal.
//! 3. **Adversarial negatives** live in `definition_bridge_negative_tests.rs`,
//!    each naming a concrete falsifying assignment and CHECKING it in-test.
//! 4. **A guard-mutation ledger** ([`GUARD_MUTATION_LEDGER`]).

use super::{plan_definitional_bridge, DefinitionBridge};
use crate::congruence_derivation::sweep_tests::falsifies;
use crate::quality::check_proof_strict;
use ay_core::{ArraySort, ProofStep, Sort, Symbol, TermId, TermStore};

// ===== fixture helpers =====

pub(super) fn uninterpreted(name: &str) -> Sort {
    Sort::Uninterpreted(name.to_string())
}

pub(super) fn element(terms: &mut TermStore, name: &str) -> TermId {
    terms.mk_var(name, uninterpreted("Element"))
}

pub(super) fn index(terms: &mut TermStore, name: &str) -> TermId {
    terms.mk_var(name, uninterpreted("Index"))
}

pub(super) fn array_sort() -> Sort {
    Sort::Array(Box::new(ArraySort::new(
        uninterpreted("Index"),
        uninterpreted("Element"),
    )))
}

pub(super) fn array(terms: &mut TermStore, name: &str) -> TermId {
    terms.mk_var(name, array_sort())
}

pub(super) fn store(terms: &mut TermStore, base: TermId, at: TermId, value: TermId) -> TermId {
    terms.mk_app(Symbol::named("store"), vec![base, at, value], array_sort())
}

pub(super) fn select(terms: &mut TermStore, base: TermId, at: TermId) -> TermId {
    terms.mk_app(
        Symbol::named("select"),
        vec![base, at],
        uninterpreted("Element"),
    )
}

/// `(= lhs rhs)` built RAW, so a fixture controls operand order exactly — the
/// same builder the shipped congruence fixtures use.
pub(super) fn eq(terms: &mut TermStore, lhs: TermId, rhs: TermId) -> TermId {
    terms.mk_app(Symbol::named("="), vec![lhs, rhs], Sort::Bool)
}

/// Plan a bridge and insist on every layer of the bar at once.
pub(super) fn bridge(
    terms: &mut TermStore,
    goal: TermId,
    candidates: &[TermId],
) -> DefinitionBridge {
    let planned =
        plan_definitional_bridge(terms, goal, candidates).expect("this goal must be bridgeable");
    // The clause the caller will resolve against.
    let mut expected: Vec<TermId> = planned
        .hypotheses
        .iter()
        .map(|&hypothesis| terms.mk_not(hypothesis))
        .collect();
    expected.push(goal);
    assert_eq!(
        planned.derivation.clause, expected,
        "the fragment's last clause must be the bridge clause, hypotheses first and goal last"
    );
    // INDEPENDENT re-check: the bridge clause must be VALID.
    assert!(
        falsifies(terms, &planned.derivation.clause).is_none(),
        "the independent evaluator found a countermodel of an ACCEPTED bridge clause"
    );
    // The UNTOUCHED strict checker replays every planned step.
    let closed = crate::close_congruence_derivation(terms, &planned.derivation);
    check_proof_strict(&closed, terms).expect("every planned step must strict-check");
    for step in &planned.derivation.steps {
        let ProofStep::Step { rule, .. } = step else {
            panic!("the planner emits only generic steps");
        };
        assert!(
            ay_core::is_checkable_alethe_rule(rule.name()),
            "planned rule {} is not externally checkable",
            rule.name()
        );
        assert_ne!(ay_core::wire_rule_name(rule.name()), "hole");
    }
    planned
}

/// The measured head of the class: `VariableSubstitution` inlined an authored
/// array definition into an authored `select` assertion.
///
/// ```text
/// authored   (= a_250 (store a1 i0 e_249))
/// authored   (= e_253 (select a_250 i2))
/// rewritten  (= e_253 (select (store a1 i0 e_249) i2))
/// ```
///
/// ONE store level, deliberately: every accept in this file is re-checked by
/// an evaluator that enumerates every PARTITION of the clause's sub-term set,
/// which is a Bell number in the node count. Nine nodes is 21 147 partitions;
/// the two-level chain is fourteen nodes and 190 million. The deep chain has
/// its own test, `a_two_level_inlined_chain_bridges`, which strict-checks the
/// fragment without the exhaustive evaluator.
pub(super) struct StoreChain {
    pub(super) goal: TermId,
    pub(super) candidates: Vec<TermId>,
    /// The hypotheses the bridge must cite, in pool order.
    pub(super) cited: Vec<TermId>,
    /// `(= e_249 e_253)` — a pool entry the explanation never needs, and one
    /// that adds no new sub-term to the sweep's alphabet.
    pub(super) spare: TermId,
}

pub(super) fn store_chain(terms: &mut TermStore) -> StoreChain {
    let a1 = array(terms, "a1");
    let a250 = array(terms, "a_250");
    let i0 = index(terms, "i0");
    let i2 = index(terms, "i2");
    let e249 = element(terms, "e_249");
    let e253 = element(terms, "e_253");

    let inner = store(terms, a1, i0, e249);
    let def250 = eq(terms, a250, inner);
    let read = select(terms, a250, i2);
    let authored = eq(terms, e253, read);
    let rewritten_read = select(terms, inner, i2);
    let goal = eq(terms, e253, rewritten_read);
    let spare = eq(terms, e249, e253);
    StoreChain {
        goal,
        candidates: vec![def250, authored],
        cited: vec![def250, authored],
        spare,
    }
}

/// The two-level chain exactly as the corpus carries it.
pub(super) fn deep_store_chain(terms: &mut TermStore) -> (TermId, Vec<TermId>) {
    let a1 = array(terms, "a1");
    let a250 = array(terms, "a_250");
    let a252 = array(terms, "a_252");
    let i0 = index(terms, "i0");
    let i1 = index(terms, "i1");
    let i2 = index(terms, "i2");
    let e249 = element(terms, "e_249");
    let e251 = element(terms, "e_251");
    let e253 = element(terms, "e_253");

    let inner = store(terms, a1, i0, e249);
    let outer = store(terms, inner, i1, e251);
    let def250 = eq(terms, a250, inner);
    let stored = store(terms, a250, i1, e251);
    let def252 = eq(terms, a252, stored);
    let read = select(terms, a252, i2);
    let authored = eq(terms, e253, read);
    let rewritten_read = select(terms, outer, i2);
    let goal = eq(terms, e253, rewritten_read);
    (goal, vec![def250, def252, authored])
}

// ===== the head of the measured distribution =====

#[test]
fn an_inlined_store_chain_bridges_to_its_authored_assertions() {
    let mut terms = TermStore::new();
    let fixture = store_chain(&mut terms);
    let planned = bridge(&mut terms, fixture.goal, &fixture.candidates);
    assert_eq!(planned.hypotheses, fixture.cited);
}

#[test]
fn the_bridge_cites_only_the_hypotheses_the_explanation_uses() {
    let mut terms = TermStore::new();
    let fixture = store_chain(&mut terms);
    // Ten irrelevant authored equalities over untouched symbols.
    let mut pool = fixture.candidates.clone();
    for step in 0..10 {
        let left = element(&mut terms, &format!("noise_l{step}"));
        let right = element(&mut terms, &format!("noise_r{step}"));
        let noise = eq(&mut terms, left, right);
        pool.push(noise);
    }
    let planned = bridge(&mut terms, fixture.goal, &pool);
    assert_eq!(
        planned.hypotheses, fixture.cited,
        "an irrelevant authored assertion must not enter the bridge clause"
    );
}

#[test]
fn the_pool_order_does_not_change_which_hypotheses_are_cited() {
    let mut terms = TermStore::new();
    let fixture = store_chain(&mut terms);
    let mut reversed = fixture.candidates.clone();
    reversed.reverse();
    let planned = plan_definitional_bridge(&mut terms, fixture.goal, &reversed)
        .expect("the goal is bridgeable in any pool order");
    let mut cited = planned.hypotheses.clone();
    cited.sort_unstable();
    let mut expected = fixture.cited.clone();
    expected.sort_unstable();
    assert_eq!(cited, expected);
}

// ===== the `purify_bool_args` bridge the ask names =====

/// `(= TRUE (bool p))` from the authored `(= TRUE (bool b))` and the CHECKED
/// definition `(= b p)` — a SINGLE congruence, as the ask claims.
#[test]
fn a_purified_boolean_proxy_bridges_by_a_single_congruence() {
    let mut terms = TermStore::new();
    let u = uninterpreted("U");
    let truth = terms.mk_var("TRUE", u.clone());
    let g = terms.mk_var("g", Sort::Bool);
    let body = terms.mk_app(Symbol::named("and"), vec![g], Sort::Bool);
    let proxy = terms.mk_var("boolarg_6", Sort::Bool);
    let wrapped_body = terms.mk_app(Symbol::named("bool"), vec![body], u.clone());
    let wrapped_proxy = terms.mk_app(Symbol::named("bool"), vec![proxy], u);
    let authored = eq(&mut terms, truth, wrapped_body);
    let definition = eq(&mut terms, body, proxy);
    let goal = eq(&mut terms, truth, wrapped_proxy);

    let planned = bridge(&mut terms, goal, &[definition, authored]);
    assert_eq!(planned.hypotheses, vec![definition, authored]);
    let rules: Vec<&str> = planned
        .derivation
        .steps
        .iter()
        .map(|step| match step {
            ProofStep::Step { rule, .. } => rule.name(),
            _ => unreachable!(),
        })
        .collect();
    assert!(
        rules.contains(&"eq_congruent"),
        "the bridge is a congruence over `bool`, got {rules:?}"
    );
}

// ===== declines =====

#[test]
fn a_goal_that_is_not_a_binary_equality_is_declined() {
    let mut terms = TermStore::new();
    let a = element(&mut terms, "a");
    let b = element(&mut terms, "b");
    let goal = terms.mk_app(Symbol::named("p"), vec![a, b], Sort::Bool);
    let hypothesis = eq(&mut terms, a, b);
    assert!(plan_definitional_bridge(&mut terms, goal, &[hypothesis]).is_none());
}

#[test]
fn an_empty_candidate_pool_is_declined() {
    let mut terms = TermStore::new();
    let fixture = store_chain(&mut terms);
    assert!(plan_definitional_bridge(&mut terms, fixture.goal, &[]).is_none());
}

#[test]
fn a_candidate_pool_over_the_cap_is_declined() {
    let mut terms = TermStore::new();
    let fixture = store_chain(&mut terms);
    let mut pool = fixture.candidates.clone();
    while pool.len() <= super::MAX_BRIDGE_CANDIDATES {
        let left = element(&mut terms, &format!("cap_l{}", pool.len()));
        let right = element(&mut terms, &format!("cap_r{}", pool.len()));
        let filler = eq(&mut terms, left, right);
        pool.push(filler);
    }
    assert!(plan_definitional_bridge(&mut terms, fixture.goal, &pool).is_none());
}

#[test]
fn a_candidate_equal_to_the_goal_is_never_used_as_its_own_hypothesis() {
    let mut terms = TermStore::new();
    let fixture = store_chain(&mut terms);
    // The goal itself in the pool must not license `(cl (not g) g)`.
    assert!(plan_definitional_bridge(&mut terms, fixture.goal, &[fixture.goal]).is_none());
}

#[test]
fn a_goal_the_pool_does_not_entail_is_declined() {
    let mut terms = TermStore::new();
    let fixture = store_chain(&mut terms);
    // Drop the definition of `a_250`: the chain no longer reaches the goal.
    let short = vec![fixture.candidates[1], fixture.spare];
    assert!(plan_definitional_bridge(&mut terms, fixture.goal, &short).is_none());
}

/// The corpus shape at full depth: TWO inlined store levels, three cited
/// hypotheses. Checked by the untouched strict checker; the exhaustive
/// evaluator is deliberately not run on it (see [`StoreChain`]).
#[test]
fn a_two_level_inlined_chain_bridges() {
    let mut terms = TermStore::new();
    let (goal, candidates) = deep_store_chain(&mut terms);
    let planned = plan_definitional_bridge(&mut terms, goal, &candidates)
        .expect("the two-level chain must bridge");
    assert_eq!(planned.hypotheses, candidates);
    let closed = crate::close_congruence_derivation(&mut terms, &planned.derivation);
    check_proof_strict(&closed, &terms).expect("every planned step must strict-check");
}

#[test]
fn a_read_over_write_goal_is_declined_because_congruence_cannot_reach_it() {
    // The measured ROW residual: `(= e_259 e_261)` where the authored
    // `(= e_261 (select a_260 i0))` needs `select(store(a,i,v),i) = v`, which
    // is an ARRAY AXIOM and not a congruence. Declining is the whole point.
    let mut terms = TermStore::new();
    let base = array(&mut terms, "a_258");
    let a260 = array(&mut terms, "a_260");
    let i0 = index(&mut terms, "i0");
    let e259 = element(&mut terms, "e_259");
    let e261 = element(&mut terms, "e_261");
    let stored = store(&mut terms, base, i0, e259);
    let definition = eq(&mut terms, a260, stored);
    let read = select(&mut terms, a260, i0);
    let authored = eq(&mut terms, e261, read);
    let goal = eq(&mut terms, e259, e261);
    assert!(plan_definitional_bridge(&mut terms, goal, &[definition, authored]).is_none());
}

/// GUARD MUTATION LEDGER — every guard deleted or weakened, the NAMED test
/// observed FAILING, the guard restored. See the module header of
/// `definition_bridge_negative_tests.rs` for the negatives.
///
/// | guard (`definition_bridge.rs`) | named test |
/// |---|---|
/// | `decode_binary_eq(terms, goal)?` | `a_goal_that_is_not_a_binary_equality_is_declined` |
/// | `candidates.len() > MAX_BRIDGE_CANDIDATES` | `a_candidate_pool_over_the_cap_is_declined` |
/// | `candidate == goal` | `a_candidate_equal_to_the_goal_is_never_used_as_its_own_hypothesis` |
/// | `positives.is_empty()` | `an_empty_candidate_pool_is_declined` |
/// | `negate` decode check | `a_candidate_whose_negation_is_not_a_plain_wrapper_is_dropped` |
/// | `hypotheses.is_empty()` | `a_goal_entailed_by_nothing_in_the_pool_is_declined` |
/// | `cited.len() != literals.len() + 1` | `a_bridge_never_carries_a_literal_outside_its_own_clause` |
/// | `derivation.clause == literals` | `the_planned_clause_is_the_clause_the_caller_resolves` |
const GUARD_MUTATION_LEDGER: () = ();

#[test]
fn the_guard_mutation_ledger_exists() {
    let () = GUARD_MUTATION_LEDGER;
}
