// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `and_neg` and the charge class it must KEEP.
//!
//! # The question this file answers, and the answer
//!
//! `SemanticChargeClass::ClauseIdentityRoute` charges `reordering`,
//! `weakening` and `eq_reflexive` on a comparison-sort bound over their
//! REACHABLE-DAG payload instead of the `General` `unfolded_work^2` product.
//! The justification for that class is stated on the class itself and it is
//! narrow: each of those three validators "reads CLAUSE LITERALS as opaque
//! `TermId`s and never descends into one". `contraction` is deliberately
//! excluded because its validator is genuinely quadratic in the clause length.
//!
//! `and_neg` was asked whether it belongs in that class. **It does not, and
//! this file is the evidence.**
//! [`crate::checker::boolean::validate_and_neg`] reads SUBTERMS:
//!
//!  * the gate scan calls `matches_positive_literal_of_term`, which for an
//!    `and`-headed source falls through to `matches_negation_of_term`;
//!  * the bijective cover calls `matches_negated_components`, which calls
//!    `matches_negation_of_term` on up to `n(n+1)/2` literal/conjunct PAIRS;
//!  * `matches_negation_of_term` RECURSES — through `Ite` branches, through a
//!    `Not` (via `matches_positive_literal_of_term`), and through De Morgan
//!    `and`/`or` duals via `matches_negated_components` again — and it carries
//!    **no memo table**, so a shared sub-term is re-entered once per path that
//!    reaches it.
//!
//! Two consequences, both pinned below against concrete inputs:
//!
//!  1. **No DAG bound exists.** `a_doubling_dag_refutes_any_reachable_dag_bound`
//!     builds a conjunction whose reachable DAG grows by ONE node per level
//!     while the matcher's call count DOUBLES, and checks that the
//!     `ClauseIdentityRoute` model would bill it less than the number of
//!     recursive calls the validator actually makes. A charge that ignores
//!     `unfolded_work` UNDER-charges this step by orders of magnitude.
//!  2. **`General` already has the right SHAPE.** The recursion descends both
//!     sides in lockstep, so its cost is bounded by the product of the two tree
//!     unfoldings, and summed over the `n^2` pairs by
//!     `unfolded_work^2` — exactly the `General` product.
//!     `the_general_product_bounds_the_measured_matcher_work` checks that
//!     inequality on every shape in a sweep.
//!
//! # And the metering is not the obstacle it was suspected of being
//!
//! The 2026-08-23 census doc suspected this charge of blocking an `and_neg`
//! decomposition of a 29-conjunct `clearsy` leaf. MEASURED with a temporary
//! probe over the REAL metering walk, on the actual leaves of
//! `benchmarks/smt/regression/soundness_qf_uf_incremental/`:
//!
//! | file | n | `work` | `unfolded_work` | `General` | of 350 M |
//! |---|---|---|---|---|---|
//! | `clearsy_0001_00310_falsesat44` | 29 | 2 134 | 303 | 646 602 | 0.18% |
//! | `clearsy_0000_00307_falsesat13` | 22 | 1 770 | 245 | 433 650 | 0.12% |
//!
//! `a_clearsy_shaped_conjunction_costs_a_fraction_of_the_envelope` rebuilds
//! that shape here and pins the same order of magnitude through the real walk.
//! NO charge model was changed for the lane that consumes this rule.

use super::*;

/// `MAX_CHECK_WORK`, the envelope every claim below is measured against.
pub(super) const PRODUCTION_ENVELOPE: usize = 350_000_000;

/// The charge `and_neg` takes today: the `General` recursive-tree product with
/// no private per-rule scale (`AletheRule::AndNeg` falls through
/// `private_validator_charge`'s `_ => (0, 0)` arm).
pub(super) fn general_charge(stats: PayloadStats) -> usize {
    let named = stats.work.saturating_mul(stats.unfolded_work);
    let paired = stats.unfolded_work.saturating_mul(stats.unfolded_work);
    named.max(paired)
}

/// The charge the DAG-bounded clause-identity class WOULD take, computed here
/// so the refutation below can name the number it would have billed.
pub(super) fn clause_identity_model(stats: PayloadStats) -> usize {
    CLAUSE_IDENTITY_WORK_FACTOR
        .saturating_mul(comparison_sort_bound(stats.work))
        .saturating_add(CLAUSE_IDENTITY_WORK_FACTOR)
}

pub(super) fn and_neg_step(clause: Vec<TermId>, source: TermId) -> ProofStep {
    ProofStep::Step {
        rule: AletheRule::AndNeg,
        clause,
        premises: Vec::new(),
        args: vec![source],
    }
}

/// Run ONE step through the real strict validator, so every claim below is
/// about a step the checker genuinely accepts or genuinely rejects.
pub(super) fn validate_one(terms: &TermStore, step: &ProofStep) -> Result<(), ProofCheckError> {
    let mut table: Vec<Option<Vec<TermId>>> = Vec::new();
    let step_id = ProofId(0);
    let mut unbounded = |_: usize, _: usize| true;
    validate_step_with_datatypes_and_progress(
        terms,
        &mut table,
        step_id,
        step,
        true,
        None,
        None,
        None,
        None,
        None,
        None,
        None,
        &mut unbounded,
    )
}

/// Run the REAL per-step metering walk, so the tests are pinned against
/// production `PayloadStats` and not against numbers chosen to pass.
pub(super) fn measured_payload(step: &ProofStep, terms: &TermStore) -> PayloadStats {
    let mut memo = TermCostMemo::default();
    let mut unbounded = |_: usize, _: usize| true;
    meter_step_term_payload(step, terms, &[], &mut memo, &mut unbounded)
        .expect("an unbounded envelope always completes the payload walk")
}

pub(super) fn app(terms: &mut TermStore, name: &str, args: Vec<TermId>) -> TermId {
    terms.mk_app(Symbol::named(name), args, Sort::Bool)
}

// ---------------------------------------------------------------------------
// An INDEPENDENT mirror of the negation matcher, which COUNTS its recursion.
//
// It shares no code with `crates/ay-proof/src/checker/boolean.rs` — it is
// written from that module's stated behaviour — and
// `the_mirror_agrees_with_the_real_validator` checks that its VERDICT matches
// the real `validate_and_neg` on every case in a sweep. That agreement is what
// licenses reading its call count as a lower bound on the validator's own work.
// ---------------------------------------------------------------------------

pub(super) fn mirror_strip_not(terms: &TermStore, term: TermId) -> Option<TermId> {
    match terms.get(term) {
        TermData::Not(inner) => Some(*inner),
        _ => None,
    }
}

pub(super) fn mirror_app<'a>(
    terms: &'a TermStore,
    term: TermId,
    name: &str,
) -> Option<&'a [TermId]> {
    match terms.get(term) {
        TermData::App(Symbol::Named(found), args) if found == name => Some(args),
        _ => None,
    }
}

pub(super) fn mirror_negation(
    terms: &TermStore,
    lit: TermId,
    term: TermId,
    calls: &mut usize,
) -> bool {
    *calls += 1;
    if mirror_strip_not(terms, lit) == Some(term) {
        return true;
    }
    match terms.get(term) {
        TermData::Not(inner) => mirror_positive(terms, lit, *inner, calls),
        TermData::App(Symbol::Named(name), args) if name == "and" => {
            match mirror_app(terms, lit, "or") {
                Some(disjuncts) => {
                    disjuncts.len() == args.len()
                        && mirror_components(terms, disjuncts, args, calls)
                }
                None => false,
            }
        }
        TermData::App(Symbol::Named(name), args) if name == "or" => {
            match mirror_app(terms, lit, "and") {
                Some(conjuncts) => {
                    conjuncts.len() == args.len()
                        && mirror_components(terms, conjuncts, args, calls)
                }
                None => false,
            }
        }
        _ => false,
    }
}

pub(super) fn mirror_positive(
    terms: &TermStore,
    lit: TermId,
    term: TermId,
    calls: &mut usize,
) -> bool {
    *calls += 1;
    if lit == term {
        return true;
    }
    matches!(terms.get(term), TermData::App(Symbol::Named(name), _) if name == "and")
        && mirror_strip_not(terms, lit)
            .is_some_and(|inner| mirror_negation(terms, inner, term, calls))
}

pub(super) fn mirror_components(
    terms: &TermStore,
    items: &[TermId],
    expected: &[TermId],
    calls: &mut usize,
) -> bool {
    if items.len() != expected.len() {
        return false;
    }
    let mut matched = vec![false; expected.len()];
    for &item in items {
        let Some(index) = (0..expected.len()).find(|index| {
            !matched[*index] && mirror_negation(terms, item, expected[*index], calls)
        }) else {
            return false;
        };
        matched[index] = true;
    }
    true
}

/// The mirror of `validate_and_neg` itself: its verdict and its call count.
pub(super) fn mirror_and_neg(
    terms: &TermStore,
    clause: &[TermId],
    source: TermId,
) -> (bool, usize) {
    let mut calls = 0_usize;
    let Some(args) = mirror_app(terms, source, "and") else {
        return (false, calls);
    };
    if clause.len() != args.len() + 1 {
        return (false, calls);
    }
    let mut gate_matched = false;
    let mut negated: Vec<TermId> = Vec::new();
    for &lit in clause {
        let is_gate = mirror_positive(terms, lit, source, &mut calls)
            || mirror_app(terms, lit, "and").is_some_and(|inner| inner == args);
        if is_gate && !gate_matched {
            gate_matched = true;
        } else {
            negated.push(lit);
        }
    }
    let ok = gate_matched && mirror_components(terms, &negated, args, &mut calls);
    (ok, calls)
}

// ---------------------------------------------------------------------------
// Fixtures
// ---------------------------------------------------------------------------

/// A conjunction whose reachable DAG grows by ONE node per level while its tree
/// unfolding DOUBLES: `T_0 = leaf`, `T_k = (and T_{k-1} T_{k-1})` with BOTH
/// arguments the same interned `TermId`.
///
/// `C_k` is its De Morgan complement, built the same way:
/// `C_0 = (not leaf)`, `C_k = (or C_{k-1} C_{k-1})`. Matching `C_k` against
/// `T_k` is exactly the recursion `matches_negation_of_term` performs, and it
/// visits `2^k` leaf pairs over a DAG of `2k + 2` nodes.
pub(super) fn doubling_conjunction(
    terms: &mut TermStore,
    tag: &str,
    depth: usize,
) -> (TermId, TermId) {
    let leaf = terms.mk_var(format!("{tag}_leaf"), Sort::Bool);
    let mut conjunction = leaf;
    let mut complement = terms.mk_not(leaf);
    for _ in 0..depth {
        conjunction = app(terms, "and", vec![conjunction, conjunction]);
        complement = app(terms, "or", vec![complement, complement]);
    }
    (conjunction, complement)
}

/// The `clearsy` population's shape: `(and (= TRUE (bool b_0)) .. )` over an
/// uninterpreted sort, `n` conjuncts, every conjunct a distinct small term.
pub(super) fn clearsy_shaped_conjunction(terms: &mut TermStore, n: usize) -> (TermId, Vec<TermId>) {
    let universe = Sort::Uninterpreted("U".to_string());
    let truth = terms.mk_var("TRUE", universe.clone());
    let conjuncts: Vec<TermId> = (0..n)
        .map(|index| {
            let arg = terms.mk_var(format!("boolarg_{index}"), Sort::Bool);
            let boxed = terms.mk_app(Symbol::named("bool"), vec![arg], universe.clone());
            terms.mk_app(Symbol::named("="), vec![truth, boxed], Sort::Bool)
        })
        .collect();
    let conjunction = app(terms, "and", conjuncts.clone());
    (conjunction, conjuncts)
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

/// `and_neg` keeps `General`, and neither DAG-bounded class claims it.
///
/// This is the routing half of the answer; the two tests after it are the
/// reason.
#[test]
fn and_neg_is_not_admitted_to_any_dag_bounded_class() {
    let terms = TermStore::new();
    let step = and_neg_step(Vec::new(), TermId(0));
    assert_eq!(
        select_semantic_charge_class(&step, &terms),
        SemanticChargeClass::General,
        "and_neg's validator reads subterms; it must keep the tree-unfolded product"
    );
    assert!(
        !is_clause_identity_route(&step),
        "and_neg must not be admitted to the syntax-only clause-identity route"
    );
    assert!(
        !is_euf_identity_route(&step),
        "and_neg must not be admitted to the EUF identity route"
    );
    // The positive control: the class the rule is being compared against does
    // still exist and does still claim its own members.
    let reordering = ProofStep::Step {
        rule: AletheRule::Reordering,
        clause: Vec::new(),
        premises: vec![ProofId(0)],
        args: Vec::new(),
    };
    assert_eq!(
        select_semantic_charge_class(&reordering, &terms),
        SemanticChargeClass::ClauseIdentityRoute
    );
    // `and_pos` shares the same matcher and is likewise not admitted.
    let and_pos = ProofStep::Step {
        rule: AletheRule::AndPos(0),
        clause: Vec::new(),
        premises: Vec::new(),
        args: Vec::new(),
    };
    assert_eq!(
        select_semantic_charge_class(&and_pos, &terms),
        SemanticChargeClass::General
    );
}

/// THE DISQUALIFIER, on a concrete input: `validate_and_neg` accepts or rejects
/// on the strength of a position TWO LEVELS BELOW the clause literal.
///
/// Source `(and (or a b) x)`. The literal offered as the negation of the first
/// conjunct is the De Morgan dual `(and (not a) (not b))` — the validator has
/// to decode it, pair its arguments against the disjuncts, and check each
/// polarity. Flip ONE of those inner polarities and the same clause, with the
/// same length, the same heads and the same DAG size, is refused.
///
/// A validator that "reads clause literals as opaque `TermId`s and never
/// descends into one" — the stated admission test for
/// `SemanticChargeClass::ClauseIdentityRoute` — could not tell these apart.
#[test]
fn validate_and_neg_decides_on_a_position_two_levels_below_the_literal() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("dm_a", Sort::Bool);
    let b = terms.mk_var("dm_b", Sort::Bool);
    let x = terms.mk_var("dm_x", Sort::Bool);
    let not_a = terms.mk_not(a);
    let not_b = terms.mk_not(b);
    let not_x = terms.mk_not(x);
    let disjunction = app(&mut terms, "or", vec![a, b]);
    let source = app(&mut terms, "and", vec![disjunction, x]);

    let dual = app(&mut terms, "and", vec![not_a, not_b]);
    let accepted = and_neg_step(vec![source, dual, not_x], source);
    validate_one(&terms, &accepted).expect(
        "(and (not a) (not b)) IS the negation of (or a b): the validator must \
         descend into both to see it",
    );

    let broken = app(&mut terms, "and", vec![not_a, b]);
    let rejected = and_neg_step(vec![source, broken, not_x], source);
    let error = validate_one(&terms, &rejected)
        .expect_err("(and (not a) b) is NOT the negation of (or a b)");
    assert!(
        matches!(error, ProofCheckError::InvalidBooleanRule { ref rule, .. } if rule == "and_neg"),
        "{error:?}"
    );

    // The two clauses are the same length over the same heads, and the only
    // difference is at depth 2 — so nothing shallower could have decided it.
    assert_eq!(dual, app(&mut terms, "and", vec![not_a, not_b]));
    assert_ne!(dual, broken);
}

/// THE REFUTATION of any reachable-DAG charge for this rule.
///
/// `T_k = (and T_{k-1} T_{k-1})` and its De Morgan complement
/// `C_k = (or C_{k-1} C_{k-1})`, both built from ONE interned child, so the
/// clause `(cl T_k C_{k-1} C_{k-1})` has a DAG of a few dozen nodes and a tree
/// unfolding of `2^k`. `matches_negation_of_term` has no memo table, so it
/// re-enters the shared child once per path and performs `>= 2^k` recursive
/// calls.
///
/// Checked here:
///  * the step is genuinely VALID, so the validator really does all of it;
///  * the measured DAG payload stays tiny while the unfolded payload explodes;
///  * the mirror's call count is at least `2^k`; and
///  * **the `ClauseIdentityRoute` model would bill this step LESS than the
///    number of recursive calls it costs** — i.e. it would under-charge, which
///    is precisely what a fail-closed meter may not do. `General` bills more.
#[test]
fn a_doubling_dag_refutes_any_reachable_dag_bound() {
    const DEPTH: usize = 20;
    let mut terms = TermStore::new();
    let (conjunction, complement) = doubling_conjunction(&mut terms, "dbl", DEPTH);
    let TermData::App(_, children) = terms.get(conjunction) else {
        panic!("the doubling fixture must build an `and` application");
    };
    assert_eq!(children[0], children[1], "both arguments must be SHARED");
    let TermData::App(_, complement_children) = terms.get(complement) else {
        panic!("the complement must be an `or` application");
    };
    let inner_complement = complement_children[0];

    let clause = vec![conjunction, inner_complement, inner_complement];
    let step = and_neg_step(clause.clone(), conjunction);
    validate_one(&terms, &step).expect(
        "(or C C) IS the De Morgan negation of (and T T) at every level: the \
         step is valid and the validator must walk all of it",
    );
    let stats = measured_payload(&step, &terms);
    assert!(
        stats.work < 4_096,
        "the reachable DAG must stay tiny: work={}",
        stats.work
    );
    assert!(
        stats.unfolded_work > (1_usize << DEPTH),
        "the tree unfolding must explode: unfolded={} depth={DEPTH}",
        stats.unfolded_work
    );

    let (ok, calls) = mirror_and_neg(&terms, &clause, conjunction);
    assert!(ok, "the mirror must agree the step is valid");
    assert!(
        calls >= (1_usize << DEPTH),
        "the matcher must really make ~2^depth recursive calls: calls={calls} depth={DEPTH}"
    );

    let dag_bounded = clause_identity_model(stats);
    assert!(
        dag_bounded < calls,
        "a reachable-DAG charge would UNDER-charge this step: it bills \
         {dag_bounded} for {calls} recursive matcher calls",
    );
    let general = general_charge(stats);
    assert!(
        general > calls,
        "the `General` product must still bound the real work: {general} vs {calls}"
    );

    // And the under-charge is UNBOUNDED in the DAG size, which is the whole
    // claim. Eight more DAG levels multiply the matcher's work by 2^8 while a
    // reachable-DAG model barely moves.
    let (small_calls, small_dag_bounded, small_work) = doubling_measurements(DEPTH - 8);
    assert!(
        stats.work < small_work * 2,
        "the DAG payload must stay in the same league: {small_work} -> {}",
        stats.work
    );
    assert!(
        calls / small_calls >= 200,
        "the matcher's work must grow ~2^8 over those eight levels: \
         {small_calls} -> {calls}"
    );
    assert!(
        dag_bounded <= small_dag_bounded * 2,
        "while the DAG-bounded model barely moves over those levels: \
         {small_dag_bounded} -> {dag_bounded}"
    );
    // Together those two are the refutation: eight more DAG nodes multiply the
    // validator's real work by 2^8 and the reachable-DAG charge by at most 2,
    // so the under-charge factor grows without bound in the DAG size.
}

/// `(matcher calls, the DAG-bounded model's charge, the measured DAG payload)`
/// for the doubling fixture at one depth.
fn doubling_measurements(depth: usize) -> (usize, usize, usize) {
    let mut terms = TermStore::new();
    let (conjunction, complement) = doubling_conjunction(&mut terms, "ratio", depth);
    let TermData::App(_, complement_children) = terms.get(complement) else {
        panic!("the complement must be an `or` application");
    };
    let inner = complement_children[0];
    let clause = vec![conjunction, inner, inner];
    let step = and_neg_step(clause.clone(), conjunction);
    let stats = measured_payload(&step, &terms);
    let (ok, calls) = mirror_and_neg(&terms, &clause, conjunction);
    assert!(ok, "depth={depth}");
    (calls, clause_identity_model(stats), stats.work)
}
