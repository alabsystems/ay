// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Schema tests for `SetCardNonNegative`.
//!
//! A lemma kind is a licence to believe a clause with no derivation, so the
//! rejections matter more than the acceptance: each one below is a clause that
//! would let a refutation be assembled out of nothing if the schema were loose.

use ay_core::{ProofId, Sort, Symbol, TermId, TermStore};

use super::{
    validate_set_card_empty, validate_set_card_empty_by_assertion, validate_set_card_member_count,
    validate_set_card_member_lower_bound, validate_set_card_non_negative, EmptySetRegistry,
};

fn set_var(terms: &mut TermStore, name: &str) -> TermId {
    terms.mk_var(name, Sort::Uninterpreted("Set".to_string()))
}

fn card_of(terms: &mut TermStore, args: Vec<TermId>) -> TermId {
    terms.mk_app(Symbol::named("set.card"), args, Sort::Int)
}

const STEP: ProofId = ProofId(0);

/// `(<= 0 (set.card s))` over a fresh set variable.
fn card_axiom(terms: &mut TermStore, bound: i64) -> TermId {
    let set = set_var(terms, "s");
    let card = card_of(terms, vec![set]);
    let bound = terms.mk_int(bound.into());
    terms.mk_le(bound, card)
}

#[test]
fn accepts_the_canonical_non_negativity_axiom() {
    let mut terms = TermStore::new();
    let clause = vec![card_axiom(&mut terms, 0)];
    assert!(validate_set_card_non_negative(&terms, STEP, &clause).is_ok());
}

/// The whole point of pinning the bound: `(<= 5 (set.card s))` is FALSE for
/// the empty set, so accepting it would licence an unsound refutation.
#[test]
fn rejects_a_positive_lower_bound() {
    let mut terms = TermStore::new();
    let clause = vec![card_axiom(&mut terms, 5)];
    let error = validate_set_card_non_negative(&terms, STEP, &clause)
        .expect_err("a positive lower bound is not valid for the empty set");
    assert!(format!("{error:?}").contains("exactly 0"), "{error:?}");
}

/// A negative bound is sound but is not the axiom AY emits; the schema is
/// exact so a producer cannot drift without the checker noticing.
#[test]
fn rejects_a_bound_other_than_zero() {
    let mut terms = TermStore::new();
    let clause = vec![card_axiom(&mut terms, -1)];
    assert!(validate_set_card_non_negative(&terms, STEP, &clause).is_err());
}

#[test]
fn rejects_a_non_unit_clause() {
    let mut terms = TermStore::new();
    let axiom = card_axiom(&mut terms, 0);
    let other = terms.mk_var("p", Sort::Bool);

    assert!(validate_set_card_non_negative(&terms, STEP, &[]).is_err());
    assert!(validate_set_card_non_negative(&terms, STEP, &[axiom, other]).is_err());
}

/// Not every integer term is a cardinality. Bounding an arbitrary integer
/// below by zero is plainly false (`x` may be negative).
#[test]
fn rejects_a_non_cardinality_lower_bound() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let zero = terms.mk_int(0.into());
    let clause = vec![terms.mk_le(zero, x)];
    assert!(validate_set_card_non_negative(&terms, STEP, &clause).is_err());
}

/// The bound must be on the LEFT. `(<= (set.card s) 0)` says the set is empty,
/// which is a different -- and generally false -- claim.
#[test]
fn rejects_the_reversed_comparison() {
    let mut terms = TermStore::new();
    let set = set_var(&mut terms, "s");
    let card = card_of(&mut terms, vec![set]);
    let zero = terms.mk_int(0.into());
    let clause = vec![terms.mk_le(card, zero)];
    assert!(validate_set_card_non_negative(&terms, STEP, &clause).is_err());
}

/// A same-named operator with the wrong arity is not the cardinality operator.
#[test]
fn rejects_a_non_unary_card_application() {
    let mut terms = TermStore::new();
    let s = set_var(&mut terms, "s");
    let t = set_var(&mut terms, "t");
    let card = card_of(&mut terms, vec![s, t]);
    let zero = terms.mk_int(0.into());
    let clause = vec![terms.mk_le(zero, card)];
    assert!(validate_set_card_non_negative(&terms, STEP, &clause).is_err());
}

// ---------------------------------------------------------------------------
// SetCardMemberLowerBound
// ---------------------------------------------------------------------------

/// `(ite (select s x) (<= 1 (set.card s)) (<= 0 (set.card s)))`.
fn member_bound(terms: &mut TermStore, card_set: Option<&str>) -> TermId {
    let s = set_var(terms, "s");
    let x = terms.mk_int(1.into());
    let condition = terms.mk_app(Symbol::named("select"), vec![s, x], Sort::Bool);

    // The cardinality may deliberately be taken over a DIFFERENT set.
    let bounded = match card_set {
        None => s,
        Some(name) => set_var(terms, name),
    };
    let card = card_of(terms, vec![bounded]);
    let one = terms.mk_int(1.into());
    let zero = terms.mk_int(0.into());
    let then_branch = terms.mk_le(one, card);
    let else_branch = terms.mk_le(zero, card);
    terms.mk_ite(condition, then_branch, else_branch)
}

#[test]
fn accepts_the_canonical_membership_lower_bound() {
    let mut terms = TermStore::new();
    let clause = vec![member_bound(&mut terms, None)];
    assert!(validate_set_card_member_lower_bound(&terms, STEP, &clause).is_ok());
}

/// The identity of the set IS the axiom. Bounding an UNRELATED set's
/// cardinality by a membership test on `s` is plainly false, so accepting it
/// would licence a refutation out of nothing.
#[test]
fn rejects_a_bound_on_a_different_set() {
    let mut terms = TermStore::new();
    let clause = vec![member_bound(&mut terms, Some("t"))];
    let error = validate_set_card_member_lower_bound(&terms, STEP, &clause)
        .expect_err("the membership test and the cardinality must share a set");
    assert!(format!("{error:?}").contains("SAME set"), "{error:?}");
}

/// The branches are not interchangeable: `x ∉ s` licenses only `|s| >= 0`.
#[test]
fn rejects_swapped_branches() {
    let mut terms = TermStore::new();
    let s = set_var(&mut terms, "s");
    let x = terms.mk_int(1.into());
    let condition = terms.mk_app(Symbol::named("select"), vec![s, x], Sort::Bool);
    let card = card_of(&mut terms, vec![s]);
    let one = terms.mk_int(1.into());
    let zero = terms.mk_int(0.into());
    let then_branch = terms.mk_le(zero, card);
    let else_branch = terms.mk_le(one, card);
    let clause = vec![terms.mk_ite(condition, then_branch, else_branch)];
    assert!(validate_set_card_member_lower_bound(&terms, STEP, &clause).is_err());
}

#[test]
fn rejects_a_non_membership_condition() {
    let mut terms = TermStore::new();
    let s = set_var(&mut terms, "s");
    let condition = terms.mk_var("p", Sort::Bool);
    let card = card_of(&mut terms, vec![s]);
    let one = terms.mk_int(1.into());
    let zero = terms.mk_int(0.into());
    let then_branch = terms.mk_le(one, card);
    let else_branch = terms.mk_le(zero, card);
    let clause = vec![terms.mk_ite(condition, then_branch, else_branch)];
    assert!(validate_set_card_member_lower_bound(&terms, STEP, &clause).is_err());
}

/// Not an ite at all, and not a unit clause.
#[test]
fn rejects_shapes_that_are_not_the_axiom() {
    let mut terms = TermStore::new();
    let plain = card_axiom(&mut terms, 0);
    assert!(validate_set_card_member_lower_bound(&terms, STEP, &[plain]).is_err());
    assert!(validate_set_card_member_lower_bound(&terms, STEP, &[]).is_err());
}

// ---------------------------------------------------------------------------
// SetCardEmpty
// ---------------------------------------------------------------------------

fn card_of_const_array(terms: &mut TermStore, fill: bool) -> TermId {
    let fill = terms.mk_bool(fill);
    let empty = terms.mk_app(
        Symbol::named("const-array"),
        vec![fill],
        Sort::Uninterpreted("Set".to_string()),
    );
    let card = card_of(terms, vec![empty]);
    let zero = terms.mk_int(0.into());
    terms.mk_app(Symbol::named("="), vec![card, zero], Sort::Bool)
}

#[test]
fn accepts_the_empty_set_cardinality_axiom() {
    let mut terms = TermStore::new();
    let clause = vec![card_of_const_array(&mut terms, false)];
    assert!(validate_set_card_empty(&terms, STEP, &clause).is_ok());
}

/// THE soundness case for this kind. A `true` fill is the UNIVERSAL set, whose
/// cardinality is the index sort's size -- infinite over `Int`. Licensing
/// `|universe| = 0` would let a refutation be built out of nothing.
#[test]
fn rejects_the_universal_set() {
    let mut terms = TermStore::new();
    let clause = vec![card_of_const_array(&mut terms, true)];
    let error = validate_set_card_empty(&terms, STEP, &clause)
        .expect_err("a const-array of `true` is the universal set, not the empty one");
    assert!(format!("{error:?}").contains("universal set"), "{error:?}");
}

/// A set that is empty only by ASSERTION is not syntactically empty; licensing
/// it here would need problem context this checker does not receive.
#[test]
fn rejects_a_set_variable() {
    let mut terms = TermStore::new();
    let s = set_var(&mut terms, "s");
    let card = card_of(&mut terms, vec![s]);
    let zero = terms.mk_int(0.into());
    let clause = vec![terms.mk_app(Symbol::named("="), vec![card, zero], Sort::Bool)];
    assert!(validate_set_card_empty(&terms, STEP, &clause).is_err());
}

/// The empty set has cardinality 0 and nothing else.
#[test]
fn rejects_a_non_zero_cardinality_for_the_empty_set() {
    let mut terms = TermStore::new();
    let fill = terms.mk_bool(false);
    let empty = terms.mk_app(
        Symbol::named("const-array"),
        vec![fill],
        Sort::Uninterpreted("Set".to_string()),
    );
    let card = card_of(&mut terms, vec![empty]);
    let two = terms.mk_int(2.into());
    let clause = vec![terms.mk_app(Symbol::named("="), vec![card, two], Sort::Bool)];
    assert!(validate_set_card_empty(&terms, STEP, &clause).is_err());
}

// ---------------------------------------------------------------------------
// SetCardMemberCount
// ---------------------------------------------------------------------------

/// `ite(member i1 s, ite(member i2 s, <= 2 card, <= 1 card),
///                   ite(member i2 s, <= 1 card, <= 0 card))`
///
/// `indices` supplies the two index terms, so a test can make them equal or
/// non-literal to exercise the distinctness rule.
fn counted_tree(terms: &mut TermStore, indices: [TermId; 2]) -> TermId {
    let s = set_var(terms, "s");
    let card = card_of(terms, vec![s]);
    let bound = |terms: &mut TermStore, k: i64| {
        let k = terms.mk_int(k.into());
        terms.mk_le(k, card)
    };
    let two = bound(terms, 2);
    let one_a = bound(terms, 1);
    let one_b = bound(terms, 1);
    let zero = bound(terms, 0);

    let outer = terms.mk_app(Symbol::named("select"), vec![s, indices[0]], Sort::Bool);
    let inner = terms.mk_app(Symbol::named("select"), vec![s, indices[1]], Sort::Bool);
    let then_branch = terms.mk_ite(inner, two, one_a);
    let else_branch = terms.mk_ite(inner, one_b, zero);
    terms.mk_ite(outer, then_branch, else_branch)
}

#[test]
fn accepts_a_counted_membership_tree() {
    let mut terms = TermStore::new();
    let i1 = terms.mk_int(1.into());
    let i2 = terms.mk_int(2.into());
    let clause = vec![counted_tree(&mut terms, [i1, i2])];
    assert!(validate_set_card_member_count(&terms, STEP, &clause).is_ok());
}

/// THE soundness case. Two VARIABLE indices may denote the same element, so
/// counting them separately would licence `|{x}| >= 2`.
#[test]
fn rejects_variable_indices() {
    let mut terms = TermStore::new();
    let i1 = terms.mk_var("i", Sort::Int);
    let i2 = terms.mk_var("j", Sort::Int);
    let clause = vec![counted_tree(&mut terms, [i1, i2])];
    let error = validate_set_card_member_count(&terms, STEP, &clause)
        .expect_err("variable indices could be equal");
    assert!(format!("{error:?}").contains("LITERALS"), "{error:?}");
}

/// The same element counted twice inflates the bound: `1 in s` twice does not
/// give `|s| >= 2`.
///
/// The rejection arrives via the leaf-count check rather than the distinctness
/// rule, because `mk_ite` folds `ite(c, ite(c, A, B), C)` to `ite(c, A, C)` --
/// the duplicate test collapses before the walk can see it, leaving a `<= 2`
/// leaf one membership deep. Either way the forged bound is refused, which is
/// what this pins; the distinctness rule still covers trees the folder leaves
/// intact.
#[test]
fn rejects_a_repeated_index() {
    let mut terms = TermStore::new();
    let i = terms.mk_int(1.into());
    let clause = vec![counted_tree(&mut terms, [i, i])];
    assert!(
        validate_set_card_member_count(&terms, STEP, &clause).is_err(),
        "counting one element twice is not a cardinality bound"
    );
}

/// The leaf counts must match the path: an inflated leaf is exactly the forged
/// bound this schema exists to stop.
#[test]
fn rejects_an_inflated_leaf_count() {
    let mut terms = TermStore::new();
    let s = set_var(&mut terms, "s");
    let card = card_of(&mut terms, vec![s]);
    let i1 = terms.mk_int(1.into());
    let five = terms.mk_int(5.into());
    let zero_k = terms.mk_int(0.into());
    let inflated = terms.mk_le(five, card); // claims |s| >= 5 from ONE member
    let base = terms.mk_le(zero_k, card);
    let condition = terms.mk_app(Symbol::named("select"), vec![s, i1], Sort::Bool);
    let clause = vec![terms.mk_ite(condition, inflated, base)];
    assert!(validate_set_card_member_count(&terms, STEP, &clause).is_err());
}

/// Every membership test must be about the same set.
#[test]
fn rejects_a_tree_mixing_two_sets() {
    let mut terms = TermStore::new();
    let s = set_var(&mut terms, "s");
    let t = set_var(&mut terms, "t");
    let card = card_of(&mut terms, vec![s]);
    let i1 = terms.mk_int(1.into());
    let i2 = terms.mk_int(2.into());
    let one = terms.mk_int(1.into());
    let zero_k = terms.mk_int(0.into());
    let two_k = terms.mk_int(2.into());
    let leaf2 = terms.mk_le(two_k, card);
    let leaf1a = terms.mk_le(one, card);
    let leaf1b = terms.mk_le(one, card);
    let leaf0 = terms.mk_le(zero_k, card);
    let outer = terms.mk_app(Symbol::named("select"), vec![s, i1], Sort::Bool);
    let inner = terms.mk_app(Symbol::named("select"), vec![t, i2], Sort::Bool);
    let then_branch = terms.mk_ite(inner, leaf2, leaf1a);
    let else_branch = terms.mk_ite(inner, leaf1b, leaf0);
    let clause = vec![terms.mk_ite(outer, then_branch, else_branch)];
    assert!(validate_set_card_member_count(&terms, STEP, &clause).is_err());
}

// ---------------------------------------------------------------------------
// SetCardEmptyByAssertion / EmptySetRegistry
// ---------------------------------------------------------------------------

fn empty_literal(terms: &mut TermStore) -> TermId {
    let fill = terms.mk_bool(false);
    terms.mk_app(
        Symbol::named("const-array"),
        vec![fill],
        Sort::Uninterpreted("Set".to_string()),
    )
}

fn card_is_zero(terms: &mut TermStore, set: TermId) -> TermId {
    let card = card_of(terms, vec![set]);
    let zero = terms.mk_int(0.into());
    terms.mk_app(Symbol::named("="), vec![card, zero], Sort::Bool)
}

fn eq(terms: &mut TermStore, lhs: TermId, rhs: TermId) -> TermId {
    terms.mk_app(Symbol::named("="), vec![lhs, rhs], Sort::Bool)
}

#[test]
fn accepts_a_set_the_problem_asserts_empty() {
    let mut terms = TermStore::new();
    let s = set_var(&mut terms, "s");
    let empty = empty_literal(&mut terms);
    let assertion = eq(&mut terms, s, empty);
    let registry = EmptySetRegistry::collect(&terms, &[assertion]);

    let clause = vec![card_is_zero(&mut terms, s)];
    assert!(validate_set_card_empty_by_assertion(&terms, STEP, &clause, Some(&registry)).is_ok());
}

/// The registry closes over CHAINS: `t = s` and `s = empty` makes `t` empty.
#[test]
fn follows_a_chain_of_asserted_equalities() {
    let mut terms = TermStore::new();
    let s = set_var(&mut terms, "s");
    let t = set_var(&mut terms, "t");
    let empty = empty_literal(&mut terms);
    let a1 = eq(&mut terms, t, s);
    let a2 = eq(&mut terms, s, empty);
    let registry = EmptySetRegistry::collect(&terms, &[a1, a2]);

    let clause = vec![card_is_zero(&mut terms, t)];
    assert!(validate_set_card_empty_by_assertion(&terms, STEP, &clause, Some(&registry)).is_ok());
}

#[test]
fn metered_registry_closes_reverse_chain_in_linear_work() {
    let mut terms = TermStore::new();
    let chain_len = 128_usize;
    let sets: Vec<TermId> = (0..=chain_len)
        .map(|index| set_var(&mut terms, &format!("linear_set_{index}")))
        .collect();
    let empty = empty_literal(&mut terms);
    // This order forced the old repeated-scan fixpoint to discover exactly one
    // predecessor per pass: O(chain_len^2).
    let mut assertions = Vec::new();
    for index in 0..chain_len {
        assertions.push(eq(&mut terms, sets[index], sets[index + 1]));
    }
    assertions.push(eq(&mut terms, sets[chain_len], empty));

    let mut work = 0_usize;
    let mut bytes = 0_usize;
    let registry = EmptySetRegistry::collect_with_progress(
        &terms,
        &assertions,
        &mut |work_delta, byte_delta| {
            work += work_delta;
            bytes += byte_delta;
            true
        },
    )
    .expect("a finite equality chain should fit an unbounded envelope");

    assert!(registry.is_known_empty(&terms, sets[0]));
    assert!(work < 20 * assertions.len(), "work was {work}");
    assert!(bytes > 0);
}

/// THE soundness case for the registry. An equality under a NEGATION is not
/// unconditional -- `(assert (not (= s empty)))` says the opposite -- so it
/// must never seed the registry.
#[test]
fn ignores_an_equality_that_is_not_a_top_level_assertion() {
    let mut terms = TermStore::new();
    let s = set_var(&mut terms, "s");
    let empty = empty_literal(&mut terms);
    let inner = eq(&mut terms, s, empty);
    let negated = terms.mk_not_raw(inner);
    let registry = EmptySetRegistry::collect(&terms, &[negated]);

    let clause = vec![card_is_zero(&mut terms, s)];
    assert!(
        validate_set_card_empty_by_assertion(&terms, STEP, &clause, Some(&registry)).is_err(),
        "a negated equality asserts the set is NOT empty"
    );
}

/// No problem assertions means no evidence: this kind is not a tautology.
#[test]
fn fails_closed_without_a_registry() {
    let mut terms = TermStore::new();
    let s = set_var(&mut terms, "s");
    let clause = vec![card_is_zero(&mut terms, s)];
    assert!(validate_set_card_empty_by_assertion(&terms, STEP, &clause, None).is_err());
}

/// A set the problem says nothing about is not empty.
#[test]
fn rejects_an_unconstrained_set() {
    let mut terms = TermStore::new();
    let s = set_var(&mut terms, "s");
    let registry = EmptySetRegistry::collect(&terms, &[]);
    let clause = vec![card_is_zero(&mut terms, s)];
    assert!(validate_set_card_empty_by_assertion(&terms, STEP, &clause, Some(&registry)).is_err());
}
