// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Schema tests for `SetCardChainRecurrence`.
//!
//! The rejections are the point. Each near-miss below is falsifiable, and
//! admitting any one of them would let a refutation be assembled out of
//! nothing — most sharply `|{x, y}| = 2`, which is simply false when `x = y`.
//!
//! The `membership_walk` section is the sharpest part of the file. The
//! membership decision RETURNS EARLY at the first write on the probed index, so
//! it can report a decided membership having never looked at the chain's root.
//! If that one walk were also relied on for the empty-root requirement, the
//! schema would accept chains rooted at the universal set and at a bare set
//! variable — and the accepted clause would not be a theorem. Those tests probe
//! an index the OUTERMOST write touches, so the walk really does short-circuit,
//! and they fail unless [`super::is_empty_rooted_chain`] is consulted
//! separately.

use ay_core::{ArraySort, ProofId, Sort, Symbol, TermId, TermStore};

use super::{decide_membership, is_empty_rooted_chain, validate_set_card_chain_recurrence};

const STEP: ProofId = ProofId(0);

fn set_sort() -> Sort {
    Sort::Array(Box::new(ArraySort {
        index_sort: Sort::Int,
        element_sort: Sort::Bool,
    }))
}

/// The constant-`false` array: the syntactic empty set, and the only legal
/// root of a chain this schema will certify.
fn empty_set(terms: &mut TermStore) -> TermId {
    let f = terms.mk_bool(false);
    terms.mk_const_array(Sort::Int, f)
}

/// The constant-`true` array: the UNIVERSAL set. Its cardinality is the index
/// sort's size, so it must never serve as a chain root.
fn universe(terms: &mut TermStore) -> TermId {
    let t = terms.mk_bool(true);
    terms.mk_const_array(Sort::Int, t)
}

fn store(terms: &mut TermStore, base: TermId, index: TermId, value: bool) -> TermId {
    let v = terms.mk_bool(value);
    let sort = terms.sort(base).clone();
    terms.mk_app(Symbol::named("store"), [base, index, v], sort)
}

fn card(terms: &mut TermStore, set: TermId) -> TermId {
    terms.mk_app(Symbol::named("set.card"), [set], Sort::Int)
}

fn int(terms: &mut TermStore, value: i64) -> TermId {
    terms.mk_int(value.into())
}

/// `(= (set.card (store base e v)) (+ (set.card base) delta))`, the exact
/// spelling the emitter produces for a one-write recurrence step.
fn recurrence_clause(
    terms: &mut TermStore,
    base: TermId,
    index: TermId,
    value: bool,
    delta: i64,
) -> Vec<TermId> {
    let outer_set = store(terms, base, index, value);
    let outer = card(terms, outer_set);
    let inner = card(terms, base);
    let rhs = if delta == 0 {
        inner
    } else {
        let magnitude = int(terms, delta.abs());
        if delta > 0 {
            terms.mk_add(vec![inner, magnitude])
        } else {
            terms.mk_sub(vec![inner, magnitude])
        }
    };
    vec![terms.mk_eq(outer, rhs)]
}

// ---------------------------------------------------------------------------
// Accepted: the definitional recurrence over an empty-rooted chain.
// ---------------------------------------------------------------------------

#[test]
fn accepts_the_empty_base_case_in_both_orientations() {
    let mut terms = TermStore::new();
    let empty = empty_set(&mut terms);
    let c = card(&mut terms, empty);
    let zero = int(&mut terms, 0);
    let forward = terms.mk_eq(c, zero);
    let reversed = terms.mk_eq(zero, c);
    assert!(validate_set_card_chain_recurrence(&terms, STEP, &[forward]).is_ok());
    assert!(validate_set_card_chain_recurrence(&terms, STEP, &[reversed]).is_ok());
}

#[test]
fn accepts_inserting_an_absent_element() {
    let mut terms = TermStore::new();
    let empty = empty_set(&mut terms);
    let x = int(&mut terms, 1);
    let clause = recurrence_clause(&mut terms, empty, x, true, 1);
    assert!(validate_set_card_chain_recurrence(&terms, STEP, &clause).is_ok());
}

/// Re-inserting an element the chain already wrote must NOT grow the count.
#[test]
fn accepts_inserting_a_present_element_without_growing_the_count() {
    let mut terms = TermStore::new();
    let empty = empty_set(&mut terms);
    let x = int(&mut terms, 1);
    let once = store(&mut terms, empty, x, true);
    let clause = recurrence_clause(&mut terms, once, x, true, 0);
    assert!(validate_set_card_chain_recurrence(&terms, STEP, &clause).is_ok());
}

#[test]
fn accepts_removing_a_present_element() {
    let mut terms = TermStore::new();
    let empty = empty_set(&mut terms);
    let x = int(&mut terms, 1);
    let once = store(&mut terms, empty, x, true);
    let clause = recurrence_clause(&mut terms, once, x, false, -1);
    assert!(validate_set_card_chain_recurrence(&terms, STEP, &clause).is_ok());
}

/// Removing an element that is not there must NOT shrink the count. The
/// distinctness of `1` and `2` is re-derived from the literals.
#[test]
fn accepts_removing_an_absent_element_without_shrinking_the_count() {
    let mut terms = TermStore::new();
    let empty = empty_set(&mut terms);
    let one_index = int(&mut terms, 1);
    let two_index = int(&mut terms, 2);
    let once = store(&mut terms, empty, one_index, true);
    let clause = recurrence_clause(&mut terms, once, two_index, false, 0);
    assert!(validate_set_card_chain_recurrence(&terms, STEP, &clause).is_ok());
}

// ---------------------------------------------------------------------------
// The membership walk short-circuits, so it CANNOT establish the empty root.
//
// Every clause in this section probes an index the OUTERMOST write touches, so
// `decide_membership` answers before it has seen a single deeper link. Each
// clause is falsified by the interpretation `card(X) = |X|` for finite `X` and
// `card(X) = N` for infinite `X`, `N` above every literal-membership count:
// that interpretation satisfies `card >= 0`, the membership lower bound,
// `card(empty) = 0` and the finite-chain recurrence, and reads each clause
// below as `N = N + 1` or `N = N - 1`.
// ---------------------------------------------------------------------------

/// The separation itself, stated directly: on `(store U 5 false)` the
/// membership walk answers `Some(false)` from the outermost write while the
/// UNIVERSAL root sits unexamined underneath, and the root test — which is what
/// the schema actually relies on — says `false`.
///
/// If these two ever agree, the schema has lost its finiteness side condition.
#[test]
fn the_membership_walk_answers_without_reaching_the_root() {
    let mut terms = TermStore::new();
    let infinite_root = universe(&mut terms);
    let five = int(&mut terms, 5);
    let chain = store(&mut terms, infinite_root, five, false);

    // Short-circuits at the outermost write: decided, root never inspected.
    assert_eq!(decide_membership(&terms, chain, five), Some(false));
    // The independent obligation, which is the one that matters.
    assert!(!is_empty_rooted_chain(&terms, chain));
}

/// The same short-circuit on a chain the schema DOES accept, so the early
/// return above is not a quirk of the universal root: it is the normal path.
#[test]
fn the_membership_walk_short_circuits_on_accepted_chains_too() {
    let mut terms = TermStore::new();
    let empty = empty_set(&mut terms);
    let five = int(&mut terms, 5);
    let chain = store(&mut terms, empty, five, true);
    assert_eq!(decide_membership(&terms, chain, five), Some(true));
    assert!(is_empty_rooted_chain(&terms, chain));
}

/// `|U| = |U \ {5}| + 1` reads `N = N + 1` under the infinite-card
/// interpretation. The membership walk short-circuits at the outer `false`
/// write and reports "absent", so ONLY the independent root test rejects this.
#[test]
fn rejects_an_increment_whose_membership_walk_stops_at_the_universal_root() {
    let mut terms = TermStore::new();
    let infinite_root = universe(&mut terms);
    let five = int(&mut terms, 5);
    let base = store(&mut terms, infinite_root, five, false);
    assert_eq!(decide_membership(&terms, base, five), Some(false));

    let clause = recurrence_clause(&mut terms, base, five, true, 1);
    assert!(validate_set_card_chain_recurrence(&terms, STEP, &clause).is_err());
}

/// `|U \ {5}| = |U| - 1` reads `N = N - 1`. The membership walk short-circuits
/// at the outer `true` write and reports "present".
#[test]
fn rejects_a_decrement_whose_membership_walk_stops_at_the_universal_root() {
    let mut terms = TermStore::new();
    let infinite_root = universe(&mut terms);
    let five = int(&mut terms, 5);
    let base = store(&mut terms, infinite_root, five, true);
    assert_eq!(decide_membership(&terms, base, five), Some(true));

    let clause = recurrence_clause(&mut terms, base, five, false, -1);
    assert!(validate_set_card_chain_recurrence(&terms, STEP, &clause).is_err());
}

/// A bare set VARIABLE may denote an infinite set, so the same two clauses are
/// unlicensed over it. Again the membership walk short-circuits above the root.
#[test]
fn rejects_an_increment_whose_membership_walk_stops_at_a_set_variable_root() {
    let mut terms = TermStore::new();
    let opaque_root = terms.mk_var("s", set_sort());
    let five = int(&mut terms, 5);
    let base = store(&mut terms, opaque_root, five, false);
    assert_eq!(decide_membership(&terms, base, five), Some(false));

    let clause = recurrence_clause(&mut terms, base, five, true, 1);
    assert!(validate_set_card_chain_recurrence(&terms, STEP, &clause).is_err());
}

#[test]
fn rejects_a_decrement_whose_membership_walk_stops_at_a_set_variable_root() {
    let mut terms = TermStore::new();
    let opaque_root = terms.mk_var("s", set_sort());
    let five = int(&mut terms, 5);
    let base = store(&mut terms, opaque_root, five, true);
    assert_eq!(decide_membership(&terms, base, five), Some(true));

    let clause = recurrence_clause(&mut terms, base, five, false, -1);
    assert!(validate_set_card_chain_recurrence(&terms, STEP, &clause).is_err());
}

/// The bad root can also be buried: the membership walk still stops at the
/// outermost write, so depth does not rescue the missing root check.
#[test]
fn rejects_an_increment_whose_membership_walk_stops_above_a_buried_bad_root() {
    let mut terms = TermStore::new();
    let infinite_root = universe(&mut terms);
    let seven = int(&mut terms, 7);
    let five = int(&mut terms, 5);
    let deeper = store(&mut terms, infinite_root, seven, true);
    let base = store(&mut terms, deeper, five, false);
    assert_eq!(decide_membership(&terms, base, five), Some(false));

    let clause = recurrence_clause(&mut terms, base, five, true, 1);
    assert!(validate_set_card_chain_recurrence(&terms, STEP, &clause).is_err());
}

/// An opaque array-valued term (here a `select` out of an array of sets) is no
/// more known to be finite than a variable is.
#[test]
fn rejects_a_chain_rooted_at_an_opaque_array_term() {
    let mut terms = TermStore::new();
    let nested_sort = Sort::Array(Box::new(ArraySort {
        index_sort: Sort::Int,
        element_sort: set_sort(),
    }));
    let sets = terms.mk_var("sets", nested_sort);
    let zero = int(&mut terms, 0);
    let opaque_root = terms.mk_app(Symbol::named("select"), [sets, zero], set_sort());
    let five = int(&mut terms, 5);
    let base = store(&mut terms, opaque_root, five, false);
    assert_eq!(decide_membership(&terms, base, five), Some(false));

    let clause = recurrence_clause(&mut terms, base, five, true, 1);
    assert!(validate_set_card_chain_recurrence(&terms, STEP, &clause).is_err());
}

// ---------------------------------------------------------------------------
// Other rejected near-misses.
// ---------------------------------------------------------------------------

/// THE load-bearing rejection. Two SYMBOLIC indices may denote the same
/// element, so `|{x, y}| = |{x}| + 1` is false when `x = y`. The chain walk
/// steps past a write only for distinct LITERALS, so this is undecidable and
/// must fail closed.
#[test]
fn rejects_a_count_increment_over_two_symbolic_indices() {
    let mut terms = TermStore::new();
    let empty = empty_set(&mut terms);
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let once = store(&mut terms, empty, x, true);
    let clause = recurrence_clause(&mut terms, once, y, true, 1);
    assert!(validate_set_card_chain_recurrence(&terms, STEP, &clause).is_err());
}

/// A chain rooted at a set VARIABLE is not known to be finite and has no
/// structural count, so the recurrence is not licensed over it.
#[test]
fn rejects_a_chain_rooted_at_a_set_variable() {
    let mut terms = TermStore::new();
    let base = terms.mk_var("s", set_sort());
    let x = int(&mut terms, 1);
    let clause = recurrence_clause(&mut terms, base, x, true, 1);
    assert!(validate_set_card_chain_recurrence(&terms, STEP, &clause).is_err());
}

/// The UNIVERSAL set is infinite over `Int`; rooting a chain there would
/// licence a finite cardinality for it.
#[test]
fn rejects_a_chain_rooted_at_the_universal_set() {
    let mut terms = TermStore::new();
    let base = universe(&mut terms);
    let x = int(&mut terms, 1);
    let clause = recurrence_clause(&mut terms, base, x, true, 1);
    assert!(validate_set_card_chain_recurrence(&terms, STEP, &clause).is_err());
}

/// The universal set's own base case: `|U| = 0` is false, and the base-case
/// arm must not treat a `true` fill as empty.
#[test]
fn rejects_a_zero_base_case_for_the_universal_set() {
    let mut terms = TermStore::new();
    let base = universe(&mut terms);
    let c = card(&mut terms, base);
    let zero = int(&mut terms, 0);
    let clause = vec![terms.mk_eq(c, zero)];
    assert!(validate_set_card_chain_recurrence(&terms, STEP, &clause).is_err());
}

/// `|∅ ∪ {x}| = |∅| + 2` is false; only an increment of exactly one is
/// licensed.
#[test]
fn rejects_an_increment_of_two() {
    let mut terms = TermStore::new();
    let empty = empty_set(&mut terms);
    let x = int(&mut terms, 1);
    let clause = recurrence_clause(&mut terms, empty, x, true, 2);
    assert!(validate_set_card_chain_recurrence(&terms, STEP, &clause).is_err());
}

/// Inserting an ABSENT element must grow the count, so equating the two
/// cardinalities is false.
#[test]
fn rejects_an_unchanged_count_when_inserting_an_absent_element() {
    let mut terms = TermStore::new();
    let empty = empty_set(&mut terms);
    let x = int(&mut terms, 1);
    let clause = recurrence_clause(&mut terms, empty, x, true, 0);
    assert!(validate_set_card_chain_recurrence(&terms, STEP, &clause).is_err());
}

/// Removing a PRESENT element must shrink the count; claiming it is unchanged
/// is false.
#[test]
fn rejects_an_unchanged_count_when_removing_a_present_element() {
    let mut terms = TermStore::new();
    let empty = empty_set(&mut terms);
    let x = int(&mut terms, 1);
    let once = store(&mut terms, empty, x, true);
    let clause = recurrence_clause(&mut terms, once, x, false, 0);
    assert!(validate_set_card_chain_recurrence(&terms, STEP, &clause).is_err());
}

/// The recurrence must relate the outer count to the count of the chain's OWN
/// immediate base, not some unrelated set.
#[test]
fn rejects_a_recurrence_against_an_unrelated_inner_set() {
    let mut terms = TermStore::new();
    let empty = empty_set(&mut terms);
    let other = terms.mk_var("other", set_sort());
    let x = int(&mut terms, 1);
    let singleton = store(&mut terms, empty, x, true);
    let outer = card(&mut terms, singleton);
    let inner = card(&mut terms, other);
    let one = int(&mut terms, 1);
    let sum = terms.mk_add(vec![inner, one]);
    let clause = vec![terms.mk_eq(outer, sum)];
    assert!(validate_set_card_chain_recurrence(&terms, STEP, &clause).is_err());
}

/// A non-zero base case for the empty set is false and would let any count be
/// manufactured.
#[test]
fn rejects_a_non_zero_empty_base_case() {
    let mut terms = TermStore::new();
    let empty = empty_set(&mut terms);
    let c = card(&mut terms, empty);
    let one = int(&mut terms, 1);
    let clause = vec![terms.mk_eq(c, one)];
    assert!(validate_set_card_chain_recurrence(&terms, STEP, &clause).is_err());
}

/// A NEGATED recurrence is the opposite claim.
#[test]
fn rejects_the_negated_recurrence() {
    let mut terms = TermStore::new();
    let empty = empty_set(&mut terms);
    let c = card(&mut terms, empty);
    let zero = int(&mut terms, 0);
    let equality = terms.mk_eq(c, zero);
    let clause = vec![terms.mk_not(equality)];
    assert!(validate_set_card_chain_recurrence(&terms, STEP, &clause).is_err());
}

#[test]
fn rejects_a_multi_literal_clause() {
    let mut terms = TermStore::new();
    let empty = empty_set(&mut terms);
    let c = card(&mut terms, empty);
    let zero = int(&mut terms, 0);
    let equality = terms.mk_eq(c, zero);
    assert!(validate_set_card_chain_recurrence(&terms, STEP, &[equality, equality]).is_err());
}
