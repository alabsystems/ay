// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! End-to-end executor tests for the native finite-set theory.
//!
//! These drive full SMT-LIB through `parse` + `Executor::execute_all`, so they
//! exercise the whole wired path: `(Set T)` sort + `set.*` elaboration → logic
//! routing (`QF_SETLIA`) → `UfSetLiaSolver` → verdict. They assert that
//! previously-MBQI-needing set facts now decide, and that out-of-fragment
//! obligations fail closed to `unknown` (never a guessed sat/unsat).

use crate::Executor;
use ay_frontend::parse;

fn solve(smt: &str) -> String {
    let commands = parse(smt).expect("parse failed");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute_all failed");
    outputs.join("\n")
}

fn verdict(output: &str) -> Option<&str> {
    output
        .lines()
        .map(str::trim)
        .find(|line| matches!(*line, "sat" | "unsat" | "unknown"))
}

// ---------------------------------------------------------------------------
// In-fragment facts decide without MBQI.
// ---------------------------------------------------------------------------

/// `s subset s` is valid: its negation is UNSAT. Decided by reflexivity, no
/// quantifier instantiation.
#[test]
fn subset_self_negation_is_unsat() {
    let smt = r#"
(set-logic QF_SET)
(declare-const s (Set Int))
(assert (not (set.subset s s)))
(check-sat)
"#;
    assert_eq!(verdict(&solve(smt)), Some("unsat"));
}

/// `e ∈ s`, `e ∉ t`, but `subset(s, t)` asserted — UNSAT via one ground witness.
#[test]
fn subset_refuted_by_ground_witness_is_unsat() {
    let smt = r#"
(set-logic QF_SET)
(declare-const s (Set Int))
(declare-const t (Set Int))
(assert (set.member 7 s))
(assert (not (set.member 7 t)))
(assert (set.subset s t))
(check-sat)
"#;
    assert_eq!(verdict(&solve(smt)), Some("unsat"));
}

/// Subset TRANSITIVITY over symbolic sets (#set-subset-transitivity-wrong-sat):
/// `A⊆B ∧ B⊆C ∧ ¬(A⊆C)` is UNSAT. Regression: this previously returned a
/// spurious `sat` with the empty model `A=B=C=∅` (where `¬(A⊆C)` is FALSE) —
/// a false-SAT. The fix instantiates the subset definition at a fresh witness
/// for the negated atom, chaining `w∈A → w∈B → w∈C` against `w∉C`.
#[test]
fn subset_transitivity_three_chain_is_unsat() {
    let smt = r#"
(set-logic QF_SET)
(declare-const a (Set Int))
(declare-const b (Set Int))
(declare-const c (Set Int))
(assert (set.subset a b))
(assert (set.subset b c))
(assert (not (set.subset a c)))
(check-sat)
"#;
    assert_eq!(verdict(&solve(smt)), Some("unsat"));
}

/// Four-set transitivity chain `A⊆B ∧ B⊆C ∧ C⊆D ∧ ¬(A⊆D)` is UNSAT — the
/// witness propagates through both intermediate subsets.
#[test]
fn subset_transitivity_four_chain_is_unsat() {
    let smt = r#"
(set-logic QF_SET)
(declare-const a (Set Int))
(declare-const b (Set Int))
(declare-const c (Set Int))
(declare-const d (Set Int))
(assert (set.subset a b))
(assert (set.subset b c))
(assert (set.subset c d))
(assert (not (set.subset a d)))
(check-sat)
"#;
    assert_eq!(verdict(&solve(smt)), Some("unsat"));
}

/// A genuinely-satisfiable negated subset must STAY sat after the witness fix:
/// `¬(A⊆B)` alone has the real model where some `w∈A, w∉B`. No false-UNSAT.
#[test]
fn negated_subset_alone_stays_sat() {
    let smt = r#"
(set-logic QF_SET)
(declare-const a (Set Int))
(declare-const b (Set Int))
(assert (not (set.subset a b)))
(check-sat)
"#;
    assert_eq!(verdict(&solve(smt)), Some("sat"));
}

/// No spurious chain: `A⊆B ∧ ¬(B⊆C)` is SAT (there is no `A⊆C`-style closure to
/// force). Guards against the witness machinery over-propagating to a false
/// UNSAT.
#[test]
fn subset_no_false_chain_is_sat() {
    let smt = r#"
(set-logic QF_SET)
(declare-const a (Set Int))
(declare-const b (Set Int))
(declare-const c (Set Int))
(assert (set.subset a b))
(assert (not (set.subset b c)))
(check-sat)
"#;
    assert_eq!(verdict(&solve(smt)), Some("sat"));
}

/// `e ∈ (set.insert e s)` is valid (store read-through): negation is UNSAT.
#[test]
fn member_of_insert_is_unsat_to_negate() {
    let smt = r#"
(set-logic QF_SET)
(declare-const s (Set Int))
(assert (not (set.member 3 (set.insert 3 s))))
(check-sat)
"#;
    assert_eq!(verdict(&solve(smt)), Some("unsat"));
}

/// `e ∉ empty`: asserting `e ∈ empty` is UNSAT (const-false array read).
#[test]
fn member_of_empty_is_unsat() {
    let smt = r#"
(set-logic QF_SET)
(assert (set.member 1 (as set.empty (Set Int))))
(check-sat)
"#;
    assert_eq!(verdict(&solve(smt)), Some("unsat"));
}

/// `card(empty) = 0`: asserting `card(empty) = 2` is UNSAT (injected axiom).
#[test]
fn card_empty_is_zero() {
    let smt = r#"
(set-logic QF_SETLIA)
(assert (= (set.card (as set.empty (Set Int))) 2))
(check-sat)
"#;
    assert_eq!(verdict(&solve(smt)), Some("unsat"));
}

/// `card(s) >= 0` is injected for every card term: `card(s) = -1` is UNSAT.
#[test]
fn card_nonnegative_for_every_card() {
    let smt = r#"
(set-logic QF_SETLIA)
(declare-const s (Set Int))
(assert (= (set.card s) (- 1)))
(check-sat)
"#;
    assert_eq!(verdict(&solve(smt)), Some("unsat"));
}

/// A consistent cardinality constraint is SAT.
#[test]
fn card_positive_is_sat() {
    let smt = r#"
(set-logic QF_SETLIA)
(declare-const s (Set Int))
(assert (= (set.card s) 5))
(check-sat)
"#;
    assert_eq!(verdict(&solve(smt)), Some("sat"));
}

/// `e ∈ s` with `s subset t` and `e ∉ t` — UNSAT, with auto-detected logic
/// (no explicit set-logic). Confirms `has_set_ops` routing.
#[test]
fn auto_detected_logic_routes_to_set_solver() {
    let smt = r#"
(declare-const s (Set Int))
(declare-const t (Set Int))
(assert (set.subset s t))
(assert (set.member 9 s))
(assert (not (set.member 9 t)))
(check-sat)
"#;
    assert_eq!(verdict(&solve(smt)), Some("unsat"));
}

// ---------------------------------------------------------------------------
// Set ops over BitVector-sorted elements route to the native set theory.
//
// deductive-checks encodes `Set<i32>` as `Array(BV32 -> Bool)` and emits `set.subset` /
// `set.card`. The membership carrier makes both `has_arrays` and `has_bv` true;
// before the set-op precedence fix these auto-detected to QF_ABV and the
// card/subset symbols degraded to opaque UF (unsound). They must instead route
// to QF_SETLIA and decide. Membership stays `select` over `Array(BV -> Bool)`;
// the card/subset saturation rules are sort-agnostic over the element sort.
// ---------------------------------------------------------------------------

/// `s subset s` over BV(32)-element sets is valid: its negation is UNSAT.
/// No explicit set-logic — exercises the auto-detection (`infer_logic`) path.
#[test]
fn bv_element_subset_self_negation_is_unsat() {
    let smt = r#"
(declare-const s (Set (_ BitVec 32)))
(assert (not (set.subset s s)))
(check-sat)
"#;
    assert_eq!(verdict(&solve(smt)), Some("unsat"));
}

/// `card(empty) = 0` over BV(32)-element sets: asserting `card(empty) = 2` is
/// UNSAT via the injected ground axiom. Auto-detected logic.
#[test]
fn bv_element_card_empty_is_zero() {
    let smt = r#"
(assert (= (set.card (as set.empty (Set (_ BitVec 32)))) 2))
(check-sat)
"#;
    assert_eq!(verdict(&solve(smt)), Some("unsat"));
}

/// Ground-witness subset refutation over BV(32) elements: `e ∈ s`, `e ∉ t`,
/// yet `subset(s, t)` asserted — UNSAT. Membership over the BV carrier is
/// decided by the array solver; auto-detected logic routes to the set theory.
#[test]
fn bv_element_subset_refuted_by_ground_witness_is_unsat() {
    let smt = r#"
(declare-const s (Set (_ BitVec 32)))
(declare-const t (Set (_ BitVec 32)))
(assert (set.member (_ bv7 32) s))
(assert (not (set.member (_ bv7 32) t)))
(assert (set.subset s t))
(check-sat)
"#;
    assert_eq!(verdict(&solve(smt)), Some("unsat"));
}

// ---------------------------------------------------------------------------
// Structural cardinality over store chains (set.singleton / set.insert /
// set.remove elaborated to `store` over the const-false membership carrier).
//
// These exercise the definitional recurrence injected by
// `collect_set_card_axioms`:
//   card(store(s,e,true))  = card(s) + ite(member(s,e), 0, 1)   (insert)
//   card(store(s,e,false)) = card(s) − ite(member(s,e), 1, 0)   (remove)
// with base card(const-false) = 0. Coverage is restricted to chains whose
// per-level membership folds to a Boolean constant (singletons, single inserts,
// concrete-index nested chains); symbolic non-folding chains and variable-base
// chains stay fail-closed `unknown` (never a guessed/wrong verdict).
// ---------------------------------------------------------------------------

/// `card(set.singleton x) = 1` is SAT (the singleton has exactly one element).
#[test]
fn card_singleton_is_one_sat() {
    let smt = r#"
(declare-const x Int)
(assert (= (set.card (set.singleton x)) 1))
(check-sat)
"#;
    assert_eq!(verdict(&solve(smt)), Some("sat"));
}

/// `card(set.singleton x) = 0` is UNSAT (the round-3 wrong-`sat` regression:
/// MUST be unsat, never sat).
#[test]
fn card_singleton_eq_zero_is_unsat() {
    let smt = r#"
(declare-const x Int)
(assert (= (set.card (set.singleton x)) 0))
(check-sat)
"#;
    assert_eq!(verdict(&solve(smt)), Some("unsat"));
}

/// `card(set.singleton x) = 2` is UNSAT (a singleton cannot have two elements).
#[test]
fn card_singleton_eq_two_is_unsat() {
    let smt = r#"
(declare-const x Int)
(assert (= (set.card (set.singleton x)) 2))
(check-sat)
"#;
    assert_eq!(verdict(&solve(smt)), Some("unsat"));
}

/// `card(set.singleton x) > 1` is UNSAT; `>= 1` is SAT (soundness bounds).
#[test]
fn card_singleton_bounds() {
    let gt = r#"
(declare-const x Int)
(assert (> (set.card (set.singleton x)) 1))
(check-sat)
"#;
    assert_eq!(verdict(&solve(gt)), Some("unsat"));
    let ge = r#"
(declare-const x Int)
(assert (>= (set.card (set.singleton x)) 1))
(check-sat)
"#;
    assert_eq!(verdict(&solve(ge)), Some("sat"));
}

/// Inserting the same element twice does not grow the cardinality:
/// `card(set.insert x (set.singleton x)) = 2` is UNSAT (the count is 1).
#[test]
fn card_insert_duplicate_element_is_one() {
    let smt = r#"
(declare-const x Int)
(assert (= (set.card (set.insert x (set.singleton x))) 2))
(check-sat)
"#;
    assert_eq!(verdict(&solve(smt)), Some("unsat"));
}

/// Two concrete distinct inserts over the empty set yield cardinality 2:
/// `= 2` is SAT and `= 1` is UNSAT.
#[test]
fn card_two_distinct_concrete_inserts_is_two() {
    let two = r#"
(assert (= (set.card (set.insert 2 (set.singleton 1))) 2))
(check-sat)
"#;
    assert_eq!(verdict(&solve(two)), Some("sat"));
    let one = r#"
(assert (= (set.card (set.insert 2 (set.singleton 1))) 1))
(check-sat)
"#;
    assert_eq!(verdict(&solve(one)), Some("unsat"));
}

/// `set.remove` semantics over the empty set / a singleton:
/// removing from empty stays 0; removing the present element gives 0;
/// removing an absent element is a no-op (stays 1).
#[test]
fn card_remove_semantics() {
    let from_empty = r#"
(declare-const x Int)
(assert (= (set.card (set.remove x (as set.empty (Set Int)))) 1))
(check-sat)
"#;
    assert_eq!(verdict(&solve(from_empty)), Some("unsat"));
    let remove_present = r#"
(assert (= (set.card (set.remove 1 (set.singleton 1))) 0))
(check-sat)
"#;
    assert_eq!(verdict(&solve(remove_present)), Some("sat"));
    let remove_absent = r#"
(assert (= (set.card (set.remove 2 (set.singleton 1))) 0))
(check-sat)
"#;
    assert_eq!(verdict(&solve(remove_absent)), Some("unsat"));
}

/// Soundness fail-closed: `card` over an insert into a *variable* set is not
/// structurally counted (the inner `card(s)` is opaque), so it stays `unknown`
/// rather than risk the round-3 wrong-`sat` (e.g. picking member=true, card=0).
#[test]
fn card_insert_over_variable_set_is_fail_closed_unknown() {
    let smt = r#"
(set-logic QF_SETLIA)
(declare-const s (Set Int))
(declare-const y Int)
(assert (= (set.card (set.insert y s)) 0))
(check-sat)
"#;
    assert_eq!(verdict(&solve(smt)), Some("unknown"));
}

/// Soundness fail-closed: a `card` over a *symbolic* two-level insert chain
/// (membership does not fold to a constant) stays `unknown` — sound, not a
/// guessed verdict.
#[test]
fn card_symbolic_nested_insert_is_fail_closed_unknown() {
    let smt = r#"
(set-logic QF_SETLIA)
(declare-const x Int)
(declare-const y Int)
(assert (= (set.card (set.insert y (set.singleton x))) 2))
(check-sat)
"#;
    assert_eq!(verdict(&solve(smt)), Some("unknown"));
}

// ---------------------------------------------------------------------------
// Aliased-variable cardinality (#set-card-aliased-wrong-sat).
//
// A `set.card` over a set VARIABLE that is equated by `(= s <set-expr>)` to a
// concrete set expression must be tied to that expression's structural count —
// not left bounded only by the `card >= 0` bridge (which used to admit a wrong
// `sat`, e.g. a positive cardinality for `s = empty`). The card argument is
// resolved through the alias chain; covered (empty-rooted) resolutions decide,
// uncovered (variable-rooted) ones fail closed to `unknown`.
// ---------------------------------------------------------------------------

/// `(= s empty)` then `card(s) = 1` is UNSAT (the empty set has cardinality 0).
/// Previously a wrong `sat`: `card(s)` was bounded only by `card(s) >= 0`.
#[test]
fn card_of_var_aliased_to_empty_is_zero() {
    let one = r#"
(set-logic ALL)
(declare-const s (Set Int))
(assert (= s (as set.empty (Set Int))))
(assert (= (set.card s) 1))
(check-sat)
"#;
    assert_eq!(verdict(&solve(one)), Some("unsat"));
    let positive = r#"
(set-logic ALL)
(declare-const s (Set Int))
(assert (= s (as set.empty (Set Int))))
(assert (> (set.card s) 0))
(check-sat)
"#;
    assert_eq!(verdict(&solve(positive)), Some("unsat"));
    let zero = r#"
(set-logic ALL)
(declare-const s (Set Int))
(assert (= s (as set.empty (Set Int))))
(assert (= (set.card s) 0))
(check-sat)
"#;
    assert_eq!(verdict(&solve(zero)), Some("sat"));
}

/// `(= s (set.remove 1 (set.singleton 1)))` reduces to the empty set, so
/// `card(s) = 1` is UNSAT and removing from empty stays empty.
#[test]
fn card_of_var_aliased_to_empty_store_chain_is_zero() {
    let remove_to_empty = r#"
(set-logic ALL)
(declare-const s (Set Int))
(assert (= s (set.remove 1 (set.singleton 1))))
(assert (= (set.card s) 1))
(check-sat)
"#;
    assert_eq!(verdict(&solve(remove_to_empty)), Some("unsat"));
    let remove_from_empty = r#"
(set-logic ALL)
(declare-const s (Set Int))
(assert (= s (set.remove 5 (as set.empty (Set Int)))))
(assert (> (set.card s) 0))
(check-sat)
"#;
    assert_eq!(verdict(&solve(remove_from_empty)), Some("unsat"));
}

/// `(= s (set.singleton 5))` then `card(s) = 1` is SAT and `card(s) = 0` is
/// UNSAT — the aliased singleton is counted structurally.
#[test]
fn card_of_var_aliased_to_singleton_is_one() {
    let one = r#"
(set-logic ALL)
(declare-const s (Set Int))
(assert (= s (set.singleton 5)))
(assert (= (set.card s) 1))
(check-sat)
"#;
    assert_eq!(verdict(&solve(one)), Some("sat"));
    let zero = r#"
(set-logic ALL)
(declare-const s (Set Int))
(assert (= s (set.singleton 5)))
(assert (= (set.card s) 0))
(check-sat)
"#;
    assert_eq!(verdict(&solve(zero)), Some("unsat"));
}

/// A chained alias `(= s t)(= t empty)` resolves `s → empty`, so `card(s) = 1`
/// is UNSAT (the resolver prefers the concrete alias over the `s ⇄ t` cycle).
#[test]
fn card_of_chained_var_alias_to_empty_is_zero() {
    let smt = r#"
(set-logic ALL)
(declare-const s (Set Int))
(declare-const t (Set Int))
(assert (= s t))
(assert (= t (as set.empty (Set Int))))
(assert (= (set.card s) 1))
(check-sat)
"#;
    assert_eq!(verdict(&solve(smt)), Some("unsat"));
}

/// Soundness fail-closed: `(= s (set.insert y t))` over a declared set variable
/// `t` is variable-rooted (uncovered), so `card(s)` is not structurally counted
/// and stays `unknown` rather than risk a wrong `sat`.
#[test]
fn card_of_var_aliased_to_variable_rooted_chain_is_fail_closed_unknown() {
    let smt = r#"
(set-logic ALL)
(declare-const s (Set Int))
(declare-const t (Set Int))
(declare-const y Int)
(assert (= s (set.insert y t)))
(assert (= (set.card s) 1))
(check-sat)
"#;
    assert_eq!(verdict(&solve(smt)), Some("unknown"));
}

// ---------------------------------------------------------------------------
// Aliased-variable subset (#set-subset-aliased-wrong-sat).
//
// A `set.subset` over set VARIABLES equated by `(= v <set-expr>)` to concrete
// set expressions must be tied to those expressions' structure — not left to
// the witness-based saturation (which only fires on present `member` atoms and
// so used to admit wrong `sat` verdicts here). Operands are resolved through the
// alias chain; empty / covered-store-chain resolutions decide structurally, and
// undecidable resolutions against a *bounded* superset fail closed to `unknown`.
// ---------------------------------------------------------------------------

/// `(= s empty)` then `(not (set.subset s t))` is UNSAT: the empty set is a
/// subset of every set, so `subset(empty, t)` is valid regardless of `t`.
/// Previously a wrong `sat` (witness saturation never connected the alias).
#[test]
fn subset_of_var_aliased_to_empty_is_true() {
    let neg = r#"
(set-logic ALL)
(declare-const s (Set Int))
(declare-const t (Set Int))
(assert (= s (as set.empty (Set Int))))
(assert (not (set.subset s t)))
(check-sat)
"#;
    assert_eq!(verdict(&solve(neg)), Some("unsat"));
    // Asserting the (valid) subset stays SAT.
    let pos = r#"
(set-logic ALL)
(declare-const s (Set Int))
(declare-const t (Set Int))
(assert (= s (as set.empty (Set Int))))
(assert (set.subset s t))
(check-sat)
"#;
    assert_eq!(verdict(&solve(pos)), Some("sat"));
}

/// `(= s (set.singleton 1))(= t empty)` then `(set.subset s t)` is UNSAT:
/// a non-empty set is not a subset of the empty set. Previously a wrong `sat`.
#[test]
fn subset_of_singleton_alias_into_empty_alias_is_false() {
    let smt = r#"
(set-logic ALL)
(declare-const s (Set Int))
(declare-const t (Set Int))
(assert (= s (set.singleton 1)))
(assert (= t (as set.empty (Set Int))))
(assert (set.subset s t))
(check-sat)
"#;
    assert_eq!(verdict(&solve(smt)), Some("unsat"));
}

/// `(= s empty)(= t empty)` then `(not (set.subset s t))` is UNSAT (∅ ⊆ ∅).
#[test]
fn subset_of_two_empty_aliases_is_true() {
    let smt = r#"
(set-logic ALL)
(declare-const s (Set Int))
(declare-const t (Set Int))
(assert (= s (as set.empty (Set Int))))
(assert (= t (as set.empty (Set Int))))
(assert (not (set.subset s t)))
(check-sat)
"#;
    assert_eq!(verdict(&solve(smt)), Some("unsat"));
}

/// `(= s {1})(= t {2})` then `(set.subset s t)` is UNSAT: `{1} ⊄ {2}`
/// (distinct concrete literals). Decided structurally over the aliases.
#[test]
fn subset_of_disjoint_singleton_aliases_is_false() {
    let smt = r#"
(set-logic ALL)
(declare-const s (Set Int))
(declare-const t (Set Int))
(assert (= s (set.singleton 1)))
(assert (= t (set.singleton 2)))
(assert (set.subset s t))
(check-sat)
"#;
    assert_eq!(verdict(&solve(smt)), Some("unsat"));
}

/// `(= s {1})(= t {1,2})` then `(set.subset s t)` is SAT and its negation is
/// UNSAT — `{1} ⊆ {1,2}` decided structurally over the aliases.
#[test]
fn subset_of_singleton_alias_into_superset_alias_is_true() {
    let pos = r#"
(set-logic ALL)
(declare-const s (Set Int))
(declare-const t (Set Int))
(assert (= s (set.singleton 1)))
(assert (= t (set.insert 2 (set.singleton 1))))
(assert (set.subset s t))
(check-sat)
"#;
    assert_eq!(verdict(&solve(pos)), Some("sat"));
    let neg = r#"
(set-logic ALL)
(declare-const s (Set Int))
(declare-const t (Set Int))
(assert (= s (set.singleton 1)))
(assert (= t (set.insert 2 (set.singleton 1))))
(assert (not (set.subset s t)))
(check-sat)
"#;
    assert_eq!(verdict(&solve(neg)), Some("unsat"));
}

/// Reflexive subset over an aliased singleton stays SAT.
#[test]
fn subset_reflexive_over_singleton_alias_is_sat() {
    let smt = r#"
(set-logic ALL)
(declare-const s (Set Int))
(assert (= s (set.singleton 1)))
(assert (set.subset s s))
(check-sat)
"#;
    assert_eq!(verdict(&solve(smt)), Some("sat"));
}

/// Genuinely-sat: an aliased non-empty subset against a FREE (unbounded)
/// superset stays SAT — the predicate is satisfiable (pick the superset to
/// contain the subset). The fix must not over-demote this to `unknown`.
#[test]
fn subset_of_singleton_alias_into_free_superset_is_sat() {
    let smt = r#"
(set-logic ALL)
(declare-const s (Set Int))
(declare-const t (Set Int))
(assert (= s (set.singleton 1)))
(assert (set.subset s t))
(check-sat)
"#;
    assert_eq!(verdict(&solve(smt)), Some("sat"));
}

/// Soundness fail-closed: an aliased variable-rooted (uncovered) subset against
/// a bounded (empty) superset is not structurally decided, so it stays
/// `unknown` rather than risk a wrong `sat`. (`insert(1, a) ⊆ ∅` is in fact
/// UNSAT, but the uncovered chain is conservatively demoted.)
#[test]
fn subset_of_var_rooted_alias_into_empty_is_fail_closed_unknown() {
    let smt = r#"
(set-logic ALL)
(declare-const a (Set Int))
(declare-const s (Set Int))
(assert (= s (set.insert 1 a)))
(assert (set.subset s (as set.empty (Set Int))))
(check-sat)
"#;
    assert_eq!(verdict(&solve(smt)), Some("unknown"));
}

// ---------------------------------------------------------------------------
// Cardinality/membership coupling (#set-card-membership-lower-bound).
// ---------------------------------------------------------------------------

/// A concrete member makes cardinality zero impossible.  Until the set/LIA
/// refutation has a strict proof lane the mandatory publication gate may
/// return `unknown`; it must never publish the old, self-contradicting `sat`.
#[test]
fn concrete_member_with_zero_cardinality_is_never_sat() {
    let smt = r#"
(set-logic ALL)
(declare-const s (Set Int))
(assert (set.member 1 s))
(assert (= 0 (set.card s)))
(check-sat)
"#;
    let out = solve(smt);
    assert!(
        matches!(verdict(&out), Some("unsat" | "unknown")),
        "membership/cardinality contradiction was published as SAT:\n{out}"
    );
}

/// Two known-distinct members cannot inhabit a singleton set.  This pins the
/// distinct-value lower bound rather than merely the one-member special case.
#[test]
fn two_distinct_members_with_cardinality_one_are_never_sat() {
    let smt = r#"
(set-logic ALL)
(declare-const s (Set Int))
(assert (set.member 1 s))
(assert (set.member 2 s))
(assert (= 1 (set.card s)))
(check-sat)
"#;
    let out = solve(smt);
    assert!(
        matches!(verdict(&out), Some("unsat" | "unknown")),
        "distinct-member lower bound was not enforced:\n{out}"
    );
}

/// The lower bound counts values, not syntactic membership probes: the model
/// may set `x = y`, so two symbolic probes with cardinality one remain SAT.
#[test]
fn two_symbolic_members_may_alias_in_a_singleton_set() {
    let smt = r#"
(set-logic ALL)
(declare-const s (Set Int))
(declare-const x Int)
(declare-const y Int)
(assert (set.member x s))
(assert (set.member y s))
(assert (= 1 (set.card s)))
(check-sat)
"#;
    let out = solve(smt);
    assert_eq!(verdict(&out), Some("sat"), "{out}");
}

// ---------------------------------------------------------------------------
// Fail-closed: out-of-fragment obligations return unknown, never guessed.
// ---------------------------------------------------------------------------

/// Ground `set.union` membership is decided, not guessed.
///
/// This asserted `unknown` when union had no sound ground membership
/// semantics. It does now: `1 ∈ s ∪ t` is plainly satisfiable (`s = {1}`), and
/// AY returns a model for it. The fail-closed guarantee this section exists to
/// protect is "never GUESSED", so the contradictory companion is asserted
/// alongside -- answering `sat` to both would be the actual regression.
#[test]
fn union_membership_is_decided_both_ways() {
    let sat = r#"
(set-logic QF_SET)
(declare-const s (Set Int))
(declare-const t (Set Int))
(assert (set.member 1 (set.union s t)))
(check-sat)
"#;
    assert_eq!(verdict(&solve(sat)), Some("sat"));

    // `1 ∈ s ∪ t` while 1 is in neither operand is unsatisfiable.
    let unsat = r#"
(set-logic QF_SET)
(declare-const s (Set Int))
(declare-const t (Set Int))
(assert (set.member 1 (set.union s t)))
(assert (not (set.member 1 s)))
(assert (not (set.member 1 t)))
(check-sat)
"#;
    assert_eq!(verdict(&solve(unsat)), Some("unsat"));
}

/// Ground `set.complement` membership over an unbounded domain, likewise.
///
/// `0 ∈ complement(s)` is satisfiable by `s = {}`; AY returns exactly that
/// model. Paired with the contradiction so a blanket `sat` cannot pass.
#[test]
fn complement_membership_is_decided_both_ways() {
    let sat = r#"
(set-logic QF_SET)
(declare-const s (Set Int))
(assert (set.member 0 (set.complement s)))
(check-sat)
"#;
    assert_eq!(verdict(&solve(sat)), Some("sat"));

    // Nothing is in both a set and its complement.
    let unsat = r#"
(set-logic QF_SET)
(declare-const s (Set Int))
(assert (set.member 0 (set.complement s)))
(assert (set.member 0 s))
(check-sat)
"#;
    assert_eq!(verdict(&solve(unsat)), Some("unsat"));
}

// ---------------------------------------------------------------------------
// Cardinality model witnesses (#set-card-model-witness).
//
// A `sat` verdict must come with a model that SATISFIES the assertion. A free
// `(Set Int)` constrained only by `(= 1 (set.card s))` used to answer `sat`
// with `((as const (Array Int Bool)) false)` — the EMPTY set — while
// `(get-value ((set.card s)))` answered `1`. The verdict was right and the
// model self-contradicting. genuine z3 5.0.0 exhibits a real witness for the
// native form (`(= 1 (set.size s))` -> `((as set.unique (FiniteSet Int)) 1 1)`).
// ---------------------------------------------------------------------------

/// Members of the printed `(Array _ Bool)` carrier: the number of store writes
/// of `true` on top of a `false` default. Panics if the carrier is printed with
/// the universal (`true`) default — a set of ANY finite cardinality must not be
/// printed co-finite.
fn printed_set_size(output: &str) -> usize {
    assert!(
        !output.contains(") true)\n") && !output.contains("Bool)) true)"),
        "set carrier printed with the universal default:\n{output}"
    );
    output.matches(" true)").count()
}

/// The value `get-value` reports for the single requested term.
fn get_value_int(output: &str) -> i64 {
    let line = output
        .lines()
        .map(str::trim)
        .find(|l| l.starts_with("(((set.card"))
        .unwrap_or_else(|| panic!("no get-value line in:\n{output}"));
    let digits: String = line
        .rsplit(')')
        .find(|chunk| chunk.chars().any(|c| c.is_ascii_digit()))
        .unwrap_or_default()
        .chars()
        .filter(|c| c.is_ascii_digit() || *c == '-')
        .collect();
    digits
        .parse()
        .unwrap_or_else(|_| panic!("bad get-value line: {line}"))
}

/// `(= 1 (set.card s))` over a free set: `sat` with a ONE-element model, and
/// `get-value` agrees with the model that was printed.
#[test]
fn card_one_model_exhibits_one_element() {
    let smt = r#"
(set-logic ALL)
(declare-const s (Set Int))
(assert (= 1 (set.card s)))
(check-sat)
(get-model)
(get-value ((set.card s)))
"#;
    let out = solve(smt);
    assert_eq!(verdict(&out), Some("sat"), "{out}");
    assert_eq!(printed_set_size(&out), 1, "{out}");
    assert_eq!(get_value_int(&out), 1, "{out}");
}

/// `(= 3 (set.card s))` yields a model with exactly three distinct elements.
#[test]
fn card_three_model_exhibits_three_elements() {
    let smt = r#"
(set-logic ALL)
(declare-const s (Set Int))
(assert (= 3 (set.card s)))
(check-sat)
(get-model)
(get-value ((set.card s)))
"#;
    let out = solve(smt);
    assert_eq!(verdict(&out), Some("sat"), "{out}");
    assert_eq!(printed_set_size(&out), 3, "{out}");
    assert_eq!(get_value_int(&out), 3, "{out}");
}

/// `(= 0 (set.card s))` yields the empty set — and `get-value` says 0.
#[test]
fn card_zero_model_is_the_empty_set() {
    let smt = r#"
(set-logic ALL)
(declare-const s (Set Int))
(assert (= 0 (set.card s)))
(check-sat)
(get-model)
(get-value ((set.card s)))
"#;
    let out = solve(smt);
    assert_eq!(verdict(&out), Some("sat"), "{out}");
    assert_eq!(printed_set_size(&out), 0, "{out}");
    assert_eq!(get_value_int(&out), 0, "{out}");
}

/// `1 ∈ s ∧ |s| = 2`: the model contains 1 plus exactly one other element.
/// Before the fix the carrier printed as the UNIVERSAL set (`(store ((as const
/// ..) true) 1 true)`), whose cardinality is not 2 by any reading.
#[test]
fn member_plus_card_two_model_has_the_member_and_one_more() {
    let smt = r#"
(set-logic ALL)
(declare-const s (Set Int))
(assert (set.member 1 s))
(assert (= 2 (set.card s)))
(check-sat)
(get-model)
(get-value ((set.card s)))
"#;
    let out = solve(smt);
    assert_eq!(verdict(&out), Some("sat"), "{out}");
    assert_eq!(printed_set_size(&out), 2, "{out}");
    assert_eq!(get_value_int(&out), 2, "{out}");
    assert!(
        out.contains(" 1 true)"),
        "member 1 missing from model:\n{out}"
    );
}

/// `1 ∈ s ∧ |s| = 1`: the single element IS 1 — no invented extra, and the
/// carrier is not the universal set.
#[test]
fn member_plus_card_one_model_is_exactly_that_member() {
    let smt = r#"
(set-logic ALL)
(declare-const s (Set Int))
(assert (set.member 1 s))
(assert (= 1 (set.card s)))
(check-sat)
(get-model)
(get-value ((set.card s)))
"#;
    let out = solve(smt);
    assert_eq!(verdict(&out), Some("sat"), "{out}");
    assert_eq!(printed_set_size(&out), 1, "{out}");
    assert_eq!(get_value_int(&out), 1, "{out}");
    assert!(
        out.contains(" 1 true)"),
        "member 1 missing from model:\n{out}"
    );
}

/// A non-member is respected: `0 ∉ s ∧ |s| = 1` picks some element other than 0.
#[test]
fn card_witness_avoids_forced_non_members() {
    let smt = r#"
(set-logic ALL)
(declare-const s (Set Int))
(assert (not (set.member 0 s)))
(assert (= 1 (set.card s)))
(check-sat)
(get-model)
(get-value ((set.card s)))
"#;
    let out = solve(smt);
    assert_eq!(verdict(&out), Some("sat"), "{out}");
    assert_eq!(printed_set_size(&out), 1, "{out}");
    assert_eq!(get_value_int(&out), 1, "{out}");
    assert!(
        out.contains(" 0 false)"),
        "non-member 0 lost from model:\n{out}"
    );
}

/// Equated carriers get the SAME witness: `(= s t) ∧ |s| = 1` must not print
/// `s = {0}` next to `t = ∅`.
#[test]
fn card_witness_is_shared_across_equated_carriers() {
    let smt = r#"
(set-logic ALL)
(declare-const s (Set Int))
(declare-const t (Set Int))
(assert (= s t))
(assert (= 1 (set.card s)))
(check-sat)
(get-model)
(get-value ((set.card s)))
"#;
    let out = solve(smt);
    assert_eq!(verdict(&out), Some("sat"), "{out}");
    // Two carriers, one element each, printed identically.
    assert_eq!(printed_set_size(&out), 2, "{out}");
    assert_eq!(get_value_int(&out), 1, "{out}");
    let carriers: Vec<&str> = out
        .lines()
        .filter(|l| {
            l.trim_start().starts_with("(store") || l.trim_start().starts_with("((as const")
        })
        .collect();
    assert_eq!(carriers.len(), 2, "{out}");
    assert_eq!(carriers[0].trim(), carriers[1].trim(), "{out}");
}

/// The balanced value term the model prints for the carrier named `name`.
fn printed_carrier_body(output: &str, name: &str) -> String {
    let head = format!("(define-fun {name} () (Array");
    let start = output
        .find(&head)
        .unwrap_or_else(|| panic!("no carrier `{name}` in:\n{output}"));
    let after = &output[start..];
    let nl = after
        .find('\n')
        .unwrap_or_else(|| panic!("carrier `{name}` has no value line:\n{output}"));
    let rest = after[nl + 1..].trim_start();
    let mut depth = 0usize;
    for (i, byte) in rest.bytes().enumerate() {
        match byte {
            b'(' => depth += 1,
            b')' => {
                depth -= 1;
                if depth == 0 {
                    return rest[..=i].to_string();
                }
            }
            _ => {}
        }
    }
    panic!("unbalanced carrier value for `{name}`:\n{output}")
}

/// The printed carrier as `(default membership, (index, member) cells)`, read
/// straight out of the `(store …)` chain — the same reading a re-parsing model
/// validator performs.
fn printed_carrier(output: &str, name: &str) -> (bool, Vec<(String, bool)>) {
    let mut cells: Vec<(String, bool)> = Vec::new();
    let mut cur = printed_carrier_body(output, name);
    loop {
        let Some(rest) = cur.strip_prefix("(store ") else {
            // `((as const (Array …)) D)` base.
            cells.reverse();
            return (cur.trim_end().ends_with("true)"), cells);
        };
        let mut depth = 0usize;
        let mut end = 0usize;
        for (i, byte) in rest.bytes().enumerate() {
            match byte {
                b'(' => depth += 1,
                b')' => {
                    depth -= 1;
                    if depth == 0 {
                        end = i + 1;
                        break;
                    }
                }
                _ => {}
            }
        }
        let base = rest[..end].to_string();
        let tail = rest[end..]
            .trim()
            .strip_suffix(')')
            .expect("store term closes")
            .trim()
            .to_string();
        // The index is a numeral or `(- n)`; the value is the final token.
        let (idx, val) = tail.rsplit_once(' ').expect("store index and value");
        cells.push((idx.trim().to_string(), val.trim() == "true"));
        cur = base;
    }
}

/// The members (true cells) of the printed carrier named `name`.
fn printed_carrier_members(output: &str, name: &str) -> Vec<String> {
    printed_carrier(output, name)
        .1
        .into_iter()
        .filter(|(_, member)| *member)
        .map(|(key, _)| key)
        .collect()
}

/// A cardinality witness must not break an asserted `set.subset`: shrinking the
/// superset to its exact size must keep the subset atom TRUE in the model that
/// is actually printed, not merely keep both carriers small.
#[test]
fn card_witness_keeps_asserted_subset_true() {
    let smt = r#"
(set-logic ALL)
(declare-const s (Set Int))
(declare-const t (Set Int))
(assert (set.subset t s))
(assert (= 1 (set.card s)))
(check-sat)
(get-model)
"#;
    let out = solve(smt);
    assert_eq!(verdict(&out), Some("sat"), "{out}");
    // `t ⊆ s` with `|s| = 1`: neither carrier may print as the universal set.
    assert!(printed_set_size(&out) <= 2, "{out}");
    // …and `t ⊆ s` must actually HOLD of the printed carriers: every element
    // `t` holds is an element `s` holds. Both defaults are `false`, which
    // `printed_set_size` already asserted.
    let s_members = printed_carrier_members(&out, "s");
    for (key, member) in printed_carrier(&out, "t").1 {
        assert!(
            !member || s_members.contains(&key),
            "printed model falsifies (set.subset t s): {key} in t but not in s\n{out}"
        );
    }
}

// ---------------------------------------------------------------------------
// Repairs of the first cardinality-witness landing (#set-card-neg-double-count,
// #set-card-equality-polarity, #set-card-witness-constraints).
// ---------------------------------------------------------------------------

/// NEGATIVE elements must count ONCE. `format_eval_value` spells the integer
/// −5 as the bare numeral `-5` while the array-witness path spells the same
/// value `(- 5)`; both landed in `ArrayInterpretation::stores`, and every
/// consumer compared keys as strings — so the one member {−5} was counted as
/// two. The carrier printed a ONE-element set while `get-value` reported 2.
#[test]
fn negative_member_is_not_double_counted() {
    let smt = r#"
(set-logic ALL)
(declare-const s (Set Int))
(assert (set.member (- 5) s))
(assert (= (set.card s) 2))
(check-sat)
(get-model)
(get-value ((set.card s)))
"#;
    let out = solve(smt);
    assert_eq!(verdict(&out), Some("sat"), "{out}");
    assert_eq!(printed_set_size(&out), 2, "{out}");
    assert_eq!(get_value_int(&out), 2, "{out}");
    let members = printed_carrier_members(&out, "s");
    assert_eq!(members.len(), 2, "duplicate cell for one index:\n{out}");
    assert!(
        members.iter().any(|k| k == "(- 5)"),
        "member -5 lost:\n{out}"
    );
}

/// The other side of the same double-count: a satisfiable query answered
/// `unknown` because the doubled member count could not reach the target.
#[test]
fn single_negative_member_with_card_one_is_sat() {
    let smt = r#"
(set-logic ALL)
(declare-const s (Set Int))
(assert (set.member (- 1) s))
(assert (= (set.card s) 1))
(check-sat)
(get-model)
(get-value ((set.card s)))
"#;
    let out = solve(smt);
    assert_eq!(verdict(&out), Some("sat"), "{out}");
    assert_eq!(printed_set_size(&out), 1, "{out}");
    assert_eq!(get_value_int(&out), 1, "{out}");
}

/// Two negative members plus one invented one.
#[test]
fn two_negative_members_with_card_three_is_sat() {
    let smt = r#"
(set-logic ALL)
(declare-const s (Set Int))
(assert (set.member (- 5) s))
(assert (set.member (- 7) s))
(assert (= (set.card s) 3))
(check-sat)
(get-model)
(get-value ((set.card s)))
"#;
    let out = solve(smt);
    assert_eq!(verdict(&out), Some("sat"), "{out}");
    assert_eq!(printed_set_size(&out), 3, "{out}");
    assert_eq!(get_value_int(&out), 3, "{out}");
}

/// A DISEQUALITY is not a defining equality. The witness guard used to match
/// `(= var expr)` anywhere in the assertion DAG, so `(not (= s (set.singleton
/// 2)))` blocked padding and a trivially satisfiable query failed closed.
#[test]
fn set_disequality_does_not_block_the_card_witness() {
    let smt = r#"
(set-logic ALL)
(declare-const s (Set Int))
(assert (= (set.card s) 1))
(assert (not (= s (set.singleton 2))))
(check-sat)
(get-model)
(get-value ((set.card s)))
"#;
    let out = solve(smt);
    assert_eq!(verdict(&out), Some("sat"), "{out}");
    assert_eq!(printed_set_size(&out), 1, "{out}");
    assert_eq!(get_value_int(&out), 1, "{out}");
    let members = printed_carrier_members(&out, "s");
    assert_eq!(members.len(), 1, "{out}");
    assert_ne!(
        members[0], "2",
        "witness equals the excluded singleton:\n{out}"
    );
}

/// The MULTI-ELEMENT twin of the case above: the forbidden witness is a
/// two-element set, so honouring the disequality is a whole-SET comparison, not
/// a single excluded key (#set-card-diseq-witness).
#[test]
fn set_disequality_against_a_two_element_set_still_witnesses() {
    let smt = r#"
(set-logic ALL)
(declare-const s (Set Int))
(assert (= (set.card s) 2))
(assert (not (= s (set.union (set.singleton 0) (set.singleton 1)))))
(check-sat)
(get-model)
(get-value ((set.card s)))
"#;
    let out = solve(smt);
    assert_eq!(verdict(&out), Some("sat"), "{out}");
    assert_eq!(printed_set_size(&out), 2, "{out}");
    assert_eq!(get_value_int(&out), 2, "{out}");
    let mut members = printed_carrier_members(&out, "s");
    members.sort();
    assert_eq!(members.len(), 2, "{out}");
    assert_ne!(
        members,
        vec!["0".to_string(), "1".to_string()],
        "witness equals the excluded two-element set:\n{out}"
    );
}

/// A set DISEQUALITY must not merge two carriers into one witness class —
/// they would then print the SAME set and falsify the disequality.
#[test]
fn disequal_carriers_are_not_merged_into_one_witness() {
    let smt = r#"
(set-logic ALL)
(declare-const s (Set Int))
(declare-const t (Set Int))
(assert (set.member 2 s))
(assert (>= (set.card s) 0))
(assert (not (= s t)))
(check-sat)
(get-model)
(get-value ((set.card s)))
"#;
    let out = solve(smt);
    assert_eq!(verdict(&out), Some("sat"), "{out}");
    let s_carrier = printed_carrier(&out, "s");
    let t_carrier = printed_carrier(&out, "t");
    assert_ne!(
        s_carrier, t_carrier,
        "disequal carriers printed equal:\n{out}"
    );
}

/// A positively asserted `set.subset` bounds the witness from ABOVE: the only
/// element `s` may hold is 1, so `|s| = 1` must land on exactly `{1}`.
#[test]
fn card_witness_respects_a_subset_upper_bound() {
    let smt = r#"
(set-logic ALL)
(declare-const s (Set Int))
(assert (set.subset s (set.singleton 1)))
(assert (= (set.card s) 1))
(check-sat)
(get-model)
(get-value ((set.card s)))
"#;
    let out = solve(smt);
    assert_eq!(verdict(&out), Some("sat"), "{out}");
    assert_eq!(printed_set_size(&out), 1, "{out}");
    assert_eq!(get_value_int(&out), 1, "{out}");
    assert_eq!(
        printed_carrier_members(&out, "s"),
        vec!["1".to_string()],
        "{out}"
    );
}

/// A positively asserted `set.subset` also bounds the witness from BELOW: the
/// superset's witness has to contain every member of the subset.
#[test]
fn card_witness_respects_a_subset_lower_bound() {
    let smt = r#"
(set-logic ALL)
(declare-const s (Set Int))
(declare-const t (Set Int))
(assert (set.member 2 s))
(assert (not (set.member 1 s)))
(assert (set.subset s t))
(assert (>= (set.card t) 2))
(check-sat)
(get-model)
(get-value ((set.card t)))
"#;
    let out = solve(smt);
    assert_eq!(verdict(&out), Some("sat"), "{out}");
    let t_members = printed_carrier_members(&out, "t");
    for (key, member) in printed_carrier(&out, "s").1 {
        assert!(
            !member || t_members.contains(&key),
            "printed model falsifies (set.subset s t): {key} in s but not in t\n{out}"
        );
    }
    assert!(t_members.len() >= 2, "{out}");
    assert_eq!(get_value_int(&out), t_members.len() as i64, "{out}");
}

/// Fail-closed: an uninterpreted element sort has no enumerable universe to
/// draw distinct witness elements from, so a positive cardinality over it is
/// `unknown` — never a `sat` whose model shows the empty set.
#[test]
fn card_over_uninterpreted_element_sort_is_fail_closed_unknown() {
    let smt = r#"
(set-logic ALL)
(declare-sort U 0)
(declare-const s (Set U))
(assert (= 2 (set.card s)))
(check-sat)
"#;
    assert_eq!(verdict(&solve(smt)), Some("unknown"));
}

/// A bitvector element sort IS enumerable, so the witness is built there.
#[test]
fn card_over_bitvector_element_sort_exhibits_a_witness() {
    let smt = r#"
(set-logic ALL)
(declare-const s (Set (_ BitVec 4)))
(assert (= 2 (set.card s)))
(check-sat)
(get-model)
(get-value ((set.card s)))
"#;
    let out = solve(smt);
    assert_eq!(verdict(&out), Some("sat"), "{out}");
    assert_eq!(printed_set_size(&out), 2, "{out}");
    assert_eq!(get_value_int(&out), 2, "{out}");
}
