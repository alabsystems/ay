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
// Fail-closed: out-of-fragment obligations return unknown, never guessed.
// ---------------------------------------------------------------------------

/// `set.union` has no sound ground membership semantics yet → unknown.
#[test]
fn union_is_fail_closed_unknown() {
    let smt = r#"
(set-logic QF_SET)
(declare-const s (Set Int))
(declare-const t (Set Int))
(assert (set.member 1 (set.union s t)))
(check-sat)
"#;
    assert_eq!(verdict(&solve(smt)), Some("unknown"));
}

/// `set.complement` over an unbounded domain → unknown (fail-closed).
#[test]
fn complement_is_fail_closed_unknown() {
    let smt = r#"
(set-logic QF_SET)
(declare-const s (Set Int))
(assert (set.member 0 (set.complement s)))
(check-sat)
"#;
    assert_eq!(verdict(&solve(smt)), Some("unknown"));
}
