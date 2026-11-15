// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The native-map fail-closed SAT gate (#map-value-semantics,
//! `executor/model/native_map_gate.rs`) and the map semantics it guards.
//!
//! A `(Map K V)` is a (value array, domain) pair: `map.insert` stores into
//! both, `map.remove` into the domain only, `map.get` reads the values in the
//! domain or not, the empty map is one unconstrained value array per sort with
//! the all-false domain, and maps are equal when both parts are. The encoding
//! carries the map as its value array and derives the domain at the readers
//! (empty map, `map.insert`, `map.remove`) or in a domain carrier. Map-sorted
//! `=` ties only the value arrays, and carriers are congruent only among maps
//! that own one, so an empty map or constructor used as a value, a carrier for
//! a map that is not a declared constant, or `map.subset` beyond reflexivity
//! leaves the elaborated formula weaker than the source. Every `rejects_*`
//! formula below is UNSAT, and each answered `sat` on `7b6e639c98` except the
//! four rows marked "already `unknown`" (the aliased-map rows were first
//! recorded by the 2026-08-02 salvage, whose repair targeted the pre-carrier
//! encoding and no longer applies).
//!
//! `unknown` is the honest floor for them, not the target: a `rejects_*` test
//! turning `sat` means the gate regressed, turning `unsat` means the encoding
//! improved. The `keeps_*` controls are inside the faithful fragment and must
//! stay decided; the `semantics_*` pins fix what a map is.

use crate::Executor;
use ay_frontend::parse;

pub(super) fn verdict(smt: &str) -> String {
    let commands = parse(smt).expect("parse failed");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute_all failed");
    let joined = outputs.join("\n");
    joined
        .lines()
        .map(str::trim)
        .find(|line| matches!(*line, "sat" | "unsat" | "unknown"))
        .unwrap_or("<none>")
        .to_string()
}

/// Declarations shared by every case.
const DECLS: &str = r#"
(declare-const m (Map Int Int))
(declare-const n (Map Int Int))
(declare-const c Bool)
"#;

pub(super) fn with_decls(body: &str) -> String {
    with_logic("QF_MAPLIA", body)
}

fn with_logic(logic: &str, body: &str) -> String {
    format!("(set-logic {logic}){DECLS}{body}\n(check-sat)\n")
}

/// An UNSAT formula must answer `unsat` or `unknown` — an actual verdict, so a
/// parse or logic error cannot pass the pin vacuously.
#[track_caller]
fn assert_never_sat_in(logic: &str, body: &str) {
    let got = verdict(&with_logic(logic, body));
    assert!(
        got == "unsat" || got == "unknown",
        "UNSAT map formula answered `{got}`:\n{body}"
    );
}

#[track_caller]
fn assert_never_sat(body: &str) {
    assert_never_sat_in("QF_MAPLIA", body);
}

#[track_caller]
fn assert_sat(body: &str) {
    let got = verdict(&with_decls(body));
    assert_eq!(
        got, "sat",
        "faithful-fragment map formula lost its `sat`:\n{body}"
    );
}

// ---------------------------------------------------------------------------
// A map variable defined by a SEPARATE equality (the salvage's rows).
// ---------------------------------------------------------------------------

#[test]
fn rejects_aliased_empty_contradicting_contains_key() {
    assert_never_sat(
        "(assert (= n (as map.empty (Map Int Int))))
         (assert (map.contains_key n 3))",
    );
}

#[test]
fn rejects_aliased_empty_when_the_reader_comes_first() {
    assert_never_sat(
        "(assert (map.contains_key n 3))
         (assert (= n (as map.empty (Map Int Int))))",
    );
}

/// Already `unknown` on `7b6e639c98`; pinned so it never turns `sat`.
#[test]
fn rejects_aliased_insert_contradicting_contains_key() {
    assert_never_sat(
        "(assert (= n (map.insert m 1 5)))
         (assert (not (map.contains_key n 1)))",
    );
}

/// Already `unknown` on `7b6e639c98`; pinned so it never turns `sat`.
#[test]
fn rejects_aliased_remove_contradicting_contains_key() {
    assert_never_sat(
        "(assert (= n (map.remove (map.insert m 1 5) 1)))
         (assert (map.contains_key n 1))",
    );
}

/// Already `unknown` on `7b6e639c98`; pinned so it never turns `sat`.
#[test]
fn rejects_aliased_insert_contradicting_get() {
    assert_never_sat(
        "(assert (= n (map.insert m 1 5)))
         (assert (= 7 (map.get n 1)))",
    );
}

/// Already `unknown` on `7b6e639c98`; pinned so it never turns `sat`.
#[test]
fn rejects_ground_subset_that_is_false() {
    assert_never_sat(
        "(assert (= m (map.insert (as map.empty (Map Int Int)) 1 5)))
         (assert (= n (as map.empty (Map Int Int))))
         (assert (map.subset m n))",
    );
}

// ---------------------------------------------------------------------------
// Empty maps and constructors used as VALUES.
// ---------------------------------------------------------------------------

/// `map.empty` is a constant: every occurrence is the same map. Each used to
/// elaborate over its own fresh default value, so these answered `sat` on
/// `7b6e639c98`; the sort's one empty map decides them outright.
#[test]
fn two_empty_maps_are_one_map() {
    let got = verdict(&with_decls(
        "(assert (distinct (as map.empty (Map Int Int)) (as map.empty (Map Int Int))))",
    ));
    assert_eq!(got, "unsat");
}

#[test]
fn empty_map_reads_agree_across_occurrences() {
    let got = verdict(&with_decls(
        "(assert (distinct (map.get (as map.empty (Map Int Int)) 1)
                           (map.get (as map.empty (Map Int Int)) 1)))",
    ));
    assert_eq!(got, "unsat");
}

#[test]
fn empty_map_reads_cannot_take_two_values() {
    let got = verdict(&with_decls(
        "(assert (= 5 (map.get (as map.empty (Map Int Int)) 1)))
         (assert (= 6 (map.get (as map.empty (Map Int Int)) 1)))",
    ));
    assert_eq!(got, "unsat");
}

/// The empty map's values are unspecified key by key, not one default: this
/// answered `unsat` while the empty map was a constant array. It is `sat`; AY
/// answers `unknown`, as it does for two distinct reads of any one map on the
/// map route (`(distinct (map.get m 1) (map.get m 2))`, measured).
#[test]
fn empty_map_values_are_unspecified_per_key() {
    let got = verdict(&with_decls(
        "(assert (let ((e (as map.empty (Map Int Int))))
           (distinct (map.get e 1) (map.get e 2))))",
    ));
    assert!(matches!(got.as_str(), "sat" | "unknown"), "got `{got}`");
}

#[test]
fn rejects_constructor_equated_to_the_empty_map() {
    assert_never_sat("(assert (= (map.insert m 1 5) (as map.empty (Map Int Int))))");
}

#[test]
fn rejects_empty_map_through_an_ite_value() {
    assert_never_sat(
        "(assert (ite (= n (as map.empty (Map Int Int))) (map.contains_key n 1) false))",
    );
}

#[test]
fn rejects_empty_map_under_an_ite_alias() {
    assert_never_sat(
        "(assert (= n (ite c m (as map.empty (Map Int Int)))))
         (assert (not c))
         (assert (map.contains_key n 1))",
    );
}

/// The empty map reached through a `define-fun`: `e` is a macro for it, so
/// `n` is the empty map used as a value.
#[test]
fn rejects_empty_map_through_a_define_fun() {
    assert_never_sat(
        "(define-fun e () (Map Int Int) (as map.empty (Map Int Int)))
         (assert (= n e))
         (assert (map.contains_key n 3))",
    );
}

/// The empty map arrives as a `check-sat-assuming` assumption.
#[test]
fn rejects_empty_map_in_an_assumption() {
    let got = verdict(&format!(
        "(set-logic QF_MAPLIA){DECLS}
         (assert (map.contains_key n 3))
         (check-sat-assuming ((= n (as map.empty (Map Int Int)))))"
    ));
    assert!(
        got == "unsat" || got == "unknown",
        "UNSAT assumption answered `{got}`"
    );
}

/// An inner map of a nested map equated to the empty map, then read: the
/// read goes through a `select` of the outer value array.
#[test]
fn rejects_empty_map_as_an_inner_map() {
    assert_never_sat(
        "(declare-const mm (Map Int (Map Int Int)))
         (assert (= (map.get mm 1) (as map.empty (Map Int Int))))
         (assert (map.contains_key (map.get mm 1) 2))",
    );
}

/// A constructor equated to a function result: `h` returns maps, and each
/// application's carrier is one free array.
#[test]
fn rejects_insert_equated_to_a_function_result() {
    assert_never_sat(
        "(declare-fun h (Int) (Map Int Int))
         (assert (= (h 1) (map.insert (h 2) 3 4)))
         (assert (not (map.contains_key (h 1) 3)))",
    );
}

/// An insert at another key reads the same empty-map value at key 1.
#[test]
fn empty_map_reads_agree_through_an_insert_at_another_key() {
    let got = verdict(&with_decls(
        "(assert (= 5 (map.get (as map.empty (Map Int Int)) 1)))
         (assert (= 6 (map.get (map.insert (as map.empty (Map Int Int)) 2 7) 1)))",
    ));
    assert_eq!(got, "unsat");
}

// ---------------------------------------------------------------------------
// `map.subset` beyond syntactic reflexivity.
// ---------------------------------------------------------------------------

#[test]
fn rejects_negated_subset_of_equal_maps() {
    assert_never_sat("(assert (= m n)) (assert (not (map.subset m n)))");
}

/// deductive-checks's route: the USER declares `map.dom` / `map.subset`, and the map
/// theory decides the declared symbols as its own. Answered `sat` on
/// `7b6e639c98`; a gate that marked only the builtin operators as a map
/// problem let it through.
#[test]
fn rejects_negated_declared_subset_of_equal_maps() {
    assert_never_sat(
        "(declare-fun map.dom ((Map Int Int)) (Array Int Bool))
         (declare-fun map.subset ((Map Int Int) (Map Int Int)) Bool)
         (assert (= m n))
         (assert (not (map.subset m n)))",
    );
}

// ---------------------------------------------------------------------------
// Domain carriers for map terms that are not declared constants.
// ---------------------------------------------------------------------------

/// The reader goes straight through an `ite` whose branch is the empty map;
/// the `ite` gets one free carrier and the empty branch vanishes into it.
#[test]
fn rejects_reader_through_an_ite_with_an_empty_branch() {
    assert_never_sat(
        "(assert c)
         (assert (map.contains_key (ite c (as map.empty (Map Int Int)) n) 1))",
    );
}

/// The empty map exists, so no key is in every map. A bound map's carrier is
/// one constant that does not depend on the bound variable.
#[test]
fn rejects_every_map_containing_a_key() {
    assert_never_sat_in(
        "MAPLIA",
        "(assert (forall ((x (Map Int Int))) (map.contains_key x 1)))",
    );
}

#[test]
fn rejects_an_empty_map_witness_containing_a_key() {
    assert_never_sat_in(
        "MAPLIA",
        "(assert (exists ((x (Map Int Int)))
           (and (= x (as map.empty (Map Int Int))) (map.contains_key x 1))))",
    );
}

#[test]
fn rejects_reader_through_an_array_of_maps() {
    assert_never_sat(
        "(declare-const a (Array Int (Map Int Int)))
         (declare-const i Int)
         (declare-const j Int)
         (assert (= i j))
         (assert (map.contains_key (select (store a i (as map.empty (Map Int Int))) j) 1))",
    );
}

// ---------------------------------------------------------------------------
// Controls: the faithful fragment stays decided.
// ---------------------------------------------------------------------------

#[test]
fn keeps_readers_through_constructors_sat() {
    assert_sat(
        "(assert (map.contains_key (map.insert m 1 5) 1))
         (assert (= 5 (map.get (map.insert m 1 5) 1)))",
    );
}

#[test]
fn keeps_equal_declared_maps_sat() {
    assert_sat(
        "(assert (= n m))
         (assert (not (map.contains_key m 2)))
         (assert (map.contains_key n 1))",
    );
}

#[test]
fn keeps_equal_declared_maps_domain_congruent() {
    let got = verdict(&with_decls(
        "(assert (= n m))
         (assert (map.contains_key m 1))
         (assert (not (map.contains_key n 1)))",
    ));
    assert_eq!(got, "unsat");
}

/// `map.get` of the empty map only READS it (an arbitrary default value).
#[test]
fn keeps_a_read_of_the_empty_map_sat() {
    assert_sat("(assert (= 5 (map.get (as map.empty (Map Int Int)) 1)))");
}

#[test]
fn keeps_reflexive_subset_sat() {
    assert_sat("(assert (map.subset m m)) (assert (map.contains_key m 1))");
}

/// A TRUE ground subset. The gate withholds it (`map.subset` over different
/// operands), and loosening the pin to accept `unsat` would be wrong.
#[test]
fn true_ground_subset_is_never_unsat() {
    let got = verdict(&with_decls(
        "(assert (map.subset
           (map.insert (as map.empty (Map Int Int)) 1 5)
           (map.insert (map.insert (as map.empty (Map Int Int)) 1 5) 2 6)))",
    ));
    assert_ne!(got, "unsat");
}

/// A problem without a native map operator is never walked.
#[test]
fn keeps_plain_arrays_untouched() {
    let got = verdict(
        "(set-logic QF_ALIA)
         (declare-const a (Array Int Int))
         (declare-const b (Array Int Int))
         (assert (= a ((as const (Array Int Int)) 0)))
         (assert (distinct a b))
         (check-sat)",
    );
    assert_eq!(got, "sat");
}

// ---------------------------------------------------------------------------
// What a map is: a (value array, domain) pair, not an extensional finite map.
// ---------------------------------------------------------------------------

/// Two maps with the same (empty) domain and different value arrays are two
/// maps. Under extensional finite maps this would be `unsat`.
#[test]
fn semantics_maps_with_one_domain_can_differ_in_their_values() {
    let got = verdict(
        "(set-logic QF_MAPLIA)
         (declare-const m (Map Bool Int))
         (declare-const n (Map Bool Int))
         (assert (not (map.contains_key m true)))
         (assert (not (map.contains_key m false)))
         (assert (not (map.contains_key n true)))
         (assert (not (map.contains_key n false)))
         (assert (distinct m n))
         (check-sat)",
    );
    assert_eq!(got, "sat");
}

/// `map.remove` leaves the value array alone, so the value `map.insert` put
/// there is still what `map.get` reads.
#[test]
fn semantics_remove_keeps_the_value() {
    let got = verdict(&with_decls(
        "(assert (not (map.contains_key m 1)))
         (assert (= (map.get m 1) 7))
         (assert (not (= 5 (map.get (map.remove (map.insert m 1 5) 1) 1))))",
    ));
    assert_eq!(got, "unsat");
}
