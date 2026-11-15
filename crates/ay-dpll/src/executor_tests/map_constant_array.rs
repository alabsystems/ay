// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! A constant array written at a map sort (#map-value-semantics).
//!
//! `((as const (Map K V)) v)` is not the empty map, and the encoding gives it
//! no domain of its own, so the native-map gate
//! (`executor/model/native_map_gate.rs`) withholds a `sat` that rests on it.
//! Its values are all `v`, and a constant ARRAY beside a map stays decided.

use super::map_value_semantics::{verdict, with_decls};

/// `((as const (Map K V)) v)` is not the empty map, and nothing gives it a
/// domain. `a8ec8b4feb` read every constant-array map as the empty map, so
/// `(map.contains_key ((as const (Map Int Int)) 0) 1)` answered `unsat`,
/// yet this formula, which says the same through `n`, answered `sat`.
/// Whether it holds depends on that domain, so `unknown` is the answer.
#[test]
fn withholds_sat_over_a_constant_array_at_a_map_sort() {
    let got = verdict(&with_decls(
        "(assert (= n ((as const (Map Int Int)) 0)))
         (assert (map.contains_key n 1))",
    ));
    assert_eq!(got, "unknown");
}

/// The map sort can be written through `define-sort` synonyms, which the
/// sort erasure would otherwise hide.
#[test]
fn withholds_sat_over_a_constant_array_at_a_map_sort_synonym() {
    let wrong = [
        ("(define-sort IntMap () (Map Int Int))", "IntMap"),
        (
            "(define-sort IntMap () (Map Int Int)) (define-sort Alias () IntMap)",
            "Alias",
        ),
        ("(define-sort Same (T) T)", "(Same (Map Int Int))"),
        ("(define-sort IntTo (V) (Map Int V))", "(IntTo Int)"),
        (
            "(define-sort Same (T) T) (define-sort Wrap (U) (Same U))",
            "(Wrap (Map Int Int))",
        ),
    ]
    .into_iter()
    .filter_map(|(synonyms, sort)| {
        let got = verdict(&with_decls(&format!(
            "{synonyms}
             (assert (= n ((as const {sort}) 0)))
             (assert (map.contains_key n 1))"
        )));
        (got != "unknown").then(|| format!("{synonyms} / {sort}: `{got}`"))
    })
    .collect::<Vec<_>>();
    assert!(wrong.is_empty(), "{wrong:#?}");
}

/// Every value of the constant map is `v`, whatever its domain.
#[test]
fn keeps_values_of_a_constant_array_at_a_map_sort_unsat() {
    let got = verdict(&with_decls(
        "(assert (= n ((as const (Map Int Int)) 0)))
         (assert (= 1 (map.get n 5)))",
    ));
    assert_eq!(got, "unsat");
}

/// A constant ARRAY in a map problem stays decided, including through a
/// synonym that once named a map sort in a popped scope.
#[test]
fn keeps_a_constant_array_beside_a_map_sat() {
    for prefix in [
        "",
        "(push 1) (define-sort S () (Map Int Int)) (pop 1)
         (define-sort S () (Array Int Int))",
    ] {
        let sort = if prefix.is_empty() {
            "(Array Int Int)"
        } else {
            "S"
        };
        let got = verdict(&with_decls(&format!(
            "{prefix}
             (declare-const a (Array Int Int))
             (assert (= a ((as const {sort}) 0)))
             (assert (map.contains_key m 1))"
        )));
        assert_eq!(got, "sat", "{prefix}");
    }
}
