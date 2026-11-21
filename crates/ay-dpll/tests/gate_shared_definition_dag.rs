// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! AY-SMT-3 (#gate-dt-free-dag): the SAT model gate must finish on Boolean
//! `define-fun` DAGs with exponentially many paths and few distinct terms.
//!
//! The first query of SMT-COMP 2026 incremental QF_UFLRA 27a0035f is 14,444
//! nested Boolean `define-fun`s: 2,523 distinct terms, about 9.4e17
//! root-to-leaf paths. The search found a model at once; the gate's
//! definition index then walked every path (`term_is_array_dt_free`, and
//! `index_walk` down to its depth bound) and the query timed out. The two
//! scripts below have the same shape. On main of 2026-11-19 both run into the
//! deadline (`-T:30`: `unknown`, "the solve did not stop within 2.0 s of the
//! deadline") with no recovery scope involved. Each must now answer `sat`,
//! confirmed by the gate, in well under the test timeout.

mod common;

use ntest::timeout;

/// `b_k = (or (and b_{k-1} p_k) (and q_k b_{k-1}))`: 2^levels paths through
/// the `or` disjuncts the definition index tests for array/datatype freedom.
fn shared_disjunct_script(levels: usize) -> String {
    let mut s = String::from("(set-logic QF_UFLRA)\n(declare-fun x () Real)\n");
    s.push_str("(declare-fun z () Bool)\n");
    for k in 1..=levels {
        s.push_str(&format!(
            "(declare-fun p{k} () Bool)\n(declare-fun q{k} () Bool)\n"
        ));
    }
    s.push_str("(define-fun b0 () Bool (< x 1.0))\n");
    for k in 1..=levels {
        let j = k - 1;
        s.push_str(&format!(
            "(define-fun a{k} () Bool (and b{j} p{k}))\n\
             (define-fun c{k} () Bool (and q{k} b{j}))\n\
             (define-fun b{k} () Bool (or a{k} c{k}))\n"
        ));
    }
    s.push_str(&format!(
        "(assert (or z b{levels}))\n(assert (not z))\n(check-sat)\n"
    ));
    s
}

/// `b_k = (and (or r_k b_{k-1}) (or s_k b_{k-1}))` with every `r_k`, `s_k`
/// asserted false: each `or` has the unique survivor `b_{k-1}`, so the
/// definition index descends both conjuncts into the same definition at
/// every level (2^32 visits at its depth bound of 32 on the old walk).
fn shared_conjunct_script(levels: usize) -> String {
    let mut s = String::from("(set-logic QF_UFLRA)\n(declare-fun x () Real)\n");
    for k in 1..=levels {
        s.push_str(&format!(
            "(declare-fun r{k} () Bool)\n(declare-fun s{k} () Bool)\n"
        ));
    }
    s.push_str("(define-fun b0 () Bool (< x 1.0))\n");
    for k in 1..=levels {
        let j = k - 1;
        s.push_str(&format!(
            "(define-fun b{k} () Bool (and (or r{k} b{j}) (or s{k} b{j})))\n"
        ));
    }
    s.push_str(&format!("(assert b{levels})\n"));
    for k in 1..=levels {
        s.push_str(&format!("(assert (not r{k}))\n(assert (not s{k}))\n"));
    }
    s.push_str("(check-sat)\n");
    s
}

fn assert_gate_confirms_sat(script: &str) {
    let (output, gate) = common::solve_authored_vec_with_gate_result(script);
    assert_eq!(
        output,
        vec!["sat".to_string()],
        "the script is satisfiable; gate: {gate:?}"
    );
    assert!(
        gate.is_some(),
        "a `sat` must carry the gate's confirmation, got none"
    );
}

#[test]
#[timeout(120_000)]
fn gate_confirms_sat_on_shared_disjunct_dag_with_2_pow_64_paths() {
    assert_gate_confirms_sat(&shared_disjunct_script(64));
}

#[test]
#[timeout(120_000)]
fn gate_confirms_sat_on_shared_conjunct_dag_with_2_pow_40_paths() {
    assert_gate_confirms_sat(&shared_conjunct_script(40));
}

/// AY-SMT-3, second cause: `d` is pinned only by an asserted definition that
/// reads `d` itself. The gate cut that cycle and answered "model does not pin
/// this leaf: d" (`unknown`) on this satisfiable query, reduced from check-sat
/// 10 of SMT-COMP 2026 incremental QF_AUFLIA 2721719d (yices2: sat). The gate
/// now solves the definition as a fixpoint and re-checks every assertion.
#[test]
#[timeout(120_000)]
fn gate_confirms_sat_on_a_self_referential_nested_store_definition() {
    assert_gate_confirms_sat(
        "(set-logic QF_AUFLIA)\n\
         (declare-fun c () (Array Int (Array Int Int)))\n\
         (declare-fun d () (Array Int (Array Int Int)))\n\
         (declare-fun i () Int)\n\
         (declare-fun j () Int)\n\
         (assert (= (store c i (store (select c i) j (select (select d i) j))) d))\n\
         (check-sat)\n",
    );
}
