// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! End-to-end convergence regressions for array interface pruning.

use std::fmt::Write as _;

use ay_dpll::Executor;
use ntest::timeout;

fn shared_read_problem(array_count: usize, force_first_pair_equal: bool) -> String {
    let mut smt = String::from(
        "(set-logic QF_AX)\n\
         (declare-sort Index 0)\n\
         (declare-sort Element 0)\n\
         (declare-const i Index)\n",
    );
    for n in 0..array_count {
        writeln!(smt, "(declare-const a{n} (Array Index Element))")
            .expect("writing to String cannot fail");
    }
    smt.push_str("(assert (distinct");
    for n in 0..array_count {
        write!(smt, " (select a{n} i)").expect("writing to String cannot fail");
    }
    smt.push_str("))\n");
    if force_first_pair_equal {
        smt.push_str("(assert (= a0 a1))\n");
    }
    smt.push_str("(check-sat)\n");
    smt
}

fn free_store_base_problem(array_count: usize, force_first_pair_equal: bool) -> String {
    let mut smt = String::from(
        "(set-logic QF_AX)\n\
         (declare-sort Index 0)\n\
         (declare-sort Element 0)\n\
         (declare-const j Index)\n",
    );
    for n in 0..array_count {
        writeln!(smt, "(declare-const b{n} (Array Index Element))")
            .expect("writing to String cannot fail");
        writeln!(smt, "(declare-const i{n} Index)").expect("writing to String cannot fail");
        writeln!(smt, "(declare-const v{n} Element)").expect("writing to String cannot fail");
    }
    smt.push_str("(assert (distinct");
    for n in 0..array_count {
        write!(smt, " (select (store b{n} i{n} v{n}) j)").expect("writing to String cannot fail");
    }
    smt.push_str("))\n");
    if force_first_pair_equal {
        smt.push_str(
            "(assert (= b0 b1))\n\
             (assert (= i0 i1))\n\
             (assert (= v0 v1))\n",
        );
    }
    smt.push_str("(check-sat)\n");
    smt
}

fn execute(smt: &str) -> (Vec<String>, u64) {
    let commands = ay_frontend::parse(smt).expect("valid generated QF_AX input");
    let mut executor = Executor::new();
    let output = executor
        .execute_all(&commands)
        .expect("shared-read convergence fixture must execute");
    let requested_interface_eqs = executor
        .statistics()
        .get_int("arrays_requested_interface_eqs")
        .unwrap_or(0);
    (output, requested_interface_eqs)
}

/// Pairwise-distinct values read from independent arrays at one shared index
/// already prove every array pair distinct. Asking SAT to decide all O(N²)
/// array equalities is redundant and historically exhausted the refinement
/// rounds, returning `unknown` around this size.
#[test]
#[timeout(10_000)]
fn shared_read_distinct_arrays_converge_to_sat_without_interface_splits() {
    let (output, requested_interface_eqs) = execute(&shared_read_problem(48, false));

    assert_eq!(
        output,
        vec!["sat"],
        "read-distinguished arrays must converge to SAT, never resource-unknown"
    );
    assert_eq!(
        requested_interface_eqs, 0,
        "shared-read distinctness must suppress every redundant array split"
    );
}

/// The optimization must not turn a contradictory array equality into SAT.
/// Equal arrays have equal reads, which conflicts with the shared-read
/// distinctness assertion.
#[test]
#[timeout(10_000)]
fn forced_equal_read_distinct_arrays_remain_unsat() {
    let (output, _) = execute(&shared_read_problem(48, true));
    assert_eq!(
        output,
        vec!["unsat"],
        "shared-read pruning must preserve the forced-equality contradiction"
    );
}

/// Store bases that have no direct reads or equality edges are not shared
/// array interfaces. Splitting every pair of them caused quadratic refinement
/// on otherwise independent stores; the free-base filter must remove those
/// requests while the shared-read filter removes the resulting store pairs.
#[test]
#[timeout(10_000)]
fn independent_free_store_bases_converge_to_sat_without_interface_splits() {
    let (output, requested_interface_eqs) = execute(&free_store_base_problem(48, false));

    assert_eq!(
        output,
        vec!["sat"],
        "independent stores over free bases must converge to SAT"
    );
    assert_eq!(
        requested_interface_eqs, 0,
        "free store bases must not generate redundant array splits"
    );
}

/// Equality edges disqualify a store base from the free-array optimization.
/// Equal bases, indices, and values make the first two stores—and therefore
/// their reads—equal, contradicting the generated distinctness assertion.
#[test]
#[timeout(10_000)]
fn forced_equal_free_store_bases_remain_unsat() {
    let (output, _) = execute(&free_store_base_problem(48, true));
    assert_eq!(
        output,
        vec!["unsat"],
        "the free-base optimization must preserve forced store equality"
    );
}
