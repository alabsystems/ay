// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! model-checker-consumer BMC queries that sum symbolic `f32`s exactly (ask
//! `2026-10-14-symbolic-fp-add-unknown-d80d17a90`).
//!
//! model-checker-consumer's BMC lane encodes `[a, b].iter().sum()` as an `fp.add` RNE chain
//! beside the slice and iterator datatypes, so every query below is
//! `(set-logic ALL)` over arrays, bit-vectors, floating point and
//! single-constructor datatypes. The frontend splits each datatype constant
//! into field constants, which leaves `(= data s!fld_data)` behind for every
//! array field nothing reads. The ABVFP lane's array elimination refused the
//! whole window for that one occurrence, the FP bit-blaster could not encode
//! the remaining `select`s, and all three answered `unknown (unsupported)` in
//! 0.01 s. The symbolic query also reads its elements through
//! `(select (store (store a 0 x) 1 y) i)`, which the elimination only accepts
//! after the read-over-write expansion, and whose expanded `ite (= ...)`
//! conditions the bit-blaster encodes since DR-47. The fixtures are
//! byte-for-byte the files model-checker-consumer attached (sha256 `c742adbb…`, `76d45c9d…`,
//! `59aa9bc9…`); the expected verdicts are z3 5.1.0's.

use crate::common::{solve_authored_vec, solve_authored_vec_with_gate_result};
use ay_dpll::Executor;
use ay_frontend::parse;

const UNREAD_BESIDE_BUG: &str =
    include_str!("../fixtures/model_checker_consumer_f32_sum_unread_beside_bug.smt2");
const SMALL_ELEMENTS_INFINITE: &str =
    include_str!("../fixtures/model_checker_consumer_f32_sum_small_elements_infinite.smt2");
const SYMBOLIC_SUM_BUG: &str =
    include_str!("../fixtures/model_checker_consumer_f32_symbolic_sum_bug.smt2");

/// Insert `extra` assertions right before the query's `check-sat`.
fn with_assertions(query: &str, extra: &str) -> String {
    assert_eq!(query.matches("(check-sat)").count(), 1);
    query.replace("(check-sat)", &format!("{extra}\n(check-sat)"))
}

/// The response lines of an authored run, with the run's
/// `abvfp_unread_arrays.eliminated` and `unknown.detail` statistics.
fn solve_with_unread_stats(smt: &str) -> (Vec<String>, Option<u64>, Option<String>) {
    let commands = parse(smt).unwrap_or_else(|err| panic!("parse failed: {err}"));
    let mut exec = Executor::new();
    let mut output = Vec::new();
    for command in &commands {
        if let Some(line) = exec
            .execute_authored(command)
            .unwrap_or_else(|err| panic!("execution failed: {err}"))
        {
            output.push(line);
        }
    }
    let stats = exec.statistics();
    (
        output,
        stats.get_int("abvfp_unread_arrays.eliminated"),
        stats.get_string("unknown.detail").map(str::to_owned),
    )
}

/// The value of a 32-bit constant in a `get-value` response line.
fn bv32(output: &[String], name: &str) -> u32 {
    let needle = format!("({name} #x");
    let line = output
        .iter()
        .find(|line| line.contains(&needle))
        .unwrap_or_else(|| panic!("no value for {name} in {output:?}"));
    let start = line.find(&needle).expect("needle present") + needle.len();
    u32::from_str_radix(&line[start..start + 8], 16).expect("eight hex digits")
}

/// The real bug beside an unread sum (`x != 7` is violated): `sat`, and the
/// witness passes the independent gate on the authored assertions.
#[test]
fn unread_sum_beside_bug_is_sat_with_a_confirmed_witness() {
    let (output, gate) = solve_authored_vec_with_gate_result(UNREAD_BESIDE_BUG);
    assert_eq!(
        output.first().map(String::as_str),
        Some("sat"),
        "{output:?}"
    );
    assert_eq!(gate.as_deref(), Some("confirmed-sat"), "{output:?}");
    assert!(
        output
            .iter()
            .any(|l| l.contains("(ay_violation_kani_assert_0 true)")),
        "{output:?}"
    );
    assert!(
        output.iter().any(|l| l.contains("(ay_any_5 #x07)")),
        "{output:?}"
    );
}

/// Two finite `f32`s whose exponents are both below 16 cannot sum to an
/// infinity: `unsat`.
#[test]
fn small_elements_cannot_sum_to_infinity() {
    let output = solve_authored_vec(SMALL_ELEMENTS_INFINITE);
    assert_eq!(
        output.first().map(String::as_str),
        Some("unsat"),
        "{output:?}"
    );
}

/// `assert!(s.is_finite())` over a symbolic two-element sum fails: `sat`, and
/// the published elements really are finite `f32`s whose RNE sum overflows.
#[test]
fn symbolic_sum_bug_is_sat_and_its_witness_overflows() {
    let (output, gate) = solve_authored_vec_with_gate_result(SYMBOLIC_SUM_BUG);
    assert_eq!(
        output.first().map(String::as_str),
        Some("sat"),
        "{output:?}"
    );
    assert_eq!(gate.as_deref(), Some("confirmed-sat"), "{output:?}");
    assert!(
        output
            .iter()
            .any(|l| l.contains("(ay_violation_kani_assert_2 true)")),
        "{output:?}"
    );
    let a = f32::from_bits(bv32(&output, "ay_any_1"));
    let b = f32::from_bits(bv32(&output, "ay_any_2"));
    assert!(a.is_finite() && b.is_finite(), "{a} {b}");
    assert!((a + b).is_infinite(), "{a} + {b} must overflow");
}

/// Negative twin of the symbolic sum: with both exponents below 16 no sum
/// overflows and both indices are in bounds, so no check can fail. `unsat`;
/// a `sat` here would be a witness the new path invented.
#[test]
fn symbolic_sum_of_small_elements_is_unsat() {
    let query = with_assertions(
        SYMBOLIC_SUM_BUG,
        "(assert (bvult ((_ extract 30 23) ay_any_1) #x10))\n\
         (assert (bvult ((_ extract 30 23) ay_any_2) #x10))",
    );
    let output = solve_authored_vec(&query);
    assert_eq!(
        output.first().map(String::as_str),
        Some("unsat"),
        "{output:?}"
    );
}

/// Negative twin of the elimination's OCCURRENCE condition: once the slice's
/// data field IS read, its defining equality is a real constraint and must
/// stay; only the iterator's unread field goes. Reading element 0 as anything
/// but `ay_any_0` is a contradiction (z3 5.1.0: `unsat`). The model gate would
/// turn a `sat` built on a wrongly dropped equality into `unknown`, so the
/// eliminated count is what catches an over-eager elimination. A residual
/// `unknown` names its gap instead of the generic theory-combination text.
#[test]
fn a_read_slice_field_keeps_its_definition() {
    let query = with_assertions(
        UNREAD_BESIDE_BUG,
        "(assert (not (= (select (fld_data |f32_sym_sum_unread_beside_bug::local_6_0|) \
         #x0000000000000000) ay_any_0)))",
    );
    let (output, eliminated, detail) = solve_with_unread_stats(&query);
    let verdict = output.first().map(String::as_str);
    assert_ne!(verdict, Some("sat"), "{output:?}");
    assert_eq!(eliminated, Some(1), "{output:?}");
    if verdict == Some("unknown") {
        let detail = detail.unwrap_or_default();
        assert!(detail.contains("ABVFP"), "{detail}");
    }
}

/// Negative twin of the elimination's POLARITY condition, the one an `unsat`
/// depends on (the model gate checks only `sat`): a negated equality over two
/// otherwise unused arrays forces them apart, so it must never be replaced by
/// `true`. z3 5.1.0: `sat`.
#[test]
fn a_negated_unread_array_equality_is_never_refuted() {
    let query = with_assertions(
        UNREAD_BESIDE_BUG,
        "(declare-const p_arr (Array (_ BitVec 64) (_ BitVec 32)))\n\
         (declare-const q_arr (Array (_ BitVec 64) (_ BitVec 32)))\n\
         (assert (not (= p_arr q_arr)))",
    );
    let output = solve_authored_vec(&query);
    assert_ne!(
        output.first().map(String::as_str),
        Some("unsat"),
        "{output:?}"
    );
}

/// Two finite `f32`s whose RNE sum is infinite, beside `links` unread memory
/// versions `m(k) = (store m(k-1) a(k) v(k))` as a BMC unrolling leaves them.
fn unread_memory_chain_beside_sum(links: usize, extra: &str) -> String {
    let mut query = String::from(
        "(set-logic QF_ABVFP)\n\
         (set-option :produce-models true)\n\
         (declare-const x (_ BitVec 32))\n\
         (declare-const y (_ BitVec 32))\n\
         (assert (not (fp.isInfinite ((_ to_fp 8 24) x))))\n\
         (assert (not (fp.isInfinite ((_ to_fp 8 24) y))))\n\
         (assert (fp.isInfinite (fp.add RNE ((_ to_fp 8 24) x) ((_ to_fp 8 24) y))))\n\
         (declare-const m0 (Array (_ BitVec 64) (_ BitVec 8)))\n",
    );
    for k in 1..=links {
        query.push_str(&format!(
            "(declare-const m{k} (Array (_ BitVec 64) (_ BitVec 8)))\n\
             (declare-const a{k} (_ BitVec 64))\n\
             (declare-const v{k} (_ BitVec 8))\n\
             (assert (= m{k} (store m{} a{k} v{k})))\n",
            k - 1
        ));
    }
    query.push_str(extra);
    query.push_str("(check-sat)\n");
    query
}

/// A 100-version unread memory chain, longer than the elimination's round
/// cap, unwinds whole: each dropped definition leaves the previous version
/// with one occurrence. `sat` (z3 5.1.0), gate-confirmed.
#[test]
fn a_long_unread_memory_chain_beside_an_overflowing_sum_is_sat() {
    let (output, gate) =
        solve_authored_vec_with_gate_result(&unread_memory_chain_beside_sum(100, ""));
    assert_eq!(
        output.first().map(String::as_str),
        Some("sat"),
        "{output:?}"
    );
    assert_eq!(gate.as_deref(), Some("confirmed-sat"), "{output:?}");
}

/// Its infinite-sum negative twin: with both exponents below 16 the sum is
/// finite. `unsat` (z3 5.1.0).
#[test]
fn a_long_unread_memory_chain_beside_small_elements_is_unsat() {
    let query = unread_memory_chain_beside_sum(
        100,
        "(assert (bvult ((_ extract 30 23) x) #x10))\n\
         (assert (bvult ((_ extract 30 23) y) #x10))\n",
    );
    let output = solve_authored_vec(&query);
    assert_eq!(
        output.first().map(String::as_str),
        Some("unsat"),
        "{output:?}"
    );
}
