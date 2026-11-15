// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Trust's external-codegen gate obligation for `(a / b) ^ c`, built through the
//! public `Solver` API exactly as external-codegen-bridge's `discharge_equal_pre`
//! builds it: the same calls in the same order, `QF_ABV`, and a per-query
//! budget in place of the gate's 120 s.
//!
//! The machine side is the decoded AArch64 lowering (`mov w0, w0` ...,
//! `udiv`/`sdiv`, `eor`): every register read is `extract(zext(0 | Wn))`, and
//! the divide carries the architecture's divide-by-zero guard
//! `ite(b = 0, 0, a / b)`. The intended side is the IR's `(a / b) ^ c`, under
//! the gate's `b != 0` precondition.
//!
//! Ay `d739a98f5` swept every bit-blast circuit of at least 2,000 gates before
//! trying to refute it. The unsigned lemma blasts one 32-bit divider under both
//! sides (17,531 gates); sweeping it used up the sweep's 120 s wall on divider
//! candidates before its closing refutation ran, and the strict wire screen
//! renders that lemma about six times per publication. Trust's gate (ay built
//! at opt-level 0) then answered `unknown (timeout)` at its 120 s budget where
//! it had answered `unsat` in about 3 s, and four external-codegen-bridge gate tests
//! went from `[VALIDATED]` to `Unknown`. The root refutes directly in 129
//! conflicts.

use ay_dpll::api::{Logic, Solver, SolverConfig, Sort, Term};
use ntest::timeout;
use num_bigint::BigInt;
use std::time::Duration;

/// A sixth of external-codegen-bridge's default per-query budget
/// (`gate_solver_config`, 120 s). This profile compiles ay at opt-level 1,
/// where the swept-first publication still answered `unsat`, but only after
/// 96.8 s; here the query answers in about 0.3 s.
const QUERY_BUDGET: Duration = Duration::from_secs(20);

/// `Wn` as the gate reads it: the low word of the 64-bit register `Xn`.
fn low_word(solver: &mut Solver, register: &str) -> Term {
    let x = solver
        .try_declare_const(register, Sort::bitvec(64))
        .expect("declare register");
    solver.try_bvextract(x, 31, 0).expect("low word")
}

/// `Wn` as the decoded machine code reads it after `mov wN, wN`
/// (`orr wN, wzr, wN`), written back into and read out of `Xn`.
fn machine_word(solver: &mut Solver, register: &str) -> Term {
    let zero = zero32(solver);
    let w = low_word(solver, register);
    let moved = solver.try_bvor(zero, w).expect("orr");
    let written = solver.try_bvzeroext(moved, 32).expect("write back");
    solver.try_bvextract(written, 31, 0).expect("read back")
}

fn zero32(solver: &mut Solver) -> Term {
    solver
        .try_bv_const_bigint(&BigInt::from(0), 32)
        .expect("zero word")
}

fn divide(solver: &mut Solver, signed: bool, a: Term, b: Term) -> Term {
    if signed {
        solver.try_bvsdiv(a, b).expect("sdiv")
    } else {
        solver.try_bvudiv(a, b).expect("udiv")
    }
}

/// Assert the gate's obligation and check it. Without `precondition` the
/// divisor may be zero, where the lowering yields 0 and SMT-LIB's quotient
/// does not: the negative control.
fn gate_obligation(signed: bool, precondition: bool) -> Solver {
    let config = SolverConfig::default().with_timeout(QUERY_BUDGET);
    let mut solver = Solver::try_new_with_config(Logic::QfAbv, config).expect("solver");

    // Machine side: extract(zext(xor(extract(zext(ite(b == 0, 0, a / b))), c))).
    let b = machine_word(&mut solver, "X1");
    let zero = zero32(&mut solver);
    let divisor_is_zero = solver.try_eq(b, zero).expect("b == 0");
    let zero = zero32(&mut solver);
    let a = machine_word(&mut solver, "X0");
    let b = machine_word(&mut solver, "X1");
    let quotient = divide(&mut solver, signed, a, b);
    let guarded = solver
        .try_ite(divisor_is_zero, zero, quotient)
        .expect("guard");
    let guarded = solver.try_bvzeroext(guarded, 32).expect("write back");
    let guarded = solver.try_bvextract(guarded, 31, 0).expect("read back");
    let c = machine_word(&mut solver, "X2");
    let machine = solver.try_bvxor(guarded, c).expect("eor");
    let machine = solver.try_bvzeroext(machine, 32).expect("write back");
    let machine = solver.try_bvextract(machine, 31, 0).expect("read back");

    // Intended side: (a / b) ^ c over the argument words.
    let a = low_word(&mut solver, "X0");
    let b = low_word(&mut solver, "X1");
    let quotient = divide(&mut solver, signed, a, b);
    let c = low_word(&mut solver, "X2");
    let intended = solver.try_bvxor(quotient, c).expect("xor");

    let equal = solver.try_eq(machine, intended).expect("equality");
    let differ = solver.try_not(equal).expect("differ");
    let goal = if precondition {
        let b = low_word(&mut solver, "X1");
        let zero = zero32(&mut solver);
        let is_zero = solver.try_eq(b, zero).expect("b == 0");
        let nonzero = solver.try_not(is_zero).expect("b != 0");
        solver.try_and(nonzero, differ).expect("pre and differ")
    } else {
        differ
    };
    solver.try_assert_term(goal).expect("assert");
    solver
}

#[test]
#[timeout(600_000)]
fn external_codegen_unsigned_quotient_xor_is_unsat_within_the_query_budget() {
    let mut solver = gate_obligation(false, true);
    let result = solver.check_sat();
    assert!(
        result.is_unsat(),
        "the guarded udiv lowering equals (a / b) ^ c when b != 0: got {result:?} ({:?})",
        solver.get_reason_unknown()
    );
}

#[test]
#[timeout(600_000)]
fn external_codegen_signed_quotient_xor_is_unsat_within_the_query_budget() {
    let mut solver = gate_obligation(true, true);
    let result = solver.check_sat();
    assert!(
        result.is_unsat(),
        "the guarded sdiv lowering equals (a / b) ^ c when b != 0: got {result:?} ({:?})",
        solver.get_reason_unknown()
    );
}

#[test]
#[timeout(600_000)]
fn external_codegen_quotient_xor_without_the_divisor_precondition_is_sat() {
    let mut solver = gate_obligation(false, false);
    let result = solver.check_sat();
    assert!(
        result.is_sat(),
        "at b = 0 the lowering yields 0 ^ c and SMT-LIB's quotient does not: got {result:?}"
    );
}
