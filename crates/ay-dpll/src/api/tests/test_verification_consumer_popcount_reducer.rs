// Copyright 2026 Andrew Yates, Inc.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use crate::api::{Logic, SolveResult, Solver, Sort, Term};
use std::time::Duration;

fn count8_log_body(solver: &mut Solver, n: Term) -> Term {
    let zero = solver.int_const(0);
    let one = solver.int_const(1);
    let mut terms = Vec::with_capacity(8);

    for bit in 0..8 {
        let modulus = solver.int_const(1_i64 << (bit + 1));
        let threshold = solver.int_const(1_i64 << bit);
        let remainder = solver
            .try_modulo(n, modulus)
            .expect("Int modulo term should be constructible");
        let bit_is_zero = solver
            .try_lt(remainder, threshold)
            .expect("Int comparison should be constructible");
        let contribution = solver
            .try_ite(bit_is_zero, zero, one)
            .expect("Int-valued ite should be constructible");
        terms.push(contribution);
    }

    solver
        .try_add_many(&terms)
        .expect("sum of Int bit contributions should be constructible")
}

fn bv64(solver: &mut Solver, value: u64) -> Term {
    solver
        .try_bv_const_u64(value, 64)
        .expect("64-bit BV constant should be constructible")
}

fn int_to_bv64(solver: &mut Solver, value: Term) -> Term {
    solver
        .try_int2bv(value, 64)
        .expect("Int to BV64 conversion should be constructible")
}

fn bv_to_int(solver: &mut Solver, value: Term) -> Term {
    solver
        .try_bv2int(value)
        .expect("BV to unsigned Int conversion should be constructible")
}

fn bv_lshr_const(solver: &mut Solver, value: Term, shift: u64) -> Term {
    let amount = bv64(solver, shift);
    solver
        .try_bvlshr(value, amount)
        .expect("BV logical shift should be constructible")
}

fn bv_and_const(solver: &mut Solver, value: Term, mask: u64) -> Term {
    let mask = bv64(solver, mask);
    solver
        .try_bvand(value, mask)
        .expect("BV and should be constructible")
}

fn swar_count8_result(solver: &mut Solver, n: Term) -> Term {
    let n_bv = int_to_bv64(solver, n);
    let shifted_one = bv_lshr_const(solver, n_bv, 1);
    let masked_one = bv_and_const(solver, shifted_one, 0x55);
    let masked_one_int = bv_to_int(solver, masked_one);
    let stage1 = solver
        .try_sub(n, masked_one_int)
        .expect("first SWAR subtraction should be constructible");

    let stage1_bv = int_to_bv64(solver, stage1);
    let stage1_low = bv_and_const(solver, stage1_bv, 0x33);
    let stage1_low_int = bv_to_int(solver, stage1_low);
    let stage1_shifted = bv_lshr_const(solver, stage1_bv, 2);
    let stage1_high = bv_and_const(solver, stage1_shifted, 0x33);
    let stage1_high_int = bv_to_int(solver, stage1_high);
    let stage2 = solver
        .try_add(stage1_low_int, stage1_high_int)
        .expect("second SWAR addition should be constructible");

    let stage2_bv = int_to_bv64(solver, stage2);
    let stage2_shifted = bv_lshr_const(solver, stage2_bv, 4);
    let stage2_shifted_int = bv_to_int(solver, stage2_shifted);
    let stage3 = solver
        .try_add(stage2, stage2_shifted_int)
        .expect("third SWAR addition should be constructible");
    let stage3_bv = int_to_bv64(solver, stage3);
    let result_bv = bv_and_const(solver, stage3_bv, 0x0f);
    bv_to_int(solver, result_bv)
}

#[test]
fn test_verification_consumer_count8_transparent_logic_fn_axiom_entails_popcount_value() {
    // The transparent logic-function axiom `(forall (n) (= count8_log_body(n)
    // (logic_count8__log n)))` is NOT a free "complete it however you like"
    // definition — it fully PINS `logic_count8__log` to integer popcount.
    // Asserting `(logic_count8__log 7) != 3` (popcount(7) == 3) must therefore
    // be refuted: the solver instantiates the axiom at 7, evaluates
    // count8_log_body(7) == 3 by pure arithmetic, and derives Unsat. This is the
    // load-bearing fact behind the soundness of #8969 below: because the axiom
    // pins the UF, the popcount verification condition is genuinely UNSAT, so a
    // SAT answer there would be a wrong (unsound) result.
    let mut solver = Solver::new(Logic::Uflia);
    solver.set_timeout(Some(Duration::from_secs(30)));

    let count8 = solver
        .try_declare_fun("logic_count8__log", &[Sort::Int], Sort::Int)
        .expect("declare transparent logic function");
    let qn = solver.fresh_var("n", Sort::Int);
    let count8_qn = solver
        .try_apply(&count8, &[qn])
        .expect("apply count8 to quantified variable");
    let rhs_qn = count8_log_body(&mut solver, qn);
    let axiom_body = solver.try_eq(rhs_qn, count8_qn).expect("axiom body");
    let axiom = solver
        .try_forall_with_triggers(&[qn], axiom_body, &[&[count8_qn]])
        .expect("axiom with application trigger");
    solver.try_assert_term(axiom).expect("assert axiom");

    let seven = solver.int_const(7);
    let three = solver.int_const(3);
    let c8_7 = solver.try_apply(&count8, &[seven]).expect("count8(7)");
    let eq = solver.try_eq(c8_7, three).expect("count8(7) = 3");
    let ne = solver.try_not(eq).expect("count8(7) != 3");
    solver.try_assert_term(ne).expect("assert count8(7) != 3");

    assert_eq!(
        solver.check_sat(),
        SolveResult::unsat(),
        "the transparent axiom entails count8(7) = popcount(7) = 3, so \
         count8(7) != 3 must be Unsat — the UF is pinned, not free"
    );
}

#[test]
fn test_verification_consumer_count8_transparent_logic_fn_vc_must_not_be_wrong_sat_8969() {
    // verification-consumer `bitvectors/popcount.rs::count8` reduces to a transparent
    // logic-function axiom for `logic_count8__log` plus a SWAR/BV-derived
    // implementation result, then asserts the NEGATED postcondition
    // `not (result == count8(n) and result <= 8)` to look for a counterexample.
    //
    // SOUNDNESS: this verification condition is UNSAT. The SWAR byte-popcount is
    // correct, so for every n in [0, 255] the implementation `result == swar(n)`
    // equals the spec `count8(n)` (the axiom pins it to popcount, see the
    // entailment test above) and that value is <= 8. Hence the negated
    // postcondition is unsatisfiable and NO counterexample exists.
    //
    // The solver cannot bit-blast the SWAR/BV pipeline against the LIA spec, so
    // it CANNOT prove the Unsat; the sound, honest verdict is therefore Unknown
    // (returning Unsat would require real BV+quantifier integration; that is the
    // ideal future result). What the solver must NEVER do is return Sat: a Sat
    // here is a fabricated counterexample to correct code — a wrong answer.
    //
    // Regression: a UF-completion relaxation that classifies this `forall` as
    // "satisfiable by freely completing count8" produces exactly that wrong Sat,
    // because the BV implementation term is opaque to model validation (it is
    // recorded as an incomplete fallback) and so the MBQI re-validation backstop
    // cannot refute it. This test pins the invariant: result is Unknown (today)
    // or Unsat (ideal), never Sat.
    let mut solver = Solver::new(Logic::Uflia);
    solver.set_timeout(Some(Duration::from_secs(30)));

    let count8 = solver
        .try_declare_fun("logic_count8__log", &[Sort::Int], Sort::Int)
        .expect("declare transparent logic function");

    let qn = solver.fresh_var("n", Sort::Int);
    let count8_qn = solver
        .try_apply(&count8, &[qn])
        .expect("apply count8 to quantified variable");
    let rhs_qn = count8_log_body(&mut solver, qn);
    let axiom_body = solver
        .try_eq(rhs_qn, count8_qn)
        .expect("transparent function axiom body");
    let axiom = solver
        .try_forall_with_triggers(&[qn], axiom_body, &[&[count8_qn]])
        .expect("transparent function axiom with application trigger");
    solver
        .try_assert_term(axiom)
        .expect("assert transparent function axiom");

    let n = solver.declare_const("n", Sort::Int);
    let n_view = solver.declare_const("n_view", Sort::Int);
    let result = solver.declare_const("result", Sort::Int);
    let result_view = solver.declare_const("result_view", Sort::Int);

    let n_view_is_n = solver.try_eq(n_view, n).expect("n_view = n");
    solver
        .try_assert_term(n_view_is_n)
        .expect("assert n_view = n");
    let result_view_is_result = solver
        .try_eq(result_view, result)
        .expect("result_view = result");
    solver
        .try_assert_term(result_view_is_result)
        .expect("assert result_view = result");

    let zero = solver.int_const(0);
    let n_ge_zero = solver.try_ge(n_view, zero).expect("n_view >= 0");
    solver.try_assert_term(n_ge_zero).expect("assert n >= 0");
    let max_u8 = solver.int_const(255);
    let n_le_u8 = solver.try_le(n_view, max_u8).expect("n_view <= 255");
    solver.try_assert_term(n_le_u8).expect("assert n <= 255");

    let rhs_n = swar_count8_result(&mut solver, n);
    let result_is_rhs = solver
        .try_eq(result, rhs_n)
        .expect("implementation result equals popcount RHS");
    solver
        .try_assert_term(result_is_rhs)
        .expect("assert implementation result");

    let count8_n = solver
        .try_apply(&count8, &[n])
        .expect("apply count8 to ground n");
    let result_matches_spec = solver
        .try_eq(result_view, count8_n)
        .expect("result matches transparent spec function");
    let eight = solver.int_const(8);
    let result_le_eight = solver.try_le(result_view, eight).expect("result <= 8");
    let postcondition = solver
        .try_and(result_matches_spec, result_le_eight)
        .expect("popcount postcondition");
    let negated_post = solver
        .try_not(postcondition)
        .expect("negated popcount postcondition");
    solver
        .try_assert_term(negated_post)
        .expect("assert negated popcount postcondition");

    let verdict = solver.check_sat();
    assert!(
        !verdict.result().is_sat(),
        "popcount VC is UNSAT (SWAR impl is correct); solver must return \
         Unknown (sound conservative) or Unsat (ideal), never a wrong Sat. \
         Got {verdict:?}"
    );
}

// --- Adversarial soundness guards for the UF-completion SAT path
// (`uf_definition_supported_by_completion` / `result_mapping`). When a
// `(forall (n) (= (f n) ...))` axiom is treated as "satisfiable by completing
// `f`", that is sound ONLY if a *conflicting* ground constraint on `f` is still
// refuted (here, via E-matching / model-driven MBQI re-validation). These tests
// pin that firewall: a contradicting ground fact must yield Unsat, never Sat.

#[test]
fn test_transparent_logic_fn_total_arith_conflicting_ground_is_unsat() {
    // `(forall (n) (= (f n) (ite (< n 0) 0 1)))` defines f(5) = 1, but the
    // ground assertion pins f(5) = 0. The completion certificate must NOT
    // shortcut this to Sat — model-driven re-instantiation at n=5 contradicts
    // the ground equality, so the only sound answer is Unsat.
    let mut solver = Solver::new(Logic::Uflia);
    solver.set_timeout(Some(Duration::from_secs(30)));

    let f = solver
        .try_declare_fun("f", &[Sort::Int], Sort::Int)
        .expect("declare f");
    let qn = solver.fresh_var("n", Sort::Int);
    let f_qn = solver.try_apply(&f, &[qn]).expect("apply f to n");
    let zero = solver.int_const(0);
    let one = solver.int_const(1);
    let n_lt_zero = solver.try_lt(qn, zero).expect("n < 0");
    let total_arith = solver
        .try_ite(n_lt_zero, zero, one)
        .expect("ite total-arith value side");
    let axiom_body = solver.try_eq(f_qn, total_arith).expect("f n = ite ...");
    let axiom = solver
        .try_forall_with_triggers(&[qn], axiom_body, &[&[f_qn]])
        .expect("forall axiom with trigger");
    solver.try_assert_term(axiom).expect("assert forall axiom");

    let five = solver.int_const(5);
    let f_five = solver.try_apply(&f, &[five]).expect("apply f to 5");
    let f_five_eq_zero = solver.try_eq(f_five, zero).expect("f 5 = 0");
    solver
        .try_assert_term(f_five_eq_zero)
        .expect("assert conflicting ground f(5) = 0");

    let result = solver.check_sat();
    assert_eq!(
        result,
        SolveResult::unsat(),
        "the completion SAT path must not mask a ground constraint that \
         contradicts the universal definition (would be wrong-SAT)"
    );
}

#[test]
fn test_transparent_logic_fn_total_arith_mod_conflicting_ground_is_unsat() {
    // Same firewall, mirroring count8's `mod`-bearing value side and a `logic_`
    // head (so it passes the div/mod head policy at mbqi.rs:1568). The
    // completion defines `(logic_g__log 5) = (mod 5 3) = 2`, but the ground
    // assertion pins it to 0 → Unsat.
    let mut solver = Solver::new(Logic::Uflia);
    solver.set_timeout(Some(Duration::from_secs(30)));

    let g = solver
        .try_declare_fun("logic_g__log", &[Sort::Int], Sort::Int)
        .expect("declare logic_g__log");
    let qn = solver.fresh_var("n", Sort::Int);
    let g_qn = solver.try_apply(&g, &[qn]).expect("apply g to n");
    let three = solver.int_const(3);
    let n_mod_three = solver.try_modulo(qn, three).expect("n mod 3");
    let axiom_body = solver.try_eq(g_qn, n_mod_three).expect("g n = n mod 3");
    let axiom = solver
        .try_forall_with_triggers(&[qn], axiom_body, &[&[g_qn]])
        .expect("forall axiom with trigger");
    solver.try_assert_term(axiom).expect("assert forall axiom");

    let five = solver.int_const(5);
    let g_five = solver.try_apply(&g, &[five]).expect("apply g to 5");
    let zero = solver.int_const(0);
    let g_five_eq_zero = solver.try_eq(g_five, zero).expect("g 5 = 0");
    solver
        .try_assert_term(g_five_eq_zero)
        .expect("assert conflicting ground g(5) = 0");

    let result = solver.check_sat();
    assert_eq!(
        result,
        SolveResult::unsat(),
        "mod-bearing completion SAT path must not mask a contradicting \
         ground constraint (would be wrong-SAT)"
    );
}

#[test]
fn test_transparent_logic_fn_total_arith_consistent_ground_is_sat() {
    // Positive control: with a CONSISTENT ground constraint the solver should
    // still report Sat (not over-refute). `(forall (n) (= (f n)
    // (ite (< n 0) 0 1)))` defines f(5) = 1, and the ground assertion agrees.
    let mut solver = Solver::new(Logic::Uflia);
    solver.set_timeout(Some(Duration::from_secs(30)));

    let f = solver
        .try_declare_fun("f", &[Sort::Int], Sort::Int)
        .expect("declare f");
    let qn = solver.fresh_var("n", Sort::Int);
    let f_qn = solver.try_apply(&f, &[qn]).expect("apply f to n");
    let zero = solver.int_const(0);
    let one = solver.int_const(1);
    let n_lt_zero = solver.try_lt(qn, zero).expect("n < 0");
    let total_arith = solver
        .try_ite(n_lt_zero, zero, one)
        .expect("ite total-arith value side");
    let axiom_body = solver.try_eq(f_qn, total_arith).expect("f n = ite ...");
    let axiom = solver
        .try_forall_with_triggers(&[qn], axiom_body, &[&[f_qn]])
        .expect("forall axiom with trigger");
    solver.try_assert_term(axiom).expect("assert forall axiom");

    let five = solver.int_const(5);
    let f_five = solver.try_apply(&f, &[five]).expect("apply f to 5");
    let f_five_eq_one = solver.try_eq(f_five, one).expect("f 5 = 1");
    solver
        .try_assert_term(f_five_eq_one)
        .expect("assert consistent ground f(5) = 1");

    let result = solver.check_sat();
    // #quantified-model-gate: the formula is satisfiable, but no finite-table
    // model with a constant `else` satisfies the two-valued total definition
    // `∀n. f(n) = ite(n<0,0,1)`, so the quantified model gate fail-closes the
    // unmaterialized completion to `Unknown` rather than emit a falsifying
    // witness. `Sat` is acceptable only with a valid printable model; `unsat`
    // never is.
    assert_ne!(
        result,
        SolveResult::unsat(),
        "a consistent ground constraint must never be refuted"
    );
    assert!(
        result == SolveResult::Sat || result == SolveResult::Unknown,
        "expected Sat (with a valid model) or fail-closed Unknown, got {result:?}"
    );
}
