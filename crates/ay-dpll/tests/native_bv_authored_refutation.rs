// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Authored native roots and exact verifier queries retain checked evidence.

use ay_dpll::api::{Logic, Solver, Sort, Term};
use std::time::Duration;

#[derive(Clone, Copy)]
enum QuotientForm {
    Full,
    Low,
}

fn quotient_problem(form: QuotientForm, incorrect: bool, guard: bool) -> Solver {
    let mut solver = Solver::new(Logic::QfBv);
    solver.set_timeout(Some(Duration::from_millis(10_000)));
    let a8 = solver.declare_const("native_a8", Sort::bitvec(8));
    let b8 = solver.declare_const("native_b8", Sort::bitvec(8));
    let x32 = solver.declare_const("native_x32", Sort::bitvec(32));
    let y32 = solver.declare_const("native_y32", Sort::bitvec(32));
    let a32 = solver.bvzeroext(a8, 24);
    let b32 = solver.bvzeroext(b8, 24);
    let x_def = solver.eq(x32, a32);
    let y_def = solver.eq(y32, b32);
    let q8 = solver.bvudiv(a8, b8);
    let q8 = if incorrect {
        let one = solver.bv_const(1, 8);
        solver.bvadd(q8, one)
    } else {
        q8
    };
    let q32 = solver.bvudiv(x32, y32);
    let (left, right) = match form {
        QuotientForm::Full => (solver.bvzeroext(q8, 24), q32),
        QuotientForm::Low => (q8, solver.bvextract(q32, 7, 0)),
    };
    let different = solver.neq(left, right);
    let mut conjuncts = vec![x_def, y_def, different];
    if guard {
        let zero = solver.bv_const(0, 8);
        let nonzero = solver.neq(b8, zero);
        conjuncts.push(nonzero);
    }
    let root = solver.and_many(&conjuncts);
    solver.assert_term(root);
    solver
}

fn assert_certified_unsat(solver: &mut Solver) {
    let result = solver.check_sat();
    assert!(result.is_unsat(), "{result:?}");
    assert!(
        result.has_unsat_emission_witness(),
        "no public certification token"
    );
    assert!(result.was_unsat_strictly_verified(), "{result:?}");
    assert!(
        !result.was_unsat_corroborated(),
        "a re-solve is not this proof control"
    );
    // Default native solves certify internally without requesting a retained
    // public proof artifact. The exact-query result carries that capability.
    assert!(result
        .accept_for_consumer()
        .expect("strict public native UNSAT")
        .is_unsat());
}

fn assert_certified_sat(solver: &mut Solver) {
    let result = solver.check_sat();
    assert!(result.is_sat(), "{result:?}");
    assert!(result.has_sat_emission_witness());
    assert!(result.was_model_validated());
    assert!(result
        .accept_for_consumer()
        .expect("checked model")
        .is_sat());
}

#[test]
fn guarded_native_8_to_32_division_has_a_strict_public_certificate() {
    for form in [QuotientForm::Full, QuotientForm::Low] {
        assert_certified_unsat(&mut quotient_problem(form, false, true));
    }
}

#[test]
fn incorrect_native_quotient_retains_a_validated_counterexample() {
    for form in [QuotientForm::Full, QuotientForm::Low] {
        assert_certified_sat(&mut quotient_problem(form, true, true));
    }
}

#[test]
fn unguarded_full_width_division_retains_the_zero_divisor_counterexample() {
    assert_certified_sat(&mut quotient_problem(QuotientForm::Full, false, false));
    // At b=0 SMT total division returns all ones at ITS OWN width:
    // zext(0xff)=0x000000ff, whereas udiv32(zext(a),0)=0xffffffff.
    let mut solver = Solver::new(Logic::QfBv);
    solver.set_timeout(Some(Duration::from_millis(10_000)));
    let a = solver.declare_const("zero_div_a", Sort::bitvec(8));
    let zero8 = solver.bv_const(0, 8);
    let a32 = solver.bvzeroext(a, 24);
    let zero32 = solver.bv_const(0, 32);
    let narrow = solver.bvudiv(a, zero8);
    let narrow32 = solver.bvzeroext(narrow, 24);
    let wide = solver.bvudiv(a32, zero32);
    let ff8 = solver.bv_const(255, 32);
    let ff32 = solver.bv_const_u64(u64::from(u32::MAX), 32);
    let narrow_value = solver.eq(narrow32, ff8);
    let wide_value = solver.eq(wide, ff32);
    let different = solver.neq(narrow32, wide);
    let root = solver.and_many(&[narrow_value, wide_value, different]);
    solver.assert_term(root);
    assert_certified_sat(&mut solver);
}

#[test]
fn native_public_assumption_and_foreign_handle_controls() {
    let mut solver = Solver::new(Logic::QfBv);
    solver.set_timeout(Some(Duration::from_millis(10_000)));
    let x = solver.declare_const("assumed_native", Sort::bitvec(4));
    let zero = solver.bv_const(0, 4);
    let one = solver.bv_const(1, 4);
    let x0 = solver.eq(x, zero);
    let x1 = solver.eq(x, one);
    solver.assert_term(x0);
    let result = solver.check_sat_assuming(&[x1]);
    assert!(result.is_unsat() && result.has_unsat_emission_witness());
    assert!(result.was_unsat_strictly_verified());
    assert_certified_sat(&mut solver);
    let mut foreign = Solver::new(Logic::QfBv);
    let wrong: Term = foreign.bool_const(false);
    assert!(solver.try_assert_term(wrong).is_err());
    assert_certified_sat(&mut solver);
}

/// The original native verifier's named SSA constraints for an unsigned
/// checked add. The alias chain and duplicated query are part of that input.
fn verifier_guarded_u8_add(second_bound: u64, duplicate: bool) -> Solver {
    let mut s = Solver::new(Logic::All);
    s.set_timeout(Some(Duration::from_millis(10_000)));
    let a = s.declare_const("tirb_v0", Sort::bitvec(8));
    let b = s.declare_const("tirb_v1", Sort::bitvec(8));
    let a_limit = s.declare_const("tirb_v2", Sort::bitvec(8));
    let a_guard = s.declare_const("tirb_v3", Sort::Bool);
    let b_limit = s.declare_const("tirb_v4", Sort::bitvec(8));
    let b_guard = s.declare_const("tirb_v5", Sort::Bool);
    let result = s.declare_const("tirb_v6", Sort::bitvec(8));
    let overflow = s.declare_const("tirb_v7", Sort::Bool);
    let flag = s.declare_const("tirb_v11", Sort::Bool);
    let zero = s.declare_const("tirb_v12", Sort::Bool);
    let assertion = s.declare_const("tirb_v13", Sort::Bool);
    let hundred = s.bv_const(100, 8);
    let limit = s.bv_const(second_bound as i64, 8);
    let bound_a = s.eq(a_limit, hundred);
    let less_a = s.bvult(a, a_limit);
    let guard_a = s.eq(a_guard, less_a);
    let bound_b = s.eq(b_limit, limit);
    let less_b = s.bvult(b, b_limit);
    let guard_b = s.eq(b_guard, less_b);
    let sum = s.bvadd(a, b);
    let value = s.eq(result, sum);
    let wide_a = s.bvzeroext(a, 8);
    let wide_b = s.bvzeroext(b, 8);
    let wide_sum = s.bvadd(wide_a, wide_b);
    let maximum = s.bv_const(255, 16);
    let safe = s.bvule(wide_sum, maximum);
    let exceeds = s.not(safe);
    let overflow_definition = s.eq(overflow, exceeds);
    let alias = s.eq(overflow, flag);
    let false_value = s.not(zero);
    let equal = s.eq(flag, zero);
    let assertion_definition = s.eq(assertion, equal);
    for (i, term) in [
        bound_a,
        guard_a,
        bound_b,
        guard_b,
        value,
        overflow_definition,
        alias,
        false_value,
        assertion_definition,
        a_guard,
        b_guard,
    ]
    .into_iter()
    .enumerate()
    {
        s.try_assert_named(term, &format!("dn{i}")).unwrap();
    }
    for i in 11..19 {
        let truth = s.bool_const(true);
        s.try_assert_named(truth, &format!("dn{i}")).unwrap();
    }
    s.try_assert_named(flag, "dn19").unwrap();
    if duplicate {
        s.try_assert_named(flag, "dn20").unwrap();
    }
    s
}

#[test]
fn verifier_guarded_u8_add_aliases_have_strict_native_refutations() {
    for duplicate in [false, true] {
        assert_certified_unsat(&mut verifier_guarded_u8_add(100, duplicate));
    }
}

#[test]
fn verifier_guarded_u8_add_looser_bound_has_a_checked_counterexample() {
    assert_certified_sat(&mut verifier_guarded_u8_add(200, false));
}

#[test]
fn verifier_guarded_u8_original_queries_keep_strict_refutations_and_models() {
    for (name, text, expected) in [
        (
            "base",
            include_str!("native_bv_authored_refutation/vc_guarded_u8/base.smt2"),
            "sat",
        ),
        (
            "overflow",
            include_str!("native_bv_authored_refutation/vc_guarded_u8/overflow.smt2"),
            "unsat",
        ),
        (
            "duplicate",
            include_str!("native_bv_authored_refutation/vc_guarded_u8/overflow_duplicate.smt2"),
            "unsat",
        ),
        (
            "unguarded",
            include_str!("native_bv_authored_refutation/vc_guarded_u8/unguarded.smt2"),
            "sat",
        ),
        (
            "negated",
            include_str!("native_bv_authored_refutation/vc_guarded_u8/negated_precondition.smt2"),
            "sat",
        ),
    ] {
        let commands = ay_frontend::parse(text).unwrap();
        let mut executor = ay_dpll::Executor::new();
        executor.set_timeout(Some(Duration::from_millis(10_000)));
        let output = executor.execute_all(&commands).unwrap();
        assert_eq!(output, vec![expected], "{name}");
        if expected == "unsat" {
            let evidence = executor
                .last_command_unsat_evidence()
                .expect("checked refutation");
            assert_eq!(evidence.level(), ay_dpll::UnsatEvidenceLevel::E2);
            assert!(evidence.corroboration().is_none());
        } else {
            let model = executor.validate_model().expect("checked verifier model");
            assert!(model.checked > 0, "{name}: {model:?}");
        }
    }
}

/// Signed checked-add regression with named SSA aliases and the verifier's
/// proof/resource settings. The legacy all-named form and the public reader's
/// pushed, unnamed-goal form are both retained. No captured SMT text is parsed.
#[derive(Clone, Copy)]
enum SignedQuery {
    GuardedOverflow,
    GuardedFeasible,
    UnguardedOverflow,
}

fn verifier_guarded_signed_add(width: u32, bound: i64, query: SignedQuery) -> Solver {
    verifier_guarded_signed_add_shape(width, bound, query, SignedShape::Legacy)
}

#[derive(Clone, Copy)]
enum SignedShape {
    Legacy,
    PublicVerifier,
}

fn verifier_guarded_signed_add_shape(
    width: u32,
    bound: i64,
    query: SignedQuery,
    shape: SignedShape,
) -> Solver {
    let mut s = Solver::new(Logic::All);
    s.set_produce_proofs(true);
    s.set_produce_unsat_cores(true);
    s.set_counterexample_style(ay_dpll::CounterexampleStyle::Readable);
    s.set_timeout(Some(Duration::from_millis(120_000)));
    s.set_quantifier_deadline_backstop(false);
    s.try_set_option("rlimit", "400000").unwrap();
    let requested = 512usize * 1024 * 1024;
    let process_limit = requested
        .max(ay_sys::default_memory_limit())
        .max(ay_sys::current_rss_bytes().saturating_add(requested));
    s.set_memory_limit(Some(process_limit));
    let a = s.declare_const("tirb_v0", Sort::bitvec(width));
    let b = s.declare_const("tirb_v1", Sort::bitvec(width));
    let a_upper = s.declare_const("tirb_v2", Sort::bitvec(width));
    let a_below = s.declare_const("tirb_v3", Sort::Bool);
    let a_lower = s.declare_const("tirb_v4", Sort::bitvec(width));
    let a_above = s.declare_const("tirb_v5", Sort::Bool);
    let b_upper = s.declare_const("tirb_v6", Sort::bitvec(width));
    let b_below = s.declare_const("tirb_v7", Sort::Bool);
    let b_lower = s.declare_const("tirb_v8", Sort::bitvec(width));
    let b_above = s.declare_const("tirb_v9", Sort::Bool);
    let sum = s.declare_const("tirb_v10", Sort::bitvec(width));
    let overflow = s.declare_const("tirb_v11", Sort::Bool);
    let flag = s.declare_const("tirb_v15", Sort::Bool);
    let zero = s.declare_const("tirb_v16", Sort::Bool);
    let assertion = s.declare_const("tirb_v17", Sort::Bool);
    let upper = s.bv_const(bound, width);
    let lower = s.bv_const(-bound, width);
    let a_upper_def = s.eq(a_upper, upper);
    let a_below_value = s.bvslt(a, a_upper);
    let a_below_def = s.eq(a_below, a_below_value);
    let a_lower_def = s.eq(a_lower, lower);
    let a_above_value = match shape {
        SignedShape::Legacy => s.bvslt(a_lower, a),
        SignedShape::PublicVerifier => s.bvsgt(a, a_lower),
    };
    let a_above_def = s.eq(a_above, a_above_value);
    let b_upper_def = s.eq(b_upper, upper);
    let b_below_value = s.bvslt(b, b_upper);
    let b_below_def = s.eq(b_below, b_below_value);
    let b_lower_def = s.eq(b_lower, lower);
    let b_above_value = match shape {
        SignedShape::Legacy => s.bvslt(b_lower, b),
        SignedShape::PublicVerifier => s.bvsgt(b, b_lower),
    };
    let b_above_def = s.eq(b_above, b_above_value);
    let sum_value = s.bvadd(a, b);
    let sum_def = s.eq(sum, sum_value);
    let wide_a = s.bvsignext(a, width);
    let wide_b = s.bvsignext(b, width);
    let wide_sum = s.bvadd(wide_a, wide_b);
    let minimum = s.bv_const(-(1i64 << (width - 1)), width * 2);
    let maximum = s.bv_const((1i64 << (width - 1)) - 1, width * 2);
    let above_minimum = match shape {
        SignedShape::Legacy => s.bvsle(minimum, wide_sum),
        SignedShape::PublicVerifier => s.bvsge(wide_sum, minimum),
    };
    let below_maximum = s.bvsle(wide_sum, maximum);
    let overflow_value = match shape {
        SignedShape::Legacy => {
            let underflow = s.not(above_minimum);
            let excess = s.not(below_maximum);
            s.or(underflow, excess)
        }
        SignedShape::PublicVerifier => {
            let within_range = s.and(above_minimum, below_maximum);
            s.not(within_range)
        }
    };
    let overflow_def = s.eq(overflow, overflow_value);
    let flag_def = s.eq(overflow, flag);
    let zero_def = s.not(zero);
    let equal = s.eq(flag, zero);
    let assertion_def = s.eq(assertion, equal);
    let mut roots = vec![
        a_upper_def,
        a_below_def,
        a_lower_def,
        a_above_def,
        b_upper_def,
        b_below_def,
        b_lower_def,
        b_above_def,
        sum_def,
        overflow_def,
        flag_def,
        zero_def,
        assertion_def,
    ];
    if !matches!(query, SignedQuery::UnguardedOverflow) {
        roots.extend([a_below, a_above, b_below, b_above]);
    }
    for _ in 0..12 {
        roots.push(s.bool_const(true));
    }
    if !matches!(query, SignedQuery::GuardedFeasible) {
        roots.push(flag);
    }
    // The actual public reader keeps named hypotheses outside the temporary
    // assertion frame, then pushes before asserting its unnamed negated goal.
    let framed_goal = if matches!(shape, SignedShape::PublicVerifier)
        && !matches!(query, SignedQuery::GuardedFeasible)
    {
        roots.pop()
    } else {
        None
    };
    for (index, root) in roots.into_iter().enumerate() {
        let name = match shape {
            SignedShape::Legacy => format!("dn{index}"),
            SignedShape::PublicVerifier => format!("__deductive_checks_assumption_{index}"),
        };
        s.try_assert_named(root, &name).unwrap();
    }
    if let Some(goal) = framed_goal {
        s.try_push().unwrap();
        s.try_assert_term(goal).unwrap();
    }
    s
}

fn assert_signed_native_refutation(width: u32) {
    let mut s = verifier_guarded_signed_add(width, 50, SignedQuery::GuardedOverflow);
    let details = s.check_sat_with_details();
    assert!(details.result.is_unsat(), "i{width}: {details:?}");
    assert!(details.result.was_unsat_strictly_verified(), "{details:?}");
    assert!(!details.result.was_unsat_corroborated(), "{details:?}");
    details
        .accept_for_consumer()
        .expect("strict native source authority");
    s.last_strict_proof_quality().unwrap().unwrap();
    let artifact = s.export_last_unsat_artifact().unwrap();
    assert!(artifact.quality.is_complete(), "{}", artifact.quality);
}

#[test]
fn verifier_guarded_i8_add_has_strict_native_refutation() {
    assert_signed_native_refutation(8);
}

#[test]
fn verifier_guarded_i16_add_has_strict_native_refutation() {
    assert_signed_native_refutation(16);
}

#[test]
fn public_verifier_i8_signed_constructor_retains_its_strict_refutation() {
    let mut solver = verifier_guarded_signed_add_shape(
        8,
        50,
        SignedQuery::GuardedOverflow,
        SignedShape::PublicVerifier,
    );
    assert_certified_unsat(&mut solver);
    solver.last_strict_proof_quality().unwrap().unwrap();
    assert!(solver
        .export_last_unsat_artifact()
        .unwrap()
        .quality
        .is_complete());
}

#[test]
fn public_verifier_i16_signed_constructor_retains_its_strict_refutation() {
    let mut solver = verifier_guarded_signed_add_shape(
        16,
        100,
        SignedQuery::GuardedOverflow,
        SignedShape::PublicVerifier,
    );
    assert_certified_unsat(&mut solver);
    solver.last_strict_proof_quality().unwrap().unwrap();
    assert!(solver
        .export_last_unsat_artifact()
        .unwrap()
        .quality
        .is_complete());
}

#[test]
fn public_verifier_framed_signed_guard_changes_keep_checked_counterexamples() {
    for (width, bound) in [(8, 100), (16, 30_000)] {
        for query in [SignedQuery::GuardedOverflow, SignedQuery::UnguardedOverflow] {
            assert_certified_sat(&mut verifier_guarded_signed_add_shape(
                width,
                bound,
                query,
                SignedShape::PublicVerifier,
            ));
        }
    }
}

#[test]
fn verifier_signed_guard_mutations_keep_checked_counterexamples() {
    for width in [8, 16] {
        assert_certified_sat(&mut verifier_guarded_signed_add(
            width,
            50,
            SignedQuery::GuardedFeasible,
        ));
        let too_loose = (1i64 << (width - 2)) + 10;
        assert_certified_sat(&mut verifier_guarded_signed_add(
            width,
            too_loose,
            SignedQuery::GuardedOverflow,
        ));
        assert_certified_sat(&mut verifier_guarded_signed_add(
            width,
            50,
            SignedQuery::UnguardedOverflow,
        ));
    }
}
