// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Preserve all three per-condition Euclidean q/r families and API interning.

use super::common::{self, Binding};
use ay_dpll::api::{FuncDecl, Solver, Term};

fn range(s: &mut Solver, x: Term) -> Term {
    let zero = s.int_const(0);
    let lower = s.try_le(zero, x).unwrap();
    // DeductiveChecks's logical && encoder interns this overflow guard first.
    let _not_lower = s.try_not(lower).unwrap();
    let max = s.int_const(4_294_967_295);
    let upper = s.try_le(x, max).unwrap();
    let no = s.bool_const(false);
    s.try_ite(lower, upper, no).unwrap()
}

fn quotient(s: &mut Solver, dividend: Term, cached: &mut Option<Term>) -> Term {
    let two = s.int_const(2);
    // encode_int_arith's division-by-zero overflow expression.
    let zero = s.int_const(0);
    let eq_zero = s.try_eq(two, zero).unwrap();
    let _not_zero = s.try_not(eq_zero).unwrap();
    if let Some(q) = *cached {
        return q;
    }
    // purified_euclidean_div_mod_literal: shared q/r plus ground axioms.
    let q = s.fresh_var("__euclid_q", ay_dpll::api::Sort::Int);
    let r = s.fresh_var("__euclid_r", ay_dpll::api::Sort::Int);
    let two = s.int_const(2);
    let qd = s.try_mul(q, two).unwrap();
    let recon = s.try_add(qd, r).unwrap();
    let def = s.try_eq(recon, dividend).unwrap();
    s.try_assert_term(def).unwrap();
    let zero = s.int_const(0);
    let lower = s.try_ge(r, zero).unwrap();
    s.try_assert_term(lower).unwrap();
    let two = s.int_const(2);
    let upper = s.try_lt(r, two).unwrap();
    s.try_assert_term(upper).unwrap();
    *cached = Some(q);
    q
}

fn clip(s: &mut Solver, f: &FuncDecl, dividend: Term, cached: &mut Option<Term>) -> Term {
    let q = quotient(s, dividend, cached);
    s.try_apply(f, &[q]).unwrap()
}

fn query(binding: Binding) -> Solver {
    let mut s = common::solver();
    let int = ay_dpll::api::Sort::Int;
    let v0 = s.try_declare_const("v0", int.clone()).unwrap();
    let v1 = s.try_declare_const("v1", int.clone()).unwrap();
    for name in ["nl_mul", "nl_div", "nl_mod"] {
        s.try_declare_fun(name, &[int.clone(), int.clone()], int.clone())
            .unwrap();
    }
    let mut clip_u32 = None;
    for name in [
        "clip_u8_oob",
        "clip_u16_oob",
        "clip_u32_oob",
        "clip_u64_oob",
        "clip_i8_oob",
        "clip_i16_oob",
        "clip_i32_oob",
        "clip_i64_oob",
        "clip_nat_oob",
    ] {
        let f = s
            .try_declare_fun(name, &[int.clone()], int.clone())
            .unwrap();
        if name == "clip_u32_oob" {
            clip_u32 = Some(f);
        }
    }
    let clip_u32 = clip_u32.unwrap();
    let h1 = range(&mut s, v0);
    s.try_assert_named(h1, "qh0").unwrap();
    let h2 = range(&mut s, v1);
    s.try_assert_named(h2, "qh1").unwrap();
    let mut cached = None;
    let q = quotient(&mut s, v0, &mut cached);
    let h3 = s.try_eq(v1, q).unwrap();
    if matches!(binding, Binding::Original) {
        s.try_assert_named(h3, "qh2").unwrap();
    }
    // resolve_condition_typed opens a NEW AstExpressionParser for each root.
    cached = None;
    let zero = s.int_const(0);
    let clipped = clip(&mut s, &clip_u32, v0, &mut cached);
    let lower = s.try_le(zero, clipped).unwrap();
    let _not_lower = s.try_not(lower).unwrap();
    let clipped = clip(&mut s, &clip_u32, v0, &mut cached);
    let max = s.int_const(4_294_967_295);
    let upper = s.try_le(clipped, max).unwrap();
    let no = s.bool_const(false);
    let h4 = s.try_ite(lower, upper, no).unwrap();
    s.try_assert_named(h4, "qh3").unwrap();
    // resolve_refutation_condition_typed likewise owns a fresh per-root memo.
    cached = None;
    let zero = s.int_const(0);
    let q = quotient(&mut s, v0, &mut cached);
    let lower = s.try_le(zero, q).unwrap();
    let _not_lower = s.try_not(lower).unwrap();
    let q = quotient(&mut s, v0, &mut cached);
    let max = s.int_const(4_294_967_295);
    let upper = s.try_le(q, max).unwrap();
    let no = s.bool_const(false);
    let condition = s.try_ite(lower, upper, no).unwrap();
    let _not_condition = s.try_not(condition).unwrap();
    let then_value = quotient(&mut s, v0, &mut cached);
    let else_value = clip(&mut s, &clip_u32, v0, &mut cached);
    let value = s.try_ite(condition, then_value, else_value).unwrap();
    let equal = s.try_eq(v1, value).unwrap();
    let counterexample = s.try_not(equal).unwrap();
    s.try_assert_term(counterexample).unwrap();
    s
}

#[test]
fn native_per_root_division_clip_unsat() {
    common::on_solver_stack(|| common::assert_unsat(query(Binding::Original)));
}

#[test]
fn native_per_root_division_clip_omitted_binding_sat() {
    common::on_solver_stack(|| common::assert_sat(query(Binding::Omitted)));
}

#[test]
fn native_direct_assumption_subset_has_integer_separation_and_no_leaked_roots() {
    common::on_solver_stack(|| {
        for binding in [Binding::Original, Binding::Omitted] {
            let mut solver = query(binding);
            let roots = solver.assertions();
            let (goal, hypotheses) = roots.split_last().expect("complete native query");
            solver
                .try_reset_assertions()
                .expect("clear permanent roots");
            solver.try_assert_term(*goal).expect("permanent goal only");
            let details = solver.check_sat_assuming_with_details(hypotheses).solve;
            assert!(
                details
                    .statistics
                    .get_int("integer.primary_separation_clauses")
                    .is_some_and(|count| count > 0 && count <= 128),
                "{details:?}"
            );
            match binding {
                Binding::Original => {
                    assert!(details.result.is_unsat(), "{details:?}");
                    assert!(details.result.has_unsat_emission_witness(), "{details:?}");
                    assert!(
                        details.result.unsat_evidence_level().is_some(),
                        "{details:?}"
                    );
                }
                Binding::Omitted => {
                    assert!(details.result.is_sat(), "{details:?}");
                    assert!(details.result.was_model_validated());
                    assert!(details.result.has_sat_emission_witness());
                    solver.try_get_model_str().expect("subset SAT model");
                    for &root in &roots {
                        assert!(matches!(
                            solver.try_get_value(root),
                            Ok(ay_dpll::api::ModelValue::Bool(true))
                        ));
                    }
                }
            }
            assert_eq!(solver.assertions(), vec![*goal]);
        }
    });
}
