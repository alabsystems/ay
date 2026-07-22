// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for the SMT backend.

#![allow(clippy::unwrap_used)]

use super::context::SmtContext;
use super::incremental::IncrementalQueryContext;
use super::types::{FarkasConflict, Partition, SmtResult, SmtValue};
use crate::{ChcExpr, ChcOp, ChcSort, ChcVar};
use ay_core::kani_compat::DetHashSet as FxHashSet;
use ay_core::term::{Constant, TermData};
use ay_core::{FarkasAnnotation, TermId};
use num_bigint::BigInt;
use num_rational::BigRational;
use std::sync::Arc;

#[test]
fn test_reset_preserves_scoped_check_timeout() {
    use std::time::Duration;

    let mut ctx = SmtContext::new();
    assert_eq!(ctx.check_timeout.get(), None);

    {
        let _guard = ctx.scoped_check_timeout(Some(Duration::from_millis(1)));
        assert_eq!(ctx.check_timeout.get(), Some(Duration::from_millis(1)));

        // Must preserve the configured timeout across reset (used by case-splitting helpers).
        ctx.reset();
        assert_eq!(ctx.check_timeout.get(), Some(Duration::from_millis(1)));
    }

    assert_eq!(ctx.check_timeout.get(), None);
}

#[test]
fn test_convert_bool_constant() {
    let mut ctx = SmtContext::new();

    let true_expr = ChcExpr::Bool(true);
    let term = ctx.convert_expr(&true_expr);
    assert!(ctx.terms.is_true(term));

    let false_expr = ChcExpr::Bool(false);
    let term = ctx.convert_expr(&false_expr);
    assert!(ctx.terms.is_false(term));
}

#[test]
fn test_convert_variable() {
    let mut ctx = SmtContext::new();

    let x = ChcVar::new("x", ChcSort::Int);
    let x_expr = ChcExpr::var(x);

    let term1 = ctx.convert_expr(&x_expr);
    let term2 = ctx.convert_expr(&x_expr);

    // Same variable should map to same term
    assert_eq!(term1, term2);
}

#[test]
fn test_convert_to_real_func_app_uses_builtin_conversion() {
    let mut ctx = SmtContext::new();

    let expr = ChcExpr::FuncApp(
        "to_real".to_string(),
        ChcSort::Real,
        vec![Arc::new(ChcExpr::Int(5))],
    );
    let term = ctx.convert_expr(&expr);

    match ctx.terms.get(term) {
        TermData::Const(Constant::Rational(value)) => {
            assert_eq!(value.0, BigRational::from_integer(BigInt::from(5)));
        }
        other => panic!("expected to_real constant to fold to Real rational, got {other:?}"),
    }
}

#[test]
fn test_convert_mixed_int_real_terms_coerce_to_real() {
    let mut ctx = SmtContext::new();
    let r = ChcExpr::var(ChcVar::new("r", ChcSort::Real));
    let b = ChcExpr::var(ChcVar::new("b", ChcSort::Bool));

    let add = ChcExpr::add(r.clone(), ChcExpr::Int(1));
    let add_term = ctx.convert_expr(&add);
    assert_eq!(ctx.terms.sort(add_term), &ay_core::Sort::Real);
    assert!(
        !ctx.conversion_budget_exceeded(),
        "mixed Real/Int add should convert without fail-closed sentinel"
    );

    ctx.reset_conversion_budget();
    let le = ChcExpr::le(r.clone(), ChcExpr::Int(0));
    let le_term = ctx.convert_expr(&le);
    assert_eq!(ctx.terms.sort(le_term), &ay_core::Sort::Bool);
    assert!(
        !ctx.conversion_budget_exceeded(),
        "mixed Real/Int comparison should convert without fail-closed sentinel"
    );

    ctx.reset_conversion_budget();
    let ne = ChcExpr::ne(r.clone(), ChcExpr::Int(0));
    let ne_term = ctx.convert_expr(&ne);
    assert_eq!(ctx.terms.sort(ne_term), &ay_core::Sort::Bool);
    assert!(
        !ctx.terms.is_true(ne_term),
        "mixed Real/Int disequality must not become a tautology"
    );

    ctx.reset_conversion_budget();
    let ite = ChcExpr::ite(b, ChcExpr::Int(0), r);
    let ite_term = ctx.convert_expr(&ite);
    assert_eq!(ctx.terms.sort(ite_term), &ay_core::Sort::Real);
    assert!(
        !ctx.conversion_budget_exceeded(),
        "mixed Real/Int ITE should convert without fail-closed sentinel"
    );
}

#[test]
fn test_convert_programmatic_mod_real_mixed_operands_fails_closed() {
    fn assert_mod_fails_closed(expr: ChcExpr) {
        let mut ctx = SmtContext::new();
        let term = ctx.convert_expr(&expr);

        assert_eq!(ctx.terms.sort(term), &ay_core::Sort::Int);
        assert!(
            ctx.conversion_budget_exceeded(),
            "Real-mixed mod should force Unknown instead of passing Real args to mk_mod"
        );
    }

    let r = ChcVar::new("r", ChcSort::Real);
    assert_mod_fails_closed(ChcExpr::mod_op(ChcExpr::var(r.clone()), ChcExpr::int(2)));
    assert_mod_fails_closed(ChcExpr::mod_op(ChcExpr::int(5), ChcExpr::var(r)));
}

#[test]
fn test_convert_symbolic_real_division_fails_closed() {
    fn real_div(lhs: ChcExpr, rhs: ChcExpr) -> ChcExpr {
        ChcExpr::Op(ChcOp::Div, vec![Arc::new(lhs), Arc::new(rhs)])
    }

    fn assert_real_div_fails_closed(expr: ChcExpr) {
        let mut ctx = SmtContext::new();
        let term = ctx.convert_expr(&expr);

        assert_eq!(ctx.terms.sort(term), &ay_core::Sort::Real);
        assert!(
            ctx.conversion_budget_exceeded(),
            "symbolic Real division should force Unknown instead of relying on division-by-zero simplifications"
        );
    }

    let r = ChcVar::new("r", ChcSort::Real);
    assert_real_div_fails_closed(real_div(ChcExpr::Real(0, 1), ChcExpr::var(r.clone())));
    assert_real_div_fails_closed(real_div(ChcExpr::var(r.clone()), ChcExpr::var(r.clone())));

    let mut ctx = SmtContext::new();
    let safe_literal_div = real_div(ChcExpr::var(r), ChcExpr::Real(2, 1));
    let term = ctx.convert_expr(&safe_literal_div);
    assert_eq!(ctx.terms.sort(term), &ay_core::Sort::Real);
    assert!(
        !ctx.conversion_budget_exceeded(),
        "nonzero literal Real denominator should remain convertible"
    );
}

#[test]
fn test_eliminate_mod_preserves_real_division_by_int_literal() {
    let r = ChcVar::new("r", ChcSort::Real);
    let expr = ChcExpr::Op(
        ChcOp::Div,
        vec![Arc::new(ChcExpr::var(r)), Arc::new(ChcExpr::int(2))],
    );

    assert_eq!(
        expr.eliminate_mod(),
        expr,
        "mod/div preprocessing must not rewrite Real division through integer Euclidean division"
    );
}

#[test]
fn test_eliminate_mod_preserves_real_mod_by_int_literal() {
    let r = ChcVar::new("r", ChcSort::Real);
    let expr = ChcExpr::mod_op(ChcExpr::var(r), ChcExpr::int(2));

    assert_eq!(
        expr.eliminate_mod(),
        expr,
        "mod preprocessing must not encode Real dividends as integer Euclidean division"
    );
}

#[test]
fn test_eliminate_mod_preserves_i64_min_divisor() {
    // i128-lockstep: the non-eliminable |divisor| boundary moved to i128::MIN
    // (an i64::MIN divisor now has an exact |k| in the widened lane).
    let x = ChcVar::new("x", ChcSort::Int);
    for op in [ChcOp::Div, ChcOp::Mod] {
        let expr = ChcExpr::Op(
            op,
            vec![
                Arc::new(ChcExpr::var(x.clone())),
                Arc::new(ChcExpr::int(i128::MIN)),
            ],
        );

        assert_eq!(
            expr.eliminate_mod(),
            expr,
            "Euclidean div/mod elimination must not encode |i128::MIN| as i128::MAX"
        );
    }
}

#[test]
fn test_check_sat_real_mixed_mod_fails_closed_after_preprocessing() {
    let r = ChcVar::new("r", ChcSort::Real);
    let query = ChcExpr::eq(
        ChcExpr::mod_op(ChcExpr::var(r), ChcExpr::int(2)),
        ChcExpr::int(0),
    );
    let mut ctx = SmtContext::new();

    assert!(
        matches!(ctx.check_sat(&query), SmtResult::Unknown),
        "normal check_sat preprocessing must preserve Real-mixed mod until conversion fails closed"
    );
}

#[test]
fn test_check_sat_symbolic_real_division_fails_closed() {
    let r = ChcVar::new("r", ChcSort::Real);
    let div = ChcExpr::Op(
        ChcOp::Div,
        vec![Arc::new(ChcExpr::Real(0, 1)), Arc::new(ChcExpr::var(r))],
    );
    let query = ChcExpr::not(ChcExpr::eq(div, ChcExpr::Real(0, 1)));
    let mut ctx = SmtContext::new();

    assert!(
        matches!(ctx.check_sat(&query), SmtResult::Unknown),
        "normal check_sat preprocessing must preserve symbolic Real division until conversion fails closed"
    );
}

#[test]
fn test_check_sat_is_int_constant_semantics() {
    let is_half_int = ChcExpr::FuncApp(
        "is_int".to_string(),
        ChcSort::Bool,
        vec![Arc::new(ChcExpr::Real(1, 2))],
    );
    let mut ctx = SmtContext::new();

    assert!(
        matches!(
            ctx.check_sat(&is_half_int),
            SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_)
        ),
        "is_int(1/2) must be false"
    );

    let mut ctx = SmtContext::new();
    assert!(
        matches!(ctx.check_sat(&ChcExpr::not(is_half_int)), SmtResult::Sat(_)),
        "not(is_int(1/2)) must be satisfiable"
    );
}

#[test]
fn test_check_sat_to_int_constant_semantics() {
    let to_int_three_halves = ChcExpr::FuncApp(
        "to_int".to_string(),
        ChcSort::Int,
        vec![Arc::new(ChcExpr::Real(3, 2))],
    );
    let equals_floor = ChcExpr::eq(to_int_three_halves.clone(), ChcExpr::int(1));
    let equals_ceiling = ChcExpr::eq(to_int_three_halves, ChcExpr::int(2));

    let mut ctx = SmtContext::new();
    assert!(
        matches!(ctx.check_sat(&equals_floor), SmtResult::Sat(_)),
        "to_int(3/2) = 1 must be satisfiable"
    );

    let mut ctx = SmtContext::new();
    assert!(
        matches!(
            ctx.check_sat(&equals_ceiling),
            SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_)
        ),
        "to_int(3/2) = 2 must be unsatisfiable"
    );
}

#[test]
fn test_convert_to_real_bad_sort_fails_closed() {
    let mut ctx = SmtContext::new();

    let expr = ChcExpr::FuncApp(
        "to_real".to_string(),
        ChcSort::Real,
        vec![Arc::new(ChcExpr::Bool(true))],
    );
    let term = ctx.convert_expr(&expr);

    assert_eq!(ctx.terms.sort(term), &ay_core::Sort::Real);
    assert!(
        ctx.conversion_budget_exceeded(),
        "bad-sort to_real should force Unknown instead of inventing UF semantics"
    );
}

#[test]
fn test_convert_arithmetic() {
    let mut ctx = SmtContext::new();

    // x + 1
    let x = ChcVar::new("x", ChcSort::Int);
    let expr = ChcExpr::add(ChcExpr::var(x), ChcExpr::int(1));

    let term = ctx.convert_expr(&expr);
    // Just verify it converts without error
    assert!(term.0 > 0);
}

#[test]
fn test_convert_comparison() {
    let mut ctx = SmtContext::new();

    // x < 5
    let x = ChcVar::new("x", ChcSort::Int);
    let expr = ChcExpr::lt(ChcExpr::var(x), ChcExpr::int(5));

    let term = ctx.convert_expr(&expr);
    // Just verify it converts without error
    assert!(term.0 > 0);
}

#[test]
fn test_check_sat_trivial() {
    let mut ctx = SmtContext::new();

    // true is SAT
    let expr = ChcExpr::Bool(true);
    let result = ctx.check_sat(&expr);
    assert!(matches!(result, SmtResult::Sat(_)));

    // false is UNSAT
    let expr = ChcExpr::Bool(false);
    ctx.reset();
    let result = ctx.check_sat(&expr);
    assert!(matches!(result, SmtResult::Unsat));
}

#[test]
fn test_check_sat_simple_constraint() {
    let mut ctx = SmtContext::new();

    // x = 5 is SAT
    let x = ChcVar::new("x", ChcSort::Int);
    let expr = ChcExpr::eq(ChcExpr::var(x), ChcExpr::int(5));
    let result = ctx.check_sat(&expr);
    assert!(matches!(result, SmtResult::Sat(_)));
}

#[test]
fn test_check_sat_model_with_arith_ite() {
    let mut ctx = SmtContext::new();

    // Base constraints (mirrors a shape that shows up in CHC predecessor queries):
    //   E = 1
    //   A + 1 = 4            => A = 3
    //   ite(E <= A, B + 1, B) = 5  => since E<=A, B = 4
    let a = ChcVar::new("A", ChcSort::Int);
    let b = ChcVar::new("B", ChcSort::Int);
    let e = ChcVar::new("E", ChcSort::Int);

    let expr = ChcExpr::and(
        ChcExpr::eq(
            ChcExpr::add(ChcExpr::int(1), ChcExpr::var(a.clone())),
            ChcExpr::int(4),
        ),
        ChcExpr::and(
            ChcExpr::eq(ChcExpr::var(e.clone()), ChcExpr::int(1)),
            ChcExpr::eq(
                ChcExpr::ite(
                    ChcExpr::le(ChcExpr::var(e), ChcExpr::var(a)),
                    ChcExpr::add(ChcExpr::int(1), ChcExpr::var(b.clone())),
                    ChcExpr::var(b),
                ),
                ChcExpr::int(5),
            ),
        ),
    );

    let result = ctx.check_sat(&expr);
    let SmtResult::Sat(model) = result else {
        panic!("expected SAT, got {result:?}");
    };

    assert_eq!(model.get("A"), Some(&SmtValue::Int(3)));
    assert_eq!(model.get("E"), Some(&SmtValue::Int(1)));
    assert_eq!(model.get("B"), Some(&SmtValue::Int(4)));
}

#[test]
fn test_check_sat_model_preserves_linear_bindings_under_context() {
    let mut ctx = SmtContext::new();

    let a = ChcVar::new("A", ChcSort::Int);
    let b = ChcVar::new("B", ChcSort::Int);
    let e = ChcVar::new("E", ChcSort::Int);

    let base = ChcExpr::and(
        ChcExpr::not(ChcExpr::le(
            ChcExpr::mul(ChcExpr::int(5), ChcExpr::var(e.clone())),
            ChcExpr::var(a.clone()),
        )),
        ChcExpr::and(
            ChcExpr::eq(
                ChcExpr::add(ChcExpr::int(1), ChcExpr::var(a.clone())),
                ChcExpr::int(4),
            ),
            ChcExpr::and(
                ChcExpr::eq(ChcExpr::var(e.clone()), ChcExpr::int(1)),
                ChcExpr::eq(
                    ChcExpr::ite(
                        ChcExpr::le(ChcExpr::var(e.clone()), ChcExpr::var(a.clone())),
                        ChcExpr::add(ChcExpr::int(1), ChcExpr::var(b.clone())),
                        ChcExpr::var(b.clone()),
                    ),
                    ChcExpr::int(5),
                ),
            ),
        ),
    );

    let context = ChcExpr::and(
        ChcExpr::ge(ChcExpr::var(a.clone()), ChcExpr::var(e.clone())),
        ChcExpr::and(
            ChcExpr::le(ChcExpr::var(e), ChcExpr::var(a.clone())),
            ChcExpr::not(ChcExpr::and(
                ChcExpr::eq(ChcExpr::var(b), ChcExpr::int(0)),
                ChcExpr::ge(ChcExpr::var(a), ChcExpr::int(4)),
            )),
        ),
    );

    let expr = ChcExpr::and(base, context);
    let result = ctx.check_sat(&expr);
    let SmtResult::Sat(model) = result else {
        panic!("expected SAT, got {result:?}");
    };

    assert_eq!(model.get("A"), Some(&SmtValue::Int(3)));
    assert_eq!(model.get("E"), Some(&SmtValue::Int(1)));
    assert_eq!(model.get("B"), Some(&SmtValue::Int(4)));
}

fn issue_8664_symbolic_store_chain_query(expected_value: bool) -> ChcExpr {
    let i = ChcVar::new("i", ChcSort::Int);
    let j = ChcVar::new("j", ChcSort::Int);
    let q = ChcVar::new("q", ChcSort::Int);

    let base = ChcExpr::const_array(ChcSort::Int, ChcExpr::Bool(false));
    let stores = ChcExpr::store(
        ChcExpr::store(base, ChcExpr::var(i.clone()), ChcExpr::Bool(true)),
        ChcExpr::var(j.clone()),
        ChcExpr::Bool(false),
    );
    let selected = ChcExpr::select(stores, ChcExpr::var(q.clone()));

    ChcExpr::and(
        ChcExpr::eq(ChcExpr::var(q), ChcExpr::var(i.clone())),
        ChcExpr::and(
            ChcExpr::ne(ChcExpr::var(i), ChcExpr::var(j)),
            ChcExpr::eq(selected, ChcExpr::Bool(expected_value)),
        ),
    )
}

#[test]
fn test_preprocess_expands_symbolic_select_store_chain_8664() {
    let query = issue_8664_symbolic_store_chain_query(false);
    assert!(query.contains_array_ops());

    let preprocessed = SmtContext::preprocess(&query);

    assert!(
        !preprocessed.contains_array_ops(),
        "bounded ROW expansion should remove the short const-array backed store chain, got {preprocessed}",
    );
}

#[test]
fn test_check_sat_symbolic_select_store_chain_unsat_8664() {
    let mut ctx = SmtContext::new();
    let query = issue_8664_symbolic_store_chain_query(false);

    let result = ctx.check_sat(&query);

    assert!(
        matches!(result, SmtResult::Unsat | SmtResult::UnsatWithCore(_)),
        "i = q and i != j force the selected value to true, got {result:?}",
    );
}

#[test]
fn test_check_sat_unsat_with_mul_and_disequality() {
    let mut ctx = SmtContext::new();

    // This is the shape produced by PDR self-inductiveness checks for discovered invariants.
    // It is UNSAT, but historically returned `Unknown` and caused invariants to be rejected.
    //
    // (= A (* 1 B))  /\  (not (= (+ 1 A) (* 1 (+ 1 B))))
    let a = ChcVar::new("A", ChcSort::Int);
    let b = ChcVar::new("B", ChcSort::Int);

    let eq = ChcExpr::eq(
        ChcExpr::var(a.clone()),
        ChcExpr::mul(ChcExpr::int(1), ChcExpr::var(b.clone())),
    );

    let diseq = ChcExpr::not(ChcExpr::eq(
        ChcExpr::add(ChcExpr::int(1), ChcExpr::var(a)),
        ChcExpr::mul(
            ChcExpr::int(1),
            ChcExpr::add(ChcExpr::int(1), ChcExpr::var(b)),
        ),
    ));

    let expr = ChcExpr::and(eq, diseq);
    let result = ctx.check_sat(&expr);
    assert!(
        matches!(
            result,
            SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_)
        ),
        "expected UNSAT, got {result:?}"
    );
}

#[test]
fn test_check_sat_contradiction() {
    let mut ctx = SmtContext::new();

    // x = 5 /\ x = 6 is UNSAT
    let x = ChcVar::new("x", ChcSort::Int);
    let eq5 = ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(5));
    let eq6 = ChcExpr::eq(ChcExpr::var(x), ChcExpr::int(6));
    let expr = ChcExpr::and(eq5, eq6);
    let result = ctx.check_sat(&expr);
    assert!(matches!(result, SmtResult::Unsat));
}

#[test]
fn test_check_sat_with_assumptions_tracks_farkas_origins() {
    let mut ctx = SmtContext::new();

    let x = ChcVar::new("x", ChcSort::Int);
    let background = vec![ChcExpr::le(ChcExpr::var(x.clone()), ChcExpr::int(0))];
    let assumptions = vec![ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(1))];

    let result = ctx.check_sat_with_assumption_conjuncts(&background, &assumptions);
    let conflicts = match result {
        SmtResult::UnsatWithCore(core) => core.farkas_conflicts,
        SmtResult::UnsatWithFarkas(conflict) => vec![conflict],
        other => panic!("expected UNSAT with Farkas conflicts, got {other:?}"),
    };

    assert!(
        !conflicts.is_empty(),
        "expected at least one Farkas conflict"
    );

    let mut saw_a = false;
    let mut saw_b = false;
    let mut saw_a_and_b_in_same_conflict = false;
    for conflict in conflicts {
        assert_eq!(
            conflict.conflict_terms.len(),
            conflict.origins.len(),
            "expected origin vector aligned with conflict terms"
        );

        let mut conflict_saw_a = false;
        let mut conflict_saw_b = false;
        for origin in conflict.origins {
            conflict_saw_a |= origin == Partition::A;
            conflict_saw_b |= origin == Partition::B;
        }

        saw_a |= conflict_saw_a;
        saw_b |= conflict_saw_b;
        saw_a_and_b_in_same_conflict |= conflict_saw_a && conflict_saw_b;
    }

    assert!(saw_a, "expected at least one A-origin literal");
    assert!(saw_b, "expected at least one B-origin literal");
    assert!(
        saw_a_and_b_in_same_conflict,
        "expected a conflict containing both A and B origins"
    );
}

#[test]
fn test_filter_farkas_conflicts_by_indices_keeps_only_needed() {
    let mk_conflict = |id: u32| FarkasConflict {
        conflict_terms: vec![TermId::new(id)],
        polarities: vec![true],
        farkas: FarkasAnnotation::from_ints(&[1]),
        origins: vec![Partition::A],
    };

    let conflicts = vec![mk_conflict(1), mk_conflict(2), mk_conflict(3)];
    let mut needed: FxHashSet<usize> = FxHashSet::default();
    needed.insert(0);
    needed.insert(2);

    let filtered = SmtContext::filter_farkas_conflicts_by_indices(&needed, conflicts);
    assert_eq!(filtered.len(), 2);
    assert_eq!(filtered[0].conflict_terms[0], TermId::new(1));
    assert_eq!(filtered[1].conflict_terms[0], TermId::new(3));
}

#[test]
fn test_filter_farkas_conflicts_by_indices_empty_needed_passes_through() {
    // When needed_conflict_indices is empty, the function preserves all
    // conflicts rather than discarding them. This avoids forcing the
    // zero-Farkas fallback when the SAT solver's UNSAT core omits
    // activation literals (see smt.rs:2405-2417).
    let conflicts = vec![FarkasConflict {
        conflict_terms: vec![TermId::new(1)],
        polarities: vec![true],
        farkas: FarkasAnnotation::from_ints(&[1]),
        origins: vec![Partition::A],
    }];

    let needed: FxHashSet<usize> = FxHashSet::default();
    let filtered = SmtContext::filter_farkas_conflicts_by_indices(&needed, conflicts.clone());
    assert_eq!(
        filtered.len(),
        conflicts.len(),
        "empty needed indices should pass through all conflicts"
    );
}

#[test]
fn test_check_sat_with_assumptions_tracks_farkas_origins_through_iuc_proxy() {
    let mut ctx = SmtContext::new();

    let x = ChcVar::new("x", ChcSort::Int);
    let proxy = ChcExpr::var(ChcVar::new("__iuc_proxy_1", ChcSort::Bool));

    // A: x <= 0
    // B: proxy, with background implication (proxy -> x >= 1)
    let background = vec![
        ChcExpr::le(ChcExpr::var(x.clone()), ChcExpr::int(0)),
        ChcExpr::or(
            ChcExpr::not(proxy.clone()),
            ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(1)),
        ),
    ];
    let assumptions = vec![proxy];

    let result = ctx.check_sat_with_assumption_conjuncts(&background, &assumptions);
    let conflicts = match result {
        SmtResult::UnsatWithCore(core) => core.farkas_conflicts,
        SmtResult::UnsatWithFarkas(conflict) => vec![conflict],
        other => panic!("expected UNSAT with Farkas conflicts, got {other:?}"),
    };

    assert!(
        !conflicts.is_empty(),
        "expected at least one Farkas conflict"
    );

    let mut saw_a = false;
    let mut saw_b = false;
    for conflict in conflicts {
        assert_eq!(
            conflict.conflict_terms.len(),
            conflict.origins.len(),
            "expected origin vector aligned with conflict terms"
        );

        for origin in conflict.origins {
            saw_a |= origin == Partition::A;
            saw_b |= origin == Partition::B;
        }
    }

    assert!(saw_a, "expected at least one A-origin literal");
    assert!(saw_b, "expected at least one B-origin literal");
}

#[test]
fn test_check_sat_with_assumptions_does_not_special_case_unassumed_iuc_proxy() {
    let mut ctx = SmtContext::new();

    let x = ChcVar::new("x", ChcSort::Int);
    let proxy = ChcExpr::var(ChcVar::new("__iuc_proxy_1", ChcSort::Bool));
    let dummy_assumption = ChcExpr::var(ChcVar::new("q", ChcSort::Bool));

    // Background asserts `proxy` directly (A partition). This makes the clause
    // (¬proxy ∨ x ≥ 1) active without the proxy being assumed.
    let background = vec![
        proxy.clone(),
        ChcExpr::le(ChcExpr::var(x.clone()), ChcExpr::int(0)),
        ChcExpr::or(
            ChcExpr::not(proxy),
            ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(1)),
        ),
    ];
    let assumptions = vec![dummy_assumption];

    let result = ctx.check_sat_with_assumption_conjuncts(&background, &assumptions);
    let conflicts = match result {
        SmtResult::UnsatWithCore(core) => core.farkas_conflicts,
        SmtResult::UnsatWithFarkas(conflict) => vec![conflict],
        other => panic!("expected UNSAT with Farkas conflicts, got {other:?}"),
    };

    assert!(
        !conflicts.is_empty(),
        "expected at least one Farkas conflict"
    );

    for conflict in conflicts {
        assert_eq!(
            conflict.conflict_terms.len(),
            conflict.origins.len(),
            "expected origin vector aligned with conflict terms"
        );
        assert!(
            conflict
                .origins
                .iter()
                .all(|&origin| origin == Partition::A),
            "expected proxy implication body to remain in A when proxy is not assumed"
        );
    }
}

#[test]
fn test_check_implies_bool() {
    let mut ctx = SmtContext::new();

    // a implies (a \/ b)
    let a = ChcVar::new("a", ChcSort::Bool);
    let b = ChcVar::new("b", ChcSort::Bool);
    let formula = ChcExpr::var(a.clone());
    let conclusion = ChcExpr::or(ChcExpr::var(a), ChcExpr::var(b));

    let result = ctx.check_implies(&formula, &conclusion);
    assert!(result);
}

#[test]
fn test_check_implies_bool_false() {
    let mut ctx = SmtContext::new();

    // a does NOT imply b
    let a = ChcVar::new("a", ChcSort::Bool);
    let b = ChcVar::new("b", ChcSort::Bool);
    let formula = ChcExpr::var(a);
    let conclusion = ChcExpr::var(b);

    let result = ctx.check_implies(&formula, &conclusion);
    assert!(!result);
}

#[test]
fn test_lia_distinct_constraint() {
    let mut ctx = SmtContext::new();

    // (x < 1) /\ (x >= 0) /\ (x != 0) should be UNSAT for integers
    let x = ChcVar::new("x", ChcSort::Int);
    let x_var = ChcExpr::var(x);

    // x < 1
    let lt1 = ChcExpr::lt(x_var.clone(), ChcExpr::int(1));
    // x >= 0 (not (x < 0))
    let ge0 = ChcExpr::not(ChcExpr::lt(x_var.clone(), ChcExpr::int(0)));
    // x != 0 (not (x = 0))
    let ne0 = ChcExpr::not(ChcExpr::eq(x_var, ChcExpr::int(0)));

    let formula = ChcExpr::and(ChcExpr::and(lt1, ge0), ne0);
    safe_eprintln!("Testing formula: {}", formula);

    let result = ctx.check_sat(&formula);
    safe_eprintln!("Result: {:?}", result);

    // For integers: x < 1 /\ x >= 0 /\ x != 0 has NO solution (only x=0 satisfies first two)
    assert!(
        matches!(
            result,
            SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_)
        ),
        "Expected UNSAT but got {result:?}"
    );
}

#[test]
fn test_lia_distinct_with_slack() {
    let mut ctx = SmtContext::new();

    // (B < 1) /\ (B != 0) should be SAT for integers (e.g., B = -1)
    // This is the query that was returning Unknown in CHC PDR
    let b = ChcVar::new("B", ChcSort::Int);
    let b_var = ChcExpr::var(b);

    // B < 1 (normalized to B <= 0 for integers)
    let lt1 = ChcExpr::lt(b_var.clone(), ChcExpr::int(1));
    // B != 0
    let ne0 = ChcExpr::ne(b_var, ChcExpr::int(0));

    let formula = ChcExpr::and(lt1, ne0);
    safe_eprintln!("Testing formula: {}", formula);

    let result = ctx.check_sat(&formula);
    safe_eprintln!("Result: {:?}", result);

    // B <= 0 /\ B != 0 means B <= -1, which is SAT (e.g., B = -1)
    assert!(
        matches!(result, SmtResult::Sat(_)),
        "Expected SAT but got {result:?}"
    );
}

#[test]
fn test_two_var_disequality() {
    let mut ctx = SmtContext::new();

    // D != E should be SAT (e.g., D = 0, E = 1)
    // This is a 2-variable disequality that was failing in CHC PDR
    let d = ChcVar::new("D", ChcSort::Int);
    let e = ChcVar::new("E", ChcSort::Int);
    let d_var = ChcExpr::var(d);
    let e_var = ChcExpr::var(e);

    let formula = ChcExpr::ne(d_var, e_var);
    safe_eprintln!("Testing formula: {}", formula);

    let result = ctx.check_sat(&formula);
    safe_eprintln!("Result: {:?}", result);

    // D != E is SAT (infinitely many solutions)
    assert!(
        matches!(result, SmtResult::Sat(_)),
        "Expected SAT but got {result:?}"
    );
}

#[test]
fn test_expression_split_is_guarded() {
    let mut ctx = SmtContext::new();

    // This is SAT (x = 0, y = 0, b = false), but can trigger an intermediate
    // `NeedExpressionSplit` when the SAT layer explores `x = y` as false.
    //
    // If the split clause is unguarded, it can overconstrain the problem by
    // permanently requiring `(x < y) ∨ (x > y)` even when `x = y` is later chosen.
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);
    let b = ChcVar::new("b", ChcSort::Bool);

    let x0 = ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0));
    let y0 = ChcExpr::eq(ChcExpr::var(y.clone()), ChcExpr::int(0));
    let eq_xy = ChcExpr::eq(ChcExpr::var(x), ChcExpr::var(y));
    let gate = ChcExpr::or(eq_xy, ChcExpr::var(b));

    let formula = ChcExpr::and(ChcExpr::and(x0, y0), gate);
    let result = ctx.check_sat(&formula);

    assert!(
        matches!(result, SmtResult::Sat(_)),
        "Expected SAT but got {result:?}"
    );
}

#[test]
fn test_compound_expr_equality() {
    let mut ctx = SmtContext::new();

    // Test: (x + 1) = (y + 1) /\ x = 5 /\ y = 6 should be UNSAT (6 != 7)
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);

    let x_plus_1 = ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1));
    let y_plus_1 = ChcExpr::add(ChcExpr::var(y.clone()), ChcExpr::int(1));
    let eq_compound = ChcExpr::eq(x_plus_1, y_plus_1);

    let x_eq_5 = ChcExpr::eq(ChcExpr::var(x), ChcExpr::int(5));
    let y_eq_6 = ChcExpr::eq(ChcExpr::var(y), ChcExpr::int(6));

    let formula = ChcExpr::and(ChcExpr::and(eq_compound, x_eq_5), y_eq_6);
    let result = ctx.check_sat(&formula);

    // (5+1) != (6+1), so should be UNSAT
    assert!(
        matches!(result, SmtResult::Unsat),
        "Expected UNSAT but got {result:?}"
    );
}

#[test]
fn test_compound_expr_equality_sat() {
    let mut ctx = SmtContext::new();

    // Test: (x + 1) = (y + 1) /\ x = 5 /\ y = 5 should be SAT (6 == 6)
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);

    let x_plus_1 = ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1));
    let y_plus_1 = ChcExpr::add(ChcExpr::var(y.clone()), ChcExpr::int(1));
    let eq_compound = ChcExpr::eq(x_plus_1, y_plus_1);

    let x_eq_5 = ChcExpr::eq(ChcExpr::var(x), ChcExpr::int(5));
    let y_eq_5 = ChcExpr::eq(ChcExpr::var(y), ChcExpr::int(5));

    let formula = ChcExpr::and(ChcExpr::and(eq_compound, x_eq_5), y_eq_5);
    let result = ctx.check_sat(&formula);

    // (5+1) == (5+1), so should be SAT
    assert!(
        matches!(result, SmtResult::Sat(_)),
        "Expected SAT but got {result:?}"
    );
}

#[test]
fn test_compound_expr_subtraction() {
    let mut ctx = SmtContext::new();

    // Test: (x - 3) = 2 /\ x = 5 should be SAT
    let x = ChcVar::new("x", ChcSort::Int);

    let x_minus_3 = ChcExpr::sub(ChcExpr::var(x.clone()), ChcExpr::int(3));
    let eq_expr = ChcExpr::eq(x_minus_3, ChcExpr::int(2));
    let x_eq_5 = ChcExpr::eq(ChcExpr::var(x), ChcExpr::int(5));

    let formula = ChcExpr::and(eq_expr, x_eq_5);
    let result = ctx.check_sat(&formula);

    // 5 - 3 = 2, so should be SAT
    assert!(
        matches!(result, SmtResult::Sat(_)),
        "Expected SAT but got {result:?}"
    );
}

#[test]
fn test_compound_expr_multiplication() {
    let mut ctx = SmtContext::new();

    // Test: (x * 2) = 10 /\ x = 5 should be SAT
    let x = ChcVar::new("x", ChcSort::Int);

    let x_times_2 = ChcExpr::mul(ChcExpr::var(x.clone()), ChcExpr::int(2));
    let eq_expr = ChcExpr::eq(x_times_2, ChcExpr::int(10));
    let x_eq_5 = ChcExpr::eq(ChcExpr::var(x), ChcExpr::int(5));

    let formula = ChcExpr::and(eq_expr, x_eq_5);
    let result = ctx.check_sat(&formula);

    // 5 * 2 = 10, so should be SAT
    assert!(
        matches!(result, SmtResult::Sat(_)),
        "Expected SAT but got {result:?}"
    );
}

#[test]
fn test_nested_compound_expr() {
    let mut ctx = SmtContext::new();

    // Test: ((x + 1) * 2) = 12 /\ x = 5 should be SAT
    let x = ChcVar::new("x", ChcSort::Int);

    let x_plus_1 = ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1));
    let x_plus_1_times_2 = ChcExpr::mul(x_plus_1, ChcExpr::int(2));
    let eq_expr = ChcExpr::eq(x_plus_1_times_2, ChcExpr::int(12));
    let x_eq_5 = ChcExpr::eq(ChcExpr::var(x), ChcExpr::int(5));

    let formula = ChcExpr::and(eq_expr, x_eq_5);
    let result = ctx.check_sat(&formula);

    // (5 + 1) * 2 = 12, so should be SAT
    assert!(
        matches!(result, SmtResult::Sat(_)),
        "Expected SAT but got {result:?}"
    );
}

// =========================================================================
// Mod elimination tests
// =========================================================================

#[test]
fn test_mod_elimination_basic() {
    // Test that mod elimination works for a simple case:
    // x = 7 /\ (mod x 3) = 1 should be SAT (7 mod 3 = 1)
    let mut ctx = SmtContext::new();

    let x = ChcVar::new("x", ChcSort::Int);
    let x_eq_7 = ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(7));
    let x_mod_3 = ChcExpr::Op(
        ChcOp::Mod,
        vec![Arc::new(ChcExpr::var(x)), Arc::new(ChcExpr::int(3))],
    );
    let mod_eq_1 = ChcExpr::eq(x_mod_3, ChcExpr::int(1));
    let formula = ChcExpr::and(x_eq_7, mod_eq_1);

    let result = ctx.check_sat(&formula);
    assert!(
        matches!(result, SmtResult::Sat(_)),
        "Expected SAT for x=7, x mod 3 = 1, got {result:?}"
    );
}

#[test]
fn test_mod_elimination_unsat() {
    // Test that mod elimination correctly detects UNSAT:
    // x = 7 /\ (mod x 3) = 2 should be UNSAT (7 mod 3 = 1, not 2)
    let mut ctx = SmtContext::new();

    let x = ChcVar::new("x", ChcSort::Int);
    let x_eq_7 = ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(7));
    let x_mod_3 = ChcExpr::Op(
        ChcOp::Mod,
        vec![Arc::new(ChcExpr::var(x)), Arc::new(ChcExpr::int(3))],
    );
    let mod_eq_2 = ChcExpr::eq(x_mod_3, ChcExpr::int(2));
    let formula = ChcExpr::and(x_eq_7, mod_eq_2);

    let result = ctx.check_sat(&formula);
    assert!(
        matches!(result, SmtResult::Unsat),
        "Expected UNSAT for x=7, x mod 3 = 2, got {result:?}"
    );
}

#[test]
fn test_mod_elimination_constraint_sat() {
    // Test mod constraint satisfaction:
    // (mod x 2) = 0 should be SAT (x can be any even number)
    let mut ctx = SmtContext::new();

    let x = ChcVar::new("x", ChcSort::Int);
    let x_mod_2 = ChcExpr::Op(
        ChcOp::Mod,
        vec![Arc::new(ChcExpr::var(x.clone())), Arc::new(ChcExpr::int(2))],
    );
    let mod_eq_0 = ChcExpr::eq(x_mod_2, ChcExpr::int(0));
    // Add bound to make it finite: 0 <= x <= 10
    let x_ge_0 = ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(0));
    let x_le_10 = ChcExpr::le(ChcExpr::var(x), ChcExpr::int(10));
    let formula = ChcExpr::and(ChcExpr::and(mod_eq_0, x_ge_0), x_le_10);

    let result = ctx.check_sat(&formula);
    assert!(
        matches!(result, SmtResult::Sat(_)),
        "Expected SAT for x mod 2 = 0 with 0 <= x <= 10, got {result:?}"
    );
}

#[test]
fn test_mod_elimination_no_solution() {
    // Test impossible constraint:
    // (mod x 5) = 10 should be UNSAT (remainder must be < divisor)
    let mut ctx = SmtContext::new();

    let x = ChcVar::new("x", ChcSort::Int);
    let x_mod_5 = ChcExpr::Op(
        ChcOp::Mod,
        vec![Arc::new(ChcExpr::var(x.clone())), Arc::new(ChcExpr::int(5))],
    );
    let mod_eq_10 = ChcExpr::eq(x_mod_5, ChcExpr::int(10));
    // Add bound to ensure solver doesn't run forever: 0 <= x <= 100
    let x_ge_0 = ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(0));
    let x_le_100 = ChcExpr::le(ChcExpr::var(x), ChcExpr::int(100));
    let formula = ChcExpr::and(ChcExpr::and(mod_eq_10, x_ge_0), x_le_100);

    let result = ctx.check_sat(&formula);
    assert!(
        matches!(
            result,
            SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_)
        ),
        "Expected UNSAT for x mod 5 = 10 (remainder cannot be >= divisor), got {result:?}"
    );
}

#[test]
fn test_mod_eliminate_expr() {
    // Unit test for the eliminate_mod method itself
    let x = ChcVar::new("x", ChcSort::Int);
    let x_mod_3 = ChcExpr::Op(
        ChcOp::Mod,
        vec![Arc::new(ChcExpr::var(x)), Arc::new(ChcExpr::int(3))],
    );
    let original = ChcExpr::eq(x_mod_3, ChcExpr::int(1));
    let eliminated = original.eliminate_mod();

    // The eliminated expression should be an AND of multiple constraints
    // (the original comparison + definitional constraints)
    match &eliminated {
        ChcExpr::Op(ChcOp::And, args) => {
            // Should have multiple conjuncts:
            // 1. x = k*q + r
            // 2. r >= 0
            // 3. r < |k|
            // 4. r = 1 (the original constraint rewritten)
            assert!(
                args.len() >= 4,
                "Expected at least 4 conjuncts after mod elimination, got {}",
                args.len()
            );
        }
        _ => panic!("Expected AND expression after mod elimination, got {eliminated:?}"),
    }
}

/// #A3: Int-valued array selects are valid Euclidean dividends.
/// `(mod (select a 0) 3)` must be eliminated (constant divisor), not left
/// behind for AUFLIA executor paths to reject as unsupported arithmetic.
#[test]
fn test_mod_eliminate_select_dividend() {
    let a = ChcVar::new(
        "a",
        ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int)),
    );
    let select = ChcExpr::select(ChcExpr::var(a), ChcExpr::int(0));
    let sel_mod_3 = ChcExpr::Op(
        ChcOp::Mod,
        vec![Arc::new(select), Arc::new(ChcExpr::int(3))],
    );
    let original = ChcExpr::eq(sel_mod_3, ChcExpr::int(1));
    let eliminated = original.eliminate_mod();
    assert!(
        !eliminated.contains_mod_or_div(),
        "select-dividend mod with literal divisor must be eliminated, got {eliminated}"
    );
}

#[test]
fn preprocess_preserves_plain_linear_constraints() {
    let x = ChcVar::new("x", ChcSort::Int);
    let plain = ChcExpr::eq(ChcExpr::var(x), ChcExpr::int(7));

    let preprocessed = SmtContext::preprocess(&plain);
    let incremental = SmtContext::preprocess_incremental_assumption(&plain, "q0");

    // Full preprocessing includes propagate_constants(), which folds x=7 to true.
    assert_eq!(preprocessed, ChcExpr::Bool(true));
    assert_eq!(incremental, plain);
    assert!(!preprocessed.contains_ite());
    assert!(!preprocessed.contains_mod_or_div());
    assert!(!preprocessed.contains_negation());
    assert!(!preprocessed.contains_strict_int_comparison());
}

#[test]
fn preprocess_eliminates_targeted_constructs() {
    let x = ChcVar::new("x", ChcSort::Int);
    let b = ChcVar::new("b", ChcSort::Bool);

    let guarded_value = ChcExpr::ite(
        ChcExpr::var(b),
        ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1)),
        ChcExpr::sub(ChcExpr::var(x.clone()), ChcExpr::int(1)),
    );
    let guarded_strict = ChcExpr::lt(guarded_value, ChcExpr::int(5));
    let negated_eq = ChcExpr::not(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0)));
    let with_mod = ChcExpr::eq(
        ChcExpr::mod_op(ChcExpr::var(x), ChcExpr::int(3)),
        ChcExpr::int(1),
    );
    let formula = ChcExpr::and(ChcExpr::and(guarded_strict, negated_eq), with_mod);

    let preprocessed = SmtContext::preprocess(&formula);
    let incremental = SmtContext::preprocess_incremental_assumption(&formula, "q0");

    for expr in [&preprocessed, &incremental] {
        assert!(!expr.contains_ite(), "ITE should be eliminated");
        assert!(!expr.contains_mod_or_div(), "mod/div should be eliminated");
        assert!(
            !expr.contains_strict_int_comparison(),
            "strict comparisons should be normalized"
        );
    }

    let negated_only = ChcExpr::not(ChcExpr::eq(
        ChcExpr::var(ChcVar::new("y", ChcSort::Int)),
        ChcExpr::int(3),
    ));
    let neg_preprocessed = SmtContext::preprocess(&negated_only);
    let neg_incremental = SmtContext::preprocess_incremental_assumption(&negated_only, "q1");
    assert!(!neg_preprocessed.contains_negation());
    assert!(!neg_incremental.contains_negation());
}

#[test]
fn preprocess_mixed_sort_eq_eliminates_generated_ite() {
    let d = ChcVar::new("d", ChcSort::Int);
    let e = ChcVar::new("e", ChcSort::Int);
    let mixed = ChcExpr::eq(
        ChcExpr::var(d),
        ChcExpr::eq(ChcExpr::var(e), ChcExpr::int(0)),
    );

    let preprocessed = SmtContext::preprocess(&mixed);
    let incremental = SmtContext::preprocess_incremental_assumption(&mixed, "q0");

    for expr in [&preprocessed, &incremental] {
        assert!(
            !expr.contains_mixed_sort_eq(),
            "mixed-sort equality should be rewritten before conversion"
        );
        assert!(
            !expr.contains_ite(),
            "ITE introduced by mixed-sort equality rewriting should be eliminated"
        );
    }
}

#[test]
fn preprocess_normalizes_strict_comparisons_generated_from_negation() {
    let x = ChcVar::new("x", ChcSort::Int);
    let negated_le = ChcExpr::not(ChcExpr::le(ChcExpr::var(x.clone()), ChcExpr::int(5)));
    let expected = ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(6));

    let preprocessed = SmtContext::preprocess(&negated_le);
    let incremental = SmtContext::preprocess_incremental_assumption(&negated_le, "q0");

    for expr in [&preprocessed, &incremental] {
        assert!(
            !expr.contains_negation(),
            "negation should be normalized away"
        );
        assert!(
            !expr.contains_strict_int_comparison(),
            "generated strict comparison should be normalized"
        );
        assert_eq!(expr, &expected, "not(<= x 5) should preprocess to x >= 6");
    }
}

#[test]
fn preprocess_normalizes_strict_bounds_generated_from_mod_elimination() {
    let x = ChcVar::new("x", ChcSort::Int);
    let mod_eq = ChcExpr::eq(
        ChcExpr::mod_op(ChcExpr::var(x), ChcExpr::int(3)),
        ChcExpr::int(1),
    );

    let preprocessed = SmtContext::preprocess(&mod_eq);
    let incremental = SmtContext::preprocess_incremental_assumption(&mod_eq, "q0");

    for expr in [&preprocessed, &incremental] {
        assert!(!expr.contains_mod_or_div(), "mod/div should be eliminated");
        assert!(
            !expr.contains_strict_int_comparison(),
            "mod elimination introduces a strict remainder bound that must be normalized"
        );
    }
}

// =========================================================================
// ITE / div-by-zero / mod-by-zero elimination tests
// =========================================================================

#[test]
fn test_ite_elimination_sat() {
    // x = (ite b 1 0) /\ b = true /\ x = 1 should be SAT.
    // Without ite elimination, `(= x (ite ...))` is not a linear arithmetic atom.
    let mut ctx = SmtContext::new();

    let b = ChcVar::new("b", ChcSort::Bool);
    let x = ChcVar::new("x", ChcSort::Int);

    let b_true = ChcExpr::eq(ChcExpr::var(b.clone()), ChcExpr::bool_const(true));
    let x_eq_ite = ChcExpr::eq(
        ChcExpr::var(x.clone()),
        ChcExpr::ite(ChcExpr::var(b), ChcExpr::int(1), ChcExpr::int(0)),
    );
    let x_eq_1 = ChcExpr::eq(ChcExpr::var(x), ChcExpr::int(1));

    let formula = ChcExpr::and(ChcExpr::and(b_true, x_eq_ite), x_eq_1);
    let result = ctx.check_sat(&formula);
    assert!(
        matches!(result, SmtResult::Sat(_)),
        "Expected SAT but got {result:?}"
    );
}

#[test]
fn test_ite_elimination_unsat() {
    // x = (ite b 1 0) /\ b = true /\ x = 0 should be UNSAT.
    let mut ctx = SmtContext::new();

    let b = ChcVar::new("b", ChcSort::Bool);
    let x = ChcVar::new("x", ChcSort::Int);

    let b_true = ChcExpr::eq(ChcExpr::var(b.clone()), ChcExpr::bool_const(true));
    let x_eq_ite = ChcExpr::eq(
        ChcExpr::var(x.clone()),
        ChcExpr::ite(ChcExpr::var(b), ChcExpr::int(1), ChcExpr::int(0)),
    );
    let x_eq_0 = ChcExpr::eq(ChcExpr::var(x), ChcExpr::int(0));

    let formula = ChcExpr::and(ChcExpr::and(b_true, x_eq_ite), x_eq_0);
    let result = ctx.check_sat(&formula);
    assert!(
        matches!(
            result,
            SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_)
        ),
        "Expected UNSAT but got {result:?}"
    );
}

#[test]
fn test_mod_by_zero_semantics() {
    // SMT-LIB: (mod x 0) = x
    let mut ctx = SmtContext::new();

    let x = ChcVar::new("x", ChcSort::Int);
    let x_eq_5 = ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(5));
    let x_mod_0 = ChcExpr::Op(
        ChcOp::Mod,
        vec![Arc::new(ChcExpr::var(x)), Arc::new(ChcExpr::int(0))],
    );

    let mod_eq_5 = ChcExpr::eq(x_mod_0.clone(), ChcExpr::int(5));
    let sat_formula = ChcExpr::and(x_eq_5.clone(), mod_eq_5);
    assert!(matches!(ctx.check_sat(&sat_formula), SmtResult::Sat(_)));

    let mod_eq_6 = ChcExpr::eq(x_mod_0, ChcExpr::int(6));
    let unsat_formula = ChcExpr::and(x_eq_5, mod_eq_6);
    assert!(matches!(
        ctx.check_sat(&unsat_formula),
        SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_)
    ));
}

#[test]
fn test_div_by_zero_semantics() {
    // SMT-LIB: (div x 0) = 0
    let mut ctx = SmtContext::new();

    let x = ChcVar::new("x", ChcSort::Int);
    let x_eq_7 = ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(7));
    let x_div_0 = ChcExpr::Op(
        ChcOp::Div,
        vec![Arc::new(ChcExpr::var(x)), Arc::new(ChcExpr::int(0))],
    );

    let div_eq_0 = ChcExpr::eq(x_div_0.clone(), ChcExpr::int(0));
    let sat_formula = ChcExpr::and(x_eq_7.clone(), div_eq_0);
    assert!(matches!(ctx.check_sat(&sat_formula), SmtResult::Sat(_)));

    let div_eq_1 = ChcExpr::eq(x_div_0, ChcExpr::int(1));
    let unsat_formula = ChcExpr::and(x_eq_7, div_eq_1);
    assert!(matches!(
        ctx.check_sat(&unsat_formula),
        SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_)
    ));
}

#[test]
fn test_incremental_context_tracks_background_formulas_for_validation() {
    let mut smt = SmtContext::new();
    let mut inc = IncrementalQueryContext::new();
    let x = ChcVar::new("x", ChcSort::Int);
    let background = ChcExpr::eq(ChcExpr::var(x), ChcExpr::int(0));

    inc.assert_background(&background, &mut smt);

    assert_eq!(inc.background_exprs.len(), 1);
    assert_eq!(inc.background_exprs[0], background);
}

/// Regression test for #6091: formulas with unhandled sort variants must not panic.
///
/// Before the fix, `check_sat` would hit `unreachable!()` when encountering sorts
/// like `Uninterpreted` that the CHC solver doesn't natively handle.
#[test]
fn test_check_sat_uninterpreted_sort_no_panic() {
    let mut ctx = SmtContext::new();
    let x = ChcVar::new("x", ChcSort::Uninterpreted("MySort".to_string()));
    let y = ChcVar::new("y", ChcSort::Uninterpreted("MySort".to_string()));
    // x = y with uninterpreted sort — should return Sat or Unknown, never panic.
    let expr = ChcExpr::eq(ChcExpr::var(x), ChcExpr::var(y));
    let result = ctx.check_sat(&expr);
    assert!(
        !matches!(result, SmtResult::Unsat),
        "x = y with uninterpreted sort should be satisfiable, got {result:?}"
    );
}

/// #6100: Warm and fresh SmtContext must produce identical var_map keys
/// and variable sorts regardless of encounter order or accumulated state.
///
/// Before the fix, a warm context that first saw `x` as Int would assign
/// the unqualified name `x` to Int. A fresh context that first saw `x` as
/// Bool would assign `x` to Bool. Sort-qualification makes the key
/// `x_Int` vs `x_Bool` deterministic regardless of traversal order.
#[test]
fn test_sort_qualified_var_map_determinism() {
    // Scenario: variable "x" appears as both Int and Bool across two
    // expressions. Warm context processes them in Int-then-Bool order;
    // fresh context processes them in Bool-then-Int order. Both must
    // produce identical var_map keys (`x_Int`, `x_Bool`).

    // Warm context: first sees x as Int, then as Bool.
    let mut warm = SmtContext::new();
    let x_int = ChcVar::new("x", ChcSort::Int);
    let x_bool = ChcVar::new("x", ChcSort::Bool);
    let expr1 = ChcExpr::var(x_int);
    let expr2 = ChcExpr::var(x_bool);
    let warm_int = warm.convert_expr(&expr1);
    let warm_bool = warm.convert_expr(&expr2);

    // Fresh context: processes the SAME two expressions but in reverse order
    // (Bool first, then Int). If sort-qualification works, TermIds are
    // deterministic — the qualified keys `x_Int` and `x_Bool` are the same
    // regardless of encounter order.
    let mut fresh = SmtContext::new();
    let fresh_bool = fresh.convert_expr(&expr2);
    let fresh_int = fresh.convert_expr(&expr1);

    // Both contexts should have exactly 2 entries in var_map.
    assert_eq!(warm.var_map.len(), 2, "warm var_map should have 2 entries");
    assert_eq!(
        fresh.var_map.len(),
        2,
        "fresh var_map should have 2 entries"
    );

    // Both should have the same qualified keys.
    let warm_keys: FxHashSet<&String> = warm.var_map.keys().collect();
    let fresh_keys: FxHashSet<&String> = fresh.var_map.keys().collect();
    assert_eq!(warm_keys, fresh_keys, "var_map keys should be identical");

    // Keys should be sort-qualified.
    assert!(warm.var_map.contains_key("x_Int"), "should have x_Int key");
    assert!(
        warm.var_map.contains_key("x_Bool"),
        "should have x_Bool key"
    );

    // Original names should map back to "x".
    assert_eq!(warm.original_var_name("x_Int"), "x");
    assert_eq!(warm.original_var_name("x_Bool"), "x");
    assert_eq!(fresh.original_var_name("x_Int"), "x");
    assert_eq!(fresh.original_var_name("x_Bool"), "x");

    // The TermIds for the same qualified key should match between warm and fresh.
    // (Note: absolute TermId values may differ between contexts since they have
    // different TermStores, but the *sorts* and *qualified names* must agree.)
    assert_eq!(
        *warm.terms.sort(warm_int),
        *fresh.terms.sort(fresh_int),
        "x_Int sort should match"
    );
    assert_eq!(
        *warm.terms.sort(warm_bool),
        *fresh.terms.sort(fresh_bool),
        "x_Bool sort should match"
    );
}

/// #6100: Model extraction should emit original (unqualified) variable names,
/// not sort-qualified names. Downstream code uses `model.get(&v.name)` where
/// `v.name` is the original CHC variable name.
#[test]
fn test_model_extraction_uses_original_names() {
    let mut ctx = SmtContext::new();

    // x = 5 (Int variable)
    let x = ChcVar::new("x", ChcSort::Int);
    let expr = ChcExpr::eq(ChcExpr::var(x), ChcExpr::int(5));
    let result = ctx.check_sat(&expr);

    if let SmtResult::Sat(model) = result {
        // Model should contain "x" (original name), not "x_Int" (qualified name).
        assert!(
            model.contains_key("x"),
            "model should contain original name 'x', got keys: {:?}",
            model.keys().collect::<Vec<_>>()
        );
        assert!(
            !model.contains_key("x_Int"),
            "model should NOT contain qualified name 'x_Int'"
        );
        assert_eq!(model.get("x"), Some(&SmtValue::Int(5)));
    } else {
        panic!("x = 5 should be SAT, got {result:?}");
    }
}

// --- #5877: SmtResult conversion tests ---
#[test]
fn test_smt_result_into_farkas_conflicts_6484() {
    // #6484: SmtResult::into_farkas_conflicts extracts certificates from UNSAT variants.

    // Plain Unsat → empty
    let r = SmtResult::Unsat;
    assert!(r.into_farkas_conflicts().is_empty());

    // UnsatWithFarkas → vec with the single conflict
    let conflict = FarkasConflict {
        conflict_terms: vec![TermId::new(1), TermId::new(2)],
        polarities: vec![true, false],
        farkas: FarkasAnnotation::from_ints(&[1, 1]),
        origins: vec![Partition::A, Partition::B],
    };
    let r = SmtResult::UnsatWithFarkas(conflict.clone());
    let extracted = r.into_farkas_conflicts();
    assert_eq!(extracted.len(), 1);
    assert_eq!(extracted[0].conflict_terms, conflict.conflict_terms);

    // UnsatWithCore → delegates to core.farkas_conflicts
    use super::types::UnsatCore;
    let core = UnsatCore {
        conjuncts: vec![],
        farkas_conflicts: vec![conflict.clone(), conflict],
        diagnostics: Default::default(),
    };
    let r = SmtResult::UnsatWithCore(core);
    let extracted = r.into_farkas_conflicts();
    assert_eq!(extracted.len(), 2);

    // Sat / Unknown → empty
    let r = SmtResult::Sat(Default::default());
    assert!(r.into_farkas_conflicts().is_empty());
    let r = SmtResult::Unknown;
    assert!(r.into_farkas_conflicts().is_empty());
}

/// #7016: Test that DT queries are routed through executor adapter without
/// producing an incorrect answer.
///
/// Declares a Pair(Int, Int) datatype with a DT-sorted variable `p`, asserts
/// `(= p (mk x 42))` and `(= (fst p) 10)`. If the executor can solve the
/// query, the model must report x = 10; a conservative `Unknown` is acceptable.
///
/// The variable `p` must have `ChcSort::Datatype` (not `Uninterpreted`) so that
/// `scan_features().has_dt` is true and `collect_dt_declarations` finds the DT.
#[test]
fn test_datatype_pair_selector_via_executor_7016() {
    use crate::{ChcDtConstructor, ChcDtSelector};

    let mut ctx = SmtContext::new();

    // Build Pair(Int, Int) datatype sort with full constructor/selector metadata.
    let pair_sort = ChcSort::Datatype {
        name: "Pair".to_string(),
        constructors: Arc::new(vec![ChcDtConstructor {
            name: "mk".to_string(),
            selectors: vec![
                ChcDtSelector {
                    name: "fst".to_string(),
                    sort: ChcSort::Int,
                },
                ChcDtSelector {
                    name: "snd".to_string(),
                    sort: ChcSort::Int,
                },
            ],
        }]),
    };

    // Variables: p : Pair, x : Int
    let p = Arc::new(ChcExpr::Var(ChcVar {
        name: "p".to_string(),
        sort: pair_sort.clone(),
    }));
    let x = Arc::new(ChcExpr::Var(ChcVar {
        name: "x".to_string(),
        sort: ChcSort::Int,
    }));
    let forty_two = Arc::new(ChcExpr::Int(42));
    let ten = Arc::new(ChcExpr::Int(10));

    // mk(x, 42) — constructor application, returns Pair sort
    let mk_pair = Arc::new(ChcExpr::FuncApp(
        "mk".to_string(),
        pair_sort,
        vec![x, forty_two],
    ));

    // fst(p) — selector application, returns Int sort
    let fst_p = Arc::new(ChcExpr::FuncApp(
        "fst".to_string(),
        ChcSort::Int,
        vec![p.clone()],
    ));

    // (and (= p (mk x 42)) (= (fst p) 10))
    let eq_p_mk = Arc::new(ChcExpr::Op(ChcOp::Eq, vec![p, mk_pair]));
    let eq_fst_ten = Arc::new(ChcExpr::Op(ChcOp::Eq, vec![fst_p, ten]));
    let conjunction = ChcExpr::Op(ChcOp::And, vec![eq_p_mk, eq_fst_ten]);

    let result = ctx.check_sat(&conjunction);
    match &result {
        SmtResult::Sat(model) => {
            let x_val = model.get("x");
            assert_eq!(
                x_val,
                Some(&SmtValue::Int(10)),
                "Expected x=10, got {x_val:?}"
            );
        }
        SmtResult::Unknown => {}
        other => panic!("Expected Sat or Unknown, got {other:?}"),
    }
}
