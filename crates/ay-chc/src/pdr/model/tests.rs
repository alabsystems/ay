// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::{ChcProblem, ChcSort, ClauseBody, ClauseHead, HornClause, PredicateId};

// =======================================================================
// Tests for PredicateInterpretation - #1651
// =======================================================================

#[test]
fn predicate_interpretation_new_stores_vars_and_formula() {
    let vars = vec![
        ChcVar::new("x", ChcSort::Int),
        ChcVar::new("y", ChcSort::Int),
    ];
    let formula = ChcExpr::and(
        ChcExpr::ge(ChcExpr::var(vars[0].clone()), ChcExpr::int(0)),
        ChcExpr::le(ChcExpr::var(vars[1].clone()), ChcExpr::int(10)),
    );

    let interp = PredicateInterpretation::new(vars, formula.clone());
    assert_eq!(interp.vars.len(), 2);
    assert_eq!(interp.vars[0].name, "x");
    assert_eq!(interp.vars[1].name, "y");
    assert_eq!(interp.formula, formula);
}

// =======================================================================
// Tests for InvariantModel basic operations - #1651
// =======================================================================

#[test]
fn invariant_model_new_is_empty() {
    let model = InvariantModel::new();
    assert!(model.is_empty());
    assert_eq!(model.len(), 0);
}

#[test]
fn invariant_model_set_and_get() {
    let mut model = InvariantModel::new();
    let pred_id = PredicateId::new(0);
    let vars = vec![ChcVar::new("x", ChcSort::Int)];
    let formula = ChcExpr::Bool(true);
    let interp = PredicateInterpretation::new(vars, formula);

    model.set(pred_id, interp);

    assert_eq!(model.len(), 1);
    assert!(!model.is_empty());
    assert!(model.get(&pred_id).is_some());
    assert_eq!(model.get(&pred_id).unwrap().vars.len(), 1);
}

#[test]
fn invariant_model_get_nonexistent_returns_none() {
    let model = InvariantModel::new();
    let pred_id = PredicateId::new(42);
    assert!(model.get(&pred_id).is_none());
}

#[test]
fn invariant_model_iter_iterates_all() {
    let mut model = InvariantModel::new();

    let pred_id_0 = PredicateId::new(0);
    let pred_id_1 = PredicateId::new(1);

    model.set(
        pred_id_0,
        PredicateInterpretation::new(vec![], ChcExpr::Bool(true)),
    );
    model.set(
        pred_id_1,
        PredicateInterpretation::new(vec![], ChcExpr::Bool(false)),
    );

    let entries: Vec<_> = model.iter().collect();
    assert_eq!(entries.len(), 2);
}

#[test]
fn replay_obligations_for_minimal_safe_certificate_cover_all_safe_kinds() {
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("inv", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);

    problem.add_clause(HornClause::new(
        ClauseBody::empty(),
        ClauseHead::Predicate(inv, vec![ChcExpr::int(0)]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ),
        ClauseHead::Predicate(
            inv,
            vec![ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1))],
        ),
    ));
    problem.add_clause(HornClause::query(ClauseBody::new(
        vec![(inv, vec![ChcExpr::var(x.clone())])],
        Some(ChcExpr::lt(ChcExpr::var(x), ChcExpr::int(0))),
    )));

    let mut model = InvariantModel::new();
    let param = ChcVar::new("x", ChcSort::Int);
    model.set(
        inv,
        PredicateInterpretation::new(
            vec![param.clone()],
            ChcExpr::ge(ChcExpr::var(param), ChcExpr::int(0)),
        ),
    );

    let obligations = model
        .replay_obligations(&problem)
        .expect("minimal safe obligations");
    let kinds = obligations.iter().map(|o| o.kind).collect::<Vec<_>>();
    assert_eq!(
        kinds,
        vec![
            ChcReplayObligationKind::Initiation,
            ChcReplayObligationKind::Consecution,
            ChcReplayObligationKind::Safety,
        ]
    );
    assert!(obligations[0].smtlib.contains("(assert (not (>= 0 0)))"));
    assert!(obligations[1].smtlib.contains("(not (>= (+ x 1) 0))"));
    assert!(obligations[2]
        .smtlib
        .contains("(assert (and (>= x 0) (< x 0)))"));
    for obligation in obligations {
        assert!(obligation.smtlib.contains("(check-sat)"));
    }
}

#[test]
fn replay_obligations_fail_closed_when_interpretation_is_missing() {
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("inv", vec![ChcSort::Int]);
    problem.add_clause(HornClause::new(
        ClauseBody::empty(),
        ClauseHead::Predicate(inv, vec![ChcExpr::int(0)]),
    ));

    let model = InvariantModel::new();
    let error = model
        .replay_obligations(&problem)
        .expect_err("missing invariant must not produce passing obligations");
    assert!(error
        .to_string()
        .contains("missing invariant interpretation"));
}

#[test]
fn constant_false_replay_uses_strict_certifiable_guard_contradiction() {
    let mut problem = ChcProblem::new();
    let error = problem.declare_predicate("error", Vec::new());
    problem.add_clause(HornClause::query(ClauseBody::predicates_only(vec![(
        error,
        Vec::new(),
    )])));

    let mut model = InvariantModel::new();
    model.set(
        error,
        PredicateInterpretation::new(Vec::new(), ChcExpr::Bool(false)),
    );

    let obligations = model
        .replay_obligations(&problem)
        .expect("nullary false replay obligation");
    let [obligation] = obligations.as_slice() else {
        panic!("fixture must produce exactly one replay obligation");
    };
    assert!(obligation
        .smtlib
        .contains("(assert chc_replay_false_guard)"));
    assert!(obligation
        .smtlib
        .contains("(assert (not chc_replay_false_guard))"));
    assert!(
        !obligation.smtlib.contains("(assert false)"),
        "literal false cannot retain authored Assume authority"
    );
    assert!(
        !obligation.smtlib.contains("(define-fun error"),
        "an unused false-bodied definition must not enter the guarded contradiction"
    );
    let cert = crate::smt::executor_adapter::smtlib_strict_unsat_cert_via_executor(
        &obligation.smtlib,
        None,
    )
    .expect("the guarded constant-false replay query must retain a native strict certificate");
    assert_eq!(
        cert.bundle.obligation_assertions.len(),
        2,
        "the strict proof must retain both sides of the authored contradiction"
    );
    let checked = ay_dpll::api::re_check_bundle_strict(&cert.bundle)
        .expect("the guarded contradiction bundle must independently recheck");
    assert!(!checked.assume_terms.is_empty());
    assert_eq!(checked.assume_terms, cert.bundle.obligation_assertions);
}

#[test]
fn replay_obligations_declare_scalar_ufs_before_use() {
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("inv", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);
    let f_x = || {
        ChcExpr::FuncApp(
            "f".to_string(),
            ChcSort::Int,
            vec![ChcExpr::var(x.clone()).into()],
        )
    };
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(f_x(), ChcExpr::Int(0))),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone())]),
    ));
    problem.add_clause(HornClause::query(ClauseBody::new(
        vec![(inv, vec![ChcExpr::var(x.clone())])],
        Some(ChcExpr::not(ChcExpr::eq(f_x(), ChcExpr::Int(0)))),
    )));

    let mut model = InvariantModel::new();
    let parameter = ChcVar::new("x", ChcSort::Int);
    let invariant_f = ChcExpr::FuncApp(
        "f".to_string(),
        ChcSort::Int,
        vec![ChcExpr::var(parameter.clone()).into()],
    );
    model.set(
        inv,
        PredicateInterpretation::new(vec![parameter], ChcExpr::eq(invariant_f, ChcExpr::Int(0))),
    );

    let obligations = model
        .replay_obligations(&problem)
        .expect("ordinary UF signatures should make replay self-contained");
    for obligation in obligations {
        let declaration = obligation
            .smtlib
            .find("(declare-fun f (Int) Int)")
            .expect("replay script must declare f");
        let use_site = obligation.smtlib.find("(f x)").expect("fixture must use f");
        assert!(
            declaration < use_site,
            "f must be declared before its first replay use: {}",
            obligation.smtlib
        );
    }
}

// =======================================================================
// Tests for expr_to_smtlib - #1651
// =======================================================================

#[test]
fn expr_to_smtlib_bool_true() {
    assert_eq!(InvariantModel::expr_to_smtlib(&ChcExpr::Bool(true)), "true");
}

#[test]
fn expr_to_smtlib_bool_false() {
    assert_eq!(
        InvariantModel::expr_to_smtlib(&ChcExpr::Bool(false)),
        "false"
    );
}

#[test]
fn expr_to_smtlib_positive_int() {
    assert_eq!(InvariantModel::expr_to_smtlib(&ChcExpr::Int(42)), "42");
}

#[test]
fn expr_to_smtlib_negative_int() {
    assert_eq!(InvariantModel::expr_to_smtlib(&ChcExpr::Int(-42)), "(- 42)");
}

#[test]
fn expr_to_smtlib_zero_int() {
    assert_eq!(InvariantModel::expr_to_smtlib(&ChcExpr::Int(0)), "0");
}

#[test]
fn expr_to_smtlib_var() {
    let v = ChcVar::new("myVar", ChcSort::Int);
    assert_eq!(InvariantModel::expr_to_smtlib(&ChcExpr::var(v)), "myVar");
}

#[test]
fn expr_to_smtlib_comparison_ops() {
    let x = ChcVar::new("x", ChcSort::Int);

    // >= operator
    let ge = ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(0));
    assert_eq!(InvariantModel::expr_to_smtlib(&ge), "(>= x 0)");

    // <= operator
    let le = ChcExpr::le(ChcExpr::var(x.clone()), ChcExpr::int(10));
    assert_eq!(InvariantModel::expr_to_smtlib(&le), "(<= x 10)");

    // = operator
    let eq = ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(5));
    assert_eq!(InvariantModel::expr_to_smtlib(&eq), "(= x 5)");

    // distinct operator
    let ne = ChcExpr::ne(ChcExpr::var(x), ChcExpr::int(0));
    assert_eq!(InvariantModel::expr_to_smtlib(&ne), "(distinct x 0)");
}

#[test]
fn expr_to_smtlib_logical_ops() {
    let x = ChcVar::new("x", ChcSort::Bool);
    let y = ChcVar::new("y", ChcSort::Bool);

    // and: use two non-trivial operands (and_all simplifies identity elements)
    let and_expr = ChcExpr::and(ChcExpr::var(x.clone()), ChcExpr::var(y.clone()));
    assert_eq!(InvariantModel::expr_to_smtlib(&and_expr), "(and x y)");

    // and with identity: and(x, true) simplifies to x
    let and_identity = ChcExpr::and(ChcExpr::var(x.clone()), ChcExpr::Bool(true));
    assert_eq!(InvariantModel::expr_to_smtlib(&and_identity), "x");

    // or: use two non-trivial operands (or_all simplifies identity elements)
    let or_expr = ChcExpr::or(ChcExpr::var(x.clone()), ChcExpr::var(y));
    assert_eq!(InvariantModel::expr_to_smtlib(&or_expr), "(or x y)");

    // or with identity: or(x, false) simplifies to x
    let or_identity = ChcExpr::or(ChcExpr::var(x.clone()), ChcExpr::Bool(false));
    assert_eq!(InvariantModel::expr_to_smtlib(&or_identity), "x");

    // not
    let not_expr = ChcExpr::not(ChcExpr::var(x));
    assert_eq!(InvariantModel::expr_to_smtlib(&not_expr), "(not x)");
}

#[test]
fn expr_to_smtlib_arithmetic_ops() {
    let x = ChcVar::new("x", ChcSort::Int);

    // +
    let add = ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1));
    assert_eq!(InvariantModel::expr_to_smtlib(&add), "(+ x 1)");

    // -
    let sub = ChcExpr::sub(ChcExpr::var(x.clone()), ChcExpr::int(1));
    assert_eq!(InvariantModel::expr_to_smtlib(&sub), "(- x 1)");

    // *
    let mul = ChcExpr::mul(ChcExpr::var(x.clone()), ChcExpr::int(2));
    assert_eq!(InvariantModel::expr_to_smtlib(&mul), "(* x 2)");

    // mod
    let mod_expr = ChcExpr::mod_op(ChcExpr::var(x), ChcExpr::int(2));
    assert_eq!(InvariantModel::expr_to_smtlib(&mod_expr), "(mod x 2)");
}

#[test]
fn expr_to_smtlib_nested_expression() {
    let x = ChcVar::new("x", ChcSort::Int);
    // (and (>= x 0) (<= x 10))
    let expr = ChcExpr::and(
        ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(0)),
        ChcExpr::le(ChcExpr::var(x), ChcExpr::int(10)),
    );
    assert_eq!(
        InvariantModel::expr_to_smtlib(&expr),
        "(and (>= x 0) (<= x 10))"
    );
}

#[test]
fn expr_to_smtlib_real_positive() {
    let real = ChcExpr::Real(3, 4); // 3/4
    assert_eq!(InvariantModel::expr_to_smtlib(&real), "(/ 3 4)");
}

#[test]
fn expr_to_smtlib_real_negative() {
    let real = ChcExpr::Real(-3, 4); // -3/4
    assert_eq!(InvariantModel::expr_to_smtlib(&real), "(/ (- 3) 4)");
}

#[test]
fn expr_to_smtlib_ite() {
    let x = ChcVar::new("x", ChcSort::Int);
    // (ite (>= x 0) 1 0)
    let ite = ChcExpr::ite(
        ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(0)),
        ChcExpr::int(1),
        ChcExpr::int(0),
    );
    assert_eq!(InvariantModel::expr_to_smtlib(&ite), "(ite (>= x 0) 1 0)");
}

// =======================================================================
// Additional expr_to_smtlib coverage - #1651 audit round
// =======================================================================

#[test]
fn expr_to_smtlib_lt_and_gt_operators() {
    let x = ChcVar::new("x", ChcSort::Int);

    // < operator
    let lt = ChcExpr::lt(ChcExpr::var(x.clone()), ChcExpr::int(10));
    assert_eq!(InvariantModel::expr_to_smtlib(&lt), "(< x 10)");

    // > operator
    let gt = ChcExpr::gt(ChcExpr::var(x), ChcExpr::int(0));
    assert_eq!(InvariantModel::expr_to_smtlib(&gt), "(> x 0)");
}

#[test]
fn expr_to_smtlib_implies_and_iff() {
    let x = ChcVar::new("x", ChcSort::Bool);
    let y = ChcVar::new("y", ChcSort::Bool);

    // => operator
    let implies = ChcExpr::implies(ChcExpr::var(x.clone()), ChcExpr::var(y.clone()));
    assert_eq!(InvariantModel::expr_to_smtlib(&implies), "(=> x y)");

    // = (iff) operator for booleans - construct manually since no helper exists
    use crate::ChcOp;
    use std::sync::Arc;
    let iff = ChcExpr::Op(
        ChcOp::Iff,
        vec![Arc::new(ChcExpr::var(x)), Arc::new(ChcExpr::var(y))],
    );
    assert_eq!(InvariantModel::expr_to_smtlib(&iff), "(= x y)");
}

#[test]
fn expr_to_smtlib_neg_and_div() {
    use crate::ChcOp;
    use std::sync::Arc;
    let x = ChcVar::new("x", ChcSort::Int);

    // Unary negation
    let neg = ChcExpr::neg(ChcExpr::var(x.clone()));
    assert_eq!(InvariantModel::expr_to_smtlib(&neg), "(- x)");

    // Division - construct manually since no helper exists
    let div = ChcExpr::Op(
        ChcOp::Div,
        vec![Arc::new(ChcExpr::var(x)), Arc::new(ChcExpr::int(2))],
    );
    assert_eq!(InvariantModel::expr_to_smtlib(&div), "(div x 2)");
}

#[test]
fn expr_to_smtlib_predicate_app_with_args() {
    let x = ChcVar::new("x", ChcSort::Int);
    let pred_app = ChcExpr::PredicateApp(
        "Inv".to_string(),
        PredicateId::new(0),
        vec![ChcExpr::var(x).into()],
    );
    assert_eq!(InvariantModel::expr_to_smtlib(&pred_app), "(Inv x)");
}

#[test]
fn expr_to_smtlib_predicate_app_no_args() {
    let pred_app = ChcExpr::PredicateApp("Init".to_string(), PredicateId::new(1), vec![]);
    assert_eq!(InvariantModel::expr_to_smtlib(&pred_app), "Init");
}

#[test]
fn expr_to_smtlib_func_app_with_args() {
    let x = ChcVar::new("x", ChcSort::Int);
    let func_app = ChcExpr::FuncApp(
        "f".to_string(),
        ChcSort::Int,
        vec![ChcExpr::var(x).into(), ChcExpr::int(1).into()],
    );
    assert_eq!(InvariantModel::expr_to_smtlib(&func_app), "(f x 1)");
}

#[test]
fn expr_to_smtlib_func_app_no_args() {
    let func_app = ChcExpr::FuncApp("const".to_string(), ChcSort::Int, vec![]);
    assert_eq!(InvariantModel::expr_to_smtlib(&func_app), "const");
}

#[test]
fn expr_to_smtlib_const_array_marker() {
    assert_eq!(
        InvariantModel::expr_to_smtlib(&ChcExpr::ConstArrayMarker(ChcSort::Int)),
        "(as const)"
    );
}

#[test]
fn expr_to_smtlib_is_tester_marker() {
    let is_tester = ChcExpr::IsTesterMarker("Cons".to_string());
    assert_eq!(InvariantModel::expr_to_smtlib(&is_tester), "(_ is Cons)");
}

#[test]
fn expr_to_smtlib_const_array() {
    use std::sync::Arc;
    let const_arr = ChcExpr::ConstArray(ChcSort::Int, Arc::new(ChcExpr::int(0)));
    assert_eq!(
        InvariantModel::expr_to_smtlib(&const_arr),
        "((as const (Array Int Int)) 0)"
    );
}

#[test]
fn expr_to_smtlib_select_and_store() {
    let arr = ChcVar::new(
        "arr",
        ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int)),
    );
    let idx = ChcVar::new("i", ChcSort::Int);

    // select
    let select = ChcExpr::select(ChcExpr::var(arr.clone()), ChcExpr::var(idx.clone()));
    assert_eq!(InvariantModel::expr_to_smtlib(&select), "(select arr i)");

    // store
    let store = ChcExpr::store(ChcExpr::var(arr), ChcExpr::var(idx), ChcExpr::int(42));
    assert_eq!(InvariantModel::expr_to_smtlib(&store), "(store arr i 42)");
}

// =======================================================================
// BV operation serialization tests - #6047
// =======================================================================

#[test]
fn expr_to_smtlib_bv_arithmetic_ops() {
    let x = ChcVar::new("x", ChcSort::BitVec(8));
    let y = ChcVar::new("y", ChcSort::BitVec(8));
    let cases = [
        (ChcOp::BvAdd, "bvadd"),
        (ChcOp::BvSub, "bvsub"),
        (ChcOp::BvMul, "bvmul"),
        (ChcOp::BvUDiv, "bvudiv"),
        (ChcOp::BvURem, "bvurem"),
        (ChcOp::BvSDiv, "bvsdiv"),
        (ChcOp::BvSRem, "bvsrem"),
        (ChcOp::BvSMod, "bvsmod"),
    ];
    for (op, expected_name) in cases {
        let expr = ChcExpr::Op(
            op,
            vec![
                ChcExpr::var(x.clone()).into(),
                ChcExpr::var(y.clone()).into(),
            ],
        );
        let smtlib = InvariantModel::expr_to_smtlib(&expr);
        assert_eq!(
            smtlib,
            format!("({expected_name} x y)"),
            "failed for {op:?}"
        );
    }
}

#[test]
fn expr_to_smtlib_bv_bitwise_ops() {
    let x = ChcVar::new("x", ChcSort::BitVec(8));
    let y = ChcVar::new("y", ChcSort::BitVec(8));
    let cases = [
        (ChcOp::BvAnd, "bvand"),
        (ChcOp::BvOr, "bvor"),
        (ChcOp::BvXor, "bvxor"),
        (ChcOp::BvNand, "bvnand"),
        (ChcOp::BvNor, "bvnor"),
        (ChcOp::BvXnor, "bvxnor"),
    ];
    for (op, expected_name) in cases {
        let expr = ChcExpr::Op(
            op,
            vec![
                ChcExpr::var(x.clone()).into(),
                ChcExpr::var(y.clone()).into(),
            ],
        );
        let smtlib = InvariantModel::expr_to_smtlib(&expr);
        assert_eq!(
            smtlib,
            format!("({expected_name} x y)"),
            "failed for {op:?}"
        );
    }
}

#[test]
fn expr_to_smtlib_bv_unary_ops() {
    let x = ChcVar::new("x", ChcSort::BitVec(8));
    let bvnot = ChcExpr::Op(ChcOp::BvNot, vec![ChcExpr::var(x.clone()).into()]);
    assert_eq!(InvariantModel::expr_to_smtlib(&bvnot), "(bvnot x)");
    let bvneg = ChcExpr::Op(ChcOp::BvNeg, vec![ChcExpr::var(x).into()]);
    assert_eq!(InvariantModel::expr_to_smtlib(&bvneg), "(bvneg x)");
}

#[test]
fn expr_to_smtlib_bv_shift_ops() {
    let x = ChcVar::new("x", ChcSort::BitVec(8));
    let y = ChcVar::new("y", ChcSort::BitVec(8));
    let cases = [
        (ChcOp::BvShl, "bvshl"),
        (ChcOp::BvLShr, "bvlshr"),
        (ChcOp::BvAShr, "bvashr"),
    ];
    for (op, expected_name) in cases {
        let expr = ChcExpr::Op(
            op,
            vec![
                ChcExpr::var(x.clone()).into(),
                ChcExpr::var(y.clone()).into(),
            ],
        );
        let smtlib = InvariantModel::expr_to_smtlib(&expr);
        assert_eq!(
            smtlib,
            format!("({expected_name} x y)"),
            "failed for {op:?}"
        );
    }
}

#[test]
fn expr_to_smtlib_bv_comparison_ops() {
    let x = ChcVar::new("x", ChcSort::BitVec(8));
    let y = ChcVar::new("y", ChcSort::BitVec(8));
    let cases = [
        (ChcOp::BvULt, "bvult"),
        (ChcOp::BvULe, "bvule"),
        (ChcOp::BvUGt, "bvugt"),
        (ChcOp::BvUGe, "bvuge"),
        (ChcOp::BvSLt, "bvslt"),
        (ChcOp::BvSLe, "bvsle"),
        (ChcOp::BvSGt, "bvsgt"),
        (ChcOp::BvSGe, "bvsge"),
        (ChcOp::BvComp, "bvcomp"),
    ];
    for (op, expected_name) in cases {
        let expr = ChcExpr::Op(
            op,
            vec![
                ChcExpr::var(x.clone()).into(),
                ChcExpr::var(y.clone()).into(),
            ],
        );
        let smtlib = InvariantModel::expr_to_smtlib(&expr);
        assert_eq!(
            smtlib,
            format!("({expected_name} x y)"),
            "failed for {op:?}"
        );
    }
}

#[test]
fn expr_to_smtlib_bv_concat() {
    let x = ChcVar::new("x", ChcSort::BitVec(8));
    let y = ChcVar::new("y", ChcSort::BitVec(8));
    let concat = ChcExpr::Op(
        ChcOp::BvConcat,
        vec![ChcExpr::var(x).into(), ChcExpr::var(y).into()],
    );
    assert_eq!(InvariantModel::expr_to_smtlib(&concat), "(concat x y)");
}

#[test]
fn expr_to_smtlib_bv_indexed_ops() {
    let x = ChcVar::new("x", ChcSort::BitVec(16));
    // extract
    let extract = ChcExpr::Op(ChcOp::BvExtract(7, 0), vec![ChcExpr::var(x.clone()).into()]);
    assert_eq!(
        InvariantModel::expr_to_smtlib(&extract),
        "((_ extract 7 0) x)"
    );
    // zero_extend
    let zext = ChcExpr::Op(
        ChcOp::BvZeroExtend(16),
        vec![ChcExpr::var(x.clone()).into()],
    );
    assert_eq!(
        InvariantModel::expr_to_smtlib(&zext),
        "((_ zero_extend 16) x)"
    );
    // sign_extend
    let sext = ChcExpr::Op(
        ChcOp::BvSignExtend(16),
        vec![ChcExpr::var(x.clone()).into()],
    );
    assert_eq!(
        InvariantModel::expr_to_smtlib(&sext),
        "((_ sign_extend 16) x)"
    );
    // rotate_left
    let rotl = ChcExpr::Op(ChcOp::BvRotateLeft(3), vec![ChcExpr::var(x.clone()).into()]);
    assert_eq!(
        InvariantModel::expr_to_smtlib(&rotl),
        "((_ rotate_left 3) x)"
    );
    // rotate_right
    let rotr = ChcExpr::Op(
        ChcOp::BvRotateRight(3),
        vec![ChcExpr::var(x.clone()).into()],
    );
    assert_eq!(
        InvariantModel::expr_to_smtlib(&rotr),
        "((_ rotate_right 3) x)"
    );
    // repeat
    let rep = ChcExpr::Op(ChcOp::BvRepeat(4), vec![ChcExpr::var(x).into()]);
    assert_eq!(InvariantModel::expr_to_smtlib(&rep), "((_ repeat 4) x)");
    // int2bv
    let i = ChcVar::new("i", ChcSort::Int);
    let int2bv = ChcExpr::Op(ChcOp::Int2Bv(32), vec![ChcExpr::var(i).into()]);
    assert_eq!(InvariantModel::expr_to_smtlib(&int2bv), "((_ int2bv 32) i)");
}

#[test]
fn expr_to_smtlib_bv2nat() {
    let x = ChcVar::new("x", ChcSort::BitVec(8));
    let bv2nat = ChcExpr::Op(ChcOp::Bv2Nat, vec![ChcExpr::var(x).into()]);
    assert_eq!(InvariantModel::expr_to_smtlib(&bv2nat), "(bv2nat x)");
}

#[test]
fn expr_to_smtlib_bitvec_literal() {
    assert_eq!(
        InvariantModel::expr_to_smtlib(&ChcExpr::BitVec(42, 8)),
        "(_ bv42 8)"
    );
}

// =======================================================================
// Qualified datatype constructor tests - #3362
// =======================================================================

#[test]
fn expr_to_smtlib_func_app_nullary_constructor_qualified() {
    // Nullary constructors with Uninterpreted sort get (as Name Sort) form
    let none = ChcExpr::FuncApp(
        "None".to_string(),
        ChcSort::Uninterpreted("Option_u32".to_string()),
        vec![],
    );
    assert_eq!(
        InvariantModel::expr_to_smtlib(&none),
        "(as None Option_u32)"
    );
}

#[test]
fn expr_to_smtlib_func_app_constructor_with_args_qualified() {
    // Constructors with args get ((as Name Sort) arg1 arg2) form
    let x = ChcVar::new("x", ChcSort::Int);
    let some = ChcExpr::FuncApp(
        "Some".to_string(),
        ChcSort::Uninterpreted("Option_u32".to_string()),
        vec![ChcExpr::var(x).into()],
    );
    assert_eq!(
        InvariantModel::expr_to_smtlib(&some),
        "((as Some Option_u32) x)"
    );
}

#[test]
fn expr_to_smtlib_func_app_non_datatype_not_qualified() {
    // FuncApps with non-Uninterpreted sort remain unqualified
    let x = ChcVar::new("x", ChcSort::Int);
    let f = ChcExpr::FuncApp("f".to_string(), ChcSort::Bool, vec![ChcExpr::var(x).into()]);
    assert_eq!(InvariantModel::expr_to_smtlib(&f), "(f x)");
}

#[test]
fn expr_to_smtlib_ambiguous_constructors_disambiguated() {
    // Two constructors named "None" for different datatypes get different qualifications
    let none_u32 = ChcExpr::FuncApp(
        "None".to_string(),
        ChcSort::Uninterpreted("Option_u32".to_string()),
        vec![],
    );
    let none_u64 = ChcExpr::FuncApp(
        "None".to_string(),
        ChcSort::Uninterpreted("Option_u64".to_string()),
        vec![],
    );
    assert_eq!(
        InvariantModel::expr_to_smtlib(&none_u32),
        "(as None Option_u32)"
    );
    assert_eq!(
        InvariantModel::expr_to_smtlib(&none_u64),
        "(as None Option_u64)"
    );
}

// =======================================================================
// Additional edge case tests - #1651 audit round 2
// =======================================================================

#[test]
fn expr_to_smtlib_var_with_special_chars() {
    // Variable names with characters requiring SMT-LIB quoting (spaces are not valid)
    let v = ChcVar::new("my var", ChcSort::Int);
    // quote_symbol should pipe-quote this since space is not a valid symbol char
    assert_eq!(InvariantModel::expr_to_smtlib(&ChcExpr::var(v)), "|my var|");
}

#[test]
fn expr_to_smtlib_var_with_reserved_word() {
    // Variable names that are reserved words need quoting
    let v = ChcVar::new("true", ChcSort::Bool);
    assert_eq!(InvariantModel::expr_to_smtlib(&ChcExpr::var(v)), "|true|");
}

#[test]
fn expr_to_smtlib_real_with_zero_numerator() {
    // Edge case: 0/N should render as (/ 0 N)
    let real = ChcExpr::Real(0, 4);
    assert_eq!(InvariantModel::expr_to_smtlib(&real), "(/ 0 4)");
}

#[test]
fn invariant_model_set_overwrites_existing() {
    let mut model = InvariantModel::new();
    let pred_id = PredicateId::new(0);

    // Set first interpretation
    let interp1 = PredicateInterpretation::new(vec![], ChcExpr::Bool(true));
    model.set(pred_id, interp1);
    assert!(matches!(
        model.get(&pred_id).unwrap().formula,
        ChcExpr::Bool(true)
    ));

    // Overwrite with second interpretation
    let interp2 = PredicateInterpretation::new(vec![], ChcExpr::Bool(false));
    model.set(pred_id, interp2);
    assert!(matches!(
        model.get(&pred_id).unwrap().formula,
        ChcExpr::Bool(false)
    ));

    // Should still only have 1 entry
    assert_eq!(model.len(), 1);
}

#[test]
fn test_expr_to_smtlib_i64_min_no_panic() {
    // i128::MIN.abs() panics — expr_to_smtlib must use unsigned_abs
    let expr = ChcExpr::Int(i128::MIN);
    let s = InvariantModel::expr_to_smtlib(&expr);
    assert!(s.contains(&i128::MIN.unsigned_abs().to_string()));

    let real = ChcExpr::Real(i64::MIN, 3);
    let s2 = InvariantModel::expr_to_smtlib(&real);
    assert!(s2.contains(&i64::MIN.unsigned_abs().to_string()));
}

// =======================================================================
// Tests for free variable sanitization - #5246
// =======================================================================

#[test]
fn sanitize_free_variables_removes_undeclared_conjuncts() {
    let params = vec![
        ChcVar::new("__p0_a0", ChcSort::Int),
        ChcVar::new("__p0_a1", ChcSort::Int),
    ];
    // Formula: (and (>= __p0_a0 0) (= obj_valid true) (<= __p0_a1 10))
    // obj_valid is NOT a parameter — its conjunct should be removed.
    let free_var = ChcVar::new("obj_valid", ChcSort::Bool);
    let formula = ChcExpr::and_all(vec![
        ChcExpr::ge(ChcExpr::var(params[0].clone()), ChcExpr::int(0)),
        ChcExpr::eq(ChcExpr::var(free_var), ChcExpr::Bool(true)),
        ChcExpr::le(ChcExpr::var(params[1].clone()), ChcExpr::int(10)),
    ]);

    let pred_id = PredicateId::new(0);
    let mut model = InvariantModel::new();
    model.set(pred_id, PredicateInterpretation::new(params, formula));

    model.sanitize_free_variables();

    let interp = model.get(&pred_id).unwrap();
    // The formula should only contain __p0_a0 and __p0_a1 conjuncts
    let vars = interp.formula.vars();
    assert!(
        vars.iter()
            .all(|v| v.name == "__p0_a0" || v.name == "__p0_a1"),
        "Formula should only contain declared parameters, got vars: {:?}",
        vars.iter().map(|v| &v.name).collect::<Vec<_>>()
    );
    // obj_valid should be gone
    assert!(
        !vars.iter().any(|v| v.name == "obj_valid"),
        "obj_valid should be removed from formula"
    );
}

#[test]
fn sanitize_free_variables_preserves_clean_formulas() {
    let params = vec![
        ChcVar::new("__p0_a0", ChcSort::Int),
        ChcVar::new("__p0_a1", ChcSort::Int),
    ];
    let formula = ChcExpr::and(
        ChcExpr::ge(ChcExpr::var(params[0].clone()), ChcExpr::int(0)),
        ChcExpr::le(ChcExpr::var(params[1].clone()), ChcExpr::int(10)),
    );

    let pred_id = PredicateId::new(0);
    let mut model = InvariantModel::new();
    model.set(
        pred_id,
        PredicateInterpretation::new(params, formula.clone()),
    );

    model.sanitize_free_variables();

    let interp = model.get(&pred_id).unwrap();
    assert_eq!(interp.formula, formula, "Clean formula should be unchanged");
}

#[test]
fn sanitize_formula_for_output_strips_free_vars() {
    let params = vec![
        ChcVar::new("__p0_a0", ChcSort::Int),
        ChcVar::new("__p0_a1", ChcSort::Int),
    ];
    let free_var = ChcVar::new("leaked_var", ChcSort::Int);
    let formula = ChcExpr::and_all(vec![
        ChcExpr::ge(ChcExpr::var(params[0].clone()), ChcExpr::int(0)),
        ChcExpr::eq(ChcExpr::var(free_var), ChcExpr::int(42)),
        ChcExpr::le(ChcExpr::var(params[1].clone()), ChcExpr::int(10)),
    ]);

    let sanitized = InvariantModel::sanitize_formula_for_output(&params, &formula);
    let smtlib = InvariantModel::expr_to_smtlib(&sanitized);

    assert!(
        !smtlib.contains("leaked_var"),
        "Output should not contain free variable 'leaked_var': {smtlib}",
    );
    assert!(
        smtlib.contains("__p0_a0"),
        "Output should contain declared param __p0_a0: {smtlib}",
    );
    assert!(
        smtlib.contains("__p0_a1"),
        "Output should contain declared param __p0_a1: {smtlib}",
    );
}

#[test]
fn to_spacer_format_no_free_variables_5246() {
    let pred_id = PredicateId::new(0);
    let params = vec![
        ChcVar::new("__p0_a0", ChcSort::Int),
        ChcVar::new("__p0_a1", ChcSort::Int),
    ];
    let leaked = ChcVar::new("obj_valid", ChcSort::Bool);
    let formula = ChcExpr::and_all(vec![
        ChcExpr::ge(ChcExpr::var(params[0].clone()), ChcExpr::int(0)),
        ChcExpr::eq(ChcExpr::var(leaked), ChcExpr::Bool(true)),
    ]);

    let mut model = InvariantModel::new();
    model.set(pred_id, PredicateInterpretation::new(params, formula));

    let mut problem = ChcProblem::new();
    problem.declare_predicate("Inv", vec![ChcSort::Int, ChcSort::Int]);

    let spacer_output = model.to_spacer_format(&problem);
    assert!(
        !spacer_output.contains("obj_valid"),
        "Spacer output must not contain undeclared 'obj_valid': {spacer_output}",
    );

    let smtlib_output = model.to_smtlib(&problem);
    assert!(
        !smtlib_output.contains("obj_valid"),
        "SMT-LIB output must not contain undeclared 'obj_valid': {smtlib_output}",
    );
}
