// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use ay_core::TermData;

fn fixture(cyclic: bool) -> (Executor, TermId, TermId, TermId) {
    let mut exec = Executor::new();
    let commands = ay_frontend::parse(
        r#"
        (set-logic ALL)
        (declare-datatypes ((DepthTree 0) (DepthForest 0))
            (((depth_leaf (depth_value Int)) (depth_node (depth_children DepthForest)))
             ((depth_nil) (depth_cons (depth_head DepthTree) (depth_tail DepthForest)))))
        (declare-const depth_tree DepthTree)
    "#,
    )
    .unwrap();
    exec.execute_all(&commands).unwrap();
    let nil = exec
        .ctx
        .exact_datatype_member_info("depth_nil")
        .unwrap()
        .term
        .unwrap();
    assert!(matches!(exec.ctx.terms.get(nil), TermData::Var(..)));
    let one = exec.ctx.terms.mk_int(BigInt::from(1));
    let tree_sort = exec.ctx.sort_definition("DepthTree").unwrap().clone();
    let forest_sort = exec.ctx.sort_definition("DepthForest").unwrap().clone();
    let leaf = if cyclic {
        exec.ctx.symbol_info("depth_tree").unwrap().term.unwrap()
    } else {
        exec.ctx
            .terms
            .mk_app(Symbol::named("depth_leaf"), vec![one], tree_sort.clone())
    };
    let cons = exec
        .ctx
        .terms
        .mk_app(Symbol::named("depth_cons"), vec![leaf, nil], forest_sort);
    let node = exec
        .ctx
        .terms
        .mk_app(Symbol::named("depth_node"), vec![cons], tree_sort);
    if cyclic {
        let equality = exec.ctx.terms.mk_eq(leaf, node);
        exec.ctx.assertions.push(equality);
    }
    (exec, nil, cons, node)
}

#[test]
fn native_batch_structural_depth_nullary_identity_completes_mutual_constructor_tree() {
    let (exec, nil, cons, node) = fixture(false);
    let model = empty_model();
    assert_eq!(
        exec.dt_structural_depth(&model, nil, 16),
        Some(BigInt::from(0))
    );
    assert_eq!(
        exec.dt_structural_depth(&model, cons, 16),
        Some(BigInt::from(1))
    );
    assert_eq!(
        exec.dt_structural_depth(&model, node, 16),
        Some(BigInt::from(2))
    );
}

#[test]
fn native_batch_structural_depth_uses_the_same_interpretation_in_datatype_field_validation() {
    let (mut exec, nil, cons, _) = fixture(false);
    let nil_depth = exec.ctx.terms.mk_app(
        Symbol::named("__ay_dt_depth_DepthForest"),
        vec![nil],
        Sort::Int,
    );
    let cons_depth = exec.ctx.terms.mk_app(
        Symbol::named("__ay_dt_depth_DepthForest"),
        vec![cons],
        Sort::Int,
    );
    let one = exec.ctx.terms.mk_int(BigInt::from(1));
    let successor = exec.ctx.terms.mk_add(vec![nil_depth, one]);
    let monotone = exec.ctx.terms.mk_le(successor, cons_depth);
    let mut model = empty_model();
    model.lia_model = Some(LiaModel {
        values: HashMap::from_iter([(nil_depth, BigInt::from(7)), (cons_depth, BigInt::from(0))]),
    });
    assert_eq!(
        exec.evaluate_term(&model, nil_depth),
        EvalValue::Rational(BigRational::from(BigInt::from(0)))
    );
    assert_eq!(
        exec.evaluate_term(&model, cons_depth),
        EvalValue::Rational(BigRational::from(BigInt::from(1)))
    );
    assert_eq!(
        exec.dt_mat_eval(&model, monotone, 64),
        EvalValue::Bool(true)
    );
}

#[test]
fn native_batch_structural_depth_foreign_same_spelling_and_cycles_are_unresolved() {
    let (mut exec, nil, _, _) = fixture(false);
    let name = match exec.ctx.terms.get(nil) {
        TermData::Var(name, _) => name.clone(),
        _ => unreachable!(),
    };
    let sort = exec.ctx.terms.sort(nil).clone();
    let foreign = exec.ctx.terms.mk_fresh_named_var(&name, sort);
    assert_ne!(foreign, nil);
    assert_eq!(exec.dt_structural_depth(&empty_model(), foreign, 16), None);
    assert_eq!(exec.dt_structural_depth(&empty_model(), nil, 0), None);
    let (exec, _, cons, node) = fixture(true);
    assert_eq!(exec.dt_structural_depth(&empty_model(), cons, 8), None);
    assert_eq!(exec.dt_structural_depth(&empty_model(), node, 8), None);
}
