// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::sync::Arc;

use super::*;
use crate::pdr::counterexample::{Counterexample, DerivationWitness, DerivationWitnessEntry};
use crate::smt::SmtValue;
use crate::transform::BvToBoolBitBlaster;
use crate::ChcOp;
use ay_core::kani_compat::DetHashMap as FxHashMap;

/// Create a minimal CHC problem with a single BV predicate of the given width.
fn make_simple_bv_problem(width: u32) -> ChcProblem {
    let mut p = ChcProblem::new();
    let inv = p.declare_predicate("inv", vec![ChcSort::BitVec(width)]);
    let x = ChcVar::new("x", ChcSort::BitVec(width));
    p.add_clause(HornClause::new(
        ClauseBody::new(vec![], None),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x)]),
    ));
    p
}

fn expr_contains_op(expr: &ChcExpr, target: &ChcOp) -> bool {
    match expr {
        ChcExpr::Op(op, args) => {
            op == target
                || args
                    .iter()
                    .any(|arg| expr_contains_op(arg.as_ref(), target))
        }
        ChcExpr::PredicateApp(_, _, args) | ChcExpr::FuncApp(_, _, args) => args
            .iter()
            .any(|arg| expr_contains_op(arg.as_ref(), target)),
        ChcExpr::ConstArray(_, value) => expr_contains_op(value.as_ref(), target),
        _ => false,
    }
}

#[test]
fn no_bv_passthrough() {
    let p = ChcProblem::new();
    let r = Box::new(BvToIntAbstractor::new()).transform(p);
    assert_eq!(r.problem.predicates().len(), 0);
}

#[test]
fn bv_sort_replacement() {
    let mut p = ChcProblem::new();
    p.declare_predicate("inv", vec![ChcSort::BitVec(32), ChcSort::Int]);
    let r = Box::new(BvToIntAbstractor::new()).transform(p);
    assert_eq!(
        r.problem.predicates()[0].arg_sorts,
        vec![ChcSort::Int, ChcSort::Int]
    );
}

#[test]
fn bvadd_exact_encoding() {
    let mut map = BvIntMap::new();
    let add = ChcExpr::Op(
        ChcOp::BvAdd,
        vec![
            Arc::new(ChcExpr::Var(ChcVar::new("x", ChcSort::BitVec(8)))),
            Arc::new(ChcExpr::Var(ChcVar::new("y", ChcSort::BitVec(8)))),
        ],
    );
    let result = abstract_expr(&add, &mut map, false);
    assert!(matches!(result, ChcExpr::Op(ChcOp::Ite, _)));
}

#[test]
fn bv_constant_to_int() {
    let mut map = BvIntMap::new();
    assert!(matches!(
        abstract_expr(&ChcExpr::BitVec(42, 32), &mut map, false),
        ChcExpr::Int(42)
    ));
}

#[test]
fn unsigned_compare_exact() {
    let mut map = BvIntMap::new();
    let ult = ChcExpr::Op(
        ChcOp::BvULt,
        vec![
            Arc::new(ChcExpr::Var(ChcVar::new("x", ChcSort::BitVec(32)))),
            Arc::new(ChcExpr::Var(ChcVar::new("y", ChcSort::BitVec(32)))),
        ],
    );
    assert!(matches!(
        abstract_expr(&ult, &mut map, false),
        ChcExpr::Op(ChcOp::Lt, _)
    ));
}

#[test]
fn bvult_bv64_normalizes_operands_7006() {
    let mut map = BvIntMap::new();
    let ult = ChcExpr::Op(
        ChcOp::BvULt,
        vec![
            Arc::new(ChcExpr::Var(ChcVar::new("x", ChcSort::BitVec(64)))),
            Arc::new(ChcExpr::Var(ChcVar::new("y", ChcSort::BitVec(64)))),
        ],
    );
    let result = abstract_expr(&ult, &mut map, false);
    match result {
        ChcExpr::Op(ChcOp::Lt, ref args) if args.len() == 2 => {
            assert!(matches!(args[0].as_ref(), ChcExpr::Op(ChcOp::Mod, _)));
            assert!(matches!(args[1].as_ref(), ChcExpr::Op(ChcOp::Mod, _)));
        }
        other => panic!("BV64 ult should normalize both operands, got: {other}"),
    }
}

#[test]
fn bvcomp_bv64_normalizes_operands_7006() {
    let mut map = BvIntMap::new();
    let comp = ChcExpr::Op(
        ChcOp::BvComp,
        vec![
            Arc::new(ChcExpr::Var(ChcVar::new("x", ChcSort::BitVec(64)))),
            Arc::new(ChcExpr::Var(ChcVar::new("y", ChcSort::BitVec(64)))),
        ],
    );
    let result = abstract_expr(&comp, &mut map, false);
    match result {
        ChcExpr::Op(ChcOp::Ite, ref args) if args.len() == 3 => {
            assert!(matches!(args[0].as_ref(), ChcExpr::Op(ChcOp::Eq, _)));
            assert!(
                expr_contains_op(&result, &ChcOp::Mod),
                "bvcomp should normalize wide operands before equality, got: {result}"
            );
        }
        other => panic!("BV64 comp should normalize both operands, got: {other}"),
    }
}

/// BV32 variable-variable AND now uses bit-decomposition (#8289).
/// The result is an Add tree (sum of per-bit products), not a UF.
#[test]
fn bvand_variable_variable_bv32_uses_bit_decomposition_8289() {
    let mut map = BvIntMap::new();
    let bvand = ChcExpr::Op(
        ChcOp::BvAnd,
        vec![
            Arc::new(ChcExpr::Var(ChcVar::new("x", ChcSort::BitVec(32)))),
            Arc::new(ChcExpr::Var(ChcVar::new("y", ChcSort::BitVec(32)))),
        ],
    );
    let result = abstract_expr(&bvand, &mut map, false);
    // Bit-decomposition produces a nested Add tree, not a FuncApp (UF)
    assert!(
        !matches!(result, ChcExpr::FuncApp(_, _, _)),
        "BV32 variable-variable AND should use bit-decomposition, not UF, got: {result}"
    );
    assert!(
        matches!(result, ChcExpr::Op(ChcOp::Add, _)),
        "BV32 variable-variable AND should produce an Add tree, got: {result}"
    );
}

/// BV64 variable-variable AND still uses UF fallback (too wide for decomposition).
#[test]
fn bvand_variable_variable_bv64_uses_uf_fallback_8289() {
    let mut map = BvIntMap::new();
    let bvand = ChcExpr::Op(
        ChcOp::BvAnd,
        vec![
            Arc::new(ChcExpr::Var(ChcVar::new("x", ChcSort::BitVec(64)))),
            Arc::new(ChcExpr::Var(ChcVar::new("y", ChcSort::BitVec(64)))),
        ],
    );
    match abstract_expr(&bvand, &mut map, false) {
        ChcExpr::FuncApp(ref n, ChcSort::Int, ref a) => {
            assert!(n.starts_with("__bv2int_"));
            assert_eq!(a.len(), 2);
        }
        other => panic!("BV64 variable AND should fall back to UF, got: {other}"),
    }
}

#[test]
fn range_constraints_added() {
    let mut p = ChcProblem::new();
    let inv = p.declare_predicate("inv", vec![ChcSort::BitVec(8)]);
    let x = ChcVar::new("x", ChcSort::BitVec(8));
    p.add_clause(HornClause::new(
        ClauseBody::new(
            vec![],
            Some(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::BitVec(0, 8))),
        ),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone())]),
    ));
    p.add_clause(HornClause::new(
        ClauseBody::new(vec![(inv, vec![ChcExpr::var(x)])], None),
        ClauseHead::False,
    ));
    let r = Box::new(BvToIntAbstractor::new()).transform(p);
    assert!(r.problem.predicates()[0]
        .arg_sorts
        .iter()
        .all(|s| *s == ChcSort::Int));
}

#[test]
fn bv_array_subsort_abstraction() {
    let mut p = ChcProblem::new();
    p.declare_predicate(
        "inv",
        vec![
            ChcSort::Array(Box::new(ChcSort::BitVec(32)), Box::new(ChcSort::Bool)),
            ChcSort::BitVec(32),
        ],
    );
    let r = Box::new(BvToIntAbstractor::new()).transform(p);
    let sorts = &r.problem.predicates()[0].arg_sorts;
    assert_eq!(
        sorts[0],
        ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Bool)),
        "Array sub-sort BV(32) should be abstracted to Int"
    );
    assert_eq!(sorts[1], ChcSort::Int);
}

#[test]
fn bv_array_subsort_abstraction_after_bv_to_bool_handoff() {
    let mut p = ChcProblem::new();
    p.declare_predicate(
        "inv",
        vec![
            ChcSort::Array(Box::new(ChcSort::BitVec(32)), Box::new(ChcSort::Bool)),
            ChcSort::BitVec(8),
        ],
    );

    let bit_blasted = Box::new(BvToBoolBitBlaster::new()).transform(p);
    let blasted_sorts = &bit_blasted.problem.predicates()[0].arg_sorts;
    assert_eq!(
        blasted_sorts[0],
        ChcSort::Array(Box::new(ChcSort::BitVec(32)), Box::new(ChcSort::Bool)),
        "BvToBool should leave Array(BV, _) arguments for the Int fallback"
    );
    assert!(
        blasted_sorts[1..].iter().all(|sort| *sort == ChcSort::Bool),
        "direct BV argument should expand to Bool bits before the Int fallback"
    );

    let abstracted = Box::new(BvToIntAbstractor::new()).transform(bit_blasted.problem);
    let abstracted_sorts = &abstracted.problem.predicates()[0].arg_sorts;
    assert_eq!(
        abstracted_sorts[0],
        ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Bool)),
        "BvToInt must still abstract recursive BV sub-sorts after BvToBool"
    );
    assert!(
        abstracted_sorts[1..]
            .iter()
            .all(|sort| *sort == ChcSort::Bool),
        "BvToInt should preserve the Bool bits produced by BvToBool"
    );
}

#[test]
fn const_array_key_sort_abstracted() {
    let mut map = BvIntMap::new();
    let const_arr = ChcExpr::ConstArray(ChcSort::BitVec(32), Arc::new(ChcExpr::Bool(false)));
    let result = abstract_expr(&const_arr, &mut map, false);
    match &result {
        ChcExpr::ConstArray(ks, _) => {
            assert_eq!(
                *ks,
                ChcSort::Int,
                "ConstArray key sort BV(32) should be abstracted to Int"
            );
        }
        other => panic!("Expected ConstArray, got: {other}"),
    }
}

#[test]
fn var_array_bv_sort_abstracted() {
    let mut map = BvIntMap::new();
    let var = ChcExpr::Var(ChcVar::new(
        "arr",
        ChcSort::Array(Box::new(ChcSort::BitVec(8)), Box::new(ChcSort::Int)),
    ));
    let result = abstract_expr(&var, &mut map, false);
    match &result {
        ChcExpr::Var(v) => {
            assert_eq!(
                v.sort,
                ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int)),
                "Var with Array(BV(8), Int) should become Array(Int, Int)"
            );
        }
        other => panic!("Expected Var, got: {other}"),
    }
}

#[test]
fn bvmul_exact_encoding() {
    let mut map = BvIntMap::new();
    let x = Arc::new(ChcExpr::Var(ChcVar::new("x", ChcSort::BitVec(8))));
    let y = Arc::new(ChcExpr::Var(ChcVar::new("y", ChcSort::BitVec(8))));
    let result = abstract_expr(&ChcExpr::Op(ChcOp::BvMul, vec![x, y]), &mut map, false);
    assert!(
        matches!(result, ChcExpr::Op(ChcOp::Mod, _)),
        "got: {result}"
    );
}

#[test]
fn back_translation_restores_bv_sorts() {
    let mut map = BvIntMap::new();
    let pid = PredicateId::new(0);
    map.pred_arg_widths
        .insert(pid, vec![Some(32), None, Some(8)]);
    let mut inv = InvariantModel::new();
    inv.set(
        pid,
        PredicateInterpretation::new(
            vec![
                ChcVar::new("x", ChcSort::Int),
                ChcVar::new("y", ChcSort::Int),
                ChcVar::new("z", ChcSort::Int),
            ],
            ChcExpr::Bool(true),
        ),
    );
    let r = concretize_inv(&inv, &map);
    let interp = r.get(&pid).unwrap();
    assert_eq!(interp.vars[0].sort, ChcSort::BitVec(32));
    assert_eq!(interp.vars[1].sort, ChcSort::Int);
    assert_eq!(interp.vars[2].sort, ChcSort::BitVec(8));
}

#[test]
fn back_translation_rewrites_sorts_by_full_var_identity_not_name() {
    fn has_select_on_array_named_dup(expr: &ChcExpr) -> bool {
        match expr {
            ChcExpr::Op(ChcOp::Select, args)
                if args.len() == 2
                    && matches!(
                        args[0].as_ref(),
                        ChcExpr::Var(v)
                            if v.name == "dup"
                                && v.sort
                                    == ChcSort::Array(
                                        Box::new(ChcSort::Int),
                                        Box::new(ChcSort::Int)
                                    )
                    ) =>
            {
                true
            }
            ChcExpr::Op(_, args)
            | ChcExpr::PredicateApp(_, _, args)
            | ChcExpr::FuncApp(_, _, args) => {
                args.iter().any(|arg| has_select_on_array_named_dup(arg))
            }
            ChcExpr::ConstArray(_, value) => has_select_on_array_named_dup(value),
            _ => false,
        }
    }

    let mut map = BvIntMap::new();
    let pid = PredicateId::new(0);
    map.pred_arg_widths.insert(pid, vec![Some(32)]);
    map.pred_arg_sorts.insert(pid, vec![ChcSort::BitVec(32)]);

    let scalar_dup = ChcVar::new("dup", ChcSort::Int);
    let array_dup = ChcVar::new(
        "dup",
        ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int)),
    );
    let formula = ChcExpr::and(
        ChcExpr::eq(ChcExpr::var(scalar_dup.clone()), ChcExpr::int(4)),
        ChcExpr::eq(
            ChcExpr::select(ChcExpr::var(array_dup), ChcExpr::int(1)),
            ChcExpr::int(4),
        ),
    );

    let mut inv = InvariantModel::new();
    inv.set(
        pid,
        PredicateInterpretation::new(vec![scalar_dup.clone()], formula),
    );

    let translated = concretize_inv(&inv, &map);
    let interp = translated.get(&pid).expect("predicate should be present");
    assert_eq!(
        interp.vars[0].sort,
        ChcSort::BitVec(32),
        "predicate parameter should still concretize back to BV32"
    );
    assert!(
        has_select_on_array_named_dup(&interp.formula),
        "array-valued local with the same name as a BV parameter must stay array-sorted: {}",
        interp.formula
    );
}

#[test]
fn invalidity_back_translation_concretizes_bitvec_instances_6293() {
    let mut problem = ChcProblem::new();
    let pred = problem.declare_predicate("inv", vec![ChcSort::BitVec(8)]);
    let transformed = Box::new(BvToIntAbstractor::new()).transform(problem);

    let canonical_name = format!("__p{}_a0", pred.index());
    let mut instances = FxHashMap::default();
    instances.insert(canonical_name.clone(), SmtValue::Int(257));

    let cex = Counterexample::with_witness(
        Vec::new(),
        DerivationWitness {
            query_clause: None,
            root: 0,
            entries: vec![DerivationWitnessEntry {
                predicate: pred,
                level: 0,
                state: ChcExpr::Bool(true),
                incoming_clause: None,
                premises: Vec::new(),
                instances,
            }],
        },
    );

    let translated = transformed.back_translator.translate_invalidity(cex);
    let witness = translated
        .witness
        .expect("translated counterexample should keep witness");
    assert_eq!(
        witness.entries[0].instances.get(&canonical_name),
        Some(&SmtValue::BitVec(1, 8))
    );
}

#[test]
fn invalidity_back_translation_concretizes_array_bv_instances_6293() {
    let mut problem = ChcProblem::new();
    let pred = problem.declare_predicate(
        "inv",
        vec![ChcSort::Array(
            Box::new(ChcSort::BitVec(8)),
            Box::new(ChcSort::BitVec(16)),
        )],
    );
    let transformed = Box::new(BvToIntAbstractor::new()).transform(problem);

    let canonical_name = format!("__p{}_a0", pred.index());
    let mut instances = FxHashMap::default();
    instances.insert(
        canonical_name.clone(),
        SmtValue::ArrayMap {
            default: Box::new(SmtValue::Int(258)),
            entries: vec![(SmtValue::Int(-1), SmtValue::Int(513))],
        },
    );

    let cex = Counterexample::with_witness(
        Vec::new(),
        DerivationWitness {
            query_clause: None,
            root: 0,
            entries: vec![DerivationWitnessEntry {
                predicate: pred,
                level: 0,
                state: ChcExpr::Bool(true),
                incoming_clause: None,
                premises: Vec::new(),
                instances,
            }],
        },
    );

    let translated = transformed.back_translator.translate_invalidity(cex);
    let witness = translated
        .witness
        .expect("translated counterexample should keep witness");
    assert_eq!(
        witness.entries[0].instances.get(&canonical_name),
        Some(&SmtValue::ArrayMap {
            default: Box::new(SmtValue::BitVec(258, 16)),
            entries: vec![(SmtValue::BitVec(255, 8), SmtValue::BitVec(513, 16))],
        })
    );
}

/// Back-translation must transform Int constants in formulas to BV constants.
/// Specifically, `select(v, 0)` where v has sort `Array(BV32, Bool)` must become
/// `select(v, (_ bv0 32))` after concretization. Without this, the formula
/// fails sort-checking during verification against the original BV problem.
#[test]
fn back_translation_transforms_formula_int_to_bv_7006() {
    let mut map = BvIntMap::new();
    let pid = PredicateId::new(0);
    // Original predicate has: BV32 counter, Array(BV32, Bool)
    let orig_sorts = vec![
        ChcSort::BitVec(32),
        ChcSort::Array(Box::new(ChcSort::BitVec(32)), Box::new(ChcSort::Bool)),
    ];
    map.pred_arg_widths.insert(pid, vec![Some(32), None]);
    map.pred_arg_sorts.insert(pid, orig_sorts);
    // Build an Int-domain invariant: `select(v1, 0) = true`
    // This is what the solver produces: array has Int key sort, Int index constant.
    let v0 = ChcVar::new("v0", ChcSort::Int);
    let v1 = ChcVar::new(
        "v1",
        ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Bool)),
    );
    let select_int = ChcExpr::select(ChcExpr::var(v1.clone()), ChcExpr::int(0));
    let formula = ChcExpr::eq(select_int, ChcExpr::Bool(true));
    let mut inv = InvariantModel::new();
    inv.set(pid, PredicateInterpretation::new(vec![v0, v1], formula));
    let r = concretize_inv(&inv, &map);
    let interp = r.get(&pid).unwrap();
    // v0 should become BV32-sorted
    assert_eq!(interp.vars[0].sort, ChcSort::BitVec(32));
    // v1 should be restored to Array(BV32, Bool) from original sorts
    assert_eq!(
        interp.vars[1].sort,
        ChcSort::Array(Box::new(ChcSort::BitVec(32)), Box::new(ChcSort::Bool)),
        "Array variable sort should be restored from pred_arg_sorts"
    );
    // The formula should have Int 0 converted to BV 0 in the select index
    let formula_str = format!("{}", interp.formula);
    assert!(
        !formula_str.contains("(select v1 0)"),
        "Int constant 0 should be converted to BV in select index, got: {formula_str}"
    );
}

#[test]
fn back_translation_coerces_const_array_nested_store_to_bv64_array_8901() {
    let mut map = BvIntMap::new();
    let pid = PredicateId::new(0);
    let bv64 = ChcSort::BitVec(64);
    let original_array_sort = ChcSort::Array(Box::new(bv64.clone()), Box::new(bv64.clone()));
    let abstract_array_sort = ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int));

    map.pred_arg_widths.insert(pid, vec![None]);
    map.pred_arg_sorts
        .insert(pid, vec![original_array_sort.clone()]);

    let arr = ChcVar::new("arr", abstract_array_sort);
    let abstract_store = ChcExpr::store(
        ChcExpr::store(
            ChcExpr::ConstArray(ChcSort::Int, Arc::new(ChcExpr::int(0))),
            ChcExpr::int(1),
            ChcExpr::int(2),
        ),
        ChcExpr::int(3),
        ChcExpr::int(4),
    );
    let expected_store = ChcExpr::store(
        ChcExpr::store(
            ChcExpr::ConstArray(ChcSort::BitVec(64), Arc::new(ChcExpr::BitVec(0, 64))),
            ChcExpr::BitVec(1, 64),
            ChcExpr::BitVec(2, 64),
        ),
        ChcExpr::BitVec(3, 64),
        ChcExpr::BitVec(4, 64),
    );

    for (formula, store_side) in [
        (
            ChcExpr::eq(ChcExpr::var(arr.clone()), abstract_store.clone()),
            1usize,
        ),
        (
            ChcExpr::eq(abstract_store.clone(), ChcExpr::var(arr.clone())),
            0,
        ),
    ] {
        let mut inv = InvariantModel::new();
        inv.set(
            pid,
            PredicateInterpretation::new(vec![arr.clone()], formula),
        );

        let translated = concretize_inv(&inv, &map);
        let interp = translated.get(&pid).expect("predicate should be present");
        assert_eq!(
            interp.vars[0].sort, original_array_sort,
            "predicate array argument should be restored to Array(BV64, BV64)"
        );

        let ChcExpr::Op(ChcOp::Eq, args) = &interp.formula else {
            panic!("expected array equality, got: {}", interp.formula);
        };
        assert_eq!(args.len(), 2);
        assert_eq!(
            args[1 - store_side].sort(),
            original_array_sort,
            "restored array variable should keep Array(BV64, BV64) sort"
        );
        assert_eq!(
            args[store_side].sort(),
            original_array_sort,
            "ConstArray/store chain should be recursively coerced to Array(BV64, BV64)"
        );
        assert_eq!(
            args[store_side].as_ref(),
            &expected_store,
            "ConstArray default, nested store indices, and store values should all be BV64"
        );
    }
}

#[test]
fn back_translation_rekeys_const_array_store_chain_to_bv_array_sort() {
    let mut map = BvIntMap::new();
    let pid = PredicateId::new(0);
    let original_sort = ChcSort::Array(Box::new(ChcSort::BitVec(8)), Box::new(ChcSort::BitVec(16)));
    map.pred_arg_widths.insert(pid, vec![None]);
    map.pred_arg_sorts.insert(pid, vec![original_sort.clone()]);

    let a = ChcVar::new(
        "a",
        ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int)),
    );
    let abstract_store_chain = ChcExpr::store(
        ChcExpr::store(
            ChcExpr::ConstArray(ChcSort::Int, Arc::new(ChcExpr::int(0))),
            ChcExpr::int(1),
            ChcExpr::int(258),
        ),
        ChcExpr::int(-1),
        ChcExpr::int(513),
    );

    let mut inv = InvariantModel::new();
    inv.set(
        pid,
        PredicateInterpretation::new(
            vec![a.clone()],
            ChcExpr::eq(ChcExpr::var(a), abstract_store_chain),
        ),
    );

    let translated = concretize_inv(&inv, &map);
    let interp = translated.get(&pid).expect("predicate should be present");
    assert_eq!(interp.vars[0].sort, original_sort);
    assert_eq!(
        interp.formula,
        ChcExpr::eq(
            ChcExpr::var(ChcVar::new(
                "a",
                ChcSort::Array(Box::new(ChcSort::BitVec(8)), Box::new(ChcSort::BitVec(16))),
            )),
            ChcExpr::store(
                ChcExpr::store(
                    ChcExpr::ConstArray(ChcSort::BitVec(8), Arc::new(ChcExpr::BitVec(0, 16))),
                    ChcExpr::BitVec(1, 8),
                    ChcExpr::BitVec(258, 16),
                ),
                ChcExpr::BitVec(255, 8),
                ChcExpr::BitVec(513, 16),
            ),
        ),
        "ConstArray/store chains should be rekeyed and retyped to the original BV array sort"
    );
}

#[test]
fn back_translation_simplifies_out_of_range_bv_upper_bound_5877() {
    let mut map = BvIntMap::new();
    let pid = PredicateId::new(0);
    map.pred_arg_widths.insert(pid, vec![Some(32)]);

    let x = ChcVar::new("x", ChcSort::Int);
    let mut inv = InvariantModel::new();
    inv.set(
        pid,
        PredicateInterpretation::new(
            vec![x.clone()],
            ChcExpr::lt(ChcExpr::var(x), ChcExpr::int(4_294_967_296_i64)),
        ),
    );

    let translated = concretize_inv(&inv, &map);
    let interp = translated.get(&pid).expect("predicate should be present");
    assert_eq!(interp.vars[0].sort, ChcSort::BitVec(32));
    assert_eq!(
        interp.formula,
        ChcExpr::Bool(true),
        "x < 2^32 must stay tautological after BV32 back-translation"
    );
}

#[test]
fn back_translation_rejects_out_of_range_bv_equality_5877() {
    let mut map = BvIntMap::new();
    let pid = PredicateId::new(0);
    map.pred_arg_widths.insert(pid, vec![Some(32)]);

    let x = ChcVar::new("x", ChcSort::Int);
    let mut inv = InvariantModel::new();
    inv.set(
        pid,
        PredicateInterpretation::new(
            vec![x.clone()],
            ChcExpr::eq(ChcExpr::var(x), ChcExpr::int(4_294_967_296_i64)),
        ),
    );

    let translated = concretize_inv(&inv, &map);
    let interp = translated.get(&pid).expect("predicate should be present");
    assert_eq!(interp.vars[0].sort, ChcSort::BitVec(32));
    assert_eq!(
        interp.formula,
        ChcExpr::Bool(false),
        "x = 2^32 must become false for BV32 back-translation"
    );
}

#[test]
fn back_translation_handles_reversed_out_of_range_bv_comparison_5877() {
    let mut map = BvIntMap::new();
    let pid = PredicateId::new(0);
    map.pred_arg_widths.insert(pid, vec![Some(32)]);

    let x = ChcVar::new("x", ChcSort::Int);
    let mut inv = InvariantModel::new();
    inv.set(
        pid,
        PredicateInterpretation::new(
            vec![x.clone()],
            ChcExpr::gt(ChcExpr::int(4_294_967_296_i64), ChcExpr::var(x)),
        ),
    );

    let translated = concretize_inv(&inv, &map);
    let interp = translated.get(&pid).expect("predicate should be present");
    assert_eq!(interp.vars[0].sort, ChcSort::BitVec(32));
    assert_eq!(
        interp.formula,
        ChcExpr::Bool(true),
        "2^32 > x must stay tautological for BV32 back-translation"
    );
}

#[test]
fn back_translation_simplifies_unsigned_range_guards_5877() {
    let mut map = BvIntMap::new();
    let pid = PredicateId::new(0);
    map.pred_arg_widths.insert(pid, vec![None, Some(32)]);
    map.pred_arg_sorts
        .insert(pid, vec![ChcSort::Bool, ChcSort::BitVec(32)]);

    let keep = ChcVar::new("keep", ChcSort::Bool);
    let x = ChcVar::new("x", ChcSort::Int);
    let mut inv = InvariantModel::new();
    inv.set(
        pid,
        PredicateInterpretation::new(
            vec![keep.clone(), x.clone()],
            ChcExpr::and_all(vec![
                ChcExpr::var(keep.clone()),
                ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(0)),
                ChcExpr::lt(ChcExpr::var(x), ChcExpr::int(4_294_967_296_i64)),
            ]),
        ),
    );

    let translated = concretize_inv(&inv, &map);
    let interp = translated.get(&pid).expect("predicate should be present");
    assert_eq!(interp.vars[0].sort, ChcSort::Bool);
    assert_eq!(interp.vars[1].sort, ChcSort::BitVec(32));
    assert_eq!(
        interp.formula,
        ChcExpr::var(keep),
        "Unsigned BV range guards must simplify away during back-translation"
    );
}

#[test]
fn back_translation_preserves_wrap_guard_ite_in_int_domain_5877() {
    let mut map = BvIntMap::new();
    let pid = PredicateId::new(0);
    map.pred_arg_widths.insert(pid, vec![Some(32)]);
    map.pred_arg_sorts.insert(pid, vec![ChcSort::BitVec(32)]);

    let x = ChcVar::new("x", ChcSort::Int);
    let sum = ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1));
    let wrap_guard = ChcExpr::lt(sum.clone(), ChcExpr::int(4_294_967_296_i64));
    let wrapped = ChcExpr::sub(sum.clone(), ChcExpr::int(4_294_967_296_i64));
    let mut inv = InvariantModel::new();
    inv.set(
        pid,
        PredicateInterpretation::new(vec![x], ChcExpr::ite(wrap_guard, sum, wrapped)),
    );

    let translated = concretize_inv(&inv, &map);
    let interp = translated.get(&pid).expect("predicate should be present");
    assert_eq!(interp.vars[0].sort, ChcSort::BitVec(32));
    let lifted_sum = ChcExpr::add(
        ChcExpr::Op(
            ChcOp::Bv2Nat,
            vec![Arc::new(ChcExpr::var(ChcVar::new(
                "x",
                ChcSort::BitVec(32),
            )))],
        ),
        ChcExpr::int(1),
    );
    assert_eq!(
        interp.formula,
        ChcExpr::ite(
            ChcExpr::lt(lifted_sum.clone(), ChcExpr::int(4_294_967_296_i64)),
            lifted_sum.clone(),
            ChcExpr::sub(lifted_sum, ChcExpr::int(4_294_967_296_i64)),
        ),
        "Back-translation should preserve the learned Int-domain wrap guard"
    );
}

/// `coerce_to_sort` must handle negative Int values with proper modular arithmetic.
#[test]
fn coerce_negative_int_to_bv() {
    // -1 mod 2^8 = 255
    let result = coerce_to_sort(&ChcExpr::Int(-1), &ChcSort::BitVec(8));
    assert_eq!(result, ChcExpr::BitVec(255, 8));

    // -256 mod 2^8 = 0
    let result = coerce_to_sort(&ChcExpr::Int(-256), &ChcSort::BitVec(8));
    assert_eq!(result, ChcExpr::BitVec(0, 8));

    // 0 mod 2^32 = 0
    let result = coerce_to_sort(&ChcExpr::Int(0), &ChcSort::BitVec(32));
    assert_eq!(result, ChcExpr::BitVec(0, 32));

    // 42 mod 2^32 = 42
    let result = coerce_to_sort(&ChcExpr::Int(42), &ChcSort::BitVec(32));
    assert_eq!(result, ChcExpr::BitVec(42, 32));
}

/// `int_cmp_to_bv` maps Int comparisons to unsigned BV comparisons.
#[test]
fn int_cmp_to_bv_mapping() {
    assert_eq!(int_cmp_to_bv(&ChcOp::Eq), ChcOp::Eq);
    assert_eq!(int_cmp_to_bv(&ChcOp::Ne), ChcOp::Ne);
    assert_eq!(int_cmp_to_bv(&ChcOp::Lt), ChcOp::BvULt);
    assert_eq!(int_cmp_to_bv(&ChcOp::Le), ChcOp::BvULe);
    assert_eq!(int_cmp_to_bv(&ChcOp::Gt), ChcOp::BvUGt);
    assert_eq!(int_cmp_to_bv(&ChcOp::Ge), ChcOp::BvUGe);
}

#[test]
fn backtranslate_bv_arithmetic_preserves_int_semantics() {
    let sort_env = FxHashMap::from_iter([(ChcVar::new("x", ChcSort::Int), ChcSort::BitVec(32))]);
    let abstract_formula = ChcExpr::lt(
        ChcExpr::add(
            ChcExpr::var(ChcVar::new("x", ChcSort::Int)),
            ChcExpr::int(1),
        ),
        ChcExpr::int(5),
    );

    let translated = int_to_bv_formula(&abstract_formula, &sort_env);
    let expected = ChcExpr::lt(
        ChcExpr::add(
            ChcExpr::Op(
                ChcOp::Bv2Nat,
                vec![Arc::new(ChcExpr::var(ChcVar::new(
                    "x",
                    ChcSort::BitVec(32),
                )))],
            ),
            ChcExpr::int(1),
        ),
        ChcExpr::int(5),
    );

    assert_eq!(
        translated, expected,
        "back-translation must preserve learned Int arithmetic over BV vars"
    );
}

#[test]
fn backtranslate_bv_comparison_uses_bv2nat_when_not_constant_foldable() {
    let sort_env = FxHashMap::from_iter([
        (ChcVar::new("x", ChcSort::Int), ChcSort::BitVec(32)),
        (ChcVar::new("y", ChcSort::Int), ChcSort::BitVec(32)),
    ]);
    let abstract_formula = ChcExpr::ge(
        ChcExpr::var(ChcVar::new("x", ChcSort::Int)),
        ChcExpr::var(ChcVar::new("y", ChcSort::Int)),
    );

    let translated = int_to_bv_formula(&abstract_formula, &sort_env);
    let expected = ChcExpr::ge(
        ChcExpr::Op(
            ChcOp::Bv2Nat,
            vec![Arc::new(ChcExpr::var(ChcVar::new(
                "x",
                ChcSort::BitVec(32),
            )))],
        ),
        ChcExpr::Op(
            ChcOp::Bv2Nat,
            vec![Arc::new(ChcExpr::var(ChcVar::new(
                "y",
                ChcSort::BitVec(32),
            )))],
        ),
    );

    assert_eq!(
        translated, expected,
        "non-foldable BV comparisons must remain Int comparisons over bv2nat"
    );
}

/// Mixed Int+BV predicate: Int arguments must be preserved after concretization.
/// This catches the bug where a predicate-wide `has_bv_args` audit would
/// incorrectly reject legitimate Int witness values in mixed-signature predicates
/// like `(Int, BitVec(8))`.
#[test]
fn invalidity_back_translation_preserves_non_bv_instances_in_mixed_signature_6293() {
    let mut problem = ChcProblem::new();
    // Mixed signature: first arg is Int, second is BitVec(8)
    let pred = problem.declare_predicate("inv", vec![ChcSort::Int, ChcSort::BitVec(8)]);
    let transformed = Box::new(BvToIntAbstractor::new()).transform(problem);

    let int_canonical = format!("__p{}_a0", pred.index());
    let bv_canonical = format!("__p{}_a1", pred.index());
    let mut instances = FxHashMap::default();
    instances.insert(int_canonical.clone(), SmtValue::Int(42));
    instances.insert(bv_canonical.clone(), SmtValue::Int(300));

    let cex = Counterexample::with_witness(
        Vec::new(),
        DerivationWitness {
            query_clause: None,
            root: 0,
            entries: vec![DerivationWitnessEntry {
                predicate: pred,
                level: 0,
                state: ChcExpr::Bool(true),
                incoming_clause: None,
                premises: Vec::new(),
                instances,
            }],
        },
    );

    let translated = transformed.back_translator.translate_invalidity(cex);
    let witness = translated
        .witness
        .expect("translated counterexample should keep witness");

    // Int argument must be preserved unchanged
    assert_eq!(
        witness.entries[0].instances.get(&int_canonical),
        Some(&SmtValue::Int(42)),
        "Int argument in mixed-signature predicate must remain Int"
    );
    // BV argument must be concretized: 300 mod 256 = 44
    assert_eq!(
        witness.entries[0].instances.get(&bv_canonical),
        Some(&SmtValue::BitVec(44, 8)),
        "BV argument in mixed-signature predicate must be concretized"
    );
}

#[test]
fn bvadd_relaxed_uses_plain_integer_addition() {
    let mut map = BvIntMap::new();
    let x_bv = ChcExpr::var(ChcVar::new("x", ChcSort::BitVec(8)));
    let y_bv = ChcExpr::var(ChcVar::new("y", ChcSort::BitVec(8)));
    let add = ChcExpr::Op(ChcOp::BvAdd, vec![Arc::new(x_bv), Arc::new(y_bv)]);
    let x_int = ChcExpr::var(ChcVar::new("x", ChcSort::Int));
    let y_int = ChcExpr::var(ChcVar::new("y", ChcSort::Int));

    let result = abstract_expr(&add, &mut map, true);

    assert_eq!(
        result,
        ChcExpr::add(x_int, y_int),
        "relaxed BV add must skip modular ITE wrapping"
    );
}

#[test]
fn bvudiv_relaxed_guards_zero_divisor() {
    let mut map = BvIntMap::new();
    let x_bv = ChcExpr::var(ChcVar::new("x", ChcSort::BitVec(16)));
    let y_bv = ChcExpr::var(ChcVar::new("y", ChcSort::BitVec(16)));
    let div = ChcExpr::Op(ChcOp::BvUDiv, vec![Arc::new(x_bv), Arc::new(y_bv)]);
    let x_int = ChcExpr::var(ChcVar::new("x", ChcSort::Int));
    let y_int = ChcExpr::var(ChcVar::new("y", ChcSort::Int));

    let result = abstract_expr(&div, &mut map, true);

    assert_eq!(
        result,
        ChcExpr::ite(
            ChcExpr::eq(y_int.clone(), ChcExpr::int(0)),
            ChcExpr::int(0),
            ChcExpr::Op(ChcOp::Div, vec![Arc::new(x_int), Arc::new(y_int)]),
        ),
        "relaxed BV udiv must guard divide-by-zero explicitly"
    );
}

#[test]
fn bvudiv_bv64_normalizes_operands_7006() {
    let mut map = BvIntMap::new();
    let div = ChcExpr::Op(
        ChcOp::BvUDiv,
        vec![
            Arc::new(ChcExpr::Var(ChcVar::new("x", ChcSort::BitVec(64)))),
            Arc::new(ChcExpr::Var(ChcVar::new("y", ChcSort::BitVec(64)))),
        ],
    );
    let result = abstract_expr(&div, &mut map, false);
    match result {
        ChcExpr::Op(ChcOp::Ite, ref args) if args.len() == 3 => {
            assert!(matches!(args[0].as_ref(), ChcExpr::Op(ChcOp::Eq, _)));
            assert!(matches!(args[2].as_ref(), ChcExpr::Op(ChcOp::Div, _)));
        }
        other => panic!("BV64 udiv should normalize both operands, got: {other}"),
    }
}

#[test]
fn bvslt_relaxed_uses_plain_integer_order() {
    let mut map = BvIntMap::new();
    let x_bv = ChcExpr::var(ChcVar::new("x", ChcSort::BitVec(8)));
    let y_bv = ChcExpr::var(ChcVar::new("y", ChcSort::BitVec(8)));
    let slt = ChcExpr::Op(ChcOp::BvSLt, vec![Arc::new(x_bv), Arc::new(y_bv)]);
    let x_int = ChcExpr::var(ChcVar::new("x", ChcSort::Int));
    let y_int = ChcExpr::var(ChcVar::new("y", ChcSort::Int));

    let result = abstract_expr(&slt, &mut map, true);

    assert_eq!(
        result,
        ChcExpr::lt(x_int, y_int),
        "relaxed signed compare must over-approximate with plain integer order"
    );
}

#[test]
fn bvneg_bv64_normalizes_operand_7006() {
    let mut map = BvIntMap::new();
    let neg = ChcExpr::Op(
        ChcOp::BvNeg,
        vec![Arc::new(ChcExpr::Var(ChcVar::new(
            "x",
            ChcSort::BitVec(64),
        )))],
    );
    let result = abstract_expr(&neg, &mut map, false);
    match result {
        ChcExpr::Op(ChcOp::Ite, ref args) if args.len() == 3 => {
            assert!(matches!(args[0].as_ref(), ChcExpr::Op(ChcOp::Eq, _)));
            assert!(matches!(args[2].as_ref(), ChcExpr::Op(ChcOp::Sub, _)));
        }
        other => panic!("BV64 neg should normalize the operand, got: {other}"),
    }
}

#[test]
fn bv2nat_bv64_normalizes_operand_7006() {
    let mut map = BvIntMap::new();
    let bv2nat = ChcExpr::Op(
        ChcOp::Bv2Nat,
        vec![Arc::new(ChcExpr::Var(ChcVar::new(
            "x",
            ChcSort::BitVec(64),
        )))],
    );
    let result = abstract_expr(&bv2nat, &mut map, false);
    assert!(
        matches!(result, ChcExpr::Op(ChcOp::Mod, _)),
        "bv2nat on BV64 should normalize via mod 2^64, got: {result}"
    );
}

#[test]
fn relaxed_transform_skips_range_constraints() {
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("inv", vec![ChcSort::BitVec(8)]);
    let x = ChcVar::new("x", ChcSort::BitVec(8));
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![], None),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x)]),
    ));

    let exact = Box::new(BvToIntAbstractor::new()).transform(problem.clone());
    let relaxed = Box::new(BvToIntAbstractor::relaxed()).transform(problem);

    assert!(
        exact.problem.clauses()[0].body.constraint.is_some(),
        "exact BV-to-Int should add head-argument range constraints"
    );
    assert!(
        relaxed.problem.clauses()[0].body.constraint.is_none(),
        "relaxed BV-to-Int must skip range constraints"
    );
}

/// BvConcat with non-BitVec second argument must not panic (#7078).
/// When an upstream transform produces a BvConcat node whose child has Int
/// sort, abstract_op falls back to UF encoding instead of crashing.
#[test]
fn bvconcat_non_bitvec_arg_does_not_panic_7078() {
    let mut map = BvIntMap::new();
    // BvConcat where second argument is Int-sorted (the crash scenario)
    let concat = ChcExpr::Op(
        ChcOp::BvConcat,
        vec![
            Arc::new(ChcExpr::Var(ChcVar::new("x", ChcSort::BitVec(8)))),
            Arc::new(ChcExpr::Var(ChcVar::new("y", ChcSort::Int))),
        ],
    );
    // Exact mode: should produce UF fallback, not panic
    let result = abstract_expr(&concat, &mut map, false);
    assert!(
        matches!(result, ChcExpr::FuncApp(_, ChcSort::Int, _)),
        "BvConcat with Int arg should fall back to UF, got: {result}"
    );
    // Relaxed mode: same UF fallback
    let result_relaxed = abstract_expr(&concat, &mut map, true);
    assert!(
        matches!(result_relaxed, ChcExpr::FuncApp(_, ChcSort::Int, _)),
        "Relaxed BvConcat with Int arg should fall back to UF, got: {result_relaxed}"
    );
}

/// BvAdd with non-BitVec args must not panic (#7078).
/// Tests the early guard for arithmetic BV ops.
#[test]
fn bvadd_non_bitvec_args_does_not_panic_7078() {
    let mut map = BvIntMap::new();
    let add = ChcExpr::Op(
        ChcOp::BvAdd,
        vec![
            Arc::new(ChcExpr::Var(ChcVar::new("x", ChcSort::Int))),
            Arc::new(ChcExpr::Var(ChcVar::new("y", ChcSort::Int))),
        ],
    );
    let result = abstract_expr(&add, &mut map, false);
    assert!(
        matches!(result, ChcExpr::FuncApp(_, ChcSort::Int, _)),
        "BvAdd with Int args should fall back to UF, got: {result}"
    );
}
#[test]
fn test_int_pow2_small_widths() {
    use super::ops::int_pow2;
    assert_eq!(int_pow2(0), ChcExpr::int(1));
    assert_eq!(int_pow2(1), ChcExpr::int(2));
    assert_eq!(int_pow2(8), ChcExpr::int(256));
    assert_eq!(int_pow2(31), ChcExpr::int(1i64 << 31));
    assert_eq!(int_pow2(32), ChcExpr::int(1i64 << 32));
    assert_eq!(int_pow2(62), ChcExpr::int(1i64 << 62));
}

#[test]
fn test_int_pow2_large_widths() {
    use super::ops::int_pow2;
    // 2^63 = 2^32 * 2^31 (doesn't fit in i64, must be expression)
    let p63 = int_pow2(63);
    assert!(
        matches!(p63, ChcExpr::Op(ChcOp::Mul, _)),
        "2^63 should be Mul expr"
    );

    // 2^64 = 2^32 * 2^32 (doesn't fit in i64, must be expression)
    let p64 = int_pow2(64);
    assert!(
        matches!(p64, ChcExpr::Op(ChcOp::Mul, _)),
        "2^64 should be Mul expr"
    );

    // Verify structure: 2^64 = 2^32 * 2^32
    if let ChcExpr::Op(ChcOp::Mul, ref args) = p64 {
        assert_eq!(*args[0], ChcExpr::int(1i64 << 32));
        assert_eq!(*args[1], ChcExpr::int(1i64 << 32));
    }

    // 2^128 should also work (recursive decomposition)
    let p128 = int_pow2(128);
    assert!(
        matches!(p128, ChcExpr::Op(ChcOp::Mul, _)),
        "2^128 should be Mul expr"
    );
}

/// BvAnd with constant low-bit mask encodes as mod (#7006).
#[test]
fn bvand_const_mask_encodes_as_mod_7006() {
    let mut map = BvIntMap::new();
    // x & 0xFF (8-bit mask on BV32) → x mod 256
    let bvand = ChcExpr::Op(
        ChcOp::BvAnd,
        vec![
            Arc::new(ChcExpr::Var(ChcVar::new("x", ChcSort::BitVec(32)))),
            Arc::new(ChcExpr::BitVec(0xFF, 32)),
        ],
    );
    let result = abstract_expr(&bvand, &mut map, false);
    // Should be mod(x, 256), not UF
    assert!(
        matches!(result, ChcExpr::Op(ChcOp::Mod, _)),
        "x & 0xFF should encode as x mod 256, got: {result}"
    );
}

/// BvAnd with zero mask → 0 (#7006).
#[test]
fn bvand_zero_mask_returns_zero_7006() {
    let mut map = BvIntMap::new();
    let bvand = ChcExpr::Op(
        ChcOp::BvAnd,
        vec![
            Arc::new(ChcExpr::Var(ChcVar::new("x", ChcSort::BitVec(32)))),
            Arc::new(ChcExpr::BitVec(0, 32)),
        ],
    );
    let result = abstract_expr(&bvand, &mut map, false);
    assert_eq!(result, ChcExpr::int(0), "x & 0 should be 0");
}

/// BvShl with constant shift encodes as mul+mod (#7006).
#[test]
fn bvshl_const_shift_encodes_as_mul_mod_7006() {
    let mut map = BvIntMap::new();
    // x << 4 on BV32 → (x * 16) mod 2^32
    let shl = ChcExpr::Op(
        ChcOp::BvShl,
        vec![
            Arc::new(ChcExpr::Var(ChcVar::new("x", ChcSort::BitVec(32)))),
            Arc::new(ChcExpr::BitVec(4, 32)),
        ],
    );
    let result = abstract_expr(&shl, &mut map, false);
    assert!(
        matches!(result, ChcExpr::Op(ChcOp::Mod, _)),
        "x << 4 should encode as mod(x*16, 2^32), got: {result}"
    );
}

/// BvLShr with constant shift encodes as integer division (#7006).
#[test]
fn bvlshr_const_shift_encodes_as_div_7006() {
    let mut map = BvIntMap::new();
    // x >> 3 on BV32 → x / 8
    let lshr = ChcExpr::Op(
        ChcOp::BvLShr,
        vec![
            Arc::new(ChcExpr::Var(ChcVar::new("x", ChcSort::BitVec(32)))),
            Arc::new(ChcExpr::BitVec(3, 32)),
        ],
    );
    let result = abstract_expr(&lshr, &mut map, false);
    assert!(
        matches!(result, ChcExpr::Op(ChcOp::Div, _)),
        "x >> 3 should encode as x / 8, got: {result}"
    );
}

/// BV64 shifts with expression-shaped constants must stay precise (#7006).
#[test]
fn bvshl_bv64_large_const_shift_returns_zero_7006() {
    let mut map = BvIntMap::new();
    let shl = ChcExpr::Op(
        ChcOp::BvShl,
        vec![
            Arc::new(ChcExpr::Var(ChcVar::new("x", ChcSort::BitVec(64)))),
            Arc::new(ChcExpr::BitVec(0xFFFF_FFFF_FFFF_FFFF, 64)),
        ],
    );
    let result = abstract_expr(&shl, &mut map, false);
    assert_eq!(
        result,
        ChcExpr::int(0),
        "x << 0xffff...ffff should encode as 0, got: {result}"
    );
}

/// BV64 logical right shifts with expression-shaped constants must stay precise (#7006).
#[test]
fn bvlshr_bv64_large_const_shift_returns_zero_7006() {
    let mut map = BvIntMap::new();
    let lshr = ChcExpr::Op(
        ChcOp::BvLShr,
        vec![
            Arc::new(ChcExpr::Var(ChcVar::new("x", ChcSort::BitVec(64)))),
            Arc::new(ChcExpr::BitVec(0xFFFF_FFFF_FFFF_FFFF, 64)),
        ],
    );
    let result = abstract_expr(&lshr, &mut map, false);
    assert_eq!(
        result,
        ChcExpr::int(0),
        "x >> 0xffff...ffff should encode as 0, got: {result}"
    );
}

/// BV64 low-slice extracts should lower to a low-bit modulus pattern (#7006).
#[test]
fn bvextract_bv64_low_slice_encodes_as_mod_7006() {
    let mut map = BvIntMap::new();
    let extract = ChcExpr::Op(
        ChcOp::BvExtract(2, 0),
        vec![Arc::new(ChcExpr::Var(ChcVar::new(
            "x",
            ChcSort::BitVec(64),
        )))],
    );
    let result = abstract_expr(&extract, &mut map, false);
    assert!(
        matches!(result, ChcExpr::Op(ChcOp::Mod, _)),
        "((_ extract 2 0) x) should encode as a low-bit mod pattern, got: {result}"
    );
}

/// BV64 top-slice extracts should lower to division by the dropped low bits (#7006).
#[test]
fn bvextract_bv64_top_slice_encodes_as_div_7006() {
    let mut map = BvIntMap::new();
    let extract = ChcExpr::Op(
        ChcOp::BvExtract(63, 3),
        vec![Arc::new(ChcExpr::Var(ChcVar::new(
            "x",
            ChcSort::BitVec(64),
        )))],
    );
    let result = abstract_expr(&extract, &mut map, false);
    assert!(
        matches!(result, ChcExpr::Op(ChcOp::Div, _)),
        "((_ extract 63 3) x) should encode as division by 8, got: {result}"
    );
}

/// BvNot encodes as 2^w - 1 - x (#7006).
#[test]
fn bvnot_encodes_as_complement_7006() {
    let mut map = BvIntMap::new();
    let not = ChcExpr::Op(
        ChcOp::BvNot,
        vec![Arc::new(ChcExpr::Var(ChcVar::new("x", ChcSort::BitVec(8))))],
    );
    let result = abstract_expr(&not, &mut map, false);
    // Should be 2^8 - 1 - x = 256 - 1 - x
    assert!(
        matches!(result, ChcExpr::Op(ChcOp::Sub, _)),
        "~x should encode as (2^w - 1) - x, got: {result}"
    );
}

/// BvOr with zero constant is identity (#7006).
#[test]
fn bvor_zero_is_identity_7006() {
    let mut map = BvIntMap::new();
    let or = ChcExpr::Op(
        ChcOp::BvOr,
        vec![
            Arc::new(ChcExpr::Var(ChcVar::new("x", ChcSort::BitVec(32)))),
            Arc::new(ChcExpr::BitVec(0, 32)),
        ],
    );
    let result = abstract_expr(&or, &mut map, false);
    // Should be just x (identity)
    assert!(
        matches!(result, ChcExpr::Var(_)),
        "x | 0 should be identity, got: {result}"
    );
}

/// BV64 alignment masks like `x & ~7` must stay precise (#7006).
#[test]
fn bvand_bv64_alignment_mask_clears_low_bits_7006() {
    let mut map = BvIntMap::new();
    let bvand = ChcExpr::Op(
        ChcOp::BvAnd,
        vec![
            Arc::new(ChcExpr::Var(ChcVar::new("x", ChcSort::BitVec(64)))),
            Arc::new(ChcExpr::Op(
                ChcOp::BvNot,
                vec![Arc::new(ChcExpr::BitVec(7, 64))],
            )),
        ],
    );
    let result = abstract_expr(&bvand, &mut map, false);
    match result {
        ChcExpr::Op(ChcOp::Mul, ref args) if args.len() == 2 => {
            assert!(
                matches!(args[0].as_ref(), ChcExpr::Op(ChcOp::Div, _)),
                "x & ~7 should clear low bits via (x / 8) * 8, got: {}",
                args[0]
            );
        }
        other => panic!("x & ~7 should not fall back to UF, got: {other}"),
    }
}

/// BV64 all-ones masks must normalize the operand, not return raw Int vars (#7006).
#[test]
fn bvand_bv64_all_ones_normalizes_operand_7006() {
    let mut map = BvIntMap::new();
    let bvand = ChcExpr::Op(
        ChcOp::BvAnd,
        vec![
            Arc::new(ChcExpr::Var(ChcVar::new("x", ChcSort::BitVec(64)))),
            Arc::new(ChcExpr::BitVec(0xFFFF_FFFF_FFFF_FFFF, 64)),
        ],
    );
    let result = abstract_expr(&bvand, &mut map, false);
    assert!(
        matches!(result, ChcExpr::Op(ChcOp::Mod, _)),
        "x & all_ones should normalize via mod 2^64, got: {result}"
    );
}

/// BV64 low-bit fill masks should encode exactly for tag packing (#7006).
#[test]
fn bvor_bv64_low_mask_sets_low_bits_7006() {
    let mut map = BvIntMap::new();
    let or = ChcExpr::Op(
        ChcOp::BvOr,
        vec![
            Arc::new(ChcExpr::Var(ChcVar::new("x", ChcSort::BitVec(64)))),
            Arc::new(ChcExpr::BitVec(7, 64)),
        ],
    );
    let result = abstract_expr(&or, &mut map, false);
    match result {
        ChcExpr::Op(ChcOp::Add, ref args) if args.len() == 2 => {
            assert!(
                matches!(args[0].as_ref(), ChcExpr::Op(ChcOp::Mul, _)),
                "x | 7 should preserve high bits and rewrite low bits, got: {}",
                args[0]
            );
        }
        other => panic!("x | 7 should not fall back to UF, got: {other}"),
    }
}

/// BV64 zero-OR must normalize the operand because range constraints are skipped (#7006).
#[test]
fn bvor_bv64_zero_normalizes_operand_7006() {
    let mut map = BvIntMap::new();
    let or = ChcExpr::Op(
        ChcOp::BvOr,
        vec![
            Arc::new(ChcExpr::Var(ChcVar::new("x", ChcSort::BitVec(64)))),
            Arc::new(ChcExpr::BitVec(0, 64)),
        ],
    );
    let result = abstract_expr(&or, &mut map, false);
    assert!(
        matches!(result, ChcExpr::Op(ChcOp::Mod, _)),
        "x | 0 should normalize via mod 2^64, got: {result}"
    );
}

/// BvXor with zero is identity, self-XOR is zero (#7006).
#[test]
fn bvxor_precise_patterns_7006() {
    let mut map = BvIntMap::new();
    let x = Arc::new(ChcExpr::Var(ChcVar::new("x", ChcSort::BitVec(32))));
    // x ^ 0 = x
    let xor_zero = ChcExpr::Op(
        ChcOp::BvXor,
        vec![x.clone(), Arc::new(ChcExpr::BitVec(0, 32))],
    );
    let result = abstract_expr(&xor_zero, &mut map, false);
    assert!(
        matches!(result, ChcExpr::Var(_)),
        "x ^ 0 should be identity, got: {result}"
    );
    // x ^ x = 0
    let xor_self = ChcExpr::Op(ChcOp::BvXor, vec![x.clone(), x.clone()]);
    let result = abstract_expr(&xor_self, &mut map, false);
    assert_eq!(result, ChcExpr::int(0), "x ^ x should be 0");
}

/// BV64 zero-XOR must normalize the operand because range constraints are skipped (#7006).
#[test]
fn bvxor_bv64_zero_normalizes_operand_7006() {
    let mut map = BvIntMap::new();
    let xor = ChcExpr::Op(
        ChcOp::BvXor,
        vec![
            Arc::new(ChcExpr::Var(ChcVar::new("x", ChcSort::BitVec(64)))),
            Arc::new(ChcExpr::BitVec(0, 64)),
        ],
    );
    let result = abstract_expr(&xor, &mut map, false);
    assert!(
        matches!(result, ChcExpr::Op(ChcOp::Mod, _)),
        "x ^ 0 should normalize via mod 2^64, got: {result}"
    );
}

/// BV64 all-ones masks are abstracted as expression trees, not single Ints (#7006).
#[test]
fn bvxor_bv64_all_ones_encodes_as_complement_7006() {
    let mut map = BvIntMap::new();
    let xor = ChcExpr::Op(
        ChcOp::BvXor,
        vec![
            Arc::new(ChcExpr::Var(ChcVar::new("x", ChcSort::BitVec(64)))),
            Arc::new(ChcExpr::BitVec(0xFFFF_FFFF_FFFF_FFFF, 64)),
        ],
    );
    let result = abstract_expr(&xor, &mut map, false);
    assert!(
        matches!(result, ChcExpr::Op(ChcOp::Sub, _)),
        "x ^ 0xffff...ffff should encode as complement, got: {result}"
    );
    assert!(
        expr_contains_op(&result, &ChcOp::Mod),
        "wide complement should normalize the operand, got: {result}"
    );
}

/// BvSignExtend must properly fill high bits for negative values (#7006).
#[test]
fn bv_sign_extend_exact_encoding_7006() {
    let mut map = BvIntMap::new();
    // sign_extend[24](x) where x is BV8: BV8 → BV32
    // For x >= 128 (negative in signed): add 2^32 - 2^8 = 4294967040
    // For x < 128 (positive): identity
    let sext = ChcExpr::Op(
        ChcOp::BvSignExtend(24),
        vec![Arc::new(ChcExpr::Var(ChcVar::new("x", ChcSort::BitVec(8))))],
    );
    let result = abstract_expr(&sext, &mut map, false);
    // Should be an ITE: ite(x >= 128, x + fill, x)
    assert!(
        matches!(result, ChcExpr::Op(ChcOp::Ite, _)),
        "sign_extend should produce ITE for sign bit check, got: {result}"
    );
}

/// Wide sign-extension must normalize its operand before checking the sign bit.
#[test]
fn bv_sign_extend_bv64_normalizes_operand_7006() {
    let mut map = BvIntMap::new();
    let sext = ChcExpr::Op(
        ChcOp::BvSignExtend(1),
        vec![Arc::new(ChcExpr::Var(ChcVar::new(
            "x",
            ChcSort::BitVec(64),
        )))],
    );
    let result = abstract_expr(&sext, &mut map, false);
    assert!(
        matches!(result, ChcExpr::Op(ChcOp::Ite, _)),
        "sign_extend should still produce ITE, got: {result}"
    );
    assert!(
        expr_contains_op(&result, &ChcOp::Mod),
        "wide sign_extend should normalize the operand, got: {result}"
    );
}

#[test]
fn bvshl_bv64_zero_normalizes_operand_7006() {
    let mut map = BvIntMap::new();
    let shl = ChcExpr::Op(
        ChcOp::BvShl,
        vec![
            Arc::new(ChcExpr::Var(ChcVar::new("x", ChcSort::BitVec(64)))),
            Arc::new(ChcExpr::BitVec(0, 64)),
        ],
    );
    let result = abstract_expr(&shl, &mut map, false);
    assert!(
        matches!(result, ChcExpr::Op(ChcOp::Mod, _)),
        "x << 0 should normalize via mod 2^64, got: {result}"
    );
}

#[test]
fn bvlshr_bv64_zero_normalizes_operand_7006() {
    let mut map = BvIntMap::new();
    let lshr = ChcExpr::Op(
        ChcOp::BvLShr,
        vec![
            Arc::new(ChcExpr::Var(ChcVar::new("x", ChcSort::BitVec(64)))),
            Arc::new(ChcExpr::BitVec(0, 64)),
        ],
    );
    let result = abstract_expr(&lshr, &mut map, false);
    assert!(
        matches!(result, ChcExpr::Op(ChcOp::Mod, _)),
        "x >> 0 should normalize via mod 2^64, got: {result}"
    );
}

#[test]
fn bvashr_bv64_zero_normalizes_operand_7006() {
    let mut map = BvIntMap::new();
    let ashr = ChcExpr::Op(
        ChcOp::BvAShr,
        vec![
            Arc::new(ChcExpr::Var(ChcVar::new("x", ChcSort::BitVec(64)))),
            Arc::new(ChcExpr::BitVec(0, 64)),
        ],
    );
    let result = abstract_expr(&ashr, &mut map, false);
    assert!(
        matches!(result, ChcExpr::Op(ChcOp::Mod, _)),
        "x ashr 0 should normalize via mod 2^64, got: {result}"
    );
}

/// BV64 constants >= 2^63 must not abort the BvToInt transformation (#7006,
/// WORD-BV #8). With i128 `ChcExpr::Int` they are exact plain constants.
#[test]
fn bv64_large_constant_no_overflow_abort_7006() {
    let mut map = BvIntMap::new();
    let problem = make_simple_bv_problem(64);
    // 0xFFFFFFFFFFFFFFFF = 2^64 - 1: exact Int constant.
    let big_val = ChcExpr::BitVec(0xFFFF_FFFF_FFFF_FFFF, 64);
    let abstracted = abstract_expr(&big_val, &mut map, false);
    assert_eq!(
        try_const_bigint(&abstracted),
        Some(BigInt::from(0xFFFF_FFFF_FFFF_FFFFu128)),
        "BV64 max value must abstract to the exact integer, got: {abstracted}"
    );

    // 0x8000000000000000 = 2^63 (smallest value that overflows i64)
    let mut map2 = BvIntMap::new();
    let half_val = ChcExpr::BitVec(0x8000_0000_0000_0000, 64);
    let abstracted2 = abstract_expr(&half_val, &mut map2, false);
    assert_eq!(
        try_const_bigint(&abstracted2),
        Some(BigInt::from(1u128 << 63)),
        "BV64 2^63 must abstract to the exact integer, got: {abstracted2}"
    );

    // Small BV64 values should still be plain Int constants.
    let mut map3 = BvIntMap::new();
    let small_val = ChcExpr::BitVec(42, 64);
    let abstracted3 = abstract_expr(&small_val, &mut map3, false);
    assert_eq!(abstracted3, ChcExpr::int(42));

    // Verify the full transformation converts BV64 problems to Int.
    let mut map4 = BvIntMap::new();
    let transformed = abstract_problem(&problem, &mut map4, false, false);
    assert_eq!(transformed.predicates()[0].arg_sorts, vec![ChcSort::Int]);
}

// ── #8289: Variable-variable bitwise bit-decomposition tests ──────────────

/// BV8 variable-variable OR uses bit-decomposition.
#[test]
fn bvor_variable_variable_bv8_uses_bit_decomposition_8289() {
    let mut map = BvIntMap::new();
    let bvor = ChcExpr::Op(
        ChcOp::BvOr,
        vec![
            Arc::new(ChcExpr::Var(ChcVar::new("x", ChcSort::BitVec(8)))),
            Arc::new(ChcExpr::Var(ChcVar::new("y", ChcSort::BitVec(8)))),
        ],
    );
    let result = abstract_expr(&bvor, &mut map, false);
    assert!(
        !matches!(result, ChcExpr::FuncApp(_, _, _)),
        "BV8 variable-variable OR should use bit-decomposition, not UF, got: {result}"
    );
    assert!(
        matches!(result, ChcExpr::Op(ChcOp::Add, _)),
        "BV8 variable-variable OR should produce an Add tree, got: {result}"
    );
}

/// BV16 variable-variable XOR uses bit-decomposition.
#[test]
fn bvxor_variable_variable_bv16_uses_bit_decomposition_8289() {
    let mut map = BvIntMap::new();
    let bvxor = ChcExpr::Op(
        ChcOp::BvXor,
        vec![
            Arc::new(ChcExpr::Var(ChcVar::new("x", ChcSort::BitVec(16)))),
            Arc::new(ChcExpr::Var(ChcVar::new("y", ChcSort::BitVec(16)))),
        ],
    );
    let result = abstract_expr(&bvxor, &mut map, false);
    assert!(
        !matches!(result, ChcExpr::FuncApp(_, _, _)),
        "BV16 variable-variable XOR should use bit-decomposition, not UF, got: {result}"
    );
    assert!(
        matches!(result, ChcExpr::Op(ChcOp::Add, _)),
        "BV16 variable-variable XOR should produce an Add tree, got: {result}"
    );
}

/// BV64 variable-variable OR and XOR still use UF fallback.
#[test]
fn bvor_bvxor_variable_variable_bv64_uses_uf_8289() {
    let mut map = BvIntMap::new();
    let bvor = ChcExpr::Op(
        ChcOp::BvOr,
        vec![
            Arc::new(ChcExpr::Var(ChcVar::new("x", ChcSort::BitVec(64)))),
            Arc::new(ChcExpr::Var(ChcVar::new("y", ChcSort::BitVec(64)))),
        ],
    );
    assert!(
        matches!(
            abstract_expr(&bvor, &mut map, false),
            ChcExpr::FuncApp(_, _, _)
        ),
        "BV64 variable OR should fall back to UF"
    );
    let bvxor = ChcExpr::Op(
        ChcOp::BvXor,
        vec![
            Arc::new(ChcExpr::Var(ChcVar::new("x", ChcSort::BitVec(64)))),
            Arc::new(ChcExpr::Var(ChcVar::new("y", ChcSort::BitVec(64)))),
        ],
    );
    assert!(
        matches!(
            abstract_expr(&bvxor, &mut map, false),
            ChcExpr::FuncApp(_, _, _)
        ),
        "BV64 variable XOR should fall back to UF"
    );
}

// ── #8289: CEGAR-style decompose_limit tests ────────────────────────────────

/// With decompose_limit=0 (UF-only mode), even BV8 variable-variable AND
/// uses UF fallback and sets the had_bitwise_uf_fallback flag.
#[test]
fn decompose_limit_zero_forces_uf_only_8289() {
    let mut map = BvIntMap::new().with_decompose_limit(0);
    let bvand = ChcExpr::Op(
        ChcOp::BvAnd,
        vec![
            Arc::new(ChcExpr::Var(ChcVar::new("x", ChcSort::BitVec(8)))),
            Arc::new(ChcExpr::Var(ChcVar::new("y", ChcSort::BitVec(8)))),
        ],
    );
    let result = abstract_expr(&bvand, &mut map, false);
    assert!(
        matches!(result, ChcExpr::FuncApp(_, _, _)),
        "decompose_limit=0 should force UF for BV8 variable AND, got: {result}"
    );
    assert!(
        map.had_bitwise_uf_fallback,
        "decompose_limit=0 should set had_bitwise_uf_fallback"
    );
}

/// With decompose_limit=64, even BV64 variable-variable XOR uses bit-decomposition.
#[test]
fn decompose_limit_64_decomposes_bv64_8289() {
    let mut map = BvIntMap::new().with_decompose_limit(64);
    let bvxor = ChcExpr::Op(
        ChcOp::BvXor,
        vec![
            Arc::new(ChcExpr::Var(ChcVar::new("x", ChcSort::BitVec(64)))),
            Arc::new(ChcExpr::Var(ChcVar::new("y", ChcSort::BitVec(64)))),
        ],
    );
    let result = abstract_expr(&bvxor, &mut map, false);
    assert!(
        !matches!(result, ChcExpr::FuncApp(_, _, _)),
        "decompose_limit=64 should decompose BV64 variable XOR, got: {result}"
    );
    assert!(
        !map.had_bitwise_uf_fallback,
        "decompose_limit=64 should not set had_bitwise_uf_fallback for BV64"
    );
}

/// Constant-argument bitwise ops are unaffected by decompose_limit=0 because
/// they use pattern-specific encodings (mod, div) not bit-decomposition.
#[test]
fn decompose_limit_zero_preserves_constant_patterns_8289() {
    let mut map = BvIntMap::new().with_decompose_limit(0);
    // x & 0xFF should still produce mod even in UF-only mode
    let bvand = ChcExpr::Op(
        ChcOp::BvAnd,
        vec![
            Arc::new(ChcExpr::Var(ChcVar::new("x", ChcSort::BitVec(32)))),
            Arc::new(ChcExpr::BitVec(0xFF, 32)),
        ],
    );
    let result = abstract_expr(&bvand, &mut map, false);
    assert!(
        matches!(result, ChcExpr::Op(ChcOp::Mod, _)),
        "x & 0xFF should still use mod encoding even with decompose_limit=0, got: {result}"
    );
    assert!(
        !map.had_bitwise_uf_fallback,
        "constant-argument AND should not trigger bitwise UF fallback flag"
    );
}

/// Back-translator correctly reports had_bitwise_uf_fallback via trait method.
#[test]
fn back_translator_reports_uf_fallback_8289() {
    // UF-only mode: should report fallback
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("inv", vec![ChcSort::BitVec(8)]);
    let x = ChcVar::new("x", ChcSort::BitVec(8));
    let y = ChcVar::new("y", ChcSort::BitVec(8));
    // Add a clause with variable-variable AND
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![],
            Some(ChcExpr::Op(
                ChcOp::BvAnd,
                vec![Arc::new(ChcExpr::var(x.clone())), Arc::new(ChcExpr::var(y))],
            )),
        ),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x)]),
    ));

    let result_uf_only =
        Box::new(BvToIntAbstractor::new().with_decompose_limit(0)).transform(problem.clone());
    assert!(
        result_uf_only.back_translator.had_bitwise_uf_fallback(),
        "UF-only mode should report bitwise UF fallback"
    );

    // Default mode: BV8 uses decomposition, so no UF fallback
    let result_default = Box::new(BvToIntAbstractor::new()).transform(problem);
    assert!(
        !result_default.back_translator.had_bitwise_uf_fallback(),
        "Default mode should not report bitwise UF fallback for BV8"
    );
}

/// Constant-argument bitwise ops should still use their specialized encodings,
/// not fall through to bit-decomposition (#7006 preserved).
#[test]
fn constant_bitwise_ops_still_use_precise_patterns_8289() {
    let mut map = BvIntMap::new();
    // x & 0xFF should still produce mod, not bit-decomposition
    let bvand = ChcExpr::Op(
        ChcOp::BvAnd,
        vec![
            Arc::new(ChcExpr::Var(ChcVar::new("x", ChcSort::BitVec(32)))),
            Arc::new(ChcExpr::BitVec(0xFF, 32)),
        ],
    );
    let result = abstract_expr(&bvand, &mut map, false);
    assert!(
        matches!(result, ChcExpr::Op(ChcOp::Mod, _)),
        "x & 0xFF should still use mod encoding, got: {result}"
    );

    // x | 0 should still be identity
    let bvor = ChcExpr::Op(
        ChcOp::BvOr,
        vec![
            Arc::new(ChcExpr::Var(ChcVar::new("x", ChcSort::BitVec(8)))),
            Arc::new(ChcExpr::BitVec(0, 8)),
        ],
    );
    let result = abstract_expr(&bvor, &mut map, false);
    assert!(
        matches!(result, ChcExpr::Var(_)),
        "x | 0 should still be identity, got: {result}"
    );

    // x ^ 0 should still be identity
    let bvxor = ChcExpr::Op(
        ChcOp::BvXor,
        vec![
            Arc::new(ChcExpr::Var(ChcVar::new("x", ChcSort::BitVec(8)))),
            Arc::new(ChcExpr::BitVec(0, 8)),
        ],
    );
    let result = abstract_expr(&bvxor, &mut map, false);
    assert!(
        matches!(result, ChcExpr::Var(_)),
        "x ^ 0 should still be identity, got: {result}"
    );
}

/// SOUNDNESS (2026-07-08, wishlist rank 2; updated for WORD-BV #8): exact-mode
/// abstraction of a BitVec constant >= 2^95 must be EXACT, never silently
/// wrap. The pre-2026-07-08 `(*val >> 32) as i64` decomposition truncated the
/// high limb — u128::MAX abstracted to `low + (-1) * 2^32`, a wrong integer
/// value feeding a wrong verdict downstream. The interim fix aborted the whole
/// transformation (#7548); WORD-BV #8 now translates via BigInt: exact for
/// every u128 value, no abort, no wrap.
#[test]
fn exact_mode_constant_ge_2_pow_95_translates_exactly() {
    let mut p = ChcProblem::new();
    let inv = p.declare_predicate("inv", vec![ChcSort::BitVec(128)]);
    let x = ChcVar::new("x", ChcSort::BitVec(128));
    // Constant whose high 32-bit limb does not fit i64 (and whose value
    // exceeds i128::MAX, forcing the Horner encoding path).
    let big = ChcExpr::BitVec(u128::MAX, 128);
    p.add_clause(HornClause::new(
        ClauseBody::new(vec![], Some(ChcExpr::eq(ChcExpr::var(x), big))),
        ClauseHead::Predicate(
            inv,
            vec![ChcExpr::var(ChcVar::new("x", ChcSort::BitVec(128)))],
        ),
    ));
    let r = Box::new(BvToIntAbstractor::new()).transform(p);
    assert_eq!(
        r.problem.predicates()[0].arg_sorts,
        vec![ChcSort::Int],
        "the transformation must now translate instead of aborting (#7548 killed)"
    );
    // The translated constraint must contain the EXACT integer value.
    let constraint = r.problem.clauses()[0]
        .body
        .constraint
        .clone()
        .expect("clause has constraint");
    // Range constraints are conjoined; find the equality conjunct.
    let eq_rhs = constraint.conjuncts().iter().find_map(|c| match c {
        ChcExpr::Op(ChcOp::Eq, args) if args.len() == 2 => try_const_bigint(&args[1]),
        _ => None,
    });
    assert_eq!(
        eq_rhs,
        Some(BigInt::from(u128::MAX)),
        "u128::MAX must translate to the exact integer (never wrap): {constraint}"
    );
}

/// Relaxed mode: a BV64 constant with the sign bit set translates to its exact
/// (negative) signed value instead of aborting (WORD-BV #8).
#[test]
fn relaxed_mode_bv64_signed_constant_translates_exactly() {
    let mut map = BvIntMap::new();
    // 0xFFFFFFFFFFFFFFFF as signed BV64 = -1.
    let minus_one = ChcExpr::BitVec(0xFFFF_FFFF_FFFF_FFFF, 64);
    let abstracted = abstract_expr(&minus_one, &mut map, true);
    assert_eq!(
        try_const_bigint(&abstracted),
        Some(BigInt::from(-1)),
        "signed BV64 -1 must translate exactly in relaxed mode, got: {abstracted}"
    );
    // 2^63 as signed BV64 = -2^63 (previously an i64 overflow abort).
    let mut map2 = BvIntMap::new();
    let int_min = ChcExpr::BitVec(1u128 << 63, 64);
    let abstracted2 = abstract_expr(&int_min, &mut map2, true);
    assert_eq!(
        try_const_bigint(&abstracted2),
        Some(-(BigInt::from(1u128 << 63))),
        "signed BV64 INT_MIN must translate exactly in relaxed mode, got: {abstracted2}"
    );
}

// ── WORD-BV #8: lazy bitwise bounded atoms ──────────────────────────────────

/// A BV64 variable-variable AND falls back to a UF, but the enclosing clause
/// must gain bounded interpreted side constraints (0 <= f <= min(x,y), ...).
#[test]
fn lazy_bitwise_uf_fallback_emits_bounded_atoms_word_bv() {
    let mut p = ChcProblem::new();
    let inv = p.declare_predicate("inv", vec![ChcSort::BitVec(64)]);
    let x = ChcVar::new("x", ChcSort::BitVec(64));
    let y = ChcVar::new("y", ChcSort::BitVec(64));
    let and_xy = ChcExpr::Op(
        ChcOp::BvAnd,
        vec![
            Arc::new(ChcExpr::var(x.clone())),
            Arc::new(ChcExpr::var(y.clone())),
        ],
    );
    p.add_clause(HornClause::new(
        ClauseBody::new(vec![], None),
        ClauseHead::Predicate(inv, vec![and_xy]),
    ));

    let mut map = BvIntMap::new();
    let transformed = abstract_problem(&p, &mut map, false, false);
    assert!(map.had_bitwise_uf_fallback);
    assert!(
        map.pending_constraints.is_empty(),
        "side constraints must be drained into the clause"
    );
    let constraint = transformed.clauses()[0]
        .body
        .constraint
        .clone()
        .expect("bounded atoms must be conjoined into the clause constraint");
    let rendered = format!("{constraint}");
    assert!(
        rendered.contains("__bv2int_bvand"),
        "bounds must mention the bitwise UF result: {rendered}"
    );
    assert!(
        expr_contains_op(&constraint, &ChcOp::Le) && expr_contains_op(&constraint, &ChcOp::Ge),
        "bounded atoms 0 <= f <= min(x,y) expected: {rendered}"
    );
}

/// Variable shift amounts also get bounded facts (and the refinement flag).
#[test]
fn lazy_bitwise_variable_shift_emits_bounded_atoms_word_bv() {
    let mut p = ChcProblem::new();
    let inv = p.declare_predicate("inv", vec![ChcSort::BitVec(32)]);
    let x = ChcVar::new("x", ChcSort::BitVec(32));
    let s = ChcVar::new("s", ChcSort::BitVec(32));
    let shr = ChcExpr::Op(
        ChcOp::BvLShr,
        vec![
            Arc::new(ChcExpr::var(x.clone())),
            Arc::new(ChcExpr::var(s.clone())),
        ],
    );
    p.add_clause(HornClause::new(
        ClauseBody::new(vec![], None),
        ClauseHead::Predicate(inv, vec![shr]),
    ));

    let mut map = BvIntMap::new();
    let transformed = abstract_problem(&p, &mut map, false, false);
    assert!(
        map.had_bitwise_uf_fallback,
        "variable shifts must be flagged for refinement on demand"
    );
    let constraint = transformed.clauses()[0]
        .body
        .constraint
        .clone()
        .expect("bounded atoms must be conjoined into the clause constraint");
    let rendered = format!("{constraint}");
    assert!(
        rendered.contains("__bv2int_bvlshr"),
        "bounds must mention the shift UF result: {rendered}"
    );
    // Logical right shift never increases the value: f <= x must be present.
    assert!(
        expr_contains_op(&constraint, &ChcOp::Le),
        "f <= x bound expected: {rendered}"
    );
}

/// Kill-switch: with lazy bounds disabled, UF fallback stays unconstrained
/// (the pre-WORD-BV behavior).
#[test]
fn lazy_bitwise_bounds_kill_switch_word_bv() {
    let mut p = ChcProblem::new();
    let inv = p.declare_predicate("inv", vec![ChcSort::BitVec(64)]);
    let x = ChcVar::new("x", ChcSort::BitVec(64));
    let y = ChcVar::new("y", ChcSort::BitVec(64));
    let and_xy = ChcExpr::Op(
        ChcOp::BvAnd,
        vec![
            Arc::new(ChcExpr::var(x.clone())),
            Arc::new(ChcExpr::var(y.clone())),
        ],
    );
    p.add_clause(HornClause::new(
        ClauseBody::new(vec![], None),
        ClauseHead::Predicate(inv, vec![and_xy]),
    ));

    let mut map = BvIntMap::new();
    map.lazy_bitwise_bounds = false;
    let transformed = abstract_problem(&p, &mut map, false, false);
    assert!(map.had_bitwise_uf_fallback);
    // Only the head-arg range constraint is added; no bitwise bound atoms.
    let constraint = transformed.clauses()[0].body.constraint.clone();
    let rendered = constraint.map(|c| format!("{c}")).unwrap_or_default();
    assert!(
        !rendered.contains("__bv2int_bvand") || !rendered.contains("<="),
        "disabled lazy bounds must not emit bitwise bound atoms: {rendered}"
    );
}

/// Control: a wide constant below 2^95 still transforms exactly (unchanged).
#[test]
fn exact_mode_constant_below_2_pow_95_still_transforms() {
    let mut p = ChcProblem::new();
    let inv = p.declare_predicate("inv", vec![ChcSort::BitVec(128)]);
    let x = ChcVar::new("x", ChcSort::BitVec(128));
    let representable = ChcExpr::BitVec((1u128 << 94) + 7, 128);
    p.add_clause(HornClause::new(
        ClauseBody::new(vec![], Some(ChcExpr::eq(ChcExpr::var(x), representable))),
        ClauseHead::Predicate(
            inv,
            vec![ChcExpr::var(ChcVar::new("x", ChcSort::BitVec(128)))],
        ),
    ));
    let r = Box::new(BvToIntAbstractor::new()).transform(p);
    assert_eq!(
        r.problem.predicates()[0].arg_sorts,
        vec![ChcSort::Int],
        "a two-limb-representable constant must still abstract to Int"
    );
}
