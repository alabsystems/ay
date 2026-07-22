// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use std::sync::Arc;

use super::*;

fn contains_subexpr(expr: &ChcExpr, needle: &ChcExpr) -> bool {
    if expr == needle {
        return true;
    }
    match expr {
        ChcExpr::Op(_, args) | ChcExpr::PredicateApp(_, _, args) | ChcExpr::FuncApp(_, _, args) => {
            args.iter().any(|arg| contains_subexpr(arg, needle))
        }
        ChcExpr::ConstArray(_, value) => contains_subexpr(value, needle),
        _ => false,
    }
}

#[test]
fn no_bv_passthrough() {
    let p = ChcProblem::new();
    let r = Box::new(BvToBoolBitBlaster::new()).transform(p);
    assert_eq!(r.problem.predicates().len(), 0);
}

#[test]
fn bv8_expanded_to_8_bools() {
    let mut p = ChcProblem::new();
    p.declare_predicate("inv", vec![ChcSort::BitVec(8), ChcSort::Int]);
    let r = Box::new(BvToBoolBitBlaster::new()).transform(p);
    let sorts = &r.problem.predicates()[0].arg_sorts;
    // 8 Bool args + 1 Int arg = 9
    assert_eq!(sorts.len(), 9);
    assert!(sorts[..8].iter().all(|s| *s == ChcSort::Bool));
    assert_eq!(sorts[8], ChcSort::Int);
}

#[test]
fn bv32_expanded_to_32_bools() {
    let mut p = ChcProblem::new();
    p.declare_predicate("inv", vec![ChcSort::BitVec(32)]);
    let r = Box::new(BvToBoolBitBlaster::new()).transform(p);
    assert_eq!(r.problem.predicates()[0].arg_sorts.len(), 32);
    assert!(r.problem.predicates()[0]
        .arg_sorts
        .iter()
        .all(|s| *s == ChcSort::Bool));
}

#[test]
fn bv64_expanded_to_64_bools() {
    // #7975: BV64 is now within the bitblast threshold (64) and should be expanded.
    let mut p = ChcProblem::new();
    p.declare_predicate("inv", vec![ChcSort::BitVec(64)]);
    let r = Box::new(BvToBoolBitBlaster::new()).transform(p);
    assert_eq!(r.problem.predicates()[0].arg_sorts.len(), 64);
    assert!(r.problem.predicates()[0]
        .arg_sorts
        .iter()
        .all(|s| *s == ChcSort::Bool));
}

#[test]
fn bv128_only_passthrough() {
    // When ALL BV args exceed the threshold (64), the transformer should skip entirely.
    let mut p = ChcProblem::new();
    p.declare_predicate("inv", vec![ChcSort::BitVec(128)]);
    let r = Box::new(BvToBoolBitBlaster::new()).transform(p);
    assert_eq!(
        r.problem.predicates()[0].arg_sorts,
        vec![ChcSort::BitVec(128)]
    );
}

#[test]
fn mixed_bv8_bv64_all_bitblasted() {
    // #7975: Both BV8 and BV64 are within the threshold (64) — both bit-blasted.
    let mut p = ChcProblem::new();
    p.declare_predicate(
        "inv",
        vec![ChcSort::BitVec(8), ChcSort::BitVec(64), ChcSort::Int],
    );
    let r = Box::new(BvToBoolBitBlaster::new()).transform(p);
    let sorts = &r.problem.predicates()[0].arg_sorts;
    // 8 Bools (from BV8) + 64 Bools (from BV64) + 1 Int = 73
    assert_eq!(sorts.len(), 73);
    assert!(sorts[..8].iter().all(|s| *s == ChcSort::Bool));
    assert!(sorts[8..72].iter().all(|s| *s == ChcSort::Bool));
    assert_eq!(sorts[72], ChcSort::Int);
}

#[test]
fn mixed_bv32_bv64_all_bitblasted() {
    // #7975: Both BV32 and BV64 are within the threshold — both bit-blasted.
    let mut p = ChcProblem::new();
    p.declare_predicate("inv", vec![ChcSort::BitVec(32), ChcSort::BitVec(64)]);
    let r = Box::new(BvToBoolBitBlaster::new()).transform(p);
    let sorts = &r.problem.predicates()[0].arg_sorts;
    // 32 Bools (from BV32) + 64 Bools (from BV64) = 96
    assert_eq!(sorts.len(), 96);
    assert!(sorts.iter().all(|s| *s == ChcSort::Bool));
}

#[test]
fn selective_bitblast_bv8_bv128_mixed() {
    // #7975: BV8 is bitblasted, BV128 exceeds threshold and is preserved.
    let mut p = ChcProblem::new();
    p.declare_predicate(
        "inv",
        vec![
            ChcSort::BitVec(128),
            ChcSort::BitVec(8),
            ChcSort::BitVec(128),
        ],
    );
    let r = Box::new(BvToBoolBitBlaster::new()).transform(p);
    let sorts = &r.problem.predicates()[0].arg_sorts;
    // 1 BitVec(128) + 8 Bools + 1 BitVec(128) = 10
    assert_eq!(sorts.len(), 10);
    assert_eq!(sorts[0], ChcSort::BitVec(128));
    assert!(sorts[1..9].iter().all(|s| *s == ChcSort::Bool));
    assert_eq!(sorts[9], ChcSort::BitVec(128));
}

#[test]
fn multiple_bv64_all_bitblasted() {
    // #7975: Multiple BV64 args should all be bit-blasted now.
    let mut p = ChcProblem::new();
    p.declare_predicate(
        "inv",
        vec![ChcSort::BitVec(64), ChcSort::BitVec(8), ChcSort::BitVec(64)],
    );
    let r = Box::new(BvToBoolBitBlaster::new()).transform(p);
    let sorts = &r.problem.predicates()[0].arg_sorts;
    // 64 Bools + 8 Bools + 64 Bools = 136
    assert_eq!(sorts.len(), 136);
    assert!(sorts.iter().all(|s| *s == ChcSort::Bool));
}

#[test]
fn back_translation_restores_bv_sorts() {
    let mut map = BvBoolMap::new();
    let pid = PredicateId::new(0);
    map.pred_original_sorts
        .insert(pid, vec![ChcSort::BitVec(8), ChcSort::Int]);
    map.pred_arg_bitblasted.insert(pid, vec![true, false]);

    let mut inv = InvariantModel::new();
    let mut vars = Vec::new();
    for i in 0..8 {
        vars.push(ChcVar::new(format!("x0_b{i}"), ChcSort::Bool));
    }
    vars.push(ChcVar::new("x1", ChcSort::Int));
    inv.set(pid, PredicateInterpretation::new(vars, ChcExpr::Bool(true)));

    let result = reconstruct_bv_invariant(&inv, &map);
    let interp = result.get(&pid).unwrap();
    // Should have 2 vars: one BV(8) and one Int
    assert_eq!(interp.vars.len(), 2);
    assert_eq!(interp.vars[0].sort, ChcSort::BitVec(8));
    assert_eq!(interp.vars[1].sort, ChcSort::Int);
}

#[test]
fn back_translation_selective_mixed_bv8_bv64() {
    // #7006/#7019: Back-translation with mixed bit-blasted and non-bit-blasted args.
    let mut map = BvBoolMap::new();
    let pid = PredicateId::new(0);
    map.pred_original_sorts.insert(
        pid,
        vec![ChcSort::BitVec(8), ChcSort::BitVec(64), ChcSort::Int],
    );
    // BV8 was bit-blasted, BV64 was not, Int was not.
    map.pred_arg_bitblasted
        .insert(pid, vec![true, false, false]);

    let mut inv = InvariantModel::new();
    let mut vars = Vec::new();
    // 8 Bool vars for the bit-blasted BV8
    for i in 0..8 {
        vars.push(ChcVar::new(format!("x0_b{i}"), ChcSort::Bool));
    }
    // 1 BV64 var (not bit-blasted, passed through)
    vars.push(ChcVar::new("x1", ChcSort::BitVec(64)));
    // 1 Int var
    vars.push(ChcVar::new("x2", ChcSort::Int));
    inv.set(pid, PredicateInterpretation::new(vars, ChcExpr::Bool(true)));

    let result = reconstruct_bv_invariant(&inv, &map);
    let interp = result.get(&pid).unwrap();
    // Should have 3 vars: BV(8), BV(64), Int
    assert_eq!(interp.vars.len(), 3);
    assert_eq!(interp.vars[0].sort, ChcSort::BitVec(8));
    assert_eq!(interp.vars[1].sort, ChcSort::BitVec(64));
    assert_eq!(interp.vars[2].sort, ChcSort::Int);
}

#[test]
fn transform_defers_only_opaque_predicate_positions_for_later_abstraction_8739() {
    let mut p = ChcProblem::new();
    let mixed = p.declare_predicate("mixed", vec![ChcSort::BitVec(8), ChcSort::BitVec(8)]);
    let safe = p.declare_predicate("safe", vec![ChcSort::BitVec(8)]);

    let x = ChcExpr::var(ChcVar::new("x", ChcSort::BitVec(8)));
    let y = ChcExpr::var(ChcVar::new("y", ChcSort::BitVec(8)));
    let arr = ChcExpr::var(ChcVar::new(
        "arr",
        ChcSort::Array(Box::new(ChcSort::BitVec(32)), Box::new(ChcSort::BitVec(8))),
    ));
    let i = ChcExpr::var(ChcVar::new("i", ChcSort::BitVec(32)));
    let sel = ChcExpr::Op(ChcOp::Select, vec![Arc::new(arr), Arc::new(i)]);

    p.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::Bool(true)),
        ClauseHead::Predicate(mixed, vec![x, sel.clone()]),
    ));
    p.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::Bool(true)),
        ClauseHead::Predicate(safe, vec![y]),
    ));

    let transformed = Box::new(BvToBoolBitBlaster::new()).transform(p).problem;
    let mut expected_mixed_sorts = vec![ChcSort::Bool; 8];
    expected_mixed_sorts.push(ChcSort::BitVec(8));
    assert_eq!(
        transformed.predicates()[mixed.index()].arg_sorts,
        expected_mixed_sorts,
        "only the opaque BV predicate position should be deferred"
    );
    assert_eq!(
        transformed.predicates()[safe.index()].arg_sorts,
        vec![ChcSort::Bool; 8],
        "an unrelated safe BV predicate should still be bit-blasted"
    );
    match &transformed.clauses()[0].head {
        ClauseHead::Predicate(_, args) => {
            assert_eq!(args.len(), 9);
            assert!(
                args[..8]
                    .iter()
                    .all(|arg| matches!(arg, ChcExpr::Var(v) if v.sort == ChcSort::Bool)),
                "the safe predicate position should still expand to Bool bits"
            );
            assert_eq!(args[8], sel);
        }
        ClauseHead::False => panic!("expected predicate head after selective transform"),
    }
}

#[test]
fn transform_preserves_bv2nat_select_constraint_when_bitblasting_other_args_8739() {
    let mut p = ChcProblem::new();
    let inv = p.declare_predicate("inv", vec![ChcSort::BitVec(8)]);

    let x = ChcExpr::var(ChcVar::new("x", ChcSort::BitVec(8)));
    let arr = ChcExpr::var(ChcVar::new(
        "arr",
        ChcSort::Array(Box::new(ChcSort::BitVec(32)), Box::new(ChcSort::BitVec(32))),
    ));
    let i = ChcExpr::var(ChcVar::new("i", ChcSort::BitVec(32)));
    let sel = ChcExpr::Op(ChcOp::Select, vec![Arc::new(arr), Arc::new(i)]);
    let bv2nat_sel = ChcExpr::Op(ChcOp::Bv2Nat, vec![Arc::new(sel)]);
    let constraint = ChcExpr::eq(bv2nat_sel.clone(), ChcExpr::Int(0));

    p.add_clause(HornClause::new(
        ClauseBody::constraint(constraint),
        ClauseHead::Predicate(inv, vec![x]),
    ));

    let transformed = Box::new(BvToBoolBitBlaster::new()).transform(p).problem;
    assert_eq!(
        transformed.predicates()[0].arg_sorts.len(),
        8,
        "safe BV predicate args should still be bit-blasted"
    );
    let transformed_constraint = transformed.clauses()[0]
        .body
        .constraint
        .as_ref()
        .expect("constraint should be preserved");
    assert!(
        contains_subexpr(transformed_constraint, &bv2nat_sel),
        "Bv2Nat(select(...)) must remain intact when helper-level lowering declines"
    );
}

#[test]
fn transform_preserves_int2bv_constraint_when_bitblasting_safe_args_8739() {
    let mut p = ChcProblem::new();
    let inv = p.declare_predicate("inv", vec![ChcSort::BitVec(8), ChcSort::BitVec(8)]);

    let x = ChcExpr::var(ChcVar::new("x", ChcSort::BitVec(8)));
    let y = ChcExpr::var(ChcVar::new("y", ChcSort::BitVec(8)));
    let n = ChcExpr::var(ChcVar::new("n", ChcSort::Int));
    let int2bv = ChcExpr::Op(ChcOp::Int2Bv(8), vec![Arc::new(n)]);
    let constraint = ChcExpr::eq(int2bv.clone(), y.clone());

    p.add_clause(HornClause::new(
        ClauseBody::constraint(constraint),
        ClauseHead::Predicate(inv, vec![x, y]),
    ));

    let transformed = Box::new(BvToBoolBitBlaster::new()).transform(p).problem;
    assert_eq!(
        transformed.predicates()[inv.index()].arg_sorts,
        vec![ChcSort::Bool; 16],
        "safe BV predicate args should still bit-blast around preserved Int2Bv constraints"
    );
    let transformed_constraint = transformed.clauses()[0]
        .body
        .constraint
        .as_ref()
        .expect("constraint should be preserved");
    assert!(
        contains_subexpr(transformed_constraint, &int2bv),
        "Int2Bv(...) must remain intact when BV-to-Bool lowering declines it"
    );
}

/// Group the `__bb_div…` havoc variables of `expr` by their prefix (the name up
/// to the trailing `_b<i>` bit index).
fn div_havoc_groups(expr: &ChcExpr) -> std::collections::BTreeSet<String> {
    expr.vars()
        .into_iter()
        .filter(|v| v.name.starts_with("__bb_div"))
        .filter_map(|v| v.name.rsplit_once("_b").map(|(p, _)| p.to_string()))
        .collect()
}

/// SOUNDNESS regression (2026-07-08, wishlist rank 2): two DIFFERENT division
/// subterms in one clause must NOT share havoc bits. The old fixed `__bb_div`
/// prefix aliased them — `bvudiv(a,2) = bvudiv(c,d)` blasted to a tautology, a
/// phantom equality that can flip a satisfiable query to UNSAT (false-Safe).
#[test]
fn distinct_divisions_get_distinct_havoc_bits() {
    let mut p = ChcProblem::new();
    let inv = p.declare_predicate("inv", vec![ChcSort::BitVec(8)]);
    let a = ChcExpr::var(ChcVar::new("a", ChcSort::BitVec(8)));
    let c = ChcExpr::var(ChcVar::new("c", ChcSort::BitVec(8)));
    let d = ChcExpr::var(ChcVar::new("d", ChcSort::BitVec(8)));
    // Non-power-of-two divisor: the rank-3 pow2 rewrite must NOT fire (it would
    // turn the division into a shift before the blaster ever sees it).
    let div1 = ChcExpr::Op(
        ChcOp::BvUDiv,
        vec![Arc::new(a.clone()), Arc::new(ChcExpr::BitVec(3, 8))],
    );
    let div2 = ChcExpr::Op(ChcOp::BvUDiv, vec![Arc::new(c), Arc::new(d)]);
    let constraint = ChcExpr::eq(div1, div2);
    p.add_clause(HornClause::new(
        ClauseBody::new(vec![], Some(constraint)),
        ClauseHead::Predicate(inv, vec![a]),
    ));
    let r = Box::new(BvToBoolBitBlaster::new()).transform(p);
    let transformed = r.problem.clauses()[0]
        .body
        .constraint
        .clone()
        .expect("transformed clause keeps its constraint");
    let groups = div_havoc_groups(&transformed);
    assert!(
        groups.len() >= 2,
        "two structurally different divisions must use two havoc groups, got {groups:?}"
    );
}

/// Congruence guard: two occurrences of the SAME division share their havoc
/// bits (structural keying, not per-occurrence freshening) — `t = t` for a
/// division term stays provable.
#[test]
fn identical_divisions_share_havoc_bits() {
    let mut p = ChcProblem::new();
    let inv = p.declare_predicate("inv", vec![ChcSort::BitVec(8)]);
    let a = ChcExpr::var(ChcVar::new("a", ChcSort::BitVec(8)));
    let mk_div = || {
        // Non-pow2 divisor: keeps the division op past the rank-3 rewrite.
        ChcExpr::Op(
            ChcOp::BvUDiv,
            vec![
                Arc::new(ChcExpr::var(ChcVar::new("a", ChcSort::BitVec(8)))),
                Arc::new(ChcExpr::BitVec(3, 8)),
            ],
        )
    };
    // The SAME division term used in two DIFFERENT atoms (an `eq(t, t)` shape
    // would fold away before blasting) — both occurrences must share bits.
    let x = ChcExpr::var(ChcVar::new("x", ChcSort::BitVec(8)));
    let y = ChcExpr::var(ChcVar::new("y", ChcSort::BitVec(8)));
    let constraint = ChcExpr::and(
        ChcExpr::Op(ChcOp::BvULt, vec![Arc::new(mk_div()), Arc::new(x)]),
        ChcExpr::Op(ChcOp::BvULt, vec![Arc::new(mk_div()), Arc::new(y)]),
    );
    p.add_clause(HornClause::new(
        ClauseBody::new(vec![], Some(constraint)),
        ClauseHead::Predicate(inv, vec![a]),
    ));
    let r = Box::new(BvToBoolBitBlaster::new()).transform(p);
    let transformed = r.problem.clauses()[0]
        .body
        .constraint
        .clone()
        .expect("transformed clause keeps its constraint");
    let groups = div_havoc_groups(&transformed);
    assert_eq!(
        groups.len(),
        1,
        "identical division subterms must share one havoc group, got {groups:?}"
    );
}
