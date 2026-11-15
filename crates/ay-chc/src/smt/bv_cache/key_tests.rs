// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Structural BV-cache keys: linear on shared DAGs, exact, and admitting
//! exactly the terms the printed key admitted.

use super::{BvCacheKey, BvCacheKeys, BvKeyMemo};
use crate::smt::context::SmtContext;
use crate::{ChcExpr, ChcOp, ChcSort, ChcVar};
use ay_core::kani_compat::DetHashSet as FxHashSet;
use ay_core::term::TermData;
use ay_core::{Sort, TermId};
use std::sync::Arc;

fn bv(name: &str, width: u32) -> ChcExpr {
    ChcExpr::var(ChcVar::new(name, ChcSort::BitVec(width)))
}

fn op(op: ChcOp, args: Vec<ChcExpr>) -> ChcExpr {
    ChcExpr::Op(op, args.into_iter().map(Arc::new).collect())
}

/// `t(0) = x`, `t(i+1) = t(i) + (t(i) ^ k(i))`, every `t(i)` one shared node:
/// `depth + 1` distinct BV terms whose tree expansion has `2^depth` leaves.
fn shared_chain(depth: usize, last_constant: u128) -> ChcExpr {
    let mut t = Arc::new(bv("x", 8));
    for i in 0..depth {
        let k = if i + 1 == depth {
            last_constant
        } else {
            (i as u128 % 250) + 1
        };
        let mixed = Arc::new(ChcExpr::Op(
            ChcOp::BvXor,
            vec![Arc::clone(&t), Arc::new(ChcExpr::BitVec(k, 8))],
        ));
        t = Arc::new(ChcExpr::Op(ChcOp::BvAdd, vec![Arc::clone(&t), mixed]));
    }
    Arc::unwrap_or_clone(t)
}

fn shared_atom(depth: usize, last_constant: u128) -> ChcExpr {
    op(
        ChcOp::BvULe,
        vec![shared_chain(depth, last_constant), bv("y", 8)],
    )
}

fn key_of(ctx: &SmtContext, keys: &mut BvCacheKeys, term: TermId) -> Option<BvCacheKey> {
    ctx.bv_cache_key(keys, term, &mut BvKeyMemo::default())
}

/// Every distinct term reachable from `root` (root included).
fn closure(ctx: &SmtContext, root: TermId) -> Vec<TermId> {
    let mut seen = FxHashSet::default();
    let mut order = Vec::new();
    let mut stack = vec![root];
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        order.push(term);
        match ctx.terms.get(term) {
            TermData::Not(inner) => stack.push(*inner),
            TermData::Ite(c, t, e) => stack.extend([*c, *t, *e]),
            TermData::App(_, args) => stack.extend(args.iter().copied()),
            _ => {}
        }
    }
    order
}

/// The old key printed this atom's `2^64`-leaf tree once per keyed term; the
/// structural key visits each distinct term once.
#[test]
#[ntest::timeout(60_000)]
fn a_shared_dag_is_keyed_in_one_visit_per_distinct_term() {
    let mut ctx = SmtContext::new();
    let atom = ctx.convert_expr(&shared_atom(64, 7));
    let mut keys = BvCacheKeys::default();
    let mut memo = BvKeyMemo::default();

    let key = ctx.bv_cache_key(&mut keys, atom, &mut memo);

    assert!(
        key.is_some(),
        "a BV comparison over CHC variables is cacheable"
    );
    let distinct = closure(&ctx, atom).len();
    assert!(
        distinct < 300,
        "the chain converts to a small DAG ({distinct} terms)"
    );
    assert_eq!(
        memo.len(),
        distinct,
        "each distinct term is keyed exactly once"
    );
    assert!(keys.len() <= distinct);
    // Keying every sub-term again (what a signature over all Tseitin atoms
    // does) only reads the memo.
    let signature = ctx.bv_cache_signature(&mut keys, closure(&ctx, atom), &mut memo);
    assert_eq!(memo.len(), distinct);
    assert_eq!(signature.len(), keys.len());
}

/// Keys name structure, not `TermId`s: the same term rebuilt after a reset
/// (a fresh `TermStore`, different ids) gets the same key; changing one
/// constant at the bottom of the shared chain changes it.
#[test]
fn equal_keys_mean_equal_terms_across_term_stores() {
    let mut keys = BvCacheKeys::default();
    let mut first = SmtContext::new();
    let atom = first.convert_expr(&shared_atom(40, 7));
    let key = key_of(&first, &mut keys, atom);

    let mut second = SmtContext::new();
    for i in 0..17 {
        let _ = second.convert_expr(&bv(&format!("padding_{i}"), 8));
    }
    let same = second.convert_expr(&shared_atom(40, 7));
    let other = second.convert_expr(&shared_atom(40, 9));
    assert_ne!(atom, same, "the padding shifts the term ids");

    assert_eq!(key_of(&second, &mut keys, same), key);
    assert_ne!(key_of(&second, &mut keys, other), key);
    assert!(key.is_some());
}

/// The printed key named variables without their sort below the root, so
/// `x <= y` over BV8 and over BV16 printed identically (`Bool::(bvule x y)`).
/// Structural keys carry every node's sort.
#[test]
fn variable_sorts_below_the_root_are_part_of_the_key() {
    let mut keys = BvCacheKeys::default();
    let mut ctx = SmtContext::new();
    let narrow = ctx.convert_expr(&op(ChcOp::BvULe, vec![bv("x", 8), bv("y", 8)]));
    let wide = ctx.convert_expr(&op(ChcOp::BvULe, vec![bv("x", 16), bv("y", 16)]));

    let narrow_key = key_of(&ctx, &mut keys, narrow);
    let wide_key = key_of(&ctx, &mut keys, wide);

    assert!(narrow_key.is_some() && wide_key.is_some());
    assert_ne!(narrow_key, wide_key);
}

/// Soundness regression: with the printed key, `x <= y` over BV8 and over
/// BV16 shared one key, so after `reset` the cache handed both atoms ONE
/// predicate literal and this satisfiable query came back `Unsat` (measured
/// on 8e2f8867b: fresh `sat`, reused `UNSAT`; likewise for `x + y = z`).
/// Queries do carry one name at two sorts (`SortUniqueRenaming` exists for
/// exactly that).
#[test]
#[serial_test::serial]
fn a_reused_cache_keeps_one_name_at_two_sorts_apart() {
    use crate::smt::SmtResult;

    let queries = [
        ChcExpr::and(
            op(ChcOp::BvULe, vec![bv("x", 8), bv("y", 8)]),
            ChcExpr::not(op(ChcOp::BvULe, vec![bv("x", 16), bv("y", 16)])),
        ),
        ChcExpr::and(
            ChcExpr::eq(op(ChcOp::BvAdd, vec![bv("x", 8), bv("y", 8)]), bv("z", 8)),
            ChcExpr::not(ChcExpr::eq(
                op(ChcOp::BvAdd, vec![bv("x", 16), bv("y", 16)]),
                bv("z", 16),
            )),
        ),
    ];
    for query in &queries {
        let mut ctx = SmtContext::new();
        let first = ctx.check_sat(query);
        assert!(
            matches!(first, SmtResult::Sat(_)),
            "fresh: {first:?} on {query}"
        );
        ctx.reset();
        let reused = ctx.check_sat(query);
        assert!(
            matches!(reused, SmtResult::Sat(_)),
            "the reused BV cache must not refute a satisfiable query: {reused:?} on {query}"
        );
    }
}

/// Only the canonical variable of a CHC name is keyed: another term store
/// variable (an auxiliary) has no query-independent meaning.
#[test]
fn a_variable_outside_the_canonical_var_map_has_no_key() {
    let mut keys = BvCacheKeys::default();
    let mut ctx = SmtContext::new();
    let canonical = ctx.convert_expr(&bv("x", 8));
    let aux = ctx.terms.mk_var("aux_not_a_chc_var", Sort::bitvec(8));

    assert!(key_of(&ctx, &mut keys, canonical).is_some());
    assert_eq!(key_of(&ctx, &mut keys, aux), None);
}

/// A `Let` node is not keyed: the printed key read it as its body, which
/// would give two different nodes one key (the CHC layer never mints `Let`).
#[test]
fn a_let_node_has_no_key_of_its_own() {
    let mut keys = BvCacheKeys::default();
    let mut ctx = SmtContext::new();
    let x = ctx.convert_expr(&bv("x", 8));
    let body = ctx.convert_expr(&op(ChcOp::BvULe, vec![bv("x", 8), bv("y", 8)]));
    let let_term = ctx.terms.mk_let(vec![("x_BitVec8".to_string(), x)], body);

    assert!(key_of(&ctx, &mut keys, body).is_some());
    assert_eq!(key_of(&ctx, &mut keys, let_term), None);
}

/// Admission is the old key's: a term is keyed iff it is built from
/// canonical variables and constants by operators `term_to_chc_expr`
/// decodes (extract, extensions and rotations stay out).
#[test]
fn admission_matches_the_decoder_the_printed_key_used() {
    let x = bv("x", 8);
    let y = bv("y", 8);
    let i = ChcExpr::var(ChcVar::new("i", ChcSort::Int));
    let array = |name: &str| {
        ChcExpr::var(ChcVar::new(
            name,
            ChcSort::Array(Box::new(ChcSort::BitVec(8)), Box::new(ChcSort::BitVec(8))),
        ))
    };
    let corpus = vec![
        op(ChcOp::BvAdd, vec![x.clone(), y.clone()]),
        op(ChcOp::BvULt, vec![x.clone(), ChcExpr::BitVec(3, 8)]),
        op(ChcOp::BvConcat, vec![x.clone(), y.clone()]),
        op(ChcOp::BvNot, vec![x.clone()]),
        op(ChcOp::Bv2Nat, vec![x.clone()]),
        op(ChcOp::Int2Bv(8), vec![i.clone()]),
        op(ChcOp::BvExtract(3, 0), vec![x.clone()]),
        op(ChcOp::BvZeroExtend(8), vec![x.clone()]),
        op(ChcOp::BvSignExtend(8), vec![x.clone()]),
        op(ChcOp::BvRotateLeft(1), vec![x.clone()]),
        ChcExpr::eq(
            op(ChcOp::BvExtract(3, 0), vec![x.clone()]),
            ChcExpr::BitVec(1, 4),
        ),
        ChcExpr::and(
            ChcExpr::eq(x.clone(), y.clone()),
            op(ChcOp::BvSLe, vec![x.clone(), ChcExpr::BitVec(9, 8)]),
        ),
        ChcExpr::not(ChcExpr::eq(x.clone(), ChcExpr::BitVec(0, 8))),
        ChcExpr::ite(
            ChcExpr::eq(x.clone(), y.clone()),
            x.clone(),
            op(ChcOp::BvMul, vec![x.clone(), y.clone()]),
        ),
        ChcExpr::eq(ChcExpr::select(array("a"), x.clone()), y.clone()),
        ChcExpr::eq(ChcExpr::store(array("a"), x.clone(), y.clone()), array("b")),
        ChcExpr::le(ChcExpr::mod_op(i.clone(), ChcExpr::int(3)), ChcExpr::int(2)),
        ChcExpr::lt(
            ChcExpr::add(i.clone(), ChcExpr::int(1)),
            ChcExpr::Real(7, 2),
        ),
    ];
    let mut ctx = SmtContext::new();
    let mut keys = BvCacheKeys::default();
    let mut memo = BvKeyMemo::default();
    let mut keyed = 0;
    for expr in &corpus {
        let term = ctx.convert_expr(expr);
        for sub in closure(&ctx, term) {
            let key = ctx.bv_cache_key(&mut keys, sub, &mut memo);
            assert_eq!(
                key.is_some(),
                ctx.term_to_chc_expr(sub).is_some(),
                "admission differs from the decoder on {:?} (from {expr})",
                ctx.terms.get(sub),
            );
            keyed += usize::from(key.is_some());
        }
    }
    assert!(
        keyed > 20,
        "the corpus exercises the admitted grammar ({keyed})"
    );
}

/// End to end: a query over the shared chain bit-blasts, captures its cache,
/// and after `reset` (a fresh `TermStore`) replays it without generating a
/// single new BV clause. With the printed key the first `check_sat` never
/// finished computing its signature.
#[test]
#[serial_test::serial]
#[ntest::timeout(60_000)]
fn a_shared_dag_query_reuses_its_bv_cache_after_reset() {
    use crate::smt::check_sat::{bv_new_clause_count_for_tests, reset_reuse_counters_for_tests};
    use crate::smt::SmtResult;

    reset_reuse_counters_for_tests();
    let query = ChcExpr::and(
        ChcExpr::eq(bv("x", 8), ChcExpr::BitVec(5, 8)),
        shared_atom(48, 7),
    );
    let mut ctx = SmtContext::new();

    let first = ctx.check_sat(&query);
    assert!(matches!(first, SmtResult::Sat(_)), "got {first:?}");
    let first_clauses = bv_new_clause_count_for_tests();
    assert!(first_clauses > 0, "the chain must be bit-blasted");

    ctx.reset();
    let second = ctx.check_sat(&query);
    assert!(matches!(second, SmtResult::Sat(_)), "got {second:?}");
    assert_eq!(
        bv_new_clause_count_for_tests(),
        first_clauses,
        "the structural signature matches after reset and the cache is replayed",
    );
}
