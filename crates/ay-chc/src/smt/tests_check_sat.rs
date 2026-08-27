// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Integration tests for check_sat BV caching and theory dispatch.
//!
//! Extracted from check_sat.rs inline tests.

use super::bv_cache::{
    bv_cache_cap_clear_count_for_tests, bv_cache_peak_entries_for_tests,
    reset_bv_cache_peak_for_tests,
};
use super::check_sat::{
    bv_bitblast_count_for_tests, bv_new_clause_count_for_tests, cached_bv_clause_count_for_tests,
    clear_bitblast_max_total_bits_override_for_tests, max_bv_width, reset_reuse_counters_for_tests,
    set_bitblast_dynamic_abort_override_for_tests, set_bitblast_max_total_bits_override_for_tests,
    total_bv_bits,
};
use super::context::{SmtContext, MAX_PERSISTENT_CACHE_ENTRIES};
use super::types::SmtResult;
use crate::{ChcExpr, ChcOp, ChcSort, ChcVar};
use serial_test::serial;
use std::sync::Arc;

/// The `2^64` divisor a wide BV64 modulus normalizes to. `ChcExpr::Int` is i64,
/// so `2^64` cannot be a literal — it is a product tree `2^32 * 2^32`, which is
/// exactly the shape W1-1B preserves and routes to the BigInt executor.
fn pow2_64() -> ChcExpr {
    ChcExpr::mul(
        ChcExpr::int(4_294_967_296_i64),
        ChcExpr::int(4_294_967_296_i64),
    )
}

/// `mod(x, 2^64)` — the wide-constant modulus a BV64 value carries after
/// unsigned normalization (`normalize_unsigned_if_wide`, #7006).
fn mod_pow2_64(x: ChcExpr) -> ChcExpr {
    ChcExpr::Op(ChcOp::Mod, vec![Arc::new(x), Arc::new(pow2_64())])
}

#[test]
#[serial]
fn test_check_sat_skips_bv_setup_for_pure_lia_6614() {
    reset_reuse_counters_for_tests();

    let mut ctx = SmtContext::new();
    let x = ChcVar::new("x", ChcSort::Int);
    let query = ChcExpr::eq(ChcExpr::var(x), ChcExpr::Int(1));

    let result = ctx.check_sat(&query);

    assert!(
        matches!(result, SmtResult::Sat(_)),
        "expected pure arithmetic query to be SAT, got {result:?}",
    );
    assert_eq!(
        bv_bitblast_count_for_tests(),
        0,
        "pure arithmetic query should not enter BV bit-blasting setup",
    );
}

#[test]
#[serial]
fn test_check_sat_runs_bv_setup_for_bv_query_6614() {
    reset_reuse_counters_for_tests();

    let mut ctx = SmtContext::new();
    let x = ChcVar::new("x", ChcSort::BitVec(8));
    let query = ChcExpr::eq(ChcExpr::var(x), ChcExpr::BitVec(1, 8));

    let result = ctx.check_sat(&query);

    assert!(
        matches!(result, SmtResult::Sat(_)),
        "expected BV equality query to be SAT, got {result:?}",
    );
    assert!(
        bv_bitblast_count_for_tests() >= 1,
        "BV query should enter BV bit-blasting setup",
    );
}

#[test]
fn test_check_sat_mixed_width_bvsle_returns_unknown_not_panic() {
    let mut ctx = SmtContext::new();
    let x32 = ChcVar::new("x", ChcSort::BitVec(32));
    let query = ChcExpr::Op(
        crate::ChcOp::BvSLe,
        vec![Arc::new(ChcExpr::BitVec(1, 8)), Arc::new(ChcExpr::var(x32))],
    );

    let result = ctx.check_sat(&query);

    assert!(
        matches!(result, SmtResult::Unknown),
        "mixed-width BV comparison should degrade to Unknown, got {result:?}",
    );
}

#[test]
fn test_check_sat_executor_rejects_bv_arithmetic_lt_without_native_fallback() {
    let mut ctx = SmtContext::new();
    let x = ChcVar::new("x", ChcSort::BitVec(8));
    let arr = ChcVar::new(
        "a",
        ChcSort::Array(Box::new(ChcSort::BitVec(8)), Box::new(ChcSort::Bool)),
    );
    let query = ChcExpr::Op(
        crate::ChcOp::And,
        vec![
            Arc::new(ChcExpr::eq(
                ChcExpr::select(ChcExpr::var(arr), ChcExpr::var(x.clone())),
                ChcExpr::Bool(true),
            )),
            Arc::new(ChcExpr::Op(
                crate::ChcOp::Lt,
                vec![Arc::new(ChcExpr::var(x)), Arc::new(ChcExpr::BitVec(1, 8))],
            )),
        ],
    );

    let result = ctx.check_sat(&query);

    assert!(
        matches!(result, SmtResult::Unknown),
        "executor-required BV arithmetic comparison must not fall through to native BV solving, got {result:?}",
    );
}

#[test]
#[serial]
fn test_check_sat_reuses_bv_clauses_after_reset_5877() {
    reset_reuse_counters_for_tests();

    let mut ctx = SmtContext::new();
    let x = ChcVar::new("x", ChcSort::BitVec(8));
    let query = ChcExpr::eq(
        ChcExpr::Op(
            crate::ChcOp::BvAdd,
            vec![
                std::sync::Arc::new(ChcExpr::var(x)),
                std::sync::Arc::new(ChcExpr::BitVec(1, 8)),
            ],
        ),
        ChcExpr::BitVec(3, 8),
    );

    let first = ctx.check_sat(&query);
    assert!(
        matches!(first, SmtResult::Sat(_)),
        "expected first BV query to be SAT, got {first:?}",
    );
    let first_new_clause_count = bv_new_clause_count_for_tests();
    assert!(
        first_new_clause_count > 0,
        "expected first BV query to generate BV clauses",
    );

    ctx.reset();

    let second = ctx.check_sat(&query);
    assert!(
        matches!(second, SmtResult::Sat(_)),
        "expected second BV query to be SAT, got {second:?}",
    );
    let second_new_clause_count = bv_new_clause_count_for_tests();
    assert_eq!(
        second_new_clause_count, first_new_clause_count,
        "expected reset()+same-query BV solve to replay cached BV clauses without new generation",
    );
}

/// Soundness regression for the #5877/#8161 incremental-BV cache on the workload
/// that actually matters: a single `SmtContext` whose `persistent_bv_cache`
/// survives `reset()` while the formula GROWS across "depths" (exactly KIND /
/// PDKIND adding transitions per BMC depth). The existing 5877 tests only cover
/// identical-query-after-reset (already sound); none exercise a growing formula.
/// A reused-context verdict of `Unsat` on a SATISFIABLE grown query is a
/// false-UNSAT (= false-SAFE = competition-disqualifying). The fresh `SmtContext`
/// is the independent oracle.
#[test]
#[serial]
fn test_check_sat_growing_formula_reuse_is_sound_vs_fresh_oracle_5877() {
    reset_reuse_counters_for_tests();

    let add_eq = |name: &str, a: u128, b: u128| -> ChcExpr {
        let v = ChcVar::new(name, ChcSort::BitVec(8));
        ChcExpr::eq(
            ChcExpr::Op(
                crate::ChcOp::BvAdd,
                vec![Arc::new(ChcExpr::var(v)), Arc::new(ChcExpr::BitVec(a, 8))],
            ),
            ChcExpr::BitVec(b, 8),
        )
    };
    let and = |args: Vec<ChcExpr>| {
        ChcExpr::Op(crate::ChcOp::And, args.into_iter().map(Arc::new).collect())
    };

    // Monotone-growing, each conjunct independently SAT (x0=2, x1=3, x2=4, x3=5).
    let c0 = add_eq("x0", 1, 3);
    let c1 = add_eq("x1", 2, 5);
    let c2 = add_eq("x2", 3, 7);
    let c3 = add_eq("x3", 4, 9);
    let queries = [
        c0.clone(),
        and(vec![c0.clone(), c1.clone()]),
        and(vec![c0.clone(), c1.clone(), c2.clone()]),
        and(vec![c0.clone(), c1.clone(), c2.clone(), c3.clone()]),
    ];

    let mut ctx = SmtContext::new();
    for (depth, q) in queries.iter().enumerate() {
        if depth > 0 {
            ctx.reset(); // persistent_bv_cache survives this (the #5877 reuse path)
        }
        let reused = ctx.check_sat(q);
        let oracle = SmtContext::new().check_sat(q);
        assert!(
            matches!(oracle, SmtResult::Sat(_)),
            "fresh oracle: growing query at depth {depth} must be SAT, got {oracle:?}",
        );
        assert!(
            !matches!(reused, SmtResult::Unsat),
            "FALSE-UNSAT at depth {depth}: the reused persistent_bv_cache context \
             returned Unsat on a SATISFIABLE growing query (fresh oracle = Sat). \
             This is the #5877/#8161 incremental-BV corruption (= false-SAFE). \
             reused={reused:?}",
        );
    }
}

#[test]
#[serial]
fn test_check_sat_does_not_reuse_bv_cache_across_width_change_5877() {
    reset_reuse_counters_for_tests();

    let mut ctx = SmtContext::new();
    let x8 = ChcVar::new("x", ChcSort::BitVec(8));
    let query8 = ChcExpr::eq(
        ChcExpr::Op(
            crate::ChcOp::BvAdd,
            vec![
                std::sync::Arc::new(ChcExpr::var(x8)),
                std::sync::Arc::new(ChcExpr::BitVec(1, 8)),
            ],
        ),
        ChcExpr::BitVec(3, 8),
    );
    let first = ctx.check_sat(&query8);
    assert!(
        matches!(first, SmtResult::Sat(_)),
        "expected 8-bit BV query to be SAT, got {first:?}",
    );
    let first_new_clause_count = bv_new_clause_count_for_tests();
    assert!(
        first_new_clause_count > 0,
        "expected 8-bit BV query to generate BV clauses",
    );

    ctx.reset();

    let x16 = ChcVar::new("x", ChcSort::BitVec(16));
    let query16 = ChcExpr::eq(
        ChcExpr::Op(
            crate::ChcOp::BvAdd,
            vec![
                std::sync::Arc::new(ChcExpr::var(x16)),
                std::sync::Arc::new(ChcExpr::BitVec(1, 16)),
            ],
        ),
        ChcExpr::BitVec(3, 16),
    );
    let second = ctx.check_sat(&query16);
    assert!(
        matches!(second, SmtResult::Sat(_)),
        "expected 16-bit BV query to be SAT, got {second:?}",
    );
    let second_new_clause_count = bv_new_clause_count_for_tests();
    assert!(
        second_new_clause_count > first_new_clause_count,
        "expected width change to force new BV clauses instead of reusing 8-bit cache",
    );
}

#[test]
#[serial]
fn test_check_sat_replaces_bv_cache_for_new_query_shape_5877() {
    let query_a = ChcExpr::eq(
        ChcExpr::Op(
            crate::ChcOp::BvAdd,
            vec![
                std::sync::Arc::new(ChcExpr::var(ChcVar::new("x", ChcSort::BitVec(8)))),
                std::sync::Arc::new(ChcExpr::BitVec(1, 8)),
            ],
        ),
        ChcExpr::BitVec(3, 8),
    );
    let query_b = ChcExpr::Op(
        crate::ChcOp::BvSLt,
        vec![
            std::sync::Arc::new(ChcExpr::var(ChcVar::new("x", ChcSort::BitVec(8)))),
            std::sync::Arc::new(ChcExpr::BitVec(10, 8)),
        ],
    );

    let mut warmed = SmtContext::new();
    let first = warmed.check_sat(&query_a);
    assert!(
        matches!(first, SmtResult::Sat(_)),
        "expected first BV query to be SAT, got {first:?}",
    );
    assert!(
        cached_bv_clause_count_for_tests(&warmed) > 0,
        "expected first BV query to populate persistent BV cache",
    );

    warmed.reset();

    let second = warmed.check_sat(&query_b);
    assert!(
        matches!(second, SmtResult::Sat(_)),
        "expected second BV query to be SAT, got {second:?}",
    );
    let warmed_cache_len = cached_bv_clause_count_for_tests(&warmed);

    let mut fresh = SmtContext::new();
    let fresh_result = fresh.check_sat(&query_b);
    assert!(
        matches!(fresh_result, SmtResult::Sat(_)),
        "expected fresh BV query to be SAT, got {fresh_result:?}",
    );
    let fresh_cache_len = cached_bv_clause_count_for_tests(&fresh);

    assert_eq!(
        warmed_cache_len, fresh_cache_len,
        "expected persistent BV cache to snapshot the latest query shape instead of accumulating prior clauses",
    );
}

/// Phase 3 Fix 4: a pairwise-distinct LIA query whose LP relaxation
/// collides used to abort to Unknown on NeedModelEqualit{y,ies} (the
/// #6091 catch-all) and only recover via the executor fallback. The
/// internal loop must now resolve it natively.
#[test]
#[serial]
fn test_model_equality_requests_resolve_natively_sat() {
    let mut ctx = SmtContext::new();
    let vars: Vec<ChcExpr> = (0..3)
        .map(|i| ChcExpr::var(ChcVar::new(format!("mdq_x{i}"), ChcSort::Int)))
        .collect();
    let mut conjuncts = Vec::new();
    for v in &vars {
        conjuncts.push(ChcExpr::ge(v.clone(), ChcExpr::Int(0)));
        conjuncts.push(ChcExpr::le(v.clone(), ChcExpr::Int(2)));
    }
    for i in 0..vars.len() {
        for j in (i + 1)..vars.len() {
            conjuncts.push(ChcExpr::ne(vars[i].clone(), vars[j].clone()));
        }
    }
    let query = ChcExpr::and_all(conjuncts);
    let result = ctx.check_sat(&query);
    assert!(
        matches!(result, SmtResult::Sat(_)),
        "3 distinct ints in [0,2] must be SAT, got {result:?}",
    );
}

/// Phase 3 Fix 4 (unsat side): 4 pairwise-distinct ints cannot fit in
/// [0,2]; must be proven UNSAT, not Unknown.
#[test]
#[serial]
fn test_model_equality_requests_resolve_natively_unsat() {
    let mut ctx = SmtContext::new();
    let vars: Vec<ChcExpr> = (0..4)
        .map(|i| ChcExpr::var(ChcVar::new(format!("mdq_y{i}"), ChcSort::Int)))
        .collect();
    let mut conjuncts = Vec::new();
    for v in &vars {
        conjuncts.push(ChcExpr::ge(v.clone(), ChcExpr::Int(0)));
        conjuncts.push(ChcExpr::le(v.clone(), ChcExpr::Int(2)));
    }
    for i in 0..vars.len() {
        for j in (i + 1)..vars.len() {
            conjuncts.push(ChcExpr::ne(vars[i].clone(), vars[j].clone()));
        }
    }
    let query = ChcExpr::and_all(conjuncts);
    let result = ctx.check_sat(&query);
    assert!(
        result.is_unsat(),
        "4 distinct ints in [0,2] must be UNSAT, got {result:?}",
    );
}

// ===== inc-13: executor-unknown-memo isolation tests =====
//
// The memo must never leak anything between queries except the
// skip-on-repeat-timeout decision. Adversarial shape: query 1 carries
// assertion A (x < 0); query 2 is SAT exactly when A is absent (x = 1,
// SAT iff query 1's assertion did not leak into query 2's solver).

#[test]
#[serial]
fn test_executor_path_no_assertion_leak_between_queries_inc13() {
    let mut ctx = SmtContext::new();
    let x = ChcVar::new("x", ChcSort::Int);

    // Query 1: x < 0 (decided fast; never memoised — only timeouts are).
    let q1 = ChcExpr::lt(ChcExpr::var(x.clone()), ChcExpr::Int(0));
    let r1 = ctx.check_sat(&q1);
    assert!(matches!(r1, SmtResult::Sat(_)), "x<0 is SAT, got {r1:?}");

    // Query 2: x = 1. SAT iff query 1's assertion (x < 0) did NOT leak.
    let q2 = ChcExpr::eq(ChcExpr::var(x), ChcExpr::Int(1));
    let r2 = ctx.check_sat(&q2);
    assert!(
        matches!(r2, SmtResult::Sat(_)),
        "x=1 must be SAT in the same context (no cross-query assertion leak), got {r2:?}",
    );
}

#[test]
#[serial]
fn test_decided_queries_are_never_memo_skipped_inc13() {
    // Re-running the exact same DECIDED query must re-answer it (the memo
    // records only timeout-class unknowns). Both verdict classes covered.
    let mut ctx = SmtContext::new();
    let x = ChcVar::new("x", ChcSort::Int);
    let sat_q = ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::Int(7));
    let unsat_q = ChcExpr::and(
        ChcExpr::lt(ChcExpr::var(x.clone()), ChcExpr::Int(0)),
        ChcExpr::gt(ChcExpr::var(x), ChcExpr::Int(0)),
    );
    for round in 0..3 {
        let rs = ctx.check_sat(&sat_q);
        assert!(
            matches!(rs, SmtResult::Sat(_)),
            "round {round}: repeated SAT query must stay SAT, got {rs:?}",
        );
        let ru = ctx.check_sat(&unsat_q);
        assert!(
            ru.is_unsat(),
            "round {round}: repeated UNSAT query must stay UNSAT, got {ru:?}",
        );
    }
}

#[test]
#[serial]
fn test_memo_survives_reset_without_state_leak_inc13() {
    // reset() rebuilds the term store; the memo (fingerprint-keyed, term-id
    // free) survives. Verdicts after reset must be unaffected.
    let mut ctx = SmtContext::new();
    let x = ChcVar::new("x", ChcSort::Int);
    let q = ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::Int(3));
    let r1 = ctx.check_sat(&q);
    assert!(matches!(r1, SmtResult::Sat(_)));
    ctx.reset();
    let r2 = ctx.check_sat(&q);
    assert!(
        matches!(r2, SmtResult::Sat(_)),
        "same query after reset must stay SAT, got {r2:?}",
    );
}

/// Build the concat/extract var-chain repro formula:
///   a = concat(#x00000090, #x00000000)   (64-bit, low 32 bits = 0)
///   b = a, c = b, d = c, e = d
///   NOT( extract(31,0, e) == rhs )
///
/// With `rhs == 0` the low-32-bit slice of `e` provably equals `rhs`, so the
/// negated equality is UNSAT. With `rhs == 1` it is SAT.
fn concat_extract_chain_query(rhs_low32: u128) -> ChcExpr {
    let bv64 = |n: &str| ChcVar::new(n, ChcSort::BitVec(64));
    let (a, b, c, d, e) = (bv64("a"), bv64("b"), bv64("c"), bv64("d"), bv64("e"));

    // concat(#x00000090, #x00000000): high half = 0x90, low half = 0.
    let concat = ChcExpr::Op(
        crate::ChcOp::BvConcat,
        vec![
            Arc::new(ChcExpr::BitVec(0x0000_0090, 32)),
            Arc::new(ChcExpr::BitVec(0x0000_0000, 32)),
        ],
    );
    // extract(31, 0, e): low 32 bits of e.
    let extract = ChcExpr::Op(
        crate::ChcOp::BvExtract(31, 0),
        vec![Arc::new(ChcExpr::var(e.clone()))],
    );

    ChcExpr::and_all([
        ChcExpr::eq(ChcExpr::var(a.clone()), concat),
        ChcExpr::eq(ChcExpr::var(b.clone()), ChcExpr::var(a)),
        ChcExpr::eq(ChcExpr::var(c.clone()), ChcExpr::var(b)),
        ChcExpr::eq(ChcExpr::var(d.clone()), ChcExpr::var(c)),
        ChcExpr::eq(ChcExpr::var(e), ChcExpr::var(d)),
        ChcExpr::not(ChcExpr::eq(extract, ChcExpr::BitVec(rhs_low32, 32))),
    ])
}

/// Soundness: `(extract 31 0 (concat #x90 #x0))` folds to 0 through a chain of
/// variable equalities, so `(not (= (extract 31 0 e) 0))` is UNSAT. The
/// embedded `SmtContext::check_sat` must NOT report Sat here (Unknown is an
/// acceptable over-approximation; a wrong Sat is a soundness bug that surfaces
/// as a spurious model-checker-consumer counterexample).
#[test]
#[serial]
fn test_check_sat_extract_over_concat_chain_is_unsat() {
    let mut ctx = SmtContext::new();
    let query = concat_extract_chain_query(0x0000_0000);
    let result = ctx.check_sat(&query);
    assert!(
        !matches!(result, SmtResult::Sat(_)),
        "extract-over-concat var chain is UNSAT; check_sat must never report Sat, got {result:?}",
    );
    assert!(
        result.is_unsat(),
        "extract-over-concat var chain should decide UNSAT, got {result:?}",
    );
}

/// Same UNSAT formula, forced through the executor-fallback entry
/// (`check_sat_with_executor_fallback`) rather than the plain internal loop.
/// The acyclic CHC error-derivation path validates candidate counterexamples
/// with this entry, so its verdict here is the linchpin of pipeline soundness:
/// a wrong Sat would let a spurious counterexample through.
#[test]
#[serial]
fn test_check_sat_extract_over_concat_chain_executor_fallback_is_unsat() {
    let mut ctx = SmtContext::new();
    let query = concat_extract_chain_query(0x0000_0000);
    let result = ctx.check_sat_with_executor_fallback(&query);
    assert!(
        !matches!(result, SmtResult::Sat(_)),
        "executor-fallback must never report Sat on the UNSAT var chain, got {result:?}",
    );
}

/// `extract(31,0, concat(h, #x00000000))` with `h` a FREE 32-bit variable.
/// The concat is NOT constant-foldable, so this exercises the actual BV
/// bit-blast encoding of concat/extract (not the constant-folding shortcut).
/// The low 32 bits are the literal zero half regardless of `h`, so the
/// disequality with 0 is UNSAT.
#[test]
#[serial]
fn test_check_sat_extract_low_of_concat_free_high_is_unsat() {
    let mut ctx = SmtContext::new();
    let a = ChcVar::new("a", ChcSort::BitVec(64));
    let h = ChcVar::new("h", ChcSort::BitVec(32));
    let concat = ChcExpr::Op(
        crate::ChcOp::BvConcat,
        vec![Arc::new(ChcExpr::var(h)), Arc::new(ChcExpr::BitVec(0, 32))],
    );
    let extract = ChcExpr::Op(
        crate::ChcOp::BvExtract(31, 0),
        vec![Arc::new(ChcExpr::var(a.clone()))],
    );
    let query = ChcExpr::and_all([
        ChcExpr::eq(ChcExpr::var(a), concat),
        ChcExpr::not(ChcExpr::eq(extract, ChcExpr::BitVec(0, 32))),
    ]);
    let result = ctx.check_sat(&query);
    assert!(
        !matches!(result, SmtResult::Sat(_)),
        "extract-low of concat(free_high, 0) is UNSAT; must not report Sat, got {result:?}",
    );
}

/// `extract(31,0, concat(#x90, #x0))` folded directly (no intermediate var):
/// low half is the zero literal, so `(not (= extract 0))` is UNSAT.
#[test]
#[serial]
fn test_check_sat_extract_directly_over_concat_is_unsat() {
    let mut ctx = SmtContext::new();
    let concat = ChcExpr::Op(
        crate::ChcOp::BvConcat,
        vec![
            Arc::new(ChcExpr::BitVec(0x90, 32)),
            Arc::new(ChcExpr::BitVec(0, 32)),
        ],
    );
    let extract = ChcExpr::Op(crate::ChcOp::BvExtract(31, 0), vec![Arc::new(concat)]);
    let query = ChcExpr::not(ChcExpr::eq(extract, ChcExpr::BitVec(0, 32)));
    let result = ctx.check_sat(&query);
    assert!(
        !matches!(result, SmtResult::Sat(_)),
        "extract directly over concat is UNSAT; must not report Sat, got {result:?}",
    );
}

/// Variadic (3-operand) concat: `concat(#x01, #x02, #x03)` (8-bit each) is the
/// 24-bit value `0x010203`, so `extract(7,0)` is `0x03`. Guards against a
/// binary-only concat encoding silently dropping operands.
#[test]
#[serial]
fn test_check_sat_extract_over_variadic_concat_is_unsat() {
    let mut ctx = SmtContext::new();
    let concat3 = ChcExpr::Op(
        crate::ChcOp::BvConcat,
        vec![
            Arc::new(ChcExpr::BitVec(0x01, 8)),
            Arc::new(ChcExpr::BitVec(0x02, 8)),
            Arc::new(ChcExpr::BitVec(0x03, 8)),
        ],
    );
    let extract = ChcExpr::Op(crate::ChcOp::BvExtract(7, 0), vec![Arc::new(concat3)]);
    let query = ChcExpr::not(ChcExpr::eq(extract, ChcExpr::BitVec(0x03, 8)));
    let result = ctx.check_sat(&query);
    assert!(
        !matches!(result, SmtResult::Sat(_)),
        "extract(7,0) of concat(1,2,3) is 3, so the disequality is UNSAT; got {result:?}",
    );
}

/// SAT sibling of the UNSAT repro: same shape but the low-32 slice (which is 0)
/// is compared against 1, so `(not (= 0 1))` holds and the formula IS SAT. This
/// guards against over-correcting the fix into a false UNSAT.
#[test]
#[serial]
fn test_check_sat_extract_over_concat_chain_sat_sibling() {
    let mut ctx = SmtContext::new();
    let query = concat_extract_chain_query(0x0000_0001);
    let result = ctx.check_sat(&query);
    assert!(
        !result.is_unsat(),
        "extract slice is 0 != 1, so the formula is SAT; must not report UNSAT, got {result:?}",
    );
    assert!(
        matches!(result, SmtResult::Sat(_)),
        "SAT sibling should decide Sat, got {result:?}",
    );
}
/// The acyclic CHC error-derivation path checks the *Int-lowered* form of the
/// extract-over-concat chain (post-BvToInt: `extract(31,0,x)` becomes
/// `mod(x, 2^32)`), so a check_sat bug in the div/mod theory would surface as a
/// spurious feasible error path just as a BV bug would. This locks the lowered
/// form UNSAT through both the internal loop and the executor fallback.
#[test]
#[serial]
fn test_check_sat_int_lowered_extract_over_concat_is_unsat() {
    // e = 618475290624 (= exact BvToInt value of concat(#x90,#x0)); mod 2^32 == 0.
    let int_var = |n: &str| ChcVar::new(n, ChcSort::Int);
    let (a, b, c, d, e) = (
        int_var("a"),
        int_var("b"),
        int_var("c"),
        int_var("d"),
        int_var("e"),
    );
    let two32 = ChcExpr::int(1i64 << 32);
    let extract = ChcExpr::mod_op(ChcExpr::var(e.clone()), two32);
    let q = ChcExpr::and_all([
        ChcExpr::eq(ChcExpr::var(a.clone()), ChcExpr::int(618_475_290_624_i64)),
        ChcExpr::eq(ChcExpr::var(b.clone()), ChcExpr::var(a)),
        ChcExpr::eq(ChcExpr::var(c.clone()), ChcExpr::var(b)),
        ChcExpr::eq(ChcExpr::var(d.clone()), ChcExpr::var(c)),
        ChcExpr::eq(ChcExpr::var(e), ChcExpr::var(d)),
        ChcExpr::not(ChcExpr::eq(extract, ChcExpr::int(0))),
    ]);
    let r1 = SmtContext::new().check_sat(&q);
    let r2 = SmtContext::new().check_sat_with_executor_fallback(&q);
    assert!(
        !matches!(r1, SmtResult::Sat(_)) && !matches!(r2, SmtResult::Sat(_)),
        "int-lowered extract-over-concat is UNSAT; must never report Sat, got {r1:?} / {r2:?}",
    );
}

// ---------------------------------------------------------------------------
// W1-1B: exact BvToInt bounds-check discharge (roadmap AY-W1).
//
// A BV64 index carries a `mod(x, 2^64)` after unsigned normalization. The
// modulus 2^64 is a product tree (i64 can't hold it), which pre-W1-1B was
// Euclidean-decomposed into a 2^64 coefficient that overflows i64/Rational64
// and stalls the query to Unknown. W1-1B preserves the wide modulus and routes
// it to the BigInt executor, which folds 2^32*2^32 -> 2^64 and decides exactly.
// ---------------------------------------------------------------------------

/// COMPLETENESS (the discharge win): `mod(idx, 2^64) >= 2^64` is UNSAT — an
/// abstracted BV64 index can never reach its own type ceiling. This is the
/// upper-range tautology that lets a `0 <= idx < len` bounds proof close; it
/// returned Unknown before W1-1B and must now be Unsat (= Safe).
#[test]
#[serial]
fn wide_const_mod_upper_range_tautology_is_unsat_w1_1b() {
    let idx = ChcExpr::var(ChcVar::new("idx", ChcSort::Int));
    let query = ChcExpr::ge(mod_pow2_64(idx), pow2_64());
    let result = SmtContext::new().check_sat(&query);
    assert!(
        matches!(
            result,
            SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_)
        ),
        "mod(idx, 2^64) >= 2^64 must be UNSAT (Safe) via the exact executor, got {result:?}",
    );
}

/// SOUNDNESS (no false Safe): a satisfiable wide-modulus query must NOT be
/// reported UNSAT. `mod(idx, 2^64) = 10` has the witness idx=10, so preserving
/// the modulus must keep it Sat — the fix must never manufacture a proof for a
/// reachable (real-OOB) state.
#[test]
#[serial]
fn wide_const_mod_sat_query_not_falsely_safe_w1_1b() {
    let idx = ChcExpr::var(ChcVar::new("idx", ChcSort::Int));
    let query = ChcExpr::eq(mod_pow2_64(idx), ChcExpr::int(10));
    let result = SmtContext::new().check_sat(&query);
    assert!(
        matches!(result, SmtResult::Sat(_)),
        "mod(idx, 2^64) = 10 is SAT (witness idx=10); preserving the wide modulus must not false-prove UNSAT, got {result:?}",
    );
}

// --- Phase-2 BigInt escape: check_sat with beyond-i128 constants ---

/// `2^128 + 1` as the parser-style Horner tree (Int-if-fits does not apply).
fn big_probe_expr() -> ChcExpr {
    ChcExpr::from_bigint((num_bigint::BigInt::from(1u8) << 128) + 1)
}

/// (= x 2^128+1) is Sat with the exact beyond-i128 witness carried as
/// `SmtValue::BigInt` and passing the SAME strict model verification as
/// every other Sat (measured baseline: the witness was skipped at model
/// extraction and the verdict demoted to Unknown).
#[test]
#[serial]
fn test_check_sat_bigint_eq_witness_is_sat_and_exact() {
    let mut ctx = SmtContext::new();
    let x = ChcVar::new("x", ChcSort::Int);
    let query = ChcExpr::eq(ChcExpr::var(x), big_probe_expr());

    let result = ctx.check_sat(&query);
    let SmtResult::Sat(model) = result else {
        panic!("expected Sat with a beyond-i128 witness, got {result:?}");
    };
    let expected = (num_bigint::BigInt::from(1u8) << 128) + 1;
    match model.get("x") {
        Some(super::types::SmtValue::BigInt(b)) => assert_eq!(
            b.as_ref(),
            &expected,
            "witness must be the exact beyond-i128 value"
        ),
        other => panic!("expected SmtValue::BigInt witness for x, got {other:?}"),
    }
}

/// Comparison feeder shape: (> x 2^128+1) ∧ (> x 5) is Sat with a
/// beyond-i128 witness strictly greater than the probe.
#[test]
#[serial]
fn test_check_sat_bigint_cmp_witness_is_sat() {
    let mut ctx = SmtContext::new();
    let x = ChcVar::new("x", ChcSort::Int);
    let query = ChcExpr::and(
        ChcExpr::gt(ChcExpr::var(x.clone()), big_probe_expr()),
        ChcExpr::gt(ChcExpr::var(x), ChcExpr::int(5)),
    );

    let result = ctx.check_sat(&query);
    let SmtResult::Sat(model) = result else {
        panic!("expected Sat with a beyond-i128 witness, got {result:?}");
    };
    let probe = (num_bigint::BigInt::from(1u8) << 128) + 1;
    match model.get("x") {
        Some(super::types::SmtValue::BigInt(b)) => {
            assert!(b.as_ref() > &probe, "witness must exceed the probe")
        }
        other => panic!("expected SmtValue::BigInt witness for x, got {other:?}"),
    }
}

/// Negative control: the beyond-i128 UNSAT probe (> x 2^128+1) ∧ (< x 0)
/// stays Unsat — the escape opens no fail-open channel.
#[test]
#[serial]
fn test_check_sat_bigint_conflict_stays_unsat() {
    let mut ctx = SmtContext::new();
    let x = ChcVar::new("x", ChcSort::Int);
    let query = ChcExpr::and(
        ChcExpr::gt(ChcExpr::var(x.clone()), big_probe_expr()),
        ChcExpr::lt(ChcExpr::var(x), ChcExpr::int(0)),
    );

    let result = ctx.check_sat(&query);
    assert!(
        result.is_unsat(),
        "beyond-i128 conflicting bounds must stay Unsat, got {result:?}"
    );
}

/// Negative control at exactly i128::MAX: the witness stays a canonical
/// `SmtValue::Int` (the BigInt variant is reserved for beyond-i128 values).
#[test]
#[serial]
fn test_check_sat_i128_max_witness_stays_int() {
    let mut ctx = SmtContext::new();
    let x = ChcVar::new("x", ChcSort::Int);
    let query = ChcExpr::eq(
        ChcExpr::var(x),
        ChcExpr::from_bigint(num_bigint::BigInt::from(i128::MAX)),
    );

    let result = ctx.check_sat(&query);
    let SmtResult::Sat(model) = result else {
        panic!("expected Sat at the i128 boundary, got {result:?}");
    };
    assert_eq!(
        model.get("x"),
        Some(&super::types::SmtValue::Int(i128::MAX)),
        "i128::MAX must stay a canonical Int witness"
    );
}

// ---------------------------------------------------------------------------
// bitblast-total (2026-07): fail-closed CUMULATIVE BV bit-blast budget guard.
//
// The per-term WIDTH guard (bitblast-bound) never fires on the REAL grind: the
// e2e run recorded ZERO width-refuse hits — every individual BV term is ≤ 256
// bits. The grind is MANY moderate-width terms whose bit-blasts ACCUMULATE past
// the 500k PersistentBvCache cap (observed 916k / 1_069k / 1_379k entries), so
// the cache clears at the cap and refills, thrashing to a ~52-min SIGKILL. The
// cumulative total-bits gate bounds the SUM across ALL terms so the thrash never
// starts. These tests reproduce the real mechanism FAITHFULLY (many moderate
// BVs, NOT one wide BV) and prove the gate bounds it.
// ---------------------------------------------------------------------------

/// FAITHFUL oracle for the real grind, updated for the DYNAMIC abort
/// (model-checker-consumer #46). Builds a query with MANY (2000) DISTINCT 256-bit BV
/// comparisons over 2000 distinct BV variables — each term far below the
/// 16_384 per-term width guard (so that guard is INERT, just as in the real
/// 0-refuse-hit run), but the blast mints entries past the 500k cache cap.
///
/// Three arms:
///   * LEGACY (dynamic abort force-OFF + static budget disabled): the un-gated
///     blast overflows the PersistentBvCache — peak entries EXCEED the cap and
///     the cap-clear fires. This is the PROOF the reproduction still matches
///     the real mechanism (many moderate BVs → cache overflow).
///   * DYNAMIC (dynamic abort force-ON + static budget disabled): even with
///     every static budget out of the way, the INTERNAL blast ABORTS the
///     moment its minted entries reach the cap (no capture, no cap-clear);
///     `check_sat`'s executor-fallback slice then decides the query on the
///     ay-dpll lane — which never touches the PersistentBvCache — so the
///     result may legitimately be a verified Sat, with the cache bounded.
///   * DEFAULTS: the counted total (~1.02M) is under the high pre-gate
///     (20x base), so the query is admitted; same contained outcome.
///     (Static counts cannot distinguish this accumulation from a legitimate
///     BMC-unrolled CHC of the same counted size; the blast itself can.)
#[test]
#[serial]
fn test_check_sat_many_moderate_bv_accumulation_gated_bitblast_total() {
    const N: usize = 2000; // 2000 distinct 256-bit comparisons over 2000 distinct vars
    const W: u32 = 256; // the WIDEST real BV width — no single term trips the width guard

    // Defensive: clear any override a prior (panicking) serial test may have left.
    clear_bitblast_max_total_bits_override_for_tests();
    set_bitblast_dynamic_abort_override_for_tests(0);

    let conjuncts: Vec<ChcExpr> = (0..N)
        .map(|i| {
            let x = ChcVar::new(format!("x{i}"), ChcSort::BitVec(W));
            ChcExpr::eq(ChcExpr::var(x), ChcExpr::BitVec(1, W))
        })
        .collect();
    let query = ChcExpr::and_all(conjuncts);

    // Faithfulness invariant: the per-term width guard is INERT (no single wide
    // term), so only the cumulative machinery can catch this — as in the real run.
    assert!(
        max_bv_width(&query) <= 16_384,
        "reproduction must have NO single wide term; max width = {}",
        max_bv_width(&query),
    );
    // The counted total exceeds the cache cap (and the base budget), but stays
    // under the 20x pre-gate — i.e. it lands in exactly the band where static
    // prediction is ambiguous and the dynamic abort must decide.
    let total_bits = total_bv_bits(&query);
    assert!(
        total_bits > MAX_PERSISTENT_CACHE_ENTRIES as u64,
        "cumulative BV bits {total_bits} must exceed the {MAX_PERSISTENT_CACHE_ENTRIES} cache cap",
    );

    // ---- LEGACY: dynamic abort off + static budget disabled → thrash --------
    set_bitblast_max_total_bits_override_for_tests(u64::MAX);
    set_bitblast_dynamic_abort_override_for_tests(2); // force-off
    reset_reuse_counters_for_tests();
    reset_bv_cache_peak_for_tests();
    let legacy = {
        let mut ctx = SmtContext::new();
        ctx.check_sat(&query)
    };
    let peak_legacy = bv_cache_peak_entries_for_tests();
    let cap_clears_legacy = bv_cache_cap_clear_count_for_tests();
    // Print only the result discriminant — the full Sat model is 2000 vars wide.
    eprintln!(
        "[bitblast-total LEGACY ] result_is_sat={} peak_entries={peak_legacy} \
         cap_clears={cap_clears_legacy} total_bits={total_bits} (cap={MAX_PERSISTENT_CACHE_ENTRIES})",
        matches!(legacy, SmtResult::Sat(_)),
    );
    // PROOF the repro is FAITHFUL: many moderate BVs overflow the cache past its
    // cap and the cap-clear thrash fires. If this fails, the mechanism is NOT
    // many-moderate-BV accumulation and the guards would be inert — STOP.
    assert!(
        peak_legacy > MAX_PERSISTENT_CACHE_ENTRIES,
        "LEGACY: peak entries {peak_legacy} must EXCEED the {MAX_PERSISTENT_CACHE_ENTRIES} cap \
         (the cache-overflow thrash) — many moderate BVs must accumulate past the cap",
    );
    assert!(
        cap_clears_legacy > 0,
        "LEGACY: cap-clear must fire (cache overflowed and cleared); got {cap_clears_legacy}",
    );

    // ---- DYNAMIC: abort force-on, static budget still disabled --------------
    set_bitblast_dynamic_abort_override_for_tests(1); // force-on
    reset_reuse_counters_for_tests();
    reset_bv_cache_peak_for_tests();
    let dynamic = {
        let mut ctx = SmtContext::new();
        ctx.check_sat(&query)
    };
    let peak_dynamic = bv_cache_peak_entries_for_tests();
    let cap_clears_dynamic = bv_cache_cap_clear_count_for_tests();
    eprintln!(
        "[bitblast-total DYNAMIC] result_is_sat={} peak_entries={peak_dynamic} \
         cap_clears={cap_clears_dynamic}",
        matches!(dynamic, SmtResult::Sat(_)),
    );
    // The internal blast aborted; the executor-fallback slice may legitimately
    // DECIDE the query (this one is trivially Sat). What must never happen:
    // a false Unsat, or the PersistentBvCache thrash.
    assert!(
        !matches!(dynamic, SmtResult::Unsat),
        "DYNAMIC: a satisfiable query must never come back Unsat; got {dynamic:?}",
    );
    // An aborted blast never reaches capture: no cap-clear, no captured peak.
    assert_eq!(
        cap_clears_dynamic, 0,
        "DYNAMIC: cap-clear must NOT fire — the internal blast aborts before capture",
    );
    assert!(
        peak_dynamic < MAX_PERSISTENT_CACHE_ENTRIES,
        "DYNAMIC: captured entries must stay under the cap; peak={peak_dynamic}",
    );

    // ---- DEFAULTS: pre-gate admits, dynamic abort contains -------------------
    clear_bitblast_max_total_bits_override_for_tests();
    set_bitblast_dynamic_abort_override_for_tests(0); // env/default path (on)
    reset_reuse_counters_for_tests();
    reset_bv_cache_peak_for_tests();
    let after = {
        let mut ctx = SmtContext::new();
        ctx.check_sat(&query)
    };
    let peak_after = bv_cache_peak_entries_for_tests();
    let cap_clears_after = bv_cache_cap_clear_count_for_tests();
    eprintln!(
        "[bitblast-total DEFAULT] result_is_sat={} peak_entries={peak_after} \
         cap_clears={cap_clears_after}",
        matches!(after, SmtResult::Sat(_)),
    );
    // Same contract as the DYNAMIC arm: the query may be decided on the
    // executor lane, but a false Unsat and the cache thrash are forbidden.
    assert!(
        !matches!(after, SmtResult::Unsat),
        "DEFAULT: a satisfiable query must never come back Unsat; got {after:?}",
    );
    assert_eq!(
        cap_clears_after, 0,
        "DEFAULT: cap-clear must NOT fire once the internal blast aborts",
    );
    assert!(
        peak_after < MAX_PERSISTENT_CACHE_ENTRIES,
        "DEFAULT: cache entries must stay under the cap; peak={peak_after}",
    );
}

/// Regression: a MODERATE number of 256-bit BV comparisons whose cumulative bits
/// stay UNDER the 400k budget is unaffected — it still bit-blasts and decides
/// Sat correctly, without stressing the cache.
#[test]
#[serial]
fn test_check_sat_moderate_bv_total_under_budget_still_decides_bitblast_total() {
    clear_bitblast_max_total_bits_override_for_tests();

    const N: usize = 100; // 100 * (256 + 256) = 51_200 bits << 400_000 budget
    const W: u32 = 256;
    let conjuncts: Vec<ChcExpr> = (0..N)
        .map(|i| {
            let y = ChcVar::new(format!("y{i}"), ChcSort::BitVec(W));
            ChcExpr::eq(ChcExpr::var(y), ChcExpr::BitVec(1, W))
        })
        .collect();
    let query = ChcExpr::and_all(conjuncts);
    let total_bits = total_bv_bits(&query);
    assert!(
        total_bits < 400_000,
        "regression query must be UNDER budget; bits={total_bits}",
    );

    reset_reuse_counters_for_tests();
    reset_bv_cache_peak_for_tests();
    let mut ctx = SmtContext::new();
    let result = ctx.check_sat(&query);

    // Every conjunct is `y_i = 1`, so the conjunction is satisfiable.
    assert!(
        matches!(result, SmtResult::Sat(_)),
        "under-budget BV conjunction must decide Sat, got {result:?}",
    );
    // It really did bit-blast (was not refused).
    assert!(
        bv_bitblast_count_for_tests() >= 1,
        "under-budget query must enter bit-blasting (not be refused)",
    );
    assert!(
        bv_new_clause_count_for_tests() > 0,
        "under-budget query must generate bit-blast clauses",
    );
    // And it never came close to the cap.
    assert!(
        bv_cache_cap_clear_count_for_tests() == 0
            && bv_cache_peak_entries_for_tests() < MAX_PERSISTENT_CACHE_ENTRIES,
        "under-budget query must not stress the cache; peak={}",
        bv_cache_peak_entries_for_tests(),
    );
}

/// The per-term WIDTH guard still works: a SINGLE arbitrarily-wide BV (the
/// `rational::Rat::inv` shape) is refused BEFORE bit-blasting, so the cache never
/// grows. Complements the cumulative test — this is the one-wide-term path.
#[test]
#[serial]
fn test_check_sat_single_wide_bv_refused_by_width_guard_bitblast_total() {
    clear_bitblast_max_total_bits_override_for_tests();
    const WIDE: u32 = 200_000; // 200k >> 16_384 per-term width budget

    reset_reuse_counters_for_tests();
    reset_bv_cache_peak_for_tests();
    let mut ctx = SmtContext::new();
    let x = ChcVar::new("wx", ChcSort::BitVec(WIDE));
    let query = ChcExpr::eq(ChcExpr::var(x), ChcExpr::BitVec(1, WIDE));
    assert!(
        max_bv_width(&query) > 16_384,
        "single-wide-BV repro must exceed the per-term width budget",
    );

    let result = ctx.check_sat(&query);
    assert!(
        matches!(result, SmtResult::Unknown),
        "wide-BV query must abstain (Unknown), got {result:?}",
    );
    assert_eq!(
        bv_cache_cap_clear_count_for_tests(),
        0,
        "width-refused blast must not trigger a cap-clear",
    );
    assert!(
        bv_cache_peak_entries_for_tests() < MAX_PERSISTENT_CACHE_ENTRIES,
        "width-refused blast must keep the cache bounded; peak={}",
        bv_cache_peak_entries_for_tests(),
    );
    assert_eq!(
        bv_new_clause_count_for_tests(),
        0,
        "a width-refused blast must not generate clauses",
    );
}

/// Regression: the WIDEST real BV width (256) is FAR below both budgets, so a
/// normal small-BV query still bit-blasts and decides. Guards against a future
/// budget being lowered into the real-obligation range.
#[test]
#[serial]
fn test_check_sat_widest_real_bv_still_bitblasts_bitblast_total() {
    clear_bitblast_max_total_bits_override_for_tests();
    reset_reuse_counters_for_tests();
    reset_bv_cache_peak_for_tests();

    let mut ctx = SmtContext::new();
    let x = ChcVar::new("rx", ChcSort::BitVec(256));
    let query = ChcExpr::eq(ChcExpr::var(x), ChcExpr::BitVec(1, 256));

    let result = ctx.check_sat(&query);
    assert!(
        matches!(result, SmtResult::Sat(_)),
        "widest real BV width (256) must still decide Sat, got {result:?}",
    );
    assert!(
        bv_bitblast_count_for_tests() >= 1,
        "256-bit BV query must enter bit-blasting (not be refused)",
    );
    assert!(
        bv_new_clause_count_for_tests() > 0,
        "256-bit BV query must generate bit-blast clauses",
    );
    assert!(
        bv_cache_cap_clear_count_for_tests() == 0
            && bv_cache_peak_entries_for_tests() < MAX_PERSISTENT_CACHE_ENTRIES,
        "256-bit BV must not stress the cache",
    );
}

/// Reuse of the persistent BV cache must keep the FULL bit-blast circuit and
/// the sub-term bit vectors, not just this query's delta and the atoms'
/// memoized predicate vars.
///
/// The bv-cache signature is the sorted set of CACHEABLE atom keys; atoms
/// `term_to_chc_expr` cannot convert (e.g. `(_ extract i j)`) contribute
/// nothing. A follow-up query that keeps the cacheable atom set but adds an
/// extract atom over an already-blasted variable therefore takes the REUSE
/// path with a genuinely fresh atom — exactly the shape of model-checker-consumer PDR
/// frame queries (stable lemma atoms + fresh per-bit cube atoms), hundreds
/// of which share one signature. Pre-fix, reuse then failed in two ways:
///
/// 1. `restore_cached_bv_state` restored only the ATOM terms' memoized
///    predicate vars (`current_terms` = the Tseitin atom terms); variable
///    bit vectors were never restored, so the fresh extract atom minted a
///    second, DISCONNECTED set of bit variables for `y`: the replayed
///    circuit constrained the old bits, the fresh atom the new bits, and
///    model extraction (reading `term_to_bits`) reported values violating
///    the memoized atoms.
/// 2. `capture_cached_bv_state` REPLACED `cache.clauses` with the query's
///    newly-minted delta, so the second reuse replayed a "circuit" that was
///    just the previous delta — the real bit-blast clauses were gone.
///
/// Both surfaced as the fail-safe WARN flood "SAT model from DPLL(T) loop
/// violates original expression ... returning Unknown" that collapsed the
/// native BV lane to Unknown on model-checker-consumer PDR workloads (the looping_id L0
/// failure).
#[test]
#[serial]
fn test_bv_cache_reuse_keeps_circuit_and_subterm_bits() {
    use super::types::SmtValue;

    let mut ctx = SmtContext::new();
    let x = ChcVar::new("x", ChcSort::BitVec(8));
    let y = ChcVar::new("y", ChcSort::BitVec(8));
    // Cacheable atom set shared by all three queries.
    let x_lt_5 = ChcExpr::Op(
        ChcOp::BvULt,
        vec![
            Arc::new(ChcExpr::var(x.clone())),
            Arc::new(ChcExpr::BitVec(5, 8)),
        ],
    );
    let y_lt_x = ChcExpr::Op(
        ChcOp::BvULt,
        vec![
            Arc::new(ChcExpr::var(y.clone())),
            Arc::new(ChcExpr::var(x.clone())),
        ],
    );
    // NON-cacheable fresh atom (extract is not term_to_chc_expr-convertible,
    // so it is invisible to the signature): forces y >= 128.
    let y_top_bit = ChcExpr::eq(
        ChcExpr::Op(
            ChcOp::BvExtract(7, 7),
            vec![Arc::new(ChcExpr::var(y.clone()))],
        ),
        ChcExpr::BitVec(1, 1),
    );

    let check_sat_model = |result: SmtResult, i: usize| match result {
        SmtResult::Sat(m) => {
            let xv = match m.get("x") {
                Some(&SmtValue::BitVec(v, 8)) => v,
                other => panic!("query {i}: model must assign x, got {other:?}"),
            };
            let yv = match m.get("y") {
                Some(&SmtValue::BitVec(v, 8)) => v,
                other => panic!("query {i}: model must assign y, got {other:?}"),
            };
            assert!(xv < 5, "query {i}: x = {xv} must be < 5");
            assert!(yv < xv, "query {i}: y = {yv} must be < x = {xv}");
        }
        other => panic!(
            "query {i} must be a strictly-verified Sat (BV cache reuse must not \
             degrade to Unknown), got {other:?}"
        ),
    };

    // Query 0: fresh blast; establishes the cached circuit + signature.
    let q0 = ChcExpr::and_vec(vec![x_lt_5.clone(), y_lt_x.clone()]);
    check_sat_model(ctx.check_sat(&q0), 0);

    // Query 1: same signature (extract atom is non-cacheable) => reuse path
    // with a genuinely fresh atom over the already-blasted `y`. UNSAT
    // (y >= 128 contradicts y < x < 5). Pre-fix: the fresh atom minted
    // disconnected bits for `y`, the SAT model violated the memoized atoms,
    // and strict re-verification demoted the query to Unknown.
    let q1 = ChcExpr::and_vec(vec![x_lt_5.clone(), y_lt_x.clone(), y_top_bit]);
    let r1 = ctx.check_sat(&q1);
    assert!(
        matches!(
            r1,
            SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_)
        ),
        "query 1 must be Unsat (y >= 128 contradicts y < x < 5), got {r1:?}"
    );

    // Query 2: second reuse of the signature. Pre-fix, the previous capture
    // had replaced the cached circuit with query 1's delta, so the replayed
    // circuit no longer constrained the bits at all.
    let q2 = ChcExpr::and_vec(vec![y_lt_x.clone(), x_lt_5.clone()]);
    check_sat_model(ctx.check_sat(&q2), 2);
}

include!("tests_check_sat/pdr_no_progress.rs");
include!("tests_check_sat/bv_range_facts.rs");
