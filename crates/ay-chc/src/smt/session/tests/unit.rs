// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! WP-3 unit locks (design §8, Rung 1): memo hits, idempotent assert, staging
//! commit, the activation-aliasing invariant, delta count, unit-kill + revive,
//! deadline -> Budget, the router mapping, and one end-to-end lock through
//! WP-2's bridge (`core ⊆ query` + a SAT follow-up). A Poison-path lock needs an
//! injection hook that does not exist yet (follow-up). Most locks need no solve
//! because staging happens BEFORE `check_assuming_unverified` and an instant
//! deadline (`Duration::ZERO`) exits that call before `run_query`.

#![allow(clippy::panic, clippy::unwrap_used)]

use std::sync::Arc;
use std::time::Duration;

use ay_core::kani_compat::DetHashSet as FxHashSet;

use crate::smt::session::convert_memo::{
    eligible, split_conjuncts, ConjunctKey, ConvertMemo, Rung, TriviallyFalse,
};
use crate::smt::session::shim::{new_session_for, session_budget, try_session};
use crate::smt::session::{
    AssertId, AssertOrigin, AssertState, BudgetKind, HornCheck, HornSmt, SessionConfig, TheoryKind,
    UnknownReason, UnsupportedKind,
};
use crate::smt::types::{Partition, SmtResult};
use crate::smt::SmtContext;
use crate::{ChcExpr, ChcSort, ChcVar};

fn real(name: &str) -> ChcExpr {
    ChcExpr::var(ChcVar::new(name, ChcSort::Real))
}

fn int(name: &str) -> ChcExpr {
    ChcExpr::var(ChcVar::new(name, ChcSort::Int))
}

fn boolean(name: &str) -> ChcExpr {
    ChcExpr::var(ChcVar::new(name, ChcSort::Bool))
}

fn r(n: i64) -> ChcExpr {
    ChcExpr::Real(n, 1)
}

/// `x >= n`
fn ge(name: &str, n: i64) -> ChcExpr {
    ChcExpr::ge(real(name), r(n))
}

/// `x <= n`
fn le(name: &str, n: i64) -> ChcExpr {
    ChcExpr::le(real(name), r(n))
}

fn session() -> HornSmt {
    HornSmt::new(SessionConfig::default(), None)
}

/// A conjunction the session accepts: a "transition" `T`, and two cube literals.
fn transition() -> ChcExpr {
    ChcExpr::and_all([
        ChcExpr::eq(real("x'"), ChcExpr::add(real("x"), r(1))),
        ChcExpr::or(boolean("b"), ge("y", 0)),
    ])
}

fn key_h1(k: ConjunctKey) -> u64 {
    let ConjunctKey::Structural { h1, .. } = k;
    h1
}

// ---------------------------------------------------------------- keys / memo

#[test]
fn structural_key_is_allocation_independent() {
    let a = ChcExpr::and_all([ge("x", 0), le("x", 5)]);
    // `and_all` re-wraps every element (F18): fresh Arcs, same structure.
    let b = ChcExpr::and_all([ge("x", 0), le("x", 5)]);
    assert_eq!(ConvertMemo::key_of(&a), ConvertMemo::key_of(&b));
    let ConjunctKey::Structural { nodes, .. } = ConvertMemo::key_of(&ge("x", 0));
    assert_eq!(nodes, 3, "ge(var, const) is three nodes");
    assert_ne!(
        ConvertMemo::key_of(&ge("x", 0)),
        ConvertMemo::key_of(&ge("x", 1))
    );
    assert_ne!(
        ConvertMemo::key_of(&ge("x", 0)),
        ConvertMemo::key_of(&le("x", 0))
    );
    // Two seeded passes: h1 and h2 differ from each other and from the plain hash.
    let k = ConvertMemo::key_of(&ge("x", 0));
    let ConjunctKey::Structural { h1, h2, .. } = k;
    assert_ne!(h1, h2);
    assert_ne!(key_h1(k), ge("x", 0).structural_hash());
}

#[test]
fn memo_hits_ptr_then_struct_then_misses() {
    let mut own = SmtContext::new();
    let mut memo = ConvertMemo::new();
    let e = Arc::new(ge("x", 0));
    let (k1, t1) = memo.convert(&mut own, &e).unwrap();
    assert_eq!((memo.hits_ptr, memo.hits_struct, memo.misses), (0, 0, 1));
    // Same Arc: pointer pre-check.
    let (k2, t2) = memo.convert(&mut own, &e).unwrap();
    assert_eq!((k1, t1), (k2, t2));
    assert_eq!((memo.hits_ptr, memo.hits_struct, memo.misses), (1, 0, 1));
    // Structurally equal, fresh allocation: structural hit, same term.
    let e2 = Arc::new(ge("x", 0));
    let (k3, t3) = memo.convert(&mut own, &e2).unwrap();
    assert_eq!((k1, t1), (k3, t3));
    assert_eq!((memo.hits_ptr, memo.hits_struct, memo.misses), (1, 1, 1));
    // ... and the fresh allocation is now a pointer hit too.
    let _ = memo.convert(&mut own, &e2).unwrap();
    assert_eq!((memo.hits_ptr, memo.hits_struct, memo.misses), (2, 1, 1));
    // A different conjunct misses and gets a different term.
    let (k4, t4) = memo.convert(&mut own, &Arc::new(ge("x", 1))).unwrap();
    assert_ne!(k1, k4);
    assert_ne!(t1, t4);
    assert_eq!(memo.misses, 2);
    assert_eq!(memo.len(), 2);
    memo.clear();
    assert_eq!(memo.len(), 0);
    let _ = memo.convert(&mut own, &e).unwrap();
    assert_eq!(memo.misses, 3, "clear() forgets both maps");
}

#[test]
fn memo_never_memoises_the_budget_sentinel_and_resets_per_conjunct() {
    let mut own = SmtContext::new();
    let mut memo = ConvertMemo::new();
    // A conjunct wide enough to reach the converter's 1024-node memory poll.
    let wide = ChcExpr::or_all((0..600).map(|i| ge("x", i)));
    own.set_term_memory_budget(Some(1));
    let r = memo.convert(&mut own, &Arc::new(wide.clone()));
    assert!(
        matches!(
            r,
            Err(UnknownReason::Unsupported(
                UnsupportedKind::ConversionBudget
            ))
        ),
        "{r:?}"
    );
    assert_eq!(memo.len(), 0, "the sentinel `true` is never memoised");
    // The budget is per conjunct: a small conjunct converts right after.
    own.set_term_memory_budget(None);
    let small = memo.convert(&mut own, &Arc::new(ge("x", 0)));
    assert!(small.is_ok(), "{small:?}");
    // And the wide one converts once the budget is lifted (a fresh attempt,
    // not a stale sentinel).
    let again = memo.convert(&mut own, &Arc::new(wide));
    assert!(again.is_ok(), "{again:?}");
    assert_eq!(memo.len(), 2);
}

#[test]
fn memo_rejects_a_non_bool_conjunct_as_ill_typed() {
    let mut own = SmtContext::new();
    let mut memo = ConvertMemo::new();
    let r = memo.convert(&mut own, &Arc::new(ChcExpr::add(real("x"), r(1))));
    assert!(
        matches!(
            r,
            Err(UnknownReason::Unsupported(UnsupportedKind::IllTyped))
        ),
        "{r:?}"
    );
    assert_eq!(memo.len(), 0);
}

// -------------------------------------------------------------------- split

#[test]
fn split_flattens_nested_and_drops_true_and_keeps_arcs() {
    let inner = Arc::new(ge("y", 2));
    let nested = ChcExpr::Op(
        crate::ChcOp::And,
        vec![
            Arc::new(ge("x", 0)),
            Arc::new(ChcExpr::Op(
                crate::ChcOp::And,
                vec![Arc::new(ChcExpr::Bool(true)), Arc::clone(&inner)],
            )),
            Arc::new(ChcExpr::Bool(true)),
        ],
    );
    let parts = split_conjuncts(&nested).unwrap();
    assert_eq!(parts.len(), 2);
    assert_eq!(*parts[0], ge("x", 0));
    assert!(
        Arc::ptr_eq(&parts[1], &inner),
        "children keep the caller's Arc"
    );
    // A non-And root is wrapped once; `true` alone is empty.
    let single = split_conjuncts(&ge("x", 0)).unwrap();
    assert_eq!(single.len(), 1);
    assert_eq!(*single[0], ge("x", 0));
    assert_eq!(
        split_conjuncts(&ChcExpr::Bool(true)).unwrap(),
        [] as [Arc<ChcExpr>; 0]
    );
    // `false` anywhere is trivially UNSAT.
    assert_eq!(split_conjuncts(&ChcExpr::Bool(false)), Err(TriviallyFalse));
    let with_false = ChcExpr::Op(
        crate::ChcOp::And,
        vec![Arc::new(ge("x", 0)), Arc::new(ChcExpr::Bool(false))],
    );
    assert_eq!(split_conjuncts(&with_false), Err(TriviallyFalse));
}

// ---------------------------------------------------------------- eligible

#[test]
fn eligible_admits_bool_and_linear_real_only() {
    let ok = [
        ge("x", 0),
        ChcExpr::or(boolean("b"), ChcExpr::not(le("x", 3))),
        ChcExpr::eq(real("x"), ChcExpr::mul(r(2), real("y"))),
        ChcExpr::ite(boolean("b"), ge("x", 1), le("x", -1)),
        ChcExpr::eq(boolean("b"), boolean("c")),
        ChcExpr::ne(real("x"), real("y")),
        ChcExpr::implies(
            boolean("b"),
            ChcExpr::gt(ChcExpr::sub(real("x"), real("y")), r(0)),
        ),
        // Int CONSTANTS are coerced to Real by the converter; only Int vars are out.
        ChcExpr::ge(real("x"), ChcExpr::int(0)),
        ChcExpr::eq(real("x"), ChcExpr::int(0)),
        ChcExpr::eq(real("x"), ChcExpr::ite(boolean("b"), ChcExpr::int(1), r(0))),
    ];
    for e in &ok {
        assert_eq!(eligible(e, TheoryKind::Lra, Rung::Rung1), Ok(()), "{e:?}");
    }
    let sort_rejects = [
        ChcExpr::ge(int("i"), ChcExpr::int(0)),
        ChcExpr::eq(
            ChcExpr::var(ChcVar::new("v", ChcSort::BitVec(8))),
            ChcExpr::BitVec(1, 8),
        ),
        ChcExpr::eq(
            ChcExpr::select(
                ChcExpr::var(ChcVar::new(
                    "a",
                    ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Real)),
                )),
                ChcExpr::int(0),
            ),
            r(0),
        ),
        ChcExpr::eq(
            ChcExpr::var(ChcVar::new("u", ChcSort::Uninterpreted("U".into()))),
            ChcExpr::var(ChcVar::new("w", ChcSort::Uninterpreted("U".into()))),
        ),
    ];
    for e in &sort_rejects {
        assert_eq!(
            eligible(e, TheoryKind::Lra, Rung::Rung1),
            Err(UnsupportedKind::Sort),
            "{e:?}"
        );
    }
    // Int vars are fine once the theory is LIA (Rung 2).
    assert_eq!(
        eligible(
            &ChcExpr::ge(int("i"), ChcExpr::int(0)),
            TheoryKind::Lia,
            Rung::Rung1
        ),
        Ok(())
    );
}

#[test]
fn eligible_rejects_nonlinear_shapes_and_ill_typed_terms() {
    let shape_rejects = [
        ChcExpr::predicate_app("P", crate::PredicateId(0), vec![real("x")]),
        ChcExpr::eq(
            ChcExpr::FuncApp("f".into(), ChcSort::Real, vec![Arc::new(real("x"))]),
            r(0),
        ),
        ChcExpr::eq(ChcExpr::mul(real("x"), real("y")), r(1)),
        ChcExpr::eq(ChcExpr::mod_op(int("i"), ChcExpr::int(2)), ChcExpr::int(1)),
        ChcExpr::eq(
            ChcExpr::Op(crate::ChcOp::Div, vec![Arc::new(real("x")), Arc::new(r(2))]),
            r(1),
        ),
    ];
    for e in &shape_rejects {
        assert_eq!(
            eligible(e, TheoryKind::Lra, Rung::Rung1),
            Err(UnsupportedKind::Shape),
            "{e:?}"
        );
    }
    // Rung 2 admits mod/div (through `eliminate_mod`); the Int var still
    // needs LIA.
    assert_eq!(
        eligible(
            &ChcExpr::eq(ChcExpr::mod_op(int("i"), ChcExpr::int(2)), ChcExpr::int(1)),
            TheoryKind::Lia,
            Rung::Rung2
        ),
        Ok(())
    );
    let ill_typed = [
        // Mixed-sort equality (Bool vs Real).
        ChcExpr::eq(boolean("b"), real("x")),
        // The converter would turn `not(real)` into `true` — a weakening.
        ChcExpr::not(real("x")),
        ChcExpr::or(boolean("b"), real("x")),
        // A non-Bool conjunct root.
        ChcExpr::add(real("x"), r(1)),
        // ITE with mismatched branch sorts.
        ChcExpr::eq(real("x"), ChcExpr::ite(boolean("b"), r(1), boolean("c"))),
    ];
    for e in &ill_typed {
        assert_eq!(
            eligible(e, TheoryKind::Lra, Rung::Rung1),
            Err(UnsupportedKind::IllTyped),
            "{e:?}"
        );
    }
}

// ------------------------------------------------------- assert / staging

#[test]
fn assert_persistent_is_idempotent_on_the_structural_key() {
    let mut s = session();
    let c = Arc::new(ge("x", 0));
    let id1 = s.assert_persistent(&c, Partition::AB).unwrap();
    let id2 = s.assert_persistent(&c, Partition::AB).unwrap();
    assert_eq!(id1, id2, "same Arc");
    let rebuilt = Arc::new(ge("x", 0));
    let id3 = s.assert_persistent(&rebuilt, Partition::AB).unwrap();
    assert_eq!(id1, id3, "structurally equal, different allocation");
    assert_eq!(s.assertions().len(), 1);
    assert_eq!(s.by_key().len(), 1);
    assert_eq!(s.assertion(id1).state, AssertState::Live);
    assert_eq!(s.assertion(id1).origin, AssertOrigin::Api);
    let other = s
        .assert_persistent(&Arc::new(ge("x", 1)), Partition::AB)
        .unwrap();
    assert_ne!(other, id1);
    assert_eq!(s.assertions().len(), 2);
    // Eligibility first: nothing asserted for a rejected conjunct.
    let r = s.assert_persistent(
        &Arc::new(ChcExpr::ge(int("i"), ChcExpr::int(0))),
        Partition::AB,
    );
    assert!(matches!(
        r,
        Err(UnknownReason::Unsupported(UnsupportedKind::Sort))
    ));
    assert_eq!(s.assertions().len(), 2);
}

#[test]
fn staging_commit_asserts_nothing_for_an_ineligible_query() {
    let mut s = session();
    let q = ChcExpr::and_all([
        ge("x", 0),
        le("x", 5),
        ChcExpr::ge(int("i"), ChcExpr::int(0)),
    ]);
    let r = s.check_conjunction(&q, Some(Duration::ZERO), None);
    assert!(
        matches!(
            r,
            HornCheck::Unknown(UnknownReason::Unsupported(UnsupportedKind::Sort))
        ),
        "{r:?}"
    );
    assert!(
        s.assertions().is_empty(),
        "eligibility is checked for EVERY conjunct first"
    );
    assert_eq!(s.stats().queries, 1);
    assert_eq!(s.stats().unknown_unsupported, 1);
    assert_eq!(s.query_no(), 0, "a rejected query never reaches the solver");
}

#[test]
fn staging_commit_kills_what_a_conversion_failure_left_behind() {
    let mut s = session();
    // Conjunct 1 converts; conjunct 2 trips the term-memory poll inside the
    // converter (>= 1024 nodes under a 1-byte budget) -> ConversionBudget.
    let wide = ChcExpr::or_all((0..600).map(|i| ge("x", i)));
    let q = ChcExpr::and_all([ge("x", 0), wide]);
    s.own_mut().set_term_memory_budget(Some(1));
    let r = s.check_conjunction(&q, Some(Duration::ZERO), None);
    assert!(
        matches!(
            r,
            HornCheck::Unknown(UnknownReason::Unsupported(
                UnsupportedKind::ConversionBudget
            ))
        ),
        "{r:?}"
    );
    assert!(
        s.assertions().iter().all(|a| a.state == AssertState::Dead),
        "nothing of a query that fails conversion stays live"
    );
    assert!(s.by_key().is_empty());
    assert_eq!(s.stats().unknown_unsupported, 1);
    assert_eq!(s.stats().delta_conjuncts, 0);
    // The session is usable afterwards: the same first conjunct comes back as
    // a NEW live assertion (the kill unit is permanent).
    s.own_mut().set_term_memory_budget(None);
    let dead = s.assertions().len();
    let _ = s.check_conjunction(&ge("x", 0), Some(Duration::ZERO), None);
    assert_eq!(s.assertions().len(), dead + 1);
    assert_eq!(s.assertions().last().unwrap().state, AssertState::Live);
}

#[test]
fn activation_vars_never_alias_tseitin_vars() {
    let mut s = session();
    // Three assertions sharing atoms and Bool vars.
    let q1 = ChcExpr::and_all([
        transition(),
        ge("x", 0),
        ChcExpr::or(boolean("b"), le("y", 1)),
    ]);
    let _ = s.check_conjunction(&q1, Some(Duration::ZERO), None);
    let q2 = ChcExpr::and_all([transition(), ge("x", 0), ChcExpr::not(boolean("b"))]);
    let _ = s.check_conjunction(&q2, Some(Duration::ZERO), None);
    let assertions = s.assertions();
    assert!(assertions.len() >= 4);
    let ts = s
        .tseitin()
        .as_ref()
        .expect("Tseitin state is parked between batches");
    let tseitin_vars: FxHashSet<usize> =
        ts.term_to_var.values().map(|&d| (d - 1) as usize).collect();
    let mut acts: FxHashSet<usize> = FxHashSet::default();
    let mut prev_act: Option<usize> = None;
    for a in assertions {
        let act = a.act.index();
        assert!(acts.insert(act), "activation vars are distinct");
        assert!(
            !tseitin_vars.contains(&act),
            "an act is never a Tseitin term var"
        );
        assert!(
            a.root_lit.variable().index() < act,
            "Tseitin vars are materialised BEFORE the activation var"
        );
        if let Some(p) = prev_act {
            assert!(p < act, "allocation order is the assertion order");
        }
        prev_act = Some(act);
    }
    // The encoder stays strictly above every allocated var at the boundary.
    let max_var = acts.iter().copied().max().unwrap();
    assert!(ts.next_var as usize > max_var + 1);
}

// ---------------------------------------------------------------- delta

#[test]
fn plan_delta_counts_only_the_new_conjuncts() {
    let mut s = session();
    let t = transition();
    let q1 = ChcExpr::and_all([t.clone(), ge("x", 0), le("x", 5)]);
    let parts1 = split_conjuncts(&q1).unwrap();
    let plan1 = s.plan_delta(&parts1);
    assert_eq!(plan1.reuse, [] as [AssertId; 0]);
    assert_eq!(plan1.revive, [] as [AssertId; 0]);
    assert_eq!(plan1.fresh.len(), parts1.len());
    let _ = s.check_conjunction(&q1, Some(Duration::ZERO), None);
    assert_eq!(s.stats().delta_conjuncts, parts1.len() as u64);

    // Same T (rebuilt through `and_all`: fresh Arcs), one cube literal kept,
    // one new; a duplicate within the query collapses.
    let q2 = ChcExpr::and_all([transition(), ge("x", 0), ge("y", 7), ge("y", 7)]);
    let parts2 = split_conjuncts(&q2).unwrap();
    let plan2 = s.plan_delta(&parts2);
    assert_eq!(
        plan2.reuse.len(),
        parts1.len() - 1,
        "T's conjuncts and `x >= 0` are live"
    );
    assert_eq!(plan2.fresh.len(), 1);
    assert_eq!(*plan2.fresh[0], ge("y", 7));
    assert_eq!(plan2.revive, [] as [AssertId; 0]);
    let before = s.stats().delta_conjuncts;
    let _ = s.check_conjunction(&q2, Some(Duration::ZERO), None);
    assert_eq!(s.stats().delta_conjuncts, before + 1);
    assert_eq!(s.stats().queries, 2);
    for a in s.assertions() {
        assert_eq!(a.origin, AssertOrigin::Shim);
    }
}

#[test]
fn unit_kill_after_four_unused_queries_then_revive_as_a_new_id() {
    let mut s = session();
    let t = transition();
    let c1 = ge("x", 0);
    let _ = s.check_conjunction(
        &ChcExpr::and_all([t.clone(), c1.clone()]),
        Some(Duration::ZERO),
        None,
    );
    let c1_id = AssertId(s.assertions().len() as u32 - 1);
    assert_eq!(*s.assertion(c1_id).expr, c1);
    assert_eq!(s.assertion(c1_id).last_used_query, 1);

    // Queries 2..=5 do not use c1: unused for 4 queries -> still live.
    for _ in 0..4 {
        let _ = s.check_conjunction(
            &ChcExpr::and_all([t.clone(), le("x", 9)]),
            Some(Duration::ZERO),
            None,
        );
    }
    assert_eq!(s.query_no(), 5);
    assert_eq!(s.assertion(c1_id).state, AssertState::Live);
    assert_eq!(s.stats().unit_kills, 0);

    // Query 6: unused for 5 > kill_after (4) -> unit-killed.
    let _ = s.check_conjunction(
        &ChcExpr::and_all([t.clone(), le("x", 9)]),
        Some(Duration::ZERO),
        None,
    );
    assert_eq!(s.assertion(c1_id).state, AssertState::Dead);
    assert_eq!(s.stats().unit_kills, 1);
    assert!(s.stats().dead_vars > 0);
    assert!(!s.by_key().values().any(|&id| id == c1_id));
    // T's conjuncts were used every query and stay live.
    let t_parts = split_conjuncts(&t).unwrap();
    let plan = s.plan_delta(&t_parts);
    assert_eq!(plan.reuse.len(), t_parts.len());
    assert_eq!(plan.fresh, [] as [Arc<ChcExpr>; 0]);

    // The same cube recurs: planned as revive + fresh, re-asserted under a NEW id.
    let q = ChcExpr::and_all([t.clone(), c1.clone()]);
    let parts = split_conjuncts(&q).unwrap();
    let plan = s.plan_delta(&parts);
    assert_eq!(plan.revive, vec![c1_id]);
    assert_eq!(plan.fresh.len(), 1);
    let before = s.assertions().len();
    let _ = s.check_conjunction(&q, Some(Duration::ZERO), None);
    assert_eq!(s.assertions().len(), before + 1);
    let new_id = AssertId(before as u32);
    assert_ne!(new_id, c1_id);
    assert_eq!(s.assertion(new_id).state, AssertState::Live);
    assert_eq!(*s.assertion(new_id).expr, c1);
    assert_eq!(
        s.assertion(c1_id).state,
        AssertState::Dead,
        "the kill is permanent"
    );
    // Same term (memo) and root literal (Tseitin `encoded` cache), fresh act.
    assert_eq!(s.assertion(new_id).term, s.assertion(c1_id).term);
    assert_eq!(s.assertion(new_id).root_lit, s.assertion(c1_id).root_lit);
    assert_ne!(s.assertion(new_id).act, s.assertion(c1_id).act);
}

#[test]
fn retention_never_kills_api_assertions() {
    let mut s = session();
    let api = s
        .assert_persistent(&Arc::new(ge("z", 3)), Partition::A)
        .unwrap();
    for _ in 0..8 {
        let _ = s.check_conjunction(
            &ChcExpr::and_all([transition(), le("x", 9)]),
            Some(Duration::ZERO),
            None,
        );
    }
    assert_eq!(s.assertion(api).state, AssertState::Live);
    assert_eq!(s.stats().unit_kills, 0);
}

#[test]
fn shim_rebuilds_before_staging_so_fresh_conjuncts_survive() {
    let base = SessionConfig::default();
    let cfg = SessionConfig {
        rebuild_queries_after: 2,
        ..base
    };
    let mut s = HornSmt::new(cfg, None);
    let t = transition();
    let _ = s.check_conjunction(
        &ChcExpr::and_all([t.clone(), ge("x", 0)]),
        Some(Duration::ZERO),
        None,
    );
    let _ = s.check_conjunction(
        &ChcExpr::and_all([t.clone(), ge("x", 1)]),
        Some(Duration::ZERO),
        None,
    );
    assert!(s.should_rebuild());
    // The third query stages a fresh conjunct; the rebuild must run before it.
    let r = s.check_conjunction(
        &ChcExpr::and_all([t.clone(), ge("x", 2)]),
        Some(Duration::ZERO),
        None,
    );
    assert!(
        matches!(
            r,
            HornCheck::Unknown(UnknownReason::Budget(BudgetKind::Deadline))
        ),
        "{r:?}"
    );
    assert_eq!(s.stats().rebuilds, 1);
    assert!(!s.is_poisoned());
    let last = s.assertions().last().unwrap();
    assert_eq!(*last.expr, ge("x", 2));
    assert_eq!(last.state, AssertState::Live);
}

// -------------------------------------------------------------- deadline

#[test]
fn zero_budget_is_a_deadline_budget_unknown_after_staging() {
    let mut s = session();
    let q = ChcExpr::and_all([ge("x", 0), le("x", 5)]);
    let r = s.check_conjunction(&q, Some(Duration::ZERO), None);
    assert!(
        matches!(
            r,
            HornCheck::Unknown(UnknownReason::Budget(BudgetKind::Deadline))
        ),
        "{r:?}"
    );
    assert_eq!(s.stats().unknown_budget, 1);
    assert_eq!(s.stats().queries, 1);
    assert_eq!(
        s.assertions().len(),
        2,
        "staging precedes the deadline check"
    );
    // Stamped as used by this query even though the solver was not reached.
    assert!(s.assertions().iter().all(|a| a.last_used_query == 1));
}

#[test]
fn trivial_queries_never_touch_the_solver() {
    let mut s = session();
    let r = s.check_conjunction(&ChcExpr::Bool(false), None, None);
    assert!(matches!(r, HornCheck::Unsat { core, over_approximate: false } if core.is_empty()));
    let r = s.check_conjunction(&ChcExpr::Bool(true), None, None);
    assert!(matches!(r, HornCheck::Sat(m) if m.is_empty()));
    assert_eq!(s.query_no(), 0);
    assert_eq!(s.stats().queries, 2);
    assert_eq!(s.stats().unsat, 1);
    assert_eq!(s.stats().sat, 1);
}

// ----------------------------------------------------------------- router

#[test]
fn try_session_maps_the_no_solver_outcomes() {
    let ctx = SmtContext::new();
    let mut s = new_session_for(&ctx);
    // Mode 0: never answers.
    assert!(try_session(&mut s, &ctx, &ge("x", 0), 0).is_none());
    // Trivially false: the legacy preprocessor's shape.
    match try_session(&mut s, &ctx, &ChcExpr::Bool(false), 1) {
        Some(SmtResult::UnsatWithCore(core)) => {
            assert_eq!(core.conjuncts, vec![ChcExpr::Bool(false)])
        }
        other => panic!("{other:?}"),
    }
    // All true: Sat through `sat_or_unknown` (the original expr evaluates to true).
    assert!(matches!(
        try_session(&mut s, &ctx, &ChcExpr::Bool(true), 1),
        Some(SmtResult::Sat(_))
    ));
    // Ineligible: legacy fall-through in mode 1, Unknown in mode 2.
    let int_q = ChcExpr::ge(int("i"), ChcExpr::int(0));
    assert!(try_session(&mut s, &ctx, &int_q, 1).is_none());
    assert!(matches!(
        try_session(&mut s, &ctx, &int_q, 2),
        Some(SmtResult::Unknown)
    ));
    assert!(s.assertions().is_empty());
    // An exhausted per-check budget on the CALLER's context is Budget -> Unknown
    // (and the query's conjuncts are staged for the next attempt).
    ctx.check_timeout.set(Some(Duration::ZERO));
    assert_eq!(session_budget(&ctx), Some(Duration::ZERO));
    assert!(matches!(
        try_session(&mut s, &ctx, &ChcExpr::and_all([ge("x", 0), le("x", 5)]), 1),
        Some(SmtResult::Unknown)
    ));
    assert_eq!(s.stats().unknown_budget, 1);
    assert_eq!(s.assertions().len(), 2);
    ctx.check_timeout.set(None);
    // An expired thread-scoped SMT deadline is the legacy instant Unknown.
    let guard = crate::smt::ScopedSmtDeadline::install(Duration::ZERO);
    assert!(matches!(
        try_session(&mut s, &ctx, &ge("x", 0), 1),
        Some(SmtResult::Unknown)
    ));
    drop(guard);
}

#[test]
fn session_budget_folds_check_timeout_and_global_deadline() {
    let ctx = SmtContext::new();
    assert_eq!(session_budget(&ctx), None);
    ctx.check_timeout.set(Some(Duration::from_secs(5)));
    assert_eq!(session_budget(&ctx), Some(Duration::from_secs(5)));
    // A global deadline in the past leaves nothing.
    let now = ay_core::time::Instant::now();
    ctx.set_global_solve_deadline(Some(now));
    assert_eq!(session_budget(&ctx), Some(Duration::ZERO));
    // A far deadline keeps the smaller per-check budget.
    ctx.set_global_solve_deadline(Some(now + Duration::from_hours(1)));
    assert_eq!(session_budget(&ctx), Some(Duration::from_secs(5)));
    ctx.check_timeout.set(None);
    let b = session_budget(&ctx).unwrap();
    assert!(b > Duration::from_mins(50) && b <= Duration::from_hours(1));
}

// -------------------------------------------------- end-to-end (WP-2 gated)

/// End-to-end through the shim and WP-2's `TheoryBridge` (LRA): a refuted
/// conjunction yields a core within the query, and a satisfiable follow-up
/// reuses the live conjuncts. (Needs the bridge bodies; green on the shared
/// tree 2026-09-19 once they landed.)
#[test]
fn unsat_core_is_a_subset_of_the_query() {
    let mut s = session();
    let q = ChcExpr::and_all([ge("x", 5), le("x", 3), ge("y", 0)]);
    match s.check_conjunction(&q, Some(Duration::from_secs(5)), None) {
        HornCheck::Unsat { core, .. } => {
            let query_ids: Vec<AssertId> = (0..s.assertions().len() as u32).map(AssertId).collect();
            assert_ne!(core, [] as [AssertId; 0]);
            assert!(core.iter().all(|id| query_ids.contains(id)));
            assert!(core.len() <= 3);
        }
        other => panic!("{other:?}"),
    }
    // A satisfiable follow-up over the same T reuses the live conjuncts.
    let r = s.check_conjunction(
        &ChcExpr::and_all([ge("x", 5), ge("y", 0)]),
        Some(Duration::from_secs(5)),
        None,
    );
    assert!(matches!(r, HornCheck::Sat(_)), "{r:?}");
}
