// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! WP-F F0a/F0b: DAG-linear hash, equality, `vars`, `scan_features` and
//! `and_all`/`or_all` return exactly what the former tree walks returned,
//! and exponentially shared DAGs (tree size ~2^60) finish in milliseconds.

use std::hash::{BuildHasher, Hash};
use std::sync::Arc;
use std::time::{Duration, Instant};

use ay_core::kani_compat::DetHashSet;
use proptest::prelude::*;

use super::digester::DagDigester;
use super::test_support::*;
use super::*;
use crate::expr::{ChcOp, ChcSort, ChcVar};
use crate::PredicateId;

// ---------------------------------------------------------------------------
// Hash
// ---------------------------------------------------------------------------

#[test]
fn hash_stream_equals_former_derive_on_fixed_shapes() {
    let dt = ChcSort::Datatype {
        name: "D".into(),
        constructors: crate::ChcDtConstructors::new(vec![]),
    };
    let x = ChcExpr::var(ChcVar::new("x", ChcSort::Int));
    let samples = vec![
        ChcExpr::Bool(true),
        ChcExpr::Int(-7),
        ChcExpr::Real(3, 4),
        ChcExpr::BitVec(9, 8),
        x.clone(),
        ChcExpr::add(x.clone(), ChcExpr::Int(1)),
        ChcExpr::predicate_app("P", PredicateId(3), vec![x.clone(), ChcExpr::Int(2)]),
        ChcExpr::FuncApp("f".into(), dt.clone(), vec![Arc::new(x.clone())]),
        ChcExpr::ConstArrayMarker(ChcSort::Int),
        ChcExpr::IsTesterMarker("cons".into()),
        ChcExpr::const_array(ChcSort::Int, ChcExpr::Int(0)),
        ChcExpr::Op(
            ChcOp::BvExtract(7, 0),
            vec![Arc::new(ChcExpr::BitVec(1, 16))],
        ),
        ChcExpr::Op(ChcOp::And, vec![]),
    ];
    for e in &samples {
        let mut a = Recorder::default();
        e.hash(&mut a);
        assert_eq!(a.0, mirror_bytes(e), "byte stream differs for {e:?}");
    }
}

fn check_hash_equals_former_derive(seed: u64, n: usize) {
    let cap = crate::expr::structural::HASH_EXACT_CHILD_VISITS as u128;
    let e = random_dag(seed, n, cap);
    assert!(tree_size(&e) <= cap);
    let m = mirror(&e);
    let mut r = Recorder::default();
    e.hash(&mut r);
    assert_eq!(mirror_bytes(&e), r.0);
    assert_eq!(
        hash_with(&e, rustc_hash::FxHasher::default()),
        hash_with(&m, rustc_hash::FxHasher::default())
    );
    assert_eq!(
        hash_with(&e, std::collections::hash_map::DefaultHasher::new()),
        hash_with(&m, std::collections::hash_map::DefaultHasher::new())
    );
    let fold = DetHashSet::<u8>::default();
    assert_eq!(fold.hasher().hash_one(&e), fold.hasher().hash_one(&m));
}

/// Seed proptest found when the generator could overshoot its tree cap.
#[test]
fn hash_equals_former_derive_pinned_seed() {
    check_hash_equals_former_derive(6_115_918_941_043_985_110, 152);
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(256))]

    /// Below the exact budget, `Hash` writes the former derive's stream, so
    /// every hasher (Fx, foldhash, SipHash) yields the former value.
    #[test]
    fn hash_equals_former_derive_below_budget(seed in any::<u64>(), n in 1usize..300) {
        check_hash_equals_former_derive(seed, n);
    }

    /// Any size: structurally equal, pointer-distinct copies hash and compare
    /// equal; `==` agrees with plain structural equality.
    #[test]
    fn hash_and_eq_are_structural_on_shared_dags(seed in any::<u64>(), n in 1usize..120) {
        let a = random_dag(seed, n, u128::MAX);
        let b = random_dag(seed, n, u128::MAX); // same structure, fresh allocations
        prop_assert!(a == b);
        prop_assert_eq!(a.structural_hash(), b.structural_hash());
        prop_assert_eq!(structural_digest_of(&a), structural_digest_of(&b));
        // Near-copies differing in one random leaf, within reference reach.
        let c = random_dag(seed, n, 200_000);
        let d = random_dag(seed ^ 0x9E37_79B9, n, 200_000);
        prop_assert_eq!(c == d, reference_eq(&c, &d));
        if c == d {
            prop_assert_eq!(c.structural_hash(), d.structural_hash());
        }
    }

    #[test]
    fn vars_equal_tree_walk(seed in any::<u64>(), n in 1usize..400) {
        let e = random_dag(seed, n, 400_000);
        prop_assert_eq!(e.vars(), reference_vars(&e));
    }

    #[test]
    fn scan_features_equal_tree_walk(seed in any::<u64>(), n in 1usize..400) {
        let e = random_dag(seed, n, 400_000);
        prop_assert_eq!(features_tuple(&e.scan_features()), reference_scan(&e));
    }

    #[test]
    fn and_all_or_all_equal_reference(seed in any::<u64>(), n in 1usize..80, k in 1usize..6) {
        // Repeated seeds give duplicate (pointer-distinct) parts.
        let parts: Vec<ChcExpr> =
            (0..k).map(|i| random_dag(seed.wrapping_add(i as u64 % 3), n, 50_000)).collect();
        let got = ChcExpr::and_all(parts.clone());
        let want = reference_connective(ChcOp::And, parts.clone());
        prop_assert!(reference_eq(&got, &want));
        let got_or = ChcExpr::or_all(parts.clone());
        let want_or = reference_connective(ChcOp::Or, parts);
        prop_assert!(reference_eq(&got_or, &want_or));
    }
}

// ---------------------------------------------------------------------------
// Exponential DAGs: linear time, exact answers
// ---------------------------------------------------------------------------

fn assert_fast(what: &str, start: Instant) {
    assert!(
        start.elapsed() < Duration::from_secs(5),
        "{what} took {:?} on a 2^60-tree DAG",
        start.elapsed()
    );
}

#[test]
fn exponential_dag_hash_eq_vars_scan_are_linear() {
    let a = ite_chain(60, "");
    let b = ite_chain(60, ""); // pointer-distinct copy
    let (dag, tree) = dag_and_tree_size(&a);
    assert!(dag < 400, "dag {dag}");
    assert!(tree > 1u128 << 59, "tree {tree}");

    let t = Instant::now();
    assert_eq!(a.structural_hash(), b.structural_hash());
    assert_fast("hash", t);

    let t = Instant::now();
    assert_eq!(*a, *b);
    let c = ite_chain(60, "z");
    assert_ne!(*a, *c);
    assert_fast("eq", t);

    let t = Instant::now();
    let vars = a.vars();
    assert_fast("vars", t);
    assert_eq!(vars.len(), 61);
    assert_eq!(vars[0].name, "c59");

    let t = Instant::now();
    let f = a.scan_features();
    assert_fast("scan_features", t);
    assert!(f.has_ite && f.has_negation && !f.has_bv && !f.has_mod_or_div);
}

#[test]
fn exponential_dag_and_all_dedups_and_keeps_sharing() {
    let a = ite_chain(60, "");
    let b = ite_chain(60, "");
    let ea = ChcExpr::eq(
        ChcExpr::var(ChcVar::new("y", ChcSort::Real)),
        a.as_ref().clone(),
    );
    let eb = ChcExpr::eq(
        ChcExpr::var(ChcVar::new("y", ChcSort::Real)),
        b.as_ref().clone(),
    );
    let inner = ChcExpr::Op(ChcOp::And, vec![Arc::new(ea.clone()), Arc::clone(&a)]);
    let t = Instant::now();
    let conj = ChcExpr::and_all(vec![inner, eb, ea]);
    assert_fast("and_all", t);
    let ChcExpr::Op(ChcOp::And, args) = &conj else {
        panic!("expected a conjunction, got a different shape");
    };
    assert_eq!(args.len(), 2, "duplicate conjuncts are dropped");
    assert!(
        Arc::ptr_eq(&args[1], &a),
        "a flattened child keeps its own Arc"
    );
}

#[test]
fn vars_depth_cut_off_matches_tree_walk_in_both_visit_orders() {
    // S: a shared node whose variables sit ~20 levels down.
    let mut s = Arc::new(ChcExpr::var(ChcVar::new("deep", ChcSort::Int)));
    for i in 0..20 {
        s = Arc::new(ChcExpr::Op(
            ChcOp::Add,
            vec![
                Arc::new(ChcExpr::var(ChcVar::new(format!("s{i}"), ChcSort::Int))),
                s,
            ],
        ));
    }
    // L: a 540-long chain that ends in S, so S is reached below the cut-off.
    let mut l = Arc::clone(&s);
    for i in 0..540 {
        l = Arc::new(ChcExpr::Op(
            ChcOp::Add,
            vec![
                Arc::new(ChcExpr::var(ChcVar::new(format!("l{i}"), ChcSort::Int))),
                l,
            ],
        ));
    }
    let wide = ite_chain(14, "w"); // ~2^14 tree nodes: forces the DAG scan
    for root in [
        ChcExpr::Op(ChcOp::Add, vec![Arc::clone(&l), Arc::clone(&s)]),
        ChcExpr::Op(ChcOp::Add, vec![Arc::clone(&s), Arc::clone(&l)]),
        ChcExpr::Op(
            ChcOp::Add,
            vec![Arc::clone(&wide), Arc::clone(&s), Arc::clone(&l)],
        ),
        ChcExpr::Op(ChcOp::Add, vec![Arc::clone(&s), Arc::clone(&wide)]),
    ] {
        assert_eq!(root.vars(), reference_vars(&root));
        assert_eq!(features_tuple(&root.scan_features()), reference_scan(&root));
    }
}

#[test]
fn longest_path_matches_definition() {
    let chain = ite_chain(10, "");
    // ite -> + -> ite -> + -> ... -> x0: two edges per level, 20 in all.
    assert!(longest_path_at_least(&chain, 20));
    assert!(!longest_path_at_least(&chain, 21));
    assert!(!longest_path_at_least(&ChcExpr::Int(1), 1));
}

#[test]
fn digester_is_structural_and_seeded() {
    let a = ite_chain(40, "");
    let b = ite_chain(40, "");
    let mut d1 = DagDigester::new(1);
    let mut d1b = DagDigester::new(1);
    let mut d2 = DagDigester::new(2);
    assert_eq!(d1.digest(&a), d1b.digest(&b));
    assert_eq!(d1.digest_of(&a), d1.digest(&a));
    assert_ne!(d1.digest(&a), d2.digest(&a));
    assert!(d1.len() > 0);
    d1.clear();
    assert_eq!(d1.len(), 0);
    assert_eq!(structural_digest(&a), structural_digest(&b));
}

/// Regression (found by the WP-F probe runs in PDKIND): one digest walk over
/// more distinct inner nodes than the bounded thread-local cache holds. The
/// cache clears itself mid-walk; an earlier iterative walk then looked up a
/// child digest that had been evicted and panicked. Digests must survive the
/// eviction and stay structural.
#[test]
fn digest_survives_cache_eviction_inside_one_walk() {
    let build = || {
        let atoms: Vec<Arc<ChcExpr>> = (0..(super::DIGEST_CACHE_CAP + 4096))
            .map(|i| {
                Arc::new(ChcExpr::le(
                    ChcExpr::var(ChcVar::new(format!("e{i}"), ChcSort::Int)),
                    ChcExpr::Int(i as i128),
                ))
            })
            .collect();
        Arc::new(ChcExpr::Op(ChcOp::And, atoms))
    };
    let a = build();
    let b = build();
    let t = Instant::now();
    let da = structural_digest(&a);
    let db = structural_digest(&b);
    assert_eq!(da, db);
    assert_eq!(a.structural_hash(), b.structural_hash());
    assert!(t.elapsed() < Duration::from_secs(20), "{:?}", t.elapsed());
}
