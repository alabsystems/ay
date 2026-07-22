// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Unit tests for the shadow weak-equivalence graph (M1).

use super::*;

/// A pure store chain c = store(store(a, i, v), j, w) yields a weak path from
/// the outer store to the base with the store indices as labels and no strong
/// reasons.
#[test]
fn test_weak_equiv_store_chain_labels() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort);
    let i = store.mk_var("i", Sort::Int);
    let j = store.mk_var("j", Sort::Int);
    let v = store.mk_var("v", Sort::Int);
    let w = store.mk_var("w", Sort::Int);

    let b = store.mk_store(a, i, v);
    let c = store.mk_store(b, j, w);
    // A select keeps the chain "active" like real queries do.
    let _sel = store.mk_select(c, j);

    let mut solver = ArraySolver::new(&store);
    solver.check();

    assert!(solver.weakly_connected(c, a));
    assert!(solver.weakly_connected(a, c));
    assert!(solver.weakly_connected(c, b));

    let (labels, reasons) = solver
        .weak_path(c, a)
        .expect("store chain endpoints must have a weak path");
    assert_eq!(
        labels,
        vec![j, i],
        "labels must follow the chain outer→base"
    );
    assert!(
        reasons.is_empty(),
        "pure store edges need no strong-equality reasons"
    );

    let (labels, reasons) = solver.weak_path(c, c).expect("trivial path");
    assert!(labels.is_empty());
    assert!(reasons.is_empty());
}

/// Strong asserted equalities collapse nodes and their literal is carried as
/// the reason of any weak path through the edge.
#[test]
fn test_weak_equiv_strong_eq_collapse_carries_reason() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort.clone());
    let x = store.mk_var("x", arr_sort);
    let i = store.mk_var("i", Sort::Int);
    let v = store.mk_var("v", Sort::Int);

    let st = store.mk_store(a, i, v);
    let eq_x_st = store.mk_eq(x, st);

    let mut solver = ArraySolver::new(&store);
    solver.assert_literal(eq_x_st, true);
    solver.check();

    assert!(solver.weakly_connected(x, a));
    let (labels, reasons) = solver
        .weak_path(x, a)
        .expect("x = store(a,i,v) implies a weak path x → a");
    assert_eq!(labels, vec![i]);
    assert_eq!(
        reasons,
        vec![TheoryLit::new(eq_x_st, true)],
        "the asserted equality literal must be carried as the path reason"
    );
}

/// External (sentinel) equalities: reason-carrying edges are traversable by
/// weak_path with their reasons; reason-free sentinel edges count for
/// connectivity only and never appear on a reason-carrying path.
#[test]
fn test_weak_equiv_external_edges_reasoned_vs_sentinel() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort.clone());
    let y = store.mk_var("y", arr_sort.clone());
    let z = store.mk_var("z", arr_sort);
    let i = store.mk_var("i", Sort::Int);
    let v = store.mk_var("v", Sort::Int);
    let p = store.mk_var("p", Sort::Bool);

    let st = store.mk_store(a, i, v);
    let _sel = store.mk_select(st, i);

    let mut solver = ArraySolver::new(&store);
    solver.check();

    // Reason-carrying external equality y = st (e.g. from LIA/EUF).
    let guard = TheoryLit::new(p, true);
    solver.assert_external_equality_with_reasons(y, st, &[guard]);
    // Reason-free sentinel equality z = a.
    solver.assert_external_equality(z, a);

    assert!(solver.weakly_connected(y, a), "reasoned edge connects");
    assert!(
        solver.weakly_connected(z, st),
        "reason-free sentinel still counts for connectivity"
    );

    let (labels, reasons) = solver
        .weak_path(y, a)
        .expect("reasoned external edge must be traversable");
    assert_eq!(labels, vec![i]);
    assert_eq!(reasons, vec![guard]);

    assert!(
        solver.weak_path(z, a).is_none(),
        "reason-free sentinel edges must not appear on reason-carrying paths"
    );
}

/// Array-sorted ite collapsed by a decided condition: asserting the equality
/// atom (= t branch) merges the ite node into the branch's class.
#[test]
fn test_weak_equiv_ite_collapsed_node() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort.clone());
    let b = store.mk_var("b", arr_sort);
    let c = store.mk_var("c", Sort::Bool);
    let i = store.mk_var("i", Sort::Int);
    let v = store.mk_var("v", Sort::Int);

    let st = store.mk_store(a, i, v);
    let t = store.mk_ite_raw(c, st, b);
    // mk_eq would Shannon-expand (= (ite ...) x); keep the raw equality atom,
    // matching how the pipeline asserts a decided ite branch to the theory.
    let eq_t_then = store.mk_eq_coerce_no_ite_expand(t, st);
    let _sel = store.mk_select(t, i);

    let mut solver = ArraySolver::new(&store);
    solver.assert_literal(eq_t_then, true);
    solver.check();

    assert!(solver.weakly_connected(t, a));
    let (labels, reasons) = solver
        .weak_path(t, a)
        .expect("collapsed ite must reach the store base");
    assert_eq!(labels, vec![i]);
    assert_eq!(reasons, vec![TheoryLit::new(eq_t_then, true)]);

    // The untaken branch is NOT collapsed.
    assert!(!solver.weakly_connected(t, b));
}

/// Distinct components stay unconnected; connectivity is per-component.
#[test]
fn test_weak_equiv_multi_component() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort.clone());
    let d = store.mk_var("d", arr_sort);
    let i = store.mk_var("i", Sort::Int);
    let j = store.mk_var("j", Sort::Int);
    let v = store.mk_var("v", Sort::Int);
    let w = store.mk_var("w", Sort::Int);

    let sa = store.mk_store(a, i, v);
    let sd = store.mk_store(d, j, w);
    let _sel_a = store.mk_select(sa, i);
    let _sel_d = store.mk_select(sd, j);

    let mut solver = ArraySolver::new(&store);
    solver.check();

    assert!(solver.weakly_connected(sa, a));
    assert!(solver.weakly_connected(sd, d));
    assert!(!solver.weakly_connected(a, d));
    assert!(!solver.weakly_connected(sa, sd));
    assert!(solver.weak_path(sa, d).is_none());
}

/// Rebuild determinism: the same inputs always produce the same graph, and
/// the versioned cache invalidates when the equality graph changes.
#[test]
fn test_weak_equiv_rebuild_deterministic_and_versioned() {
    let build = |assert_eq_lit: bool| {
        let mut store = TermStore::new();
        let arr_sort = make_array_sort();
        let a = store.mk_var("a", arr_sort.clone());
        let x = store.mk_var("x", arr_sort);
        let i = store.mk_var("i", Sort::Int);
        let v = store.mk_var("v", Sort::Int);
        let st = store.mk_store(a, i, v);
        let eq = store.mk_eq(x, st);
        let _sel = store.mk_select(st, i);
        let mut solver = ArraySolver::new(&store);
        if assert_eq_lit {
            solver.assert_literal(eq, true);
        }
        solver.check();
        (*solver.weak_equiv_graph()).clone()
    };

    // Same inputs → identical graphs across independent solver instances
    // (the debug build also re-checks this on every rebuild internally).
    assert_eq!(build(true), build(true));
    assert_eq!(build(false), build(false));
    // Different equality assignments → different graphs.
    assert_ne!(build(true), build(false));

    // Versioned invalidation: asserting a collapsing equality after a first
    // query must be reflected by fresh queries.
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();
    let a = store.mk_var("a", arr_sort.clone());
    let x = store.mk_var("x", arr_sort);
    let i = store.mk_var("i", Sort::Int);
    let v = store.mk_var("v", Sort::Int);
    let st = store.mk_store(a, i, v);
    let eq = store.mk_eq(x, st);
    let _sel = store.mk_select(st, i);

    let mut solver = ArraySolver::new(&store);
    solver.check();
    assert!(!solver.weakly_connected(x, a));
    solver.assert_literal(eq, true);
    solver.check();
    assert!(
        solver.weakly_connected(x, a),
        "graph must rebuild after the equality graph changes"
    );
}

// ---------------------------------------------------------------------------
// M1 weak-equivalence-modulo-index primitive (`weakly_equiv_mod_j`)
// ---------------------------------------------------------------------------

/// A store at an index PROVABLY distinct from the query index is crossable:
/// `store(a, 1, v)` does not touch index `2`, so `select(store, 2) = select(a, 2)`
/// is forced — `weakly_equiv_mod_j(store, a, 2)` is true. At the store's OWN
/// index it is NOT crossable (`mod_j` at `1` is false).
#[test]
fn test_weak_equiv_mod_j_distinct_const_index_crossable() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort);
    let one = store.mk_int(BigInt::from(1));
    let two = store.mk_int(BigInt::from(2));
    let v = store.mk_var("v", Sort::Int);

    let st = store.mk_store(a, one, v);
    let _sel = store.mk_select(st, two);

    let mut solver = ArraySolver::new(&store);
    solver.check();

    // Distinct constants 1 ≠ 2: the store at index 1 cannot affect index 2.
    assert!(
        solver.weakly_equiv_mod_j(st, a, two),
        "store at index 1 must be crossable modulo query index 2"
    );
    assert!(
        solver.weakly_equiv_mod_j(a, st, two),
        "modulo-j connectivity is symmetric"
    );
    // At the store's own index, the read is NOT forced equal.
    assert!(
        !solver.weakly_equiv_mod_j(st, a, one),
        "store at index 1 must NOT be crossable modulo index 1 (it writes there)"
    );
    // Reflexive.
    assert!(solver.weakly_equiv_mod_j(a, a, one));
}

/// A store whose index disequality with the query index is UNDECIDED is NOT
/// crossable (conservative): `store(a, i, v)` with `i` vs `j` unknown ⇒
/// `weakly_equiv_mod_j(store, a, j)` is false. Asserting `i ≠ j` makes it
/// crossable (live distinctness, rebuilt on the diseq change).
#[test]
fn test_weak_equiv_mod_j_undecided_index_not_crossable_until_diseq() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort);
    let i = store.mk_var("i", Sort::Int);
    let j = store.mk_var("j", Sort::Int);
    let v = store.mk_var("v", Sort::Int);

    let st = store.mk_store(a, i, v);
    let _sel = store.mk_select(st, j);
    let eq_ij = store.mk_eq(i, j);

    let mut solver = ArraySolver::new(&store);
    solver.check();
    // i vs j undecided ⇒ the store MIGHT touch j ⇒ not crossable.
    assert!(
        !solver.weakly_equiv_mod_j(st, a, j),
        "undecided store index must be treated as possibly-touching j"
    );

    // Assert i ≠ j: now the store provably cannot touch j ⇒ crossable.
    solver.assert_literal(eq_ij, false);
    solver.check();
    assert!(
        solver.weakly_equiv_mod_j(st, a, j),
        "asserting i != j must make the store crossable modulo j"
    );
}

/// Strong equality edges are always crossable; a multi-store path forces the
/// read only when EVERY store on it is distinct from the query index.
#[test]
fn test_weak_equiv_mod_j_multi_store_path_all_distinct() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort.clone());
    let x = store.mk_var("x", arr_sort);
    let one = store.mk_int(BigInt::from(1));
    let two = store.mk_int(BigInt::from(2));
    let three = store.mk_int(BigInt::from(3));
    let v = store.mk_var("v", Sort::Int);
    let w = store.mk_var("w", Sort::Int);

    // x = store(store(a,1,v),2,w); query index 3 is distinct from both.
    let inner = store.mk_store(a, one, v);
    let outer = store.mk_store(inner, two, w);
    let eq_x_outer = store.mk_eq(x, outer);
    let _sel = store.mk_select(outer, three);

    let mut solver = ArraySolver::new(&store);
    solver.assert_literal(eq_x_outer, true);
    solver.check();

    // Path x ≈ outer —[2]— inner —[1]— a; both store indices ≠ 3.
    assert!(
        solver.weakly_equiv_mod_j(x, a, three),
        "both stores distinct from 3 ⇒ select(x,3)=select(a,3) forced"
    );
    // Modulo index 2, the outer store touches it ⇒ NOT forced.
    assert!(
        !solver.weakly_equiv_mod_j(x, a, two),
        "the outer store writes index 2 ⇒ not crossable modulo 2"
    );
    // Modulo index 1, the inner store touches it ⇒ NOT forced.
    assert!(
        !solver.weakly_equiv_mod_j(x, a, one),
        "the inner store writes index 1 ⇒ not crossable modulo 1"
    );
}

// ---------------------------------------------------------------------------
// M5 verdict-only authority flip: the near-linear no-conflict prune at the
// SingletonOnly store-chain-witness + its wrong-SAT soundness gate.
// ---------------------------------------------------------------------------

/// The M5 flip must NOT prune a genuine singleton-support witness. Two sibling
/// stores off a COMMON base that differ at exactly one index are weakly
/// connected (through the base), so the graph verdict is *possible conflict*,
/// legacy still fires, and the wrong-SAT differential gate
/// (`base_eq ⟹ weakly_connected`) records zero disagreement. This is the M3
/// extensionality-derived-base shape: `base_eq` reaches through the shared base
/// and the graph tracks that reach exactly.
#[test]
fn test_weq5_flip_keeps_common_base_singleton_witness() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort);
    let k = store.mk_int(BigInt::from(5)); // the single differing store index
    let i = store.mk_var("i", Sort::Int); // the read index (undecided vs k)
    let w1 = store.mk_int(BigInt::from(1));
    let w2 = store.mk_int(BigInt::from(2));

    // Siblings off `a` differing only at index 5 (values 1 vs 2).
    let array1 = store.mk_store(a, k, w1);
    let array2 = store.mk_store(a, k, w2);
    let sel1 = store.mk_select(array1, i);
    let sel2 = store.mk_select(array2, i);
    let eq_sels = store.mk_eq(sel1, sel2);

    let mut solver = ArraySolver::new(&store);
    solver.assert_literal(eq_sels, false); // select(array1,i) != select(array2,i)
    solver.check();

    // Graph verdict: array1 and array2 are weakly connected through `a`, so the
    // flip does NOT prune this pair.
    assert!(
        solver.weakly_connected(array1, array2),
        "sibling stores off a common base must be weakly connected"
    );

    crate::weak_equiv::weq5_shadow::reset();
    let result = solver.check_store_chain_select_difference_witness_singleton();
    let snap = crate::weak_equiv::weq5_shadow::snapshot();

    // The witness fired (was NOT pruned by the flip): it demands the model
    // equality `i = 5` (the read index must be the single differing index).
    assert!(
        result.is_some(),
        "the singleton-support witness must still fire under the M5 flip"
    );
    // Soundness gate: no base-eq pair was pruned as not-weakly-connected.
    assert_eq!(
        snap.disagree_base_eq_not_wc, 0,
        "wrong-SAT gate: a base-eq witness pair must always be weakly connected"
    );
    assert!(
        snap.base_eq_holds >= 1,
        "the witness pair must have been recorded as a base-eq pair"
    );
    assert!(
        snap.support_nonempty >= 1,
        "the single differing index must produce a non-empty support"
    );
    assert_eq!(
        snap.graph_pruned, 0,
        "a weakly-connected witness pair must not be graph-pruned"
    );
}

/// The M5 flip must NOT prune when the common base is reached through a
/// SEPARATE asserted array equality (`b1 = b2`, an `eq_adj` edge) — the closest
/// constructible analogue of an extensionality-derived base equality. The graph
/// ingests that strong edge, so the pair stays weakly connected and the witness
/// still fires; the wrong-SAT gate stays at zero.
#[test]
fn test_weq5_flip_keeps_asserted_cross_base_witness() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let b1 = store.mk_var("b1", arr_sort.clone());
    let b2 = store.mk_var("b2", arr_sort);
    let k = store.mk_int(BigInt::from(7));
    let i = store.mk_var("i", Sort::Int);
    let w1 = store.mk_int(BigInt::from(3));
    let w2 = store.mk_int(BigInt::from(4));

    let array1 = store.mk_store(b1, k, w1);
    let array2 = store.mk_store(b2, k, w2);
    let sel1 = store.mk_select(array1, i);
    let sel2 = store.mk_select(array2, i);
    let eq_bases = store.mk_eq(b1, b2);
    let eq_sels = store.mk_eq(sel1, sel2);

    let mut solver = ArraySolver::new(&store);
    solver.assert_literal(eq_bases, true); // b1 = b2 (the "ext-derived" base eq)
    solver.assert_literal(eq_sels, false); // select(array1,i) != select(array2,i)
    solver.check();

    assert!(
        solver.weakly_connected(array1, array2),
        "cross-base siblings joined by an asserted base equality must be \
         weakly connected"
    );

    crate::weak_equiv::weq5_shadow::reset();
    let result = solver.check_store_chain_select_difference_witness_singleton();
    let snap = crate::weak_equiv::weq5_shadow::snapshot();

    assert!(
        result.is_some(),
        "the cross-base singleton witness must still fire under the M5 flip"
    );
    assert_eq!(
        snap.disagree_base_eq_not_wc, 0,
        "wrong-SAT gate: asserted-cross-base pair must stay weakly connected"
    );
    assert!(snap.base_eq_holds >= 1);
    assert_eq!(snap.graph_pruned, 0);
}

/// The M5 flip DOES prune a candidate pair whose select arrays are in different
/// weak-equivalence components — they cannot share a common base, so legacy
/// would find no witness either. The prune is recorded and no witness fires.
#[test]
fn test_weq5_flip_prunes_disconnected_pair() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    // Two independent arrays, no connecting equality.
    let a = store.mk_var("a", arr_sort.clone());
    let d = store.mk_var("d", arr_sort);
    let k = store.mk_int(BigInt::from(9));
    let i = store.mk_var("i", Sort::Int);
    let v = store.mk_var("v", Sort::Int);
    let w = store.mk_var("w", Sort::Int);

    let array1 = store.mk_store(a, k, v);
    let array2 = store.mk_store(d, k, w);
    let sel1 = store.mk_select(array1, i);
    let sel2 = store.mk_select(array2, i);
    let eq_sels = store.mk_eq(sel1, sel2);

    let mut solver = ArraySolver::new(&store);
    solver.assert_literal(eq_sels, false);
    solver.check();

    assert!(
        !solver.weakly_connected(array1, array2),
        "arrays in different components must not be weakly connected"
    );

    crate::weak_equiv::weq5_shadow::reset();
    let result = solver.check_store_chain_select_difference_witness_singleton();
    let snap = crate::weak_equiv::weq5_shadow::snapshot();

    assert!(
        result.is_none(),
        "no witness can fire on a disconnected (no common base) pair"
    );
    assert!(
        snap.graph_pruned >= 1,
        "the disconnected pair must be graph-pruned by the M5 flip"
    );
    assert_eq!(
        snap.disagree_base_eq_not_wc, 0,
        "pruning a disconnected pair is sound: legacy base-eq also fails"
    );
}

/// Disconnected components are never modulo-j equivalent.
#[test]
fn test_weak_equiv_mod_j_disconnected_components() {
    let mut store = TermStore::new();
    let arr_sort = make_array_sort();

    let a = store.mk_var("a", arr_sort.clone());
    let d = store.mk_var("d", arr_sort);
    let one = store.mk_int(BigInt::from(1));
    let five = store.mk_int(BigInt::from(5));
    let v = store.mk_var("v", Sort::Int);

    let st = store.mk_store(a, one, v);
    let _sel = store.mk_select(st, five);

    let mut solver = ArraySolver::new(&store);
    solver.check();

    assert!(
        !solver.weakly_equiv_mod_j(st, d, five),
        "unconnected arrays are never modulo-j equivalent"
    );
}
