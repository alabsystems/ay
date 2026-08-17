// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

fn t(n: u32) -> TermId {
    TermId(n)
}

fn asserted(n: u32) -> EqJustification {
    EqJustification::Asserted { eq_term: t(n) }
}

#[test]
fn union_find_round_trip() {
    let mut uf = ArrayUnionFind::default();
    assert_eq!(uf.find(t(1)), t(1));
    assert!(uf.union(t(1), t(2), asserted(100)));
    assert!(uf.same_class(t(1), t(2)));
    assert!(!uf.same_class(t(1), t(3)));
    // Duplicate union is a no-op.
    assert!(!uf.union(t(2), t(1), asserted(101)));
    assert_eq!(uf.merge_log().len(), 1);
    assert!(uf.union(t(3), t(4), asserted(102)));
    assert!(uf.union(t(1), t(3), asserted(103)));
    assert!(uf.same_class(t(2), t(4)));
    assert_eq!(uf.merge_log().len(), 3);
    let mut members = uf.class_members(t(4));
    members.sort_unstable_by_key(|x| x.0);
    assert_eq!(members, vec![t(1), t(2), t(3), t(4)]);
}

#[test]
fn scope_push_pop_undoes_unions_exactly() {
    let mut uf = ArrayUnionFind::default();
    uf.union(t(1), t(2), asserted(100));
    uf.push_scope();
    uf.union(t(3), t(4), asserted(101));
    uf.union(t(1), t(4), asserted(102));
    assert!(uf.same_class(t(2), t(3)));
    assert_eq!(uf.merge_log().len(), 3);
    uf.pop_scope();
    // Scope contents inverted; pre-scope union intact.
    assert!(uf.same_class(t(1), t(2)));
    assert!(!uf.same_class(t(3), t(4)));
    assert!(!uf.same_class(t(1), t(4)));
    assert_eq!(uf.merge_log().len(), 1);
    assert_eq!(uf.class_members(t(3)), vec![t(3)]);
    assert_eq!(uf.class_members(t(4)), vec![t(4)]);
    // Nested scopes.
    uf.push_scope();
    uf.union(t(1), t(5), asserted(103));
    uf.push_scope();
    uf.union(t(6), t(7), asserted(104));
    uf.pop_scope();
    assert!(!uf.same_class(t(6), t(7)));
    assert!(uf.same_class(t(5), t(2)));
    uf.pop_scope();
    assert!(!uf.same_class(t(5), t(1)));
}

#[test]
fn class_member_motion_absorbed_into_kept() {
    let mut uf = ArrayUnionFind::default();
    // Build a rank-1 class {1,2,3} and a rank-0 class {4}.
    uf.union(t(1), t(2), asserted(100));
    uf.union(t(1), t(3), asserted(101));
    let big_root = uf.find(t(1));
    uf.union(t(4), t(1), asserted(102));
    // The lower-rank singleton is absorbed into the bigger class's root.
    assert_eq!(uf.find(t(4)), big_root);
    assert_eq!(uf.merge_log().last(), Some(&(big_root, t(4))));
    let members = uf.class_members(t(4));
    assert_eq!(members.len(), 4);
    // Kept class's members stay in place; absorbed members are appended.
    assert_eq!(members.last(), Some(&t(4)));
}

#[test]
fn proof_forest_edge_recording_asserted_vs_sentinel() {
    let mut uf = ArrayUnionFind::default();
    uf.union(t(1), t(2), asserted(100));
    let child = if uf.find(t(1)) == t(1) { t(2) } else { t(1) };
    let edge = uf.edge(child).expect("absorbed root has an edge");
    assert_eq!((edge.a, edge.b), (t(1), t(2)));
    assert!(edge.just.is_asserted());
    assert_eq!(edge.just, asserted(100));
    // Roots have no edge.
    assert!(uf.edge(uf.find(t(1))).is_none());

    let ext = EqJustification::External {
        key: (t(3), t(4)),
        has_reasons: true,
    };
    uf.union(t(3), t(4), ext);
    let child = if uf.find(t(3)) == t(3) { t(4) } else { t(3) };
    let edge = uf.edge(child).expect("absorbed root has an edge");
    assert!(!edge.just.is_asserted());
    assert_eq!(edge.just, ext);
}

#[test]
fn deterministic_across_rebuild() {
    let edges = [(1u32, 2u32), (3, 4), (2, 3), (5, 6), (6, 1), (7, 8)];
    let build = || {
        let mut uf = ArrayUnionFind::default();
        for (i, &(a, b)) in edges.iter().enumerate() {
            uf.union(t(a), t(b), asserted(100 + i as u32));
        }
        uf
    };
    let uf1 = build();
    let uf2 = build();
    assert_eq!(uf1.merge_log(), uf2.merge_log());
    assert_eq!(uf1.non_singleton_classes(), uf2.non_singleton_classes());
    for n in 1..=8 {
        assert_eq!(uf1.find(t(n)), uf2.find(t(n)));
    }
    // clear() starts a fresh era.
    let mut uf3 = build();
    uf3.clear();
    assert!(uf3.merge_log().is_empty());
    assert!(!uf3.same_class(t(1), t(2)));
    assert!(uf3.non_singleton_classes().is_empty());
}

/// The explanation edges, viewed as an undirected relation, must connect
/// the queried endpoints (transitive closure check).
fn assert_edges_connect(edges: &[EqEdge], from: TermId, to: TermId) {
    let mut reached = vec![from];
    let mut changed = true;
    while changed && !reached.contains(&to) {
        changed = false;
        for e in edges {
            let has_a = reached.contains(&e.a);
            let has_b = reached.contains(&e.b);
            if has_a && !has_b {
                reached.push(e.b);
                changed = true;
            } else if has_b && !has_a {
                reached.push(e.a);
                changed = true;
            }
        }
    }
    assert!(
        reached.contains(&to),
        "explanation edges must connect {from:?} to {to:?}: {edges:?}"
    );
}

#[test]
fn explain_connects_endpoints_on_chains_and_diamonds() {
    let mut uf = ArrayUnionFind::default();
    assert_eq!(uf.explain(t(1), t(1)), Some(vec![]));
    assert_eq!(uf.explain(t(1), t(2)), None);

    // Chain 1-2-3-4-5 built out of order, plus a diamond shortcut that is
    // a no-op union (not in the forest).
    uf.union(t(1), t(2), asserted(100));
    uf.union(t(4), t(5), asserted(101));
    uf.union(t(3), t(4), asserted(102));
    uf.union(t(2), t(3), asserted(103));
    assert!(!uf.union(t(1), t(5), asserted(104)));

    for (x, y) in [(1u32, 5u32), (5, 1), (2, 4), (1, 3), (3, 5)] {
        let edges = uf.explain(t(x), t(y)).expect("same class");
        assert_edges_connect(&edges, t(x), t(y));
        // Only recorded (forest) justifications appear.
        assert!(edges.iter().all(|e| e.just != asserted(104)));
    }
    assert_eq!(uf.explain(t(1), t(6)), None);
}

#[test]
fn explain_crosses_class_merges_of_unrelated_endpoints() {
    // Merge two multi-member classes by an edge between non-root members;
    // explaining across it requires the recursive sub-explanations.
    let mut uf = ArrayUnionFind::default();
    uf.union(t(1), t(2), asserted(100));
    uf.union(t(2), t(3), asserted(101));
    uf.union(t(10), t(11), asserted(102));
    uf.union(t(11), t(12), asserted(103));
    uf.union(t(3), t(12), asserted(104)); // bridge between members
    let edges = uf.explain(t(1), t(10)).expect("same class");
    assert_edges_connect(&edges, t(1), t(10));

    // Mixed asserted/external justifications survive the walk.
    let ext = EqJustification::External {
        key: (t(20), t(1)),
        has_reasons: true,
    };
    uf.union(t(20), t(1), ext);
    let edges = uf.explain(t(20), t(10)).expect("same class");
    assert_edges_connect(&edges, t(20), t(10));
    assert!(edges.iter().any(|e| e.just == ext));
}

#[test]
fn explain_soundness_stress() {
    // Randomized: many union sequences; every same-class pair's explanation
    // must (a) use only recorded union edges and (b) connect the endpoints.
    let mut state: u64 = 0x9E3779B97F4A7C15;
    let mut rand = || {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        state
    };
    for _ in 0..400 {
        let mut uf = ArrayUnionFind::default();
        let n = 3 + (rand() % 12) as u32;
        let mut recorded: Vec<(TermId, TermId)> = Vec::new();
        let edge_count = 2 + (rand() % 20) as usize;
        for k in 0..edge_count {
            let a = t(1 + (rand() % n as u64) as u32);
            let b = t(1 + (rand() % n as u64) as u32);
            if uf.union(a, b, asserted(1000 + k as u32)) {
                recorded.push((a, b));
            }
        }
        for x in 1..=n {
            for y in 1..=n {
                let ex = uf.explain(t(x), t(y));
                if uf.same_class(t(x), t(y)) {
                    let edges = ex.expect("same class must explain");
                    // (a) every returned edge is a recorded union edge.
                    for e in &edges {
                        assert!(
                            recorded.contains(&(e.a, e.b)) || recorded.contains(&(e.b, e.a)),
                            "explain returned a non-recorded edge {e:?}"
                        );
                    }
                    // (b) the edges connect x to y.
                    assert_edges_connect(&edges, t(x), t(y));
                } else {
                    assert_eq!(ex, None, "distinct classes must not explain");
                }
            }
        }
    }
}

#[test]
fn non_singleton_classes_partitions() {
    let mut uf = ArrayUnionFind::default();
    uf.union(t(5), t(9), asserted(100));
    uf.union(t(2), t(3), asserted(101));
    uf.union(t(9), t(7), asserted(102));
    // Touch a singleton via a scoped union then undo it.
    uf.push_scope();
    uf.union(t(11), t(5), asserted(103));
    uf.pop_scope();
    assert_eq!(
        uf.non_singleton_classes(),
        vec![vec![t(2), t(3)], vec![t(5), t(7), t(9)]]
    );
}
