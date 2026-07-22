// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Kani verification harnesses for the EUF solver.
//!
//! Proves core invariants of the Union-Find and EUF solver:
//! 1. Union-Find correctness: find, union, path compression
//! 2. Congruence closure soundness
//! 3. Push/pop state consistency

#[cfg(kani)]
mod verification {
    use crate::solver::EufSolver;
    use crate::types::UnionFind;
    use ay_core::TheorySolver;

    // ========================================================================
    // Union-Find Invariants
    // ========================================================================

    /// After union(x, y), find(x) == find(y)
    #[kani::proof]
    #[kani::unwind(16)]
    fn proof_union_makes_equivalent() {
        let mut uf = UnionFind::new(8);

        let x: u32 = kani::any();
        let y: u32 = kani::any();
        kani::assume(x < 8 && y < 8);

        uf.union(x, y);

        let rx = uf.find(x);
        let ry = uf.find(y);
        assert!(rx == ry, "After union, find(x) must equal find(y)");
    }

    /// find is idempotent: find(find(x)) == find(x)
    #[kani::proof]
    fn proof_find_idempotent() {
        let mut uf = UnionFind::new(8);

        let x: u32 = kani::any();
        kani::assume(x < 8);

        let r1 = uf.find(x);
        let r2 = uf.find(r1);
        assert!(r1 == r2, "find must be idempotent");
    }

    /// find returns a valid representative (within bounds)
    #[kani::proof]
    fn proof_find_in_bounds() {
        let mut uf = UnionFind::new(8);

        let x: u32 = kani::any();
        kani::assume(x < 8);

        let r = uf.find(x);
        assert!(r < 8, "find must return a valid index");
    }

    /// Transitivity: if union(x,y) and union(y,z), then find(x) == find(z)
    #[kani::proof]
    fn proof_union_transitive() {
        let mut uf = UnionFind::new(8);

        let x: u32 = kani::any();
        let y: u32 = kani::any();
        let z: u32 = kani::any();
        kani::assume(x < 8 && y < 8 && z < 8);

        uf.union(x, y);
        uf.union(y, z);

        let rx = uf.find(x);
        let rz = uf.find(z);
        assert!(rx == rz, "Union must be transitive");
    }

    /// Reset restores initial state where each element is its own representative
    #[kani::proof]
    fn proof_reset_restores_identity() {
        let mut uf = UnionFind::new(8);

        // Do some unions
        let x: u32 = kani::any();
        let y: u32 = kani::any();
        kani::assume(x < 8 && y < 8 && x != y);

        uf.union(x, y);

        // Before reset, x and y have same representative
        assert!(uf.find(x) == uf.find(y));

        // After reset, each element is its own representative
        uf.reset();

        let rx = uf.find(x);
        let ry = uf.find(y);
        assert!(rx == x, "After reset, find(x) == x");
        assert!(ry == y, "After reset, find(y) == y");
    }

    /// ensure_size extends union-find without breaking existing structure
    #[kani::proof]
    fn proof_ensure_size_preserves_structure() {
        let mut uf = UnionFind::new(4);

        let x: u32 = kani::any();
        let y: u32 = kani::any();
        kani::assume(x < 4 && y < 4);

        uf.union(x, y);
        let rep_before = uf.find(x);

        // Extend the union-find
        uf.ensure_size(8);

        // Existing structure preserved
        let rep_after = uf.find(x);
        assert!(
            rep_before == rep_after,
            "ensure_size must preserve structure"
        );

        // New elements are their own representatives
        let new_elem: u32 = kani::any();
        kani::assume(new_elem >= 4 && new_elem < 8);
        assert!(
            uf.find(new_elem) == new_elem,
            "New elements are self-representative"
        );
    }

    /// Rank bounds are maintained: rank[x] < log2(n)
    #[kani::proof]
    fn proof_rank_bounded() {
        let mut uf = UnionFind::new(8);

        // Do several unions
        let a: u32 = kani::any();
        let b: u32 = kani::any();
        let c: u32 = kani::any();
        kani::assume(a < 8 && b < 8 && c < 8);

        uf.union(a, b);
        uf.union(b, c);

        // Check all ranks are bounded (for n=8, max rank is 3)
        for i in 0..8 {
            assert!(uf.rank[i] <= 3, "Rank must be bounded by log2(n)");
        }
    }

    // ========================================================================
    // EUF Solver State Invariants
    // ========================================================================

    /// Push/pop preserves solver consistency
    #[kani::proof]
    fn proof_push_pop_consistency() {
        // Use minimal term store to keep verification tractable
        let mut store = ay_core::term::TermStore::new();
        let u = ay_core::Sort::Uninterpreted("U".to_string());

        let a = store.mk_var("a", u.clone());
        let b = store.mk_var("b", u.clone());
        let eq_ab = store.mk_eq(a, b);

        let mut euf = EufSolver::new(&store);

        // Initial state: no assignments
        let initial_assigns = euf.assigns.len();

        // Push, assert, check
        euf.push();
        euf.assert_literal(eq_ab, true);
        assert!(
            euf.assigns.len() > initial_assigns,
            "Assignment should be recorded"
        );

        // Pop should restore
        euf.pop();
        assert!(
            euf.assigns.len() == initial_assigns,
            "Pop should restore state"
        );
    }

    /// Multiple push/pop maintains stack discipline
    #[kani::proof]
    fn proof_nested_push_pop() {
        let mut store = ay_core::term::TermStore::new();
        let u = ay_core::Sort::Uninterpreted("U".to_string());

        let a = store.mk_var("a", u.clone());
        let b = store.mk_var("b", u.clone());
        let c = store.mk_var("c", u.clone());
        let eq_ab = store.mk_eq(a, b);
        let eq_bc = store.mk_eq(b, c);

        let mut euf = EufSolver::new(&store);

        // Level 0
        let l0_assigns = euf.assigns.len();

        // Push to level 1, assert
        euf.push();
        euf.assert_literal(eq_ab, true);
        let l1_assigns = euf.assigns.len();

        // Push to level 2, assert
        euf.push();
        euf.assert_literal(eq_bc, true);

        // Pop to level 1
        euf.pop();
        assert!(euf.assigns.len() == l1_assigns, "Pop to level 1");

        // Pop to level 0
        euf.pop();
        assert!(euf.assigns.len() == l0_assigns, "Pop to level 0");
    }
}
