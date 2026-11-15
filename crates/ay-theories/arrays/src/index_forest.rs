// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Path-halving union-find over an index forest.
//!
//! The structural invariant -- `parent` is a forest over `0..len`, every entry
//! names a valid index -- is not expressible to the verifier in a form it can
//! use here: a `forall` in a `requires` is accepted, but the matching loop
//! `invariant` is refused ("no unique exact compiler-typed proposition"), and
//! with the contract machinery engaged `find` went from ONE refuted obligation
//! to seven. Measured 2026-09-10 on seal trust-28aee49d.
//!
//! So the invariant is checked where it is USED instead: every index read
//! from the forest is asserted in range before it indexes. On a well-formed
//! forest that is the identity; on a malformed one it panics with a message
//! naming the violation, where the implicit index would have panicked with a
//! bounds message -- same outcome, and now a stated, explicit check rather
//! than an unstated assumption.
//!
//! `is_forest` is the whole-forest form. It is O(len), so a caller debug-
//! asserts it ONCE per forest, after the batch of writes that built it --
//! never per lookup: at `find` entry it made every lookup (and so every
//! `union`) O(len) in debug and test builds, and a caller that looks up once
//! per element went quadratic (see `ay_euf`'s twin of this module for the
//! measured deadline overrun).

/// `parent` is a forest over `0..len`: every entry names a valid index.
///
/// O(len): assert it once per forest, never per lookup (see the module doc).
#[inline]
pub(crate) fn is_forest(parent: &[usize]) -> bool {
    #[cfg(test)]
    WHOLE_FOREST_SCANS.with(|n| n.set(n.get().saturating_add(1)));
    parent.iter().all(|&p| p < parent.len())
}

/// Root of `x` in the forest `parent`, halving the path as it walks.
///
/// O(path length): no whole-forest scan here (see the module doc); each
/// index read is asserted as it is read.
///
/// # Panics
/// If `x` or any parent entry reached is not a valid index (a malformed
/// forest).
pub(crate) fn find(parent: &mut [usize], mut x: usize) -> usize {
    let len = parent.len();
    // Every read goes through `get`: an assert ahead of a bare index is a
    // fact the verifier does not carry across this loop's back-edge, so the
    // three indexings here were refuted even with their asserts in place.
    // The panics are the same checks with the same messages, now at the read.
    loop {
        // `x` is the caller's index on the first pass and an entry asserted in
        // range below on every later one, so only a bad argument reaches this.
        let Some(&p) = parent.get(x) else {
            panic!("union-find: index {x} out of range for forest of {len}");
        };
        if p == x {
            return x;
        }
        let Some(&gp) = parent.get(p) else {
            panic!("union-find: forest entry {p} out of range for forest of {len}");
        };
        assert!(
            gp < len,
            "union-find: forest entry {gp} out of range for forest of {len}"
        );
        // `x` was read in range at the top of this pass.
        if let Some(slot) = parent.get_mut(x) {
            *slot = gp;
        }
        x = gp;
    }
}

/// Join the classes of `a` and `b`, attaching to the smaller root so the
/// produced forest is deterministic.
///
/// # Panics
/// As [`find`].
pub(crate) fn union(parent: &mut [usize], a: usize, b: usize) {
    let ra = find(parent, a);
    let rb = find(parent, b);
    // `find` returns an index of `parent` on any forest it did not panic on,
    // but that is not a fact the verifier can carry across the call without a
    // contract this grammar cannot express (see the module doc), so the two
    // roots are asserted here before they index.
    let len = parent.len();
    assert!(
        ra < len,
        "union-find: root {ra} out of range for forest of {len}"
    );
    assert!(
        rb < len,
        "union-find: root {rb} out of range for forest of {len}"
    );
    if ra != rb {
        if ra < rb {
            parent[rb] = ra;
        } else {
            parent[ra] = rb;
        }
    }
}

#[cfg(test)]
thread_local! {
    /// `is_forest` calls on this thread (test builds only).
    static WHOLE_FOREST_SCANS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

/// `is_forest` calls so far on this thread (test builds only).
#[cfg(test)]
pub(crate) fn whole_forest_scans() -> usize {
    WHOLE_FOREST_SCANS.with(std::cell::Cell::get)
}

#[cfg(test)]
mod tests {
    use super::{find, is_forest, union, whole_forest_scans};

    /// Lookups and unions never scan the whole forest. A per-lookup
    /// `debug_assert!(is_forest(..))` makes this 12,286 scans (50M entry
    /// reads) in a debug build; the checked forest costs its one scan below.
    #[test]
    fn lookups_and_unions_do_not_scan_the_whole_forest() {
        const N: usize = 4096;
        let mut parent: Vec<usize> = (0..N).collect();
        let before = whole_forest_scans();
        // Chain every index onto its predecessor: one class rooted at 0.
        for (prev, i) in (0..N).zip(1..N) {
            union(&mut parent, i, prev);
        }
        assert!(is_forest(&parent));
        for x in 0..N {
            assert_eq!(find(&mut parent, x), 0);
        }
        assert_eq!(
            whole_forest_scans().saturating_sub(before),
            1,
            "one whole-forest check, zero per lookup or union"
        );
    }

    /// The whole-forest check was moved, not dropped: partitioning 2 * 512
    /// index occurrences (1,536 unions over the three groupings, then 2,048
    /// lookups) scans the forest exactly once in a debug build (never in
    /// release, where `debug_assert!` is compiled out), where the per-lookup
    /// form scanned it 5,120 times.
    #[test]
    fn index_conflict_partition_checks_its_forest_once() {
        use crate::ArraySolver;
        use ay_core::term::{TermId, TermStore};
        use ay_core::Sort;
        const N: usize = 512;
        let mut store = TermStore::new();
        let vars: Vec<TermId> = (0..N)
            .map(|i| store.mk_var(format!("idx{i}"), Sort::Int))
            .collect();
        // Every index twice, so each grouping unions the two occurrences.
        let indices: Vec<TermId> = vars.iter().chain(vars.iter()).copied().collect();
        let solver = ArraySolver::new(&store);
        let before = whole_forest_scans();
        let partition = solver.index_conflict_partition(&indices);
        assert_eq!(
            whole_forest_scans().saturating_sub(before),
            usize::from(cfg!(debug_assertions)),
            "one whole-forest check per partition, zero per lookup or union"
        );
        assert_eq!(partition.len(), N);
        for v in &vars {
            assert_eq!(
                partition.get(v),
                Some(v),
                "distinct variables stay in singleton blocks"
            );
        }
    }

    /// The per-read assert IS the check: a malformed entry reached by the walk
    /// panics naming it (not a bare bounds message, and not a whole-forest
    /// debug assertion firing first at entry).
    #[test]
    #[should_panic(expected = "union-find: forest entry 7 out of range for forest of 3")]
    fn a_malformed_entry_panics_where_it_is_read() {
        let mut parent: Vec<usize> = vec![0, 7, 1];
        find(&mut parent, 2);
    }

    #[test]
    #[should_panic(expected = "union-find: index 3 out of range for forest of 3")]
    fn an_out_of_range_union_panics() {
        let mut parent: Vec<usize> = vec![0, 1, 2];
        union(&mut parent, 0, 3);
    }
}
