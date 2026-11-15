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
//! never per lookup: at `find` entry it made every lookup O(len) in debug and
//! test builds, and a caller that looks up once per element went quadratic
//! (see `ay_euf`'s twin of this module for the measured deadline overrun).

/// `parent` is a forest over `0..len`: every entry names a valid index.
///
/// O(len): assert it once per forest, never per lookup (see the module doc).
#[inline]
pub(super) fn is_forest(parent: &[usize]) -> bool {
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
pub(super) fn find(parent: &mut [usize], mut x: usize) -> usize {
    assert!(
        x < parent.len(),
        "union-find: index {x} out of range for forest of {}",
        parent.len()
    );
    loop {
        let p = parent[x];
        if p == x {
            return x;
        }
        assert!(
            p < parent.len(),
            "union-find: forest entry {p} out of range for forest of {}",
            parent.len()
        );
        let gp = parent[p];
        assert!(
            gp < parent.len(),
            "union-find: forest entry {gp} out of range for forest of {}",
            parent.len()
        );
        parent[x] = gp;
        x = gp;
    }
}

#[cfg(test)]
thread_local! {
    /// `is_forest` calls on this thread (test builds only).
    static WHOLE_FOREST_SCANS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

/// `is_forest` calls so far on this thread (test builds only).
#[cfg(test)]
pub(super) fn whole_forest_scans() -> usize {
    WHOLE_FOREST_SCANS.with(std::cell::Cell::get)
}

#[cfg(test)]
mod tests {
    use super::{find, is_forest, whole_forest_scans};

    /// Lookups never scan the whole forest. A per-lookup `debug_assert!(
    /// is_forest(..))` makes this 4,096 scans (16.7M entry reads) in a debug
    /// build; the checked forest costs its one scan below and no more.
    #[test]
    fn lookups_do_not_scan_the_whole_forest() {
        const N: usize = 4096;
        // A single path N-1 -> N-2 -> ... -> 0: the deepest forest.
        let mut parent: Vec<usize> = (0..N).map(|i| i.saturating_sub(1)).collect();
        let before = whole_forest_scans();
        assert!(is_forest(&parent));
        for x in (0..N).rev() {
            assert_eq!(find(&mut parent, x), 0);
        }
        assert_eq!(
            whole_forest_scans().saturating_sub(before),
            1,
            "one whole-forest check, zero per lookup"
        );
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
    fn an_out_of_range_lookup_panics() {
        let mut parent: Vec<usize> = vec![0, 1, 2];
        find(&mut parent, 3);
    }
}
