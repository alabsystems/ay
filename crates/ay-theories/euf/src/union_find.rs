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
//! from the forest is read through a checked access before it indexes. On a
//! well-formed forest that is the identity; on a malformed one `sfind`
//! returns a [`ForestError`] naming the violation (where the implicit index
//! would have panicked with a bare bounds message), and the caller decides
//! what a malformed forest means for it. The Trust gate's Level 0 refutes
//! every reachable panic, a stated `assert!` included, so the check is an
//! error value, not a panic.
//!
//! `is_forest` is the whole-forest form. It is O(len), so a caller debug-
//! asserts it ONCE per forest, after the batch of writes that built it --
//! never per lookup. At `sfind` entry it made every lookup O(len) in debug and
//! test builds, and `bool_arg_model_is_congruent` (a few lookups per e-node,
//! all inside one theory check, while the split loop polls its deadline only
//! between checks) went quadratic. Measured 2026-09-23 on 2b5034408: under a
//! 10 s executor deadline the eager heap__swaparray_000 BMC replay script
//! returned after 14.0-14.2 s, one 5.3-5.5 s guard call straddling the
//! deadline (9.0-10.2 s without the scan; cf9c2103f recorded 14.4 s), and
//! ay-dpll's `euf_bool_arg_guard_seed` took 5.2-5.5 s instead of 0.6-1.1 s.

/// `parent` is a forest over `0..len`: every entry names a valid index.
///
/// O(len): assert it once per forest, never per lookup (see the module doc).
#[inline]
pub(crate) fn is_forest(parent: &[u32]) -> bool {
    #[cfg(test)]
    WHOLE_FOREST_SCANS.with(|n| n.set(n.get().saturating_add(1)));
    parent.iter().all(|&p| (p as usize) < parent.len())
}

/// A malformed forest, found by [`sfind`] where the bad index was read.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ForestError {
    /// The looked-up index is not in `0..len`.
    IndexOutOfRange {
        /// The looked-up index.
        index: u32,
        /// The forest's length.
        len: usize,
    },
    /// A parent entry reached by the walk is not in `0..len`.
    EntryOutOfRange {
        /// The out-of-range entry.
        entry: u32,
        /// The forest's length.
        len: usize,
    },
}

impl std::fmt::Display for ForestError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::IndexOutOfRange { index, len } => {
                write!(
                    f,
                    "union-find: index {index} out of range for forest of {len}"
                )
            }
            Self::EntryOutOfRange { entry, len } => {
                write!(
                    f,
                    "union-find: forest entry {entry} out of range for forest of {len}"
                )
            }
        }
    }
}

impl std::error::Error for ForestError {}

/// Root of `x` in the forest `parent`, halving the path as it walks.
///
/// O(path length): no whole-forest scan here (see the module doc); each
/// index read is checked as it is read.
///
/// # Errors
/// If `x` or any parent entry reached is not a valid index (a malformed
/// forest). The walk stops at the bad read: every path-halving write made
/// before it stored an entry already checked in range.
pub(crate) fn sfind(parent: &mut [u32], mut x: u32) -> Result<u32, ForestError> {
    let len = parent.len();
    let Some(&first) = parent.get(x as usize) else {
        return Err(ForestError::IndexOutOfRange { index: x, len });
    };
    // Invariant: `p == parent[x]` and `x` is in range.
    let mut p = first;
    loop {
        if p == x {
            return Ok(x);
        }
        let Some(&gp) = parent.get(p as usize) else {
            return Err(ForestError::EntryOutOfRange { entry: p, len });
        };
        // `gp` is checked in range before it is stored.
        if (gp as usize) >= len {
            return Err(ForestError::EntryOutOfRange { entry: gp, len });
        }
        if let Some(slot) = parent.get_mut(x as usize) {
            *slot = gp;
        }
        x = gp;
        let Some(&next) = parent.get(x as usize) else {
            return Err(ForestError::EntryOutOfRange { entry: x, len });
        };
        p = next;
    }
}

#[cfg(test)]
thread_local! {
    /// `is_forest` calls on this thread (test builds only).
    static WHOLE_FOREST_SCANS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

#[cfg(test)]
mod tests {
    use super::{is_forest, sfind, ForestError, WHOLE_FOREST_SCANS};

    fn scans() -> usize {
        WHOLE_FOREST_SCANS.with(std::cell::Cell::get)
    }

    /// Lookups never scan the whole forest. A per-lookup `debug_assert!(
    /// is_forest(..))` makes this 4,096 scans (16.7M entry reads) in a debug
    /// build; the checked forest costs its one scan below and no more.
    #[test]
    fn lookups_do_not_scan_the_whole_forest() -> Result<(), Box<dyn std::error::Error>> {
        const N: u32 = 4096;
        // A single path N-1 -> N-2 -> ... -> 0: the deepest forest.
        let mut parent: Vec<u32> = (0..N).map(|i| i.saturating_sub(1)).collect();
        let before = scans();
        if !is_forest(&parent) {
            return Err("a single path is a forest".into());
        }
        for x in (0..N).rev() {
            let root = sfind(&mut parent, x)?;
            if root != 0 {
                return Err(format!("root of {x} is {root}, expected 0").into());
            }
        }
        let n_scans = scans().saturating_sub(before);
        if n_scans != 1 {
            return Err(
                format!("one whole-forest check, zero per lookup: got {n_scans} scans").into(),
            );
        }
        Ok(())
    }

    /// The whole-forest check was moved, not dropped: the Bool-arg guard over
    /// 2,048+ e-nodes scans its forest exactly twice in a debug build (after
    /// seeding, after the merges; never in release, where `debug_assert!` is
    /// compiled out), where the per-lookup form scanned it on every lookup --
    /// 6,168 times in this call.
    #[test]
    fn bool_arg_guard_checks_its_forest_once_per_batch() {
        use crate::EufSolver;
        use ay_core::term::{Symbol, TermStore};
        use ay_core::{Sort, TheorySolver};
        let mut store = TermStore::new();
        let u = Sort::Uninterpreted("U".to_string());
        let fillers: Vec<_> = (0..2048)
            .map(|i| store.mk_var(format!("u{i}"), u.clone()))
            .collect();
        let p = store.mk_var("p", Sort::Bool);
        let q = store.mk_var("q", Sort::Bool);
        let fp = store.mk_app(Symbol::named("f"), vec![p], u.clone());
        let fq = store.mk_app(Symbol::named("f"), vec![q], u);
        let mut euf = EufSolver::new(&store);
        euf.init_enodes();
        assert!(euf.enodes.len() > fillers.len());
        euf.assert_literal(p, true);
        euf.assert_literal(q, true);
        let before = scans();
        // `f(p)` and `f(q)` have equal Bool-arg values, so the guard records
        // one forced edge and runs its second batch; nothing forces them apart.
        assert!(euf.bool_arg_model_is_congruent());
        assert_eq!(euf.last_bool_arg_forced_edges, vec![(fp, fq)]);
        assert_eq!(
            scans().saturating_sub(before),
            if cfg!(debug_assertions) { 2 } else { 0 },
            "one whole-forest check per batch, zero per lookup"
        );
    }

    /// The per-read check IS the check: a malformed entry reached by the walk
    /// is reported naming it (not a bare bounds message, and not a
    /// whole-forest debug assertion firing first at entry).
    #[test]
    fn a_malformed_entry_is_reported_where_it_is_read() -> Result<(), Box<dyn std::error::Error>> {
        let mut parent: Vec<u32> = vec![0, 7, 1];
        let err = match sfind(&mut parent, 2) {
            Ok(root) => return Err(format!("malformed forest yielded root {root}").into()),
            Err(err) => err,
        };
        if err != (ForestError::EntryOutOfRange { entry: 7, len: 3 }) {
            return Err(format!("wrong error: {err:?}").into());
        }
        let msg = err.to_string();
        if msg != "union-find: forest entry 7 out of range for forest of 3" {
            return Err(format!("wrong message: {msg}").into());
        }
        // The walk stopped at the bad read: `2 -> 1` was not halved to `7`.
        if parent != [0, 7, 1] {
            return Err(format!("forest written past the bad read: {parent:?}").into());
        }
        Ok(())
    }

    #[test]
    fn an_out_of_range_lookup_is_reported() -> Result<(), Box<dyn std::error::Error>> {
        let mut parent: Vec<u32> = vec![0, 1, 2];
        let err = match sfind(&mut parent, 3) {
            Ok(root) => return Err(format!("out-of-range lookup yielded root {root}").into()),
            Err(err) => err,
        };
        if err != (ForestError::IndexOutOfRange { index: 3, len: 3 }) {
            return Err(format!("wrong error: {err:?}").into());
        }
        let msg = err.to_string();
        if msg != "union-find: index 3 out of range for forest of 3" {
            return Err(format!("wrong message: {msg}").into());
        }
        Ok(())
    }
}
