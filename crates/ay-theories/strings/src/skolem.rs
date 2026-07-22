// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Skolem variable cache for the string theory solver.
//!
//! Creates fresh string variables for split lemmas and caches them to avoid
//! redundant creation. Supports incremental push/pop for backtracking.
//!
//! Reference: CVC5 `skolem_cache.cpp` — simplified for AY's initial needs.
//! CVC5 normalizes all skolem IDs down to `SK_PURIFY(substr(...))` for maximal
//! sharing. AY uses a simpler `(t1, t2, kind, char_offset)` cache without
//! substr-based normalization.

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::DetHashMap as HashMap;
#[cfg(test)]
use ay_core::term::TermStore;
#[cfg(test)]
use ay_core::Sort;
use ay_core::TermId;

/// Kinds of skolem variables created during string solving.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[allow(clippy::enum_variant_names)] // Domain names: these are types of splits.
pub(crate) enum SkolemKind {
    /// Empty string split: `x = "" OR x != ""`.
    EmptySplit,
    /// Constant prefix split: `x = "c" ++ k`.
    ConstSplit,
    /// Variable split: `x = y ++ k OR y = x ++ k`.
    VarSplit,
    /// Purification: `k = t` (fresh variable equal to a term).
    #[cfg(test)]
    Purify,
}

/// Cache key: `(term1, term2, kind, char_offset)`.
type CacheKey = (TermId, TermId, SkolemKind, usize);

/// Sentinel for single-argument skolem kinds (EmptySplit, Purify).
const DUMMY: TermId = TermId(u32::MAX);
const NO_OFFSET: usize = 0;

/// Skolem variable cache with push/pop support.
///
/// Each skolem is a fresh `TermData::Var` with `Sort::String` created via
/// `TermStore::mk_fresh_var`. Skolems are cached by
/// `(t1, t2, kind, char_offset)` to avoid creating duplicate variables for the
/// same split.
pub(crate) struct SkolemCache {
    cache: HashMap<CacheKey, CacheValue>,
    /// Trail of cache keys for backtracking; `None` marks push boundaries.
    trail: Vec<Option<CacheKey>>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum CacheValue {
    Marker,
    #[cfg(test)]
    Skolem(TermId),
}

impl SkolemCache {
    pub(crate) fn new() -> Self {
        Self {
            cache: HashMap::default(),
            trail: Vec::new(),
        }
    }

    fn normalize_var_pair(x: TermId, y: TermId) -> (TermId, TermId) {
        if x <= y {
            (x, y)
        } else {
            (y, x)
        }
    }

    fn mark_key(&mut self, key: CacheKey) -> bool {
        if self.cache.contains_key(&key) {
            return false;
        }
        self.cache.insert(key, CacheValue::Marker);
        self.trail.push(Some(key));
        true
    }

    /// Record that an empty string split has been emitted for `x`.
    ///
    /// Returns `true` if this is new (caller should emit the lemma).
    /// Returns `false` if the same split was already requested in this scope
    /// (duplicate suppression across NF pair comparisons in the same check round).
    pub(crate) fn mark_empty_split(&mut self, x: TermId) -> bool {
        self.mark_key((x, DUMMY, SkolemKind::EmptySplit, NO_OFFSET))
    }

    /// Record that a constant split has been emitted for `(x, constant)`.
    ///
    /// `char_offset` distinguishes partial-prefix split requests for the same
    /// `(x, constant)` pair.
    pub(crate) fn mark_const_split(
        &mut self,
        x: TermId,
        constant: TermId,
        char_offset: usize,
    ) -> bool {
        self.mark_key((x, constant, SkolemKind::ConstSplit, char_offset))
    }

    /// Record that a variable split has been emitted for `(x, y)`.
    ///
    /// Order is normalized so `(x, y)` and `(y, x)` are treated as equivalent.
    pub(crate) fn mark_var_split(&mut self, x: TermId, y: TermId) -> bool {
        let (lhs, rhs) = Self::normalize_var_pair(x, y);
        self.mark_key((lhs, rhs, SkolemKind::VarSplit, NO_OFFSET))
    }

    /// Get or create a skolem for a constant prefix split: `x = "c" ++ k`.
    #[cfg(test)]
    pub(crate) fn get_const_split(
        &mut self,
        terms: &mut TermStore,
        x: TermId,
        constant: TermId,
        char_offset: usize,
    ) -> TermId {
        let key = (x, constant, SkolemKind::ConstSplit, char_offset);
        if let Some(CacheValue::Skolem(sk)) = self.cache.get(&key).copied() {
            return sk;
        }
        let sk = terms.mk_fresh_var("sk_cspt", Sort::String);
        let was_new = !self.cache.contains_key(&key);
        self.cache.insert(key, CacheValue::Skolem(sk));
        if was_new {
            self.trail.push(Some(key));
        }
        sk
    }

    /// Get or create a skolem for a variable split: `x = y ++ k OR y = x ++ k`.
    #[cfg(test)]
    pub(crate) fn get_var_split(&mut self, terms: &mut TermStore, x: TermId, y: TermId) -> TermId {
        let (lhs, rhs) = Self::normalize_var_pair(x, y);
        let key = (lhs, rhs, SkolemKind::VarSplit, NO_OFFSET);
        if let Some(CacheValue::Skolem(sk)) = self.cache.get(&key).copied() {
            return sk;
        }
        let sk = terms.mk_fresh_var("sk_vspt", Sort::String);
        let was_new = !self.cache.contains_key(&key);
        self.cache.insert(key, CacheValue::Skolem(sk));
        if was_new {
            self.trail.push(Some(key));
        }
        sk
    }

    /// Get or create a purification skolem: fresh variable `k` equal to term `t`.
    #[cfg(test)]
    pub(crate) fn get_purify(&mut self, terms: &mut TermStore, t: TermId) -> TermId {
        let key = (t, DUMMY, SkolemKind::Purify, NO_OFFSET);
        if let Some(CacheValue::Skolem(sk)) = self.cache.get(&key).copied() {
            return sk;
        }
        let sk = terms.mk_fresh_var("sk_purify", Sort::String);
        let was_new = !self.cache.contains_key(&key);
        self.cache.insert(key, CacheValue::Skolem(sk));
        if was_new {
            self.trail.push(Some(key));
        }
        sk
    }

    /// Push a scope marker for backtracking.
    pub(crate) fn push(&mut self) {
        self.trail.push(None);
    }

    /// Pop the most recent scope, removing skolems created since last push.
    pub(crate) fn pop(&mut self) {
        while let Some(entry) = self.trail.pop() {
            match entry {
                None => break,
                Some(key) => {
                    self.cache.remove(&key);
                }
            }
        }
    }

    /// Reset the cache completely.
    pub(crate) fn reset(&mut self) {
        self.cache.clear();
        self.trail.clear();
    }
}

#[cfg(test)]
#[path = "skolem_tests.rs"]
mod tests;

#[cfg(kani)]
#[path = "skolem_verification.rs"]
mod verification;
