// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Shared skolem cache for executor-level string decompositions.
//!
//! The string pipeline has multiple decomposition paths (pre-registration and
//! runtime lemmas). This cache ensures each logical decomposition key reuses a
//! canonical skolem `TermId` instead of creating incompatible fresh variables.

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::term::TermStore;
use ay_core::{Sort, TermId};

const DUMMY: TermId = TermId(u32::MAX);

/// Decomposition kinds used in executor-level string preprocessing and lemmas.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(in crate::executor::theories) enum SkolemKind {
    ConstSplit,
    VarSplit,
    ContainsPre,
    ContainsPost,
    PrefixRemainder,
    SuffixRemainder,
    SubstrPre,
    SubstrResult,
    SubstrSuffix,
    IndexofPre,
    IndexofSuffix,
    ReplaceResult,
    ReplacePre,
    ReplaceSuffix,
    /// Single-character digit skolem `d_i` for the `str.to_int` digit
    /// decomposition (extf wave 2). The `usize` key slot carries the
    /// 1-based character position; the same position skolem is shared
    /// across all length cases.
    ToIntDigit,
    /// Integer value skolem `v_i` for the `str.to_int` digit at position
    /// `i` (extf wave 2): `-1` for a non-digit, else `0..=9`.
    ToIntDigitVal,
    /// First-match prefix skolem for the `str.replace_all` one-step
    /// reduction (extf wave 2).
    ReplaceAllPre,
    /// First-match suffix skolem for the `str.replace_all` one-step
    /// reduction (extf wave 2). The recursive `replace_all(suf, t, u)`
    /// application is built on this skolem.
    ReplaceAllSuffix,
    /// Result skolem bridging a `str.from_int` application to a plain
    /// string variable (strings increment P3, default ON): keeps the
    /// normal-form machinery from bailing on the opaque extf component,
    /// mirroring `ReplaceResult` for the regex-replace reductions.
    FromIntResult,
}

type CacheKey = (TermId, TermId, SkolemKind, usize);

/// Canonical skolem registry for string decomposition paths.
#[derive(Debug, Default)]
pub(in crate::executor) struct ExecutorSkolemCache {
    cache: HashMap<CacheKey, TermId>,
}

impl ExecutorSkolemCache {
    pub(in crate::executor::theories) fn new() -> Self {
        Self {
            cache: HashMap::default(),
        }
    }

    fn get_or_create(
        &mut self,
        terms: &mut TermStore,
        key: CacheKey,
        prefix: &'static str,
    ) -> TermId {
        self.get_or_create_sorted(terms, key, prefix, Sort::String)
    }

    fn get_or_create_sorted(
        &mut self,
        terms: &mut TermStore,
        key: CacheKey,
        prefix: &'static str,
        sort: Sort,
    ) -> TermId {
        if let Some(existing) = self.cache.get(&key).copied() {
            return existing;
        }
        let fresh = terms.mk_fresh_var(prefix, sort);
        self.cache.insert(key, fresh);
        fresh
    }

    fn normalized_pair(lhs: TermId, rhs: TermId) -> (TermId, TermId) {
        if lhs <= rhs {
            (lhs, rhs)
        } else {
            (rhs, lhs)
        }
    }

    pub(in crate::executor::theories) fn const_split(
        &mut self,
        terms: &mut TermStore,
        x: TermId,
        constant: TermId,
        char_offset: usize,
    ) -> TermId {
        self.get_or_create(
            terms,
            (x, constant, SkolemKind::ConstSplit, char_offset),
            "sk_cspt",
        )
    }

    pub(in crate::executor::theories) fn var_split(
        &mut self,
        terms: &mut TermStore,
        x: TermId,
        y: TermId,
    ) -> TermId {
        let (lhs, rhs) = Self::normalized_pair(x, y);
        self.get_or_create(terms, (lhs, rhs, SkolemKind::VarSplit, 0), "sk_vspt")
    }

    pub(in crate::executor::theories) fn contains_pre(
        &mut self,
        terms: &mut TermStore,
        haystack: TermId,
        needle: TermId,
    ) -> TermId {
        self.get_or_create(
            terms,
            (haystack, needle, SkolemKind::ContainsPre, 0),
            "sk_ctn_pre",
        )
    }

    pub(in crate::executor::theories) fn contains_post(
        &mut self,
        terms: &mut TermStore,
        haystack: TermId,
        needle: TermId,
    ) -> TermId {
        self.get_or_create(
            terms,
            (haystack, needle, SkolemKind::ContainsPost, 0),
            "sk_ctn_post",
        )
    }

    pub(in crate::executor::theories) fn prefix_remainder(
        &mut self,
        terms: &mut TermStore,
        haystack: TermId,
        pattern: TermId,
    ) -> TermId {
        self.get_or_create(
            terms,
            (haystack, pattern, SkolemKind::PrefixRemainder, 0),
            "sk_pfx_suf",
        )
    }

    pub(in crate::executor::theories) fn suffix_remainder(
        &mut self,
        terms: &mut TermStore,
        haystack: TermId,
        pattern: TermId,
    ) -> TermId {
        self.get_or_create(
            terms,
            (haystack, pattern, SkolemKind::SuffixRemainder, 0),
            "sk_sfx_pre",
        )
    }

    pub(in crate::executor::theories) fn substr_pre(
        &mut self,
        terms: &mut TermStore,
        substr_term: TermId,
    ) -> TermId {
        self.get_or_create(
            terms,
            (substr_term, DUMMY, SkolemKind::SubstrPre, 0),
            "sk_sub_pre",
        )
    }

    pub(in crate::executor::theories) fn substr_result(
        &mut self,
        terms: &mut TermStore,
        substr_term: TermId,
    ) -> TermId {
        self.get_or_create(
            terms,
            (substr_term, DUMMY, SkolemKind::SubstrResult, 0),
            "sk_sub_res",
        )
    }

    pub(in crate::executor::theories) fn substr_suffix(
        &mut self,
        terms: &mut TermStore,
        substr_term: TermId,
    ) -> TermId {
        self.get_or_create(
            terms,
            (substr_term, DUMMY, SkolemKind::SubstrSuffix, 0),
            "sk_sub_suf",
        )
    }

    /// Window prefix skolem for the `str.indexof` first-occurrence reduction
    /// (CAP-2): the part of the search window before the first match.
    pub(in crate::executor::theories) fn indexof_pre(
        &mut self,
        terms: &mut TermStore,
        indexof_term: TermId,
    ) -> TermId {
        self.get_or_create(
            terms,
            (indexof_term, DUMMY, SkolemKind::IndexofPre, 0),
            "sk_io_pre",
        )
    }

    /// Window suffix skolem for the `str.indexof` first-occurrence reduction
    /// (CAP-2): the part of the search window after the first match.
    pub(in crate::executor::theories) fn indexof_suffix(
        &mut self,
        terms: &mut TermStore,
        indexof_term: TermId,
    ) -> TermId {
        self.get_or_create(
            terms,
            (indexof_term, DUMMY, SkolemKind::IndexofSuffix, 0),
            "sk_io_suf",
        )
    }

    pub(in crate::executor::theories) fn replace_result(
        &mut self,
        terms: &mut TermStore,
        replace_term: TermId,
    ) -> TermId {
        self.get_or_create(
            terms,
            (replace_term, DUMMY, SkolemKind::ReplaceResult, 0),
            "sk_rep_res",
        )
    }

    pub(in crate::executor::theories) fn replace_pre(
        &mut self,
        terms: &mut TermStore,
        replace_term: TermId,
    ) -> TermId {
        self.get_or_create(
            terms,
            (replace_term, DUMMY, SkolemKind::ReplacePre, 0),
            "sk_rep_pre",
        )
    }

    pub(in crate::executor::theories) fn replace_suffix(
        &mut self,
        terms: &mut TermStore,
        replace_term: TermId,
    ) -> TermId {
        self.get_or_create(
            terms,
            (replace_term, DUMMY, SkolemKind::ReplaceSuffix, 0),
            "sk_rep_suf",
        )
    }

    /// Single-character digit skolem `d_i` (1-based position `i`) for the
    /// `str.to_int` digit decomposition (extf wave 2).
    // Named after the SMT-LIB `str.to_int` operator, not a `to_*` conversion.
    #[allow(clippy::wrong_self_convention)]
    pub(in crate::executor::theories) fn to_int_digit(
        &mut self,
        terms: &mut TermStore,
        to_int_term: TermId,
        position: usize,
    ) -> TermId {
        self.get_or_create(
            terms,
            (to_int_term, DUMMY, SkolemKind::ToIntDigit, position),
            "sk_ti_dig",
        )
    }

    /// Integer digit-value skolem `v_i` (1-based position `i`) for the
    /// `str.to_int` digit decomposition (extf wave 2). Int sorted:
    /// `-1` when `d_i` is a non-digit, else the digit value `0..=9`.
    // Named after the SMT-LIB `str.to_int` operator, not a `to_*` conversion.
    #[allow(clippy::wrong_self_convention)]
    pub(in crate::executor::theories) fn to_int_digit_val(
        &mut self,
        terms: &mut TermStore,
        to_int_term: TermId,
        position: usize,
    ) -> TermId {
        self.get_or_create_sorted(
            terms,
            (to_int_term, DUMMY, SkolemKind::ToIntDigitVal, position),
            "sk_ti_val",
            Sort::Int,
        )
    }

    /// First-match prefix skolem for the `str.replace_all` one-step
    /// reduction (extf wave 2).
    pub(in crate::executor::theories) fn replace_all_pre(
        &mut self,
        terms: &mut TermStore,
        replace_all_term: TermId,
    ) -> TermId {
        self.get_or_create(
            terms,
            (replace_all_term, DUMMY, SkolemKind::ReplaceAllPre, 0),
            "sk_rpa_pre",
        )
    }

    /// First-match suffix skolem for the `str.replace_all` one-step
    /// reduction (extf wave 2).
    pub(in crate::executor::theories) fn replace_all_suffix(
        &mut self,
        terms: &mut TermStore,
        replace_all_term: TermId,
    ) -> TermId {
        self.get_or_create(
            terms,
            (replace_all_term, DUMMY, SkolemKind::ReplaceAllSuffix, 0),
            "sk_rpa_suf",
        )
    }

    /// Result skolem bridging a `str.from_int` application to a plain string
    /// variable (strings increment P3).
    // Named after the SMT-LIB `str.from_int` operator, not a `from_*` constructor.
    #[allow(clippy::wrong_self_convention)]
    pub(in crate::executor::theories) fn from_int_result(
        &mut self,
        terms: &mut TermStore,
        from_int_term: TermId,
    ) -> TermId {
        self.get_or_create(
            terms,
            (from_int_term, DUMMY, SkolemKind::FromIntResult, 0),
            "sk_fi_res",
        )
    }
}

#[cfg(test)]
#[path = "skolem_cache_tests.rs"]
mod tests;
