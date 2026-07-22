// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regex membership solver for ground `str.in_re` constraints.
//!
//! When both the string and regex resolve to concrete values, evaluates
//! membership by recursive descent over the regex structure. Non-ground
//! memberships are marked incomplete.
//!
//! The algorithm is equivalent to Brzozowski derivatives applied to concrete
//! strings, but avoids creating intermediate regex terms (TermStore is
//! immutable in the theory solver context).
//!
//! Reference: CVC5 `regexp_eval.cpp` and `regexp_operation.cpp` (BSD license).
//! Algorithm: Brzozowski, J.A. "Derivatives of Regular Expressions" (1964).

use ay_core::term::{Constant, TermData, TermId, TermStore};
use ay_core::{Symbol, TheoryLit};

use crate::infer::{InferenceKind, InferenceManager};
use crate::state::SolverState;

/// Result of searching for the first regex match in a string.
#[derive(Debug)]
pub(crate) enum MatchResult {
    /// Match found at byte range [start, end).
    Found(usize, usize),
    /// No match anywhere in the string.
    NoMatch,
    /// Regex contains unresolvable constructs.
    Incomplete,
}

/// Regex membership solver.
///
/// Evaluates `str.in_re(s, R)` assertions when both `s` and `R` are ground
/// (fully resolved to concrete values). Non-ground memberships are left
/// incomplete for the DPLL(T) loop to handle via splits.
pub(crate) struct RegExpSolver {
    /// Whether this check round found unresolvable regex memberships.
    incomplete: bool,
}

impl RegExpSolver {
    /// Create a new regex solver.
    pub(crate) fn new() -> Self {
        Self { incomplete: false }
    }

    /// Clear per-check state.
    pub(crate) fn clear(&mut self) {
        self.incomplete = false;
    }

    /// Whether the regex solver has unresolved memberships.
    pub(crate) fn is_incomplete(&self) -> bool {
        self.incomplete
    }

    /// Check all regex membership assertions.
    ///
    /// Scans assertions for `str.in_re(s, R)` atoms. For each:
    /// - If both `s` and `R` resolve to ground values, evaluates membership.
    /// - If the evaluation contradicts the asserted polarity, raises a conflict.
    /// - If either side is non-ground, marks incomplete.
    ///
    /// Returns true if a conflict was found.
    pub(crate) fn check(
        &mut self,
        terms: &TermStore,
        state: &SolverState,
        infer: &mut InferenceManager,
    ) -> bool {
        for &lit in state.assertions() {
            let (atom, polarity) = Self::atom_and_polarity(terms, lit);

            let TermData::App(sym, args) = terms.get(atom) else {
                continue;
            };

            if !matches!(sym.name(), "str.in_re" | "str.in.re") || args.len() != 2 {
                continue;
            }

            let string_term = args[0];
            let regex_term = args[1];

            // Try to resolve the string to a concrete value.
            let string_val = Self::resolve_string(terms, state, string_term);

            if let Some(ref s) = string_val {
                let result = Self::evaluate(terms, s, regex_term);
                match result {
                    Some(matches) => {
                        if matches != polarity {
                            // Evaluation contradicts asserted polarity.
                            // Explain: the membership literal + why string_term
                            // equals its constant representative.
                            let mut explanation = vec![lit];
                            if let Some(const_id) = state.find_constant_term_id(terms, string_term)
                            {
                                if const_id != string_term {
                                    explanation.extend(state.explain(string_term, const_id));
                                }
                            }
                            infer.add_conflict(InferenceKind::PredicateConflict, explanation);
                            return true;
                        }
                    }
                    None => {
                        // Could not evaluate (non-ground regex).
                        self.incomplete = true;
                    }
                }
            } else {
                // String not resolved.
                self.incomplete = true;
            }
        }

        infer.has_conflict()
    }

    /// Evaluate whether concrete string `s` matches regex term `r`.
    ///
    /// Returns `Some(true/false)` for ground regexes, `None` for non-ground.
    ///
    /// This is a recursive descent evaluator that works directly on the
    /// term representation without creating intermediate terms.
    pub(crate) fn evaluate(terms: &TermStore, s: &str, r: TermId) -> Option<bool> {
        let TermData::App(sym, args) = terms.get(r) else {
            return None;
        };

        match sym.name() {
            // re.none: empty language — nothing matches.
            "re.none" if args.is_empty() => Some(false),

            // re.all: universal language — everything matches.
            "re.all" if args.is_empty() => Some(true),

            // re.allchar: matches exactly one character.
            "re.allchar" if args.is_empty() => Some(s.chars().count() == 1),

            // re.range(lo, hi): matches a single character c with lo <= c <= hi.
            //
            // Per SMT-LIB (and z3), (re.range lo hi) denotes the EMPTY language
            // whenever lo or hi is not a single character (length != 1), or when
            // lo > hi. In every such case membership is false for all strings.
            "re.range" if args.len() == 2 => {
                let lo = Self::resolve_string_const(terms, args[0])?;
                let hi = Self::resolve_string_const(terms, args[1])?;
                if lo.chars().count() != 1 || hi.chars().count() != 1 {
                    // Non-singleton endpoint(s): empty language, matches nothing.
                    return Some(false);
                }
                let lo_char = lo.chars().next().unwrap();
                let hi_char = hi.chars().next().unwrap();
                if lo_char > hi_char {
                    // Reversed range: empty language, matches nothing.
                    return Some(false);
                }
                if s.chars().count() != 1 {
                    return Some(false);
                }
                let c = s.chars().next().unwrap();
                Some(lo_char <= c && c <= hi_char)
            }

            // str.to_re(t): matches exactly the string t.
            "str.to_re" | "str.to.re" if args.len() == 1 => {
                let t = Self::resolve_string_const(terms, args[0])?;
                Some(s == t)
            }

            // re.++(R1, R2, ...Rn): concatenation.
            // s matches iff s can be split into s1.s2...sn where si matches Ri.
            "re.++" if !args.is_empty() => {
                let children: Vec<_> = args.clone();
                Self::eval_concat(terms, s, &children, 0)
            }

            // re.union(R1, R2, ...): s matches iff s matches any Ri.
            "re.union" if !args.is_empty() => {
                for &child in args {
                    if Self::evaluate(terms, s, child)? {
                        return Some(true);
                    }
                }
                Some(false)
            }

            // re.inter(R1, R2, ...): s matches iff s matches all Ri.
            "re.inter" if !args.is_empty() => {
                for &child in args {
                    if !Self::evaluate(terms, s, child)? {
                        return Some(false);
                    }
                }
                Some(true)
            }

            // re.*(R): Kleene star. s matches iff s = "" or s can be split
            // into s1.s2...sn where each si is non-empty and matches R.
            "re.*" if args.len() == 1 => {
                if s.is_empty() {
                    return Some(true);
                }
                Self::eval_star(terms, s, args[0])
            }

            // re.+(R): one or more. s matches iff s is non-empty and can be
            // split into parts each matching R.
            "re.+" if args.len() == 1 => {
                if s.is_empty() {
                    return Self::delta(terms, args[0]);
                }
                Self::eval_star(terms, s, args[0])
            }

            // re.opt(R): zero or one. s matches iff s = "" or s matches R.
            "re.opt" if args.len() == 1 => {
                if s.is_empty() {
                    return Some(true);
                }
                Self::evaluate(terms, s, args[0])
            }

            // re.comp(R): complement. s matches iff s does NOT match R.
            "re.comp" if args.len() == 1 => Self::evaluate(terms, s, args[0]).map(|b| !b),

            // re.diff(R1, R2): difference. s matches iff s matches R1 and not R2.
            "re.diff" if args.len() == 2 => {
                let m1 = Self::evaluate(terms, s, args[0])?;
                if !m1 {
                    return Some(false);
                }
                let m2 = Self::evaluate(terms, s, args[1])?;
                Some(!m2)
            }

            // (_ re.loop n m) R: bounded repetition.
            // s matches iff s can be split into k pieces (n <= k <= m) each matching R.
            "re.loop" if args.len() == 1 => {
                let Symbol::Indexed(_, indices) = sym else {
                    return None;
                };
                if indices.len() != 2 {
                    return None;
                }
                let lo = indices[0] as usize;
                let hi = indices[1] as usize;
                if lo > hi {
                    return Some(false);
                }
                Self::eval_loop(terms, s, args[0], lo, hi)
            }

            _ => None,
        }
    }

    /// Evaluate concatenation: does `s` match `children[idx..]`?
    ///
    /// Tries all possible split points for the first child's match length.
    /// Uses backtracking to find a valid decomposition.
    fn eval_concat(terms: &TermStore, s: &str, children: &[TermId], idx: usize) -> Option<bool> {
        if idx >= children.len() {
            return Some(s.is_empty());
        }

        if idx == children.len() - 1 {
            // Last child must match the entire remaining string.
            return Self::evaluate(terms, s, children[idx]);
        }

        // Optimization: if current child is str.to_re(constant), only one
        // split point is valid (the constant must be a prefix).
        if let Some(prefix) = Self::fixed_string(terms, children[idx]) {
            if s.starts_with(prefix.as_str()) {
                return Self::eval_concat(terms, &s[prefix.len()..], children, idx + 1);
            } else {
                return Some(false);
            }
        }

        // General case: try all character-boundary split points.
        // Split at position i: s[..i] matches children[idx], s[i..] matches rest.
        let char_count = s.chars().count();
        for i in 0..=char_count {
            let byte_offset = s.char_indices().nth(i).map(|(b, _)| b).unwrap_or(s.len());
            let prefix = &s[..byte_offset];
            let suffix = &s[byte_offset..];

            if Self::evaluate(terms, prefix, children[idx])?
                && Self::eval_concat(terms, suffix, children, idx + 1)?
            {
                return Some(true);
            }
        }

        Some(false)
    }

    /// Evaluate Kleene star: does non-empty `s` match `R*`?
    ///
    /// Tries all non-empty prefixes of `s` that match `R`, then recursively
    /// checks the remainder against `R*`.
    fn eval_star(terms: &TermStore, s: &str, r: TermId) -> Option<bool> {
        if s.is_empty() {
            return Some(true);
        }

        // Optimization for str.to_re(constant) under star: the constant must
        // tile the string exactly.
        if let Some(pat) = Self::fixed_string(terms, r) {
            if pat.is_empty() {
                // (re.* (str.to_re "")) matches only "".
                return Some(s.is_empty());
            }
            // Check if s is a repetition of pat.
            let mut remaining = s;
            while !remaining.is_empty() {
                if remaining.starts_with(pat.as_str()) {
                    remaining = &remaining[pat.len()..];
                } else {
                    return Some(false);
                }
            }
            return Some(true);
        }

        // General case: try all non-empty prefix lengths.
        let char_count = s.chars().count();
        for len in 1..=char_count {
            let byte_offset = s.char_indices().nth(len).map(|(b, _)| b).unwrap_or(s.len());
            let prefix = &s[..byte_offset];
            let suffix = &s[byte_offset..];

            if Self::evaluate(terms, prefix, r)? && Self::eval_star(terms, suffix, r)? {
                return Some(true);
            }
        }

        Some(false)
    }

    /// Evaluate bounded repetition: does `s` match `R` repeated between `lo` and `hi` times?
    fn eval_loop(terms: &TermStore, s: &str, r: TermId, lo: usize, hi: usize) -> Option<bool> {
        if hi == 0 {
            return Some(s.is_empty());
        }
        if s.is_empty() {
            // The empty string matches the remaining loop iff no more iterations
            // are required (`lo == 0`) OR the body `r` is NULLABLE — in which case
            // each of the remaining `lo` required iterations can match "". The
            // old `lo == 0` check ignored nullable bodies, e.g. `"a"` ∈ `((_
            // re.loop 2 2) (re.opt re.allchar))` (one iteration matches "a", the
            // other matches "" because `re.opt` is nullable) was wrongly rejected
            // → wrong-UNSAT (#regex-loop-nullable).
            if lo == 0 {
                return Some(true);
            }
            return Self::is_nullable(terms, r);
        }
        let char_count = s.chars().count();
        for len in 1..=char_count {
            let byte_offset = s.char_indices().nth(len).map(|(b, _)| b).unwrap_or(s.len());
            let prefix = &s[..byte_offset];
            let suffix = &s[byte_offset..];

            if Self::evaluate(terms, prefix, r)? {
                let new_lo = lo.saturating_sub(1);
                if Self::eval_loop(terms, suffix, r, new_lo, hi - 1)? {
                    return Some(true);
                }
            }
        }
        Some(false)
    }

    /// Whether the regex `r` accepts the empty string (is nullable).
    ///
    /// Returns `Some(true)` if nullable, `Some(false)` if it cannot match the
    /// empty string, `None` if the regex is not ground-evaluable.
    ///
    /// Exposed for the core solver's soundness guard: a non-nullable regex
    /// membership over a string variable implies a positive length lower
    /// bound, which the eager DPLL reductions do not propagate.
    pub(crate) fn is_nullable(terms: &TermStore, r: TermId) -> Option<bool> {
        Self::delta(terms, r)
    }

    /// Nullable check: does the regex accept the empty string?
    ///
    /// Returns `Some(true)` if nullable, `Some(false)` if not,
    /// `None` if unknown (non-ground regex).
    ///
    /// Reference: CVC5 `regexp_operation.cpp:124-264`.
    fn delta(terms: &TermStore, r: TermId) -> Option<bool> {
        let TermData::App(sym, args) = terms.get(r) else {
            return None;
        };

        match sym.name() {
            "re.none" if args.is_empty() => Some(false),
            "re.allchar" if args.is_empty() => Some(false),
            "re.all" if args.is_empty() => Some(true),
            "re.range" if args.len() == 2 => Some(false),

            "str.to_re" | "str.to.re" if args.len() == 1 => {
                let s = Self::resolve_string_const(terms, args[0])?;
                Some(s.is_empty())
            }

            "re.++" if !args.is_empty() => {
                for &child in args {
                    if !Self::delta(terms, child)? {
                        return Some(false);
                    }
                }
                Some(true)
            }

            "re.union" if !args.is_empty() => {
                for &child in args {
                    if Self::delta(terms, child)? {
                        return Some(true);
                    }
                }
                Some(false)
            }

            "re.inter" if !args.is_empty() => {
                for &child in args {
                    if !Self::delta(terms, child)? {
                        return Some(false);
                    }
                }
                Some(true)
            }

            "re.*" | "re.opt" if args.len() == 1 => Some(true),
            "re.+" if args.len() == 1 => Self::delta(terms, args[0]),
            "re.comp" if args.len() == 1 => Self::delta(terms, args[0]).map(|b| !b),

            "re.diff" if args.len() == 2 => {
                let d1 = Self::delta(terms, args[0])?;
                let d2 = Self::delta(terms, args[1])?;
                Some(d1 && !d2)
            }

            // (_ re.loop n m) R: nullable iff n == 0 or R is nullable.
            "re.loop" if args.len() == 1 => {
                let Symbol::Indexed(_, indices) = sym else {
                    return None;
                };
                if indices.len() != 2 {
                    return None;
                }
                if indices[0] == 0 {
                    Some(true)
                } else {
                    Self::delta(terms, args[0])
                }
            }

            _ => None,
        }
    }

    /// Compute the EXACT set of string lengths accepted by regex `r`, but only
    /// when that set is FINITE and bounded.
    ///
    /// Returns:
    /// - `Some(set)` — the regex accepts exactly the lengths in `set` (a finite,
    ///   exhaustive enumeration). A string `s` matches `r` ONLY IF
    ///   `s.chars().count() ∈ set`.
    /// - `None` — the accepted-length set is infinite (e.g. Kleene star over a
    ///   non-empty body) OR the regex contains constructs this analysis cannot
    ///   characterize exactly. Callers MUST treat `None` as "no information".
    ///
    /// SOUNDNESS: this is the cornerstone of the regex-length disjointness
    /// refutation. The returned `Some(set)` is an exact NECESSARY condition on
    /// the length of any accepted string. If an asserted-true `str.in_re(x, r)`
    /// has `accepted_lengths(r) = Some(L)` and `x`'s length is provably some
    /// `n ∉ L`, the membership is unsatisfiable. We NEVER return `Some` for an
    /// over-approximation: every length in the returned set is exact for the
    /// FINITE case, and any regex that could accept an unbounded length yields
    /// `None`. A cap (`MAX_LEN_SET`) on the set size also fails closed to `None`
    /// to avoid pathological blowup; that only ever weakens to "no info".
    ///
    /// Reference: the accepted-length set is the Parikh image projected onto
    /// total length; for these finite-language fragments it is exact.
    pub(crate) fn accepted_lengths(
        terms: &TermStore,
        r: TermId,
    ) -> Option<std::collections::BTreeSet<usize>> {
        Self::accepted_lengths_inner(terms, r, 0)
    }

    /// Maximum cardinality of an accepted-length set before failing closed to
    /// `None`. Bounds work; a larger set is still sound but not worth tracking.
    const MAX_LEN_SET: usize = 4096;

    /// Maximum recursion depth for `accepted_lengths_inner` (guards against
    /// adversarial nesting). Exceeding it fails closed to `None`.
    const MAX_LEN_DEPTH: usize = 64;

    /// Maximum upper repetition bound expanded by the exact `re.loop` length
    /// analysis. Loop indices are untrusted `u32` values; walking `0..=hi`
    /// without a separate work cap lets a constant-size regex request billions
    /// of iterations. Exceeding the cap fails closed to `None` (no length
    /// information), which can only disable an optimization/refutation.
    const MAX_LOOP_LENGTH_UNROLL: usize = 4096;

    fn accepted_lengths_inner(
        terms: &TermStore,
        r: TermId,
        depth: usize,
    ) -> Option<std::collections::BTreeSet<usize>> {
        use std::collections::BTreeSet;
        if depth > Self::MAX_LEN_DEPTH {
            return None;
        }
        let TermData::App(sym, args) = terms.get(r) else {
            return None;
        };

        match sym.name() {
            // Empty language: accepts nothing → empty length set.
            "re.none" if args.is_empty() => Some(BTreeSet::new()),

            // re.allchar: exactly one character → length exactly 1.
            "re.allchar" if args.is_empty() => Some([1].into_iter().collect()),

            // re.range(lo, hi): a single character (if both endpoints are single
            // characters and lo <= hi) → length 1, else the EMPTY language →
            // empty length set. Non-singleton endpoints (length != 1) and a
            // reversed range (lo > hi) both denote the empty language per
            // SMT-LIB. Either way the length set is finite.
            "re.range" if args.len() == 2 => {
                let lo = Self::resolve_string_const(terms, args[0])?;
                let hi = Self::resolve_string_const(terms, args[1])?;
                if lo.chars().count() != 1 || hi.chars().count() != 1 {
                    return Some(BTreeSet::new());
                }
                let lo_char = lo.chars().next().unwrap();
                let hi_char = hi.chars().next().unwrap();
                if lo_char <= hi_char {
                    Some([1].into_iter().collect())
                } else {
                    Some(BTreeSet::new())
                }
            }

            // str.to_re(constant): exactly one string of fixed length.
            "str.to_re" | "str.to.re" if args.len() == 1 => {
                let t = Self::resolve_string_const(terms, args[0])?;
                Some([t.chars().count()].into_iter().collect())
            }

            // re.++(R1..Rn): length set is the pointwise (Minkowski) sum of the
            // children's length sets. Finite iff every child is finite.
            "re.++" if !args.is_empty() => {
                let mut acc: BTreeSet<usize> = [0].into_iter().collect();
                for &child in args {
                    let child_set = Self::accepted_lengths_inner(terms, child, depth + 1)?;
                    if child_set.is_empty() {
                        // A child accepting nothing makes the whole concat empty.
                        return Some(BTreeSet::new());
                    }
                    let mut next = BTreeSet::new();
                    for &a in &acc {
                        for &b in &child_set {
                            let s = a.checked_add(b)?;
                            next.insert(s);
                            if next.len() > Self::MAX_LEN_SET {
                                return None;
                            }
                        }
                    }
                    acc = next;
                }
                Some(acc)
            }

            // re.union(R1..Rn): length set is the union of children's sets.
            "re.union" if !args.is_empty() => {
                let mut acc = BTreeSet::new();
                for &child in args {
                    let child_set = Self::accepted_lengths_inner(terms, child, depth + 1)?;
                    for v in child_set {
                        acc.insert(v);
                        if acc.len() > Self::MAX_LEN_SET {
                            return None;
                        }
                    }
                }
                Some(acc)
            }

            // re.inter(R1..Rn): length set is the intersection. SOUND because a
            // string accepted by the intersection is accepted by every child,
            // so its length is in every child's length set. A single finite
            // child bounds the result; if EVERY child is infinite we can't
            // compute it (any `?` on a child returns None and we bail).
            "re.inter" if !args.is_empty() => {
                let mut acc: Option<BTreeSet<usize>> = None;
                for &child in args {
                    let child_set = Self::accepted_lengths_inner(terms, child, depth + 1)?;
                    acc = Some(match acc {
                        None => child_set,
                        Some(prev) => prev.intersection(&child_set).copied().collect(),
                    });
                }
                acc
            }

            // re.opt(R): zero or one R → {0} ∪ lengths(R).
            "re.opt" if args.len() == 1 => {
                let mut set = Self::accepted_lengths_inner(terms, args[0], depth + 1)?;
                set.insert(0);
                Some(set)
            }

            // re.comp(R): complement. Even if R has a finite length set, its
            // complement is generally infinite. Fail closed to None (no info).
            "re.comp" => None,

            // re.diff(R1, R2): subset of R1. Length set ⊆ lengths(R1), so if R1
            // is finite the difference is finite (and bounded by lengths(R1)).
            // This may keep a length that R2 actually removes, but it never adds
            // a length not in R1 → still an exact NECESSARY condition on length.
            "re.diff" if args.len() == 2 => Self::accepted_lengths_inner(terms, args[0], depth + 1),

            // (_ re.loop n m) R: between n and m repetitions of R. Finite iff R
            // is finite. Length set = ⋃_{k=n}^{m} (k-fold Minkowski sum of R).
            "re.loop" if args.len() == 1 => {
                let Symbol::Indexed(_, indices) = sym else {
                    return None;
                };
                if indices.len() != 2 {
                    return None;
                }
                let lo = indices[0] as usize;
                let hi = indices[1] as usize;
                if lo > hi {
                    return Some(BTreeSet::new());
                }
                let body = Self::accepted_lengths_inner(terms, args[0], depth + 1)?;
                // Exact constant-time folds must precede the work cap. The
                // empty language repeated zero times is epsilon (and is empty
                // for any positive lower bound); a body whose only possible
                // length is zero keeps length zero under every repetition.
                if body.is_empty() {
                    return if lo == 0 {
                        Some([0].into_iter().collect())
                    } else {
                        Some(BTreeSet::new())
                    };
                }
                if body.len() == 1 && body.contains(&0) {
                    return Some([0].into_iter().collect());
                }
                if hi > Self::MAX_LOOP_LENGTH_UNROLL {
                    return None;
                }
                // Accumulate ⋃_{k=lo}^{hi} (k-fold sum of body) by iterating the
                // running k-fold Minkowski sum from k=0.
                let mut result = BTreeSet::new();
                let mut kfold: BTreeSet<usize> = [0].into_iter().collect();
                for k in 0..=hi {
                    if k >= lo {
                        for &v in &kfold {
                            result.insert(v);
                            if result.len() > Self::MAX_LEN_SET {
                                return None;
                            }
                        }
                    }
                    if k == hi || body.is_empty() {
                        break;
                    }
                    let mut next = BTreeSet::new();
                    for &a in &kfold {
                        for &b in &body {
                            let s = a.checked_add(b)?;
                            next.insert(s);
                            if next.len() > Self::MAX_LEN_SET {
                                return None;
                            }
                        }
                    }
                    kfold = next;
                }
                Some(result)
            }

            // re.all, re.*, re.+ over a non-empty body, and anything else:
            // potentially unbounded length → no finite characterization.
            _ => None,
        }
    }

    /// If `r` is `str.to_re(constant)`, return the constant string.
    fn fixed_string(terms: &TermStore, r: TermId) -> Option<String> {
        let TermData::App(sym, args) = terms.get(r) else {
            return None;
        };
        if !matches!(sym.name(), "str.to_re" | "str.to.re") || args.len() != 1 {
            return None;
        }
        Self::resolve_string_const(terms, args[0])
    }

    // ── String resolution helpers ──────────────────────────────────────

    /// Resolve a term to a concrete string constant via the term store.
    fn resolve_string_const(terms: &TermStore, t: TermId) -> Option<String> {
        match terms.get(t) {
            TermData::Const(Constant::String(s)) => Some(s.clone()),
            _ => None,
        }
    }

    /// Resolve a term to a concrete string using EQC representatives.
    fn resolve_string(terms: &TermStore, state: &SolverState, t: TermId) -> Option<String> {
        if let Some(s) = Self::resolve_string_const(terms, t) {
            return Some(s);
        }
        let rep = state.find(t);
        if rep != t {
            if let Some(s) = Self::resolve_string_const(terms, rep) {
                return Some(s);
            }
        }
        // Check EQC info for a constant value.
        state.get_eqc(&rep).and_then(|info| info.constant.clone())
    }

    /// Normalize a theory literal into `(atom, expected_truth_value)`.
    fn atom_and_polarity(terms: &TermStore, lit: TheoryLit) -> (TermId, bool) {
        let mut term = lit.term;
        let mut polarity = lit.value;
        while let TermData::Not(inner) = terms.get(term) {
            term = *inner;
            polarity = !polarity;
        }
        (term, polarity)
    }

    /// Find the first (leftmost shortest) match of regex `r` in string `s`.
    ///
    /// Tries every start position and returns the shortest match at the
    /// leftmost position. Returns `Incomplete` if the regex contains
    /// constructs that `evaluate()` cannot handle.
    pub(crate) fn find_first_match(terms: &TermStore, s: &str, r: TermId) -> MatchResult {
        let chars: Vec<char> = s.chars().collect();
        for start in 0..=chars.len() {
            let start_byte = chars[..start].iter().map(|c| c.len_utf8()).sum::<usize>();
            for end in start..=chars.len() {
                let end_byte = chars[..end].iter().map(|c| c.len_utf8()).sum::<usize>();
                let substr = &s[start_byte..end_byte];
                match Self::evaluate(terms, substr, r) {
                    Some(true) => return MatchResult::Found(start_byte, end_byte),
                    Some(false) => {}
                    None => return MatchResult::Incomplete,
                }
            }
        }
        MatchResult::NoMatch
    }
}

#[allow(clippy::panic)]
#[cfg(test)]
#[path = "regexp_tests.rs"]
mod tests;
