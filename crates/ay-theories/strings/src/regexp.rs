// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regex membership solver for ground `str.in_re` constraints.
//!
//! When both the string and regex resolve to concrete values, evaluates
//! membership with exact Brzozowski derivatives when the regex translates
//! within fixed limits. Unsupported or oversized translations fall back to
//! the existing memoised recursive descent. Non-ground memberships are marked
//! incomplete.
//!
//! Reference: CVC5 `regexp_eval.cpp` and `regexp_operation.cpp` (BSD license).
//! Algorithm: Brzozowski, J.A. "Derivatives of Regular Expressions" (1964).

use ay_core::term::{Constant, TermData, TermId, TermStore};
use ay_core::{Symbol, TheoryLit};

use crate::infer::{InferenceKind, InferenceManager};
use crate::state::SolverState;
use crate::we_regex::WeRegex;
use crate::RegexWorkLimitExceeded;

/// Add `value` to a structural allocation bound, declining once `cap` would
/// be exceeded. `None` is a fail-open signal for the derivative fast path.
fn add_to_bound(total: &mut usize, value: usize, cap: usize) -> Option<()> {
    *total = total.checked_add(value)?;
    (*total <= cap).then_some(())
}

/// [`WeRegex::size`] with checked, early-capped arithmetic and cooperative
/// traversal charging.
fn regex_size_bounded(regex: &WeRegex, cap: usize, budget: &mut RegexWorkBudget) -> Option<usize> {
    if !budget.charge() {
        return None;
    }
    let total = match regex {
        WeRegex::None | WeRegex::Eps | WeRegex::AnyChar | WeRegex::All | WeRegex::Range(..) => 1,
        WeRegex::Lit(value) => 1usize.checked_add(value.len() / 8)?,
        WeRegex::Concat(parts) | WeRegex::Union(parts) | WeRegex::Inter(parts) => {
            let mut total = 1;
            for part in parts {
                add_to_bound(&mut total, regex_size_bounded(part, cap, budget)?, cap)?;
            }
            total
        }
        WeRegex::Star(inner) | WeRegex::Comp(inner) | WeRegex::Loop(inner, ..) => {
            1usize.checked_add(regex_size_bounded(inner, cap, budget)?)?
        }
    };
    if total > cap {
        return None;
    }
    Some(total)
}

/// Conservative upper bound on structural regex material cloned or built by
/// one call to [`WeRegex::derive`].
///
/// In particular, a nullable concat can derive every suffix and clone those
/// suffixes into separate arms, so its transient work can be quadratic even
/// when the post-simplification result is small. Computing this recurrence
/// before calling `derive` prevents that speculative expansion from crossing
/// the same cap as the retained derivative. A declined bound falls back to the
/// memoised term evaluator without allocating the derivative.
fn derivative_transient_bound(
    regex: &WeRegex,
    cap: usize,
    budget: &mut RegexWorkBudget,
) -> Option<usize> {
    if !budget.charge() {
        return None;
    }
    match regex {
        WeRegex::None | WeRegex::Eps | WeRegex::AnyChar | WeRegex::All | WeRegex::Range(..) => {
            (1 <= cap).then_some(1)
        }
        WeRegex::Lit(value) => {
            let size = 1usize.checked_add(value.len() / 8)?;
            (size <= cap).then_some(size)
        }
        WeRegex::Concat(parts) => concat_derivative_transient_bound(parts, cap, budget),
        WeRegex::Union(parts) | WeRegex::Inter(parts) => {
            let mut total = 1;
            for part in parts {
                add_to_bound(
                    &mut total,
                    derivative_transient_bound(part, cap, budget)?,
                    cap,
                )?;
            }
            Some(total)
        }
        WeRegex::Star(inner) => {
            let mut total = 1;
            add_to_bound(
                &mut total,
                derivative_transient_bound(inner, cap, budget)?,
                cap,
            )?;
            // `derive(Star(r))` clones the complete star into the concat tail.
            add_to_bound(&mut total, regex_size_bounded(regex, cap, budget)?, cap)?;
            Some(total)
        }
        WeRegex::Comp(inner) => {
            let mut total = 1;
            add_to_bound(
                &mut total,
                derivative_transient_bound(inner, cap, budget)?,
                cap,
            )?;
            Some(total)
        }
        WeRegex::Loop(inner, ..) => {
            let mut total = 2;
            add_to_bound(
                &mut total,
                derivative_transient_bound(inner, cap, budget)?,
                cap,
            )?;
            // The counter step clones the body before rebuilding the loop.
            add_to_bound(&mut total, regex_size_bounded(inner, cap, budget)?, cap)?;
            Some(total)
        }
    }
}

fn nullable_with_budget(regex: &WeRegex, budget: &mut RegexWorkBudget) -> Option<bool> {
    if !budget.charge() {
        return None;
    }
    match regex {
        WeRegex::None | WeRegex::Lit(_) | WeRegex::AnyChar | WeRegex::Range(..) => Some(false),
        WeRegex::Eps | WeRegex::All | WeRegex::Star(_) => Some(true),
        WeRegex::Concat(parts) | WeRegex::Inter(parts) => {
            for part in parts {
                if !nullable_with_budget(part, budget)? {
                    return Some(false);
                }
            }
            Some(true)
        }
        WeRegex::Union(parts) => {
            for part in parts {
                if nullable_with_budget(part, budget)? {
                    return Some(true);
                }
            }
            Some(false)
        }
        WeRegex::Comp(inner) => nullable_with_budget(inner, budget).map(|value| !value),
        WeRegex::Loop(inner, lo, _) => {
            if *lo == 0 {
                Some(true)
            } else {
                nullable_with_budget(inner, budget)
            }
        }
    }
}

fn concat_derivative_transient_bound(
    parts: &[WeRegex],
    cap: usize,
    budget: &mut RegexWorkBudget,
) -> Option<usize> {
    if parts.is_empty() {
        return (1 <= cap).then_some(1);
    }

    // Walk only the nullable prefix that `WeRegex::derive` can actually enter.
    // Maintaining the remaining suffix size makes the preflight linear without
    // allocating an attacker-width side table.
    let mut suffix_parts_size = 0;
    for part in parts {
        add_to_bound(
            &mut suffix_parts_size,
            regex_size_bounded(part, cap, budget)?,
            cap,
        )?;
    }
    let mut total = 0;

    for (index, first) in parts.iter().enumerate() {
        suffix_parts_size =
            suffix_parts_size.checked_sub(regex_size_bounded(first, cap, budget)?)?;
        let remaining = parts.len() - index - 1;
        if remaining == 0 {
            add_to_bound(
                &mut total,
                derivative_transient_bound(first, cap, budget)?,
                cap,
            )?;
            break;
        }

        // `derive(Concat)` clones the complete suffix to form `rest_re`, clones
        // `rest_re` into the first arm, and may derive that suffix as a second
        // arm. Three shells cover the suffix concat, first arm, and arm union.
        add_to_bound(&mut total, 3, cap)?;
        add_to_bound(&mut total, suffix_parts_size, cap)?;
        add_to_bound(
            &mut total,
            derivative_transient_bound(first, cap, budget)?,
            cap,
        )?;
        add_to_bound(&mut total, suffix_parts_size, cap)?;
        if remaining > 1 {
            // `rest_re` retains one concat shell in addition to its children.
            add_to_bound(&mut total, 1, cap)?;
        }
        if !nullable_with_budget(first, budget)? {
            break;
        }
    }

    Some(total)
}

/// One memoised sub-problem of the concrete-membership evaluator.
///
/// The evaluator is a pure function of `(TermStore, s, node)`, and `TermStore`
/// is immutable for the whole call, so a `(node, s)` pair has ONE answer. The
/// backtracking split loops in `eval_concat` / `eval_star` / `eval_loop` ask
/// for the same pair over and over — that is exactly what makes an unmemoised
/// recursive-descent matcher exponential (catastrophic backtracking). Caching
/// the five recursion entry points makes the evaluator polynomial without
/// changing a single answer it returns.
#[derive(PartialEq, Eq, Hash, Clone, Copy, Debug)]
enum ReKey {
    /// `evaluate(s, node)`.
    Eval(TermId),
    /// `eval_star(s, body)` — "s is a concatenation of `body` matches".
    Star(TermId),
    /// `eval_concat(s, args_of(node), idx)`.
    Concat(TermId, u32),
    /// `eval_loop(s, body, lo, hi)`.
    Loop(TermId, u32, u32),
    /// `delta(node)` — "node accepts the empty string".
    Delta(TermId),
}

/// Memo for ONE top-level [`RegExpSolver::evaluate`] call. The `&'a str` keys
/// are sub-slices of that call's input, so they cost nothing to store.
type ReMemo<'a> = ay_core::kani_compat::DetHashMap<(ReKey, &'a str), Option<bool>>;

/// Memo entry cap. Bounds memory on a pathological (long string × large regex)
/// pair; a new miss at the cap fails closed instead of resuming potentially
/// exponential uncached recursion.
const RE_MEMO_CAP: usize = 1 << 20;

/// Shared cooperative budget for one bounded regex operation.
///
/// `str.replace_re_all` deliberately carries one of these through every
/// successive match search. Resetting it for each candidate substring or
/// replacement would turn a per-operation bound into an unbounded multiplier.
pub(crate) struct RegexWorkBudget {
    remaining: Option<u64>,
    memo_cap: usize,
    exhausted: bool,
}

impl RegexWorkBudget {
    pub(crate) fn unlimited() -> Self {
        Self {
            remaining: None,
            memo_cap: RE_MEMO_CAP,
            exhausted: false,
        }
    }

    pub(crate) fn limited(limit: u64) -> Self {
        Self {
            remaining: Some(limit),
            memo_cap: RE_MEMO_CAP,
            exhausted: false,
        }
    }

    #[cfg(test)]
    fn limited_with_memo_cap(limit: u64, memo_cap: usize) -> Self {
        Self {
            remaining: Some(limit),
            memo_cap,
            exhausted: false,
        }
    }

    /// Charge deterministic structural work before performing it.
    fn charge_many(&mut self, units: usize) -> bool {
        let units = u64::try_from(units).unwrap_or(u64::MAX);
        if let Some(remaining) = &mut self.remaining {
            if *remaining < units {
                *remaining = 0;
                self.exhausted = true;
                return false;
            }
            *remaining -= units;
        }
        record_work(units);
        true
    }

    /// Charge one memoised matcher consultation.
    fn charge(&mut self) -> bool {
        self.charge_many(1)
    }
}

fn record_work(units: u64) {
    RE_WORK.with(|counter| counter.set(counter.get().saturating_add(units)));
}

thread_local! {
    /// Monotone count of membership structural-work units on this thread.
    /// The regex matcher's whole cost lives inside one
    /// `evaluate_term` frame, so the evaluator's own node-visit clock cannot
    /// see it — a single `str.in_re` atom over an industrial regex can be
    /// four orders of magnitude more expensive than a whole `str.substr` nest.
    /// Memo consultations cost one unit; derivative translation and scans cost
    /// their structural size. Callers that budget work by counting (the W4
    /// witness search) add this to their clock so both shapes are bounded by
    /// one number.
    static RE_WORK: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
}

/// This thread's regex membership work counter (see `RE_WORK`).
pub(crate) fn eval_work() -> u64 {
    RE_WORK.with(std::cell::Cell::get)
}

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
    /// Exactly translatable terms first use Brzozowski derivatives. Translation
    /// or derivative size-limit failure falls through to the existing memoised
    /// recursive descent, preserving support for every legacy term shape.
    pub(crate) fn evaluate(terms: &TermStore, s: &str, r: TermId) -> Option<bool> {
        let mut budget = RegexWorkBudget::unlimited();
        Self::evaluate_with_budget(terms, s, r, &mut budget).unwrap_or_default()
    }

    /// Bounded counterpart of [`Self::evaluate`].
    pub(crate) fn evaluate_with_work_limit(
        terms: &TermStore,
        s: &str,
        r: TermId,
        limit: u64,
    ) -> Result<Option<bool>, RegexWorkLimitExceeded> {
        let mut budget = RegexWorkBudget::limited(limit);
        Self::evaluate_with_budget(terms, s, r, &mut budget)
    }

    fn evaluate_with_budget(
        terms: &TermStore,
        s: &str,
        r: TermId,
        budget: &mut RegexWorkBudget,
    ) -> Result<Option<bool>, RegexWorkLimitExceeded> {
        if budget.exhausted {
            return Err(RegexWorkLimitExceeded);
        }
        let derivative = Self::evaluate_derivative_with_budget(terms, s, r, budget);
        if budget.exhausted {
            return Err(RegexWorkLimitExceeded);
        }
        if derivative.is_some() {
            return Ok(derivative);
        }

        let out = Self::evaluate_fallback_with_budget(terms, s, r, budget);
        if budget.exhausted {
            return Err(RegexWorkLimitExceeded);
        }
        Ok(out)
    }

    /// Exact derivative fast path, bounded by the caller's existing work
    /// budget. `None` means translation/derivative limits were reached and the
    /// memoised term evaluator should be tried; an exhausted budget is recorded
    /// on `budget` and must not fall through.
    fn evaluate_derivative_with_budget(
        terms: &TermStore,
        s: &str,
        r: TermId,
        budget: &mut RegexWorkBudget,
    ) -> Option<bool> {
        let limits = crate::term_regex::TranslateLimits::for_ground_eval();
        let mut regex = {
            let mut charge = |units| budget.charge_many(units);
            crate::term_regex::translate_with_charge(terms, r, &limits, &mut charge)?
        };
        let mut regex_size = regex.size();

        for c in s.chars() {
            // Preflight the complete transient expansion, not only the retained
            // result: nullable concats can otherwise allocate a quadratic set
            // of derivative arms before the post-derive size check sees it.
            let derivative_work = derivative_transient_bound(&regex, limits.max_size, budget)?;
            if !budget.charge_many(derivative_work) {
                return None;
            }
            regex = regex.derive(c);
            if regex.is_empty_lang() {
                return Some(false);
            }
            regex_size = regex.size();
            if regex_size > limits.max_size {
                return None;
            }
        }

        // `nullable` is another structural traversal and is part of the same
        // in-evaluator budget (including the empty-subject case).
        if !budget.charge_many(regex_size.max(1)) {
            return None;
        }
        Some(regex.nullable())
    }

    /// Existing exact recursive-descent fallback with its current memo.
    fn evaluate_fallback_with_budget(
        terms: &TermStore,
        s: &str,
        r: TermId,
        budget: &mut RegexWorkBudget,
    ) -> Option<bool> {
        let mut memo = ReMemo::default();
        Self::eval_memo(terms, s, r, &mut memo, budget)
    }

    #[cfg(test)]
    fn evaluate_fallback(terms: &TermStore, s: &str, r: TermId) -> Option<bool> {
        let mut budget = RegexWorkBudget::unlimited();
        Self::evaluate_fallback_with_budget(terms, s, r, &mut budget)
    }

    #[cfg(test)]
    fn evaluate_fallback_with_work_limit(
        terms: &TermStore,
        s: &str,
        r: TermId,
        limit: u64,
    ) -> Result<Option<bool>, RegexWorkLimitExceeded> {
        let mut budget = RegexWorkBudget::limited(limit);
        let out = Self::evaluate_fallback_with_budget(terms, s, r, &mut budget);
        if budget.exhausted {
            Err(RegexWorkLimitExceeded)
        } else {
            Ok(out)
        }
    }

    /// Memo lookup/insert wrapper shared by the four recursion entry points.
    #[inline]
    fn memoised<'a>(
        memo: &mut ReMemo<'a>,
        key: (ReKey, &'a str),
        budget: &mut RegexWorkBudget,
        compute: impl FnOnce(&mut ReMemo<'a>, &mut RegexWorkBudget) -> Option<bool>,
    ) -> Option<bool> {
        // Charged on every CONSULTATION, hit or miss: a cached hit still costs
        // a key hash over the substring, and the backtracking split loops are
        // overwhelmingly hits — counting only misses under-reports the
        // matcher's real cost by one to two orders of magnitude.
        if !budget.charge() {
            return None;
        }
        if let Some(&hit) = memo.get(&key) {
            return hit;
        }
        if memo.len() >= budget.memo_cap {
            return None;
        }
        let out = compute(memo, budget);
        // Never memoize a budget-aborted `None`: that is not a semantic answer
        // and must not poison another lookup if this context is inspected.
        if !budget.exhausted && memo.len() < budget.memo_cap {
            memo.insert(key, out);
        }
        out
    }

    /// The memoised body of [`Self::evaluate`]. Every recursive call in this
    /// module goes through here (or through the memoised `eval_*` helpers), so
    /// each `(node, substring)` pair is decided at most once per top-level call.
    fn eval_memo<'a>(
        terms: &TermStore,
        s: &'a str,
        r: TermId,
        memo: &mut ReMemo<'a>,
        budget: &mut RegexWorkBudget,
    ) -> Option<bool> {
        Self::memoised(memo, (ReKey::Eval(r), s), budget, |memo, budget| {
            Self::eval_uncached(terms, s, r, memo, budget)
        })
    }

    fn eval_uncached<'a>(
        terms: &TermStore,
        s: &'a str,
        r: TermId,
        memo: &mut ReMemo<'a>,
        budget: &mut RegexWorkBudget,
    ) -> Option<bool> {
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
                Self::eval_concat(terms, s, r, &children, 0, memo, budget)
            }

            // re.union(R1, R2, ...): s matches iff s matches any Ri.
            "re.union" if !args.is_empty() => {
                for &child in args {
                    if Self::eval_memo(terms, s, child, memo, budget)? {
                        return Some(true);
                    }
                }
                Some(false)
            }

            // re.inter(R1, R2, ...): s matches iff s matches all Ri.
            "re.inter" if !args.is_empty() => {
                for &child in args {
                    if !Self::eval_memo(terms, s, child, memo, budget)? {
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
                Self::eval_star(terms, s, args[0], memo, budget)
            }

            // re.+(R): one or more. s matches iff s is non-empty and can be
            // split into parts each matching R.
            "re.+" if args.len() == 1 => {
                if s.is_empty() {
                    return Self::delta_memo(terms, args[0], memo, budget);
                }
                Self::eval_star(terms, s, args[0], memo, budget)
            }

            // re.opt(R): zero or one. s matches iff s = "" or s matches R.
            "re.opt" if args.len() == 1 => {
                if s.is_empty() {
                    return Some(true);
                }
                Self::eval_memo(terms, s, args[0], memo, budget)
            }

            // re.comp(R): complement. s matches iff s does NOT match R.
            "re.comp" if args.len() == 1 => {
                Self::eval_memo(terms, s, args[0], memo, budget).map(|b| !b)
            }

            // re.diff(R1, R2): difference. s matches iff s matches R1 and not R2.
            "re.diff" if args.len() == 2 => {
                let m1 = Self::eval_memo(terms, s, args[0], memo, budget)?;
                if !m1 {
                    return Some(false);
                }
                let m2 = Self::eval_memo(terms, s, args[1], memo, budget)?;
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
                Self::eval_loop(terms, s, args[0], lo, hi, memo, budget)
            }

            _ => None,
        }
    }

    /// Evaluate concatenation: does `s` match `children[idx..]`?
    ///
    /// Tries all possible split points for the first child's match length.
    /// Uses backtracking to find a valid decomposition.
    fn eval_concat<'a>(
        terms: &TermStore,
        s: &'a str,
        node: TermId,
        children: &[TermId],
        idx: usize,
        memo: &mut ReMemo<'a>,
        budget: &mut RegexWorkBudget,
    ) -> Option<bool> {
        // `node` identifies the `re.++` term, so `(node, idx, s)` names this
        // sub-problem uniquely — `children` is exactly `args_of(node)`.
        Self::memoised(
            memo,
            (ReKey::Concat(node, idx as u32), s),
            budget,
            |memo, budget| Self::eval_concat_uncached(terms, s, node, children, idx, memo, budget),
        )
    }

    fn eval_concat_uncached<'a>(
        terms: &TermStore,
        s: &'a str,
        node: TermId,
        children: &[TermId],
        idx: usize,
        memo: &mut ReMemo<'a>,
        budget: &mut RegexWorkBudget,
    ) -> Option<bool> {
        if idx >= children.len() {
            return Some(s.is_empty());
        }

        if idx == children.len() - 1 {
            // Last child must match the entire remaining string.
            return Self::eval_memo(terms, s, children[idx], memo, budget);
        }

        // Optimization: if current child is str.to_re(constant), only one
        // split point is valid (the constant must be a prefix).
        if let Some(prefix) = Self::fixed_string(terms, children[idx]) {
            if s.starts_with(prefix.as_str()) {
                return Self::eval_concat(
                    terms,
                    &s[prefix.len()..],
                    node,
                    children,
                    idx + 1,
                    memo,
                    budget,
                );
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

            if Self::eval_memo(terms, prefix, children[idx], memo, budget)?
                && Self::eval_concat(terms, suffix, node, children, idx + 1, memo, budget)?
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
    fn eval_star<'a>(
        terms: &TermStore,
        s: &'a str,
        r: TermId,
        memo: &mut ReMemo<'a>,
        budget: &mut RegexWorkBudget,
    ) -> Option<bool> {
        Self::memoised(memo, (ReKey::Star(r), s), budget, |memo, budget| {
            Self::eval_star_uncached(terms, s, r, memo, budget)
        })
    }

    fn eval_star_uncached<'a>(
        terms: &TermStore,
        s: &'a str,
        r: TermId,
        memo: &mut ReMemo<'a>,
        budget: &mut RegexWorkBudget,
    ) -> Option<bool> {
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

            if Self::eval_memo(terms, prefix, r, memo, budget)?
                && Self::eval_star(terms, suffix, r, memo, budget)?
            {
                return Some(true);
            }
        }

        Some(false)
    }

    /// Evaluate bounded repetition: does `s` match `R` repeated between `lo` and `hi` times?
    fn eval_loop<'a>(
        terms: &TermStore,
        s: &'a str,
        r: TermId,
        lo: usize,
        hi: usize,
        memo: &mut ReMemo<'a>,
        budget: &mut RegexWorkBudget,
    ) -> Option<bool> {
        Self::memoised(
            memo,
            (
                ReKey::Loop(
                    r,
                    lo.min(u32::MAX as usize) as u32,
                    hi.min(u32::MAX as usize) as u32,
                ),
                s,
            ),
            budget,
            |memo, budget| Self::eval_loop_uncached(terms, s, r, lo, hi, memo, budget),
        )
    }

    fn eval_loop_uncached<'a>(
        terms: &TermStore,
        s: &'a str,
        r: TermId,
        lo: usize,
        hi: usize,
        memo: &mut ReMemo<'a>,
        budget: &mut RegexWorkBudget,
    ) -> Option<bool> {
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
            return Self::delta_memo(terms, r, memo, budget);
        }
        let char_count = s.chars().count();
        for len in 1..=char_count {
            let byte_offset = s.char_indices().nth(len).map(|(b, _)| b).unwrap_or(s.len());
            let prefix = &s[..byte_offset];
            let suffix = &s[byte_offset..];

            if Self::eval_memo(terms, prefix, r, memo, budget)? {
                let new_lo = lo.saturating_sub(1);
                if Self::eval_loop(terms, suffix, r, new_lo, hi - 1, memo, budget)? {
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
        let mut memo = ReMemo::default();
        let mut budget = RegexWorkBudget::unlimited();
        Self::delta_memo(terms, r, &mut memo, &mut budget)
    }

    fn delta_memo(
        terms: &TermStore,
        r: TermId,
        memo: &mut ReMemo<'_>,
        budget: &mut RegexWorkBudget,
    ) -> Option<bool> {
        Self::memoised(memo, (ReKey::Delta(r), ""), budget, |memo, budget| {
            Self::delta_uncached(terms, r, memo, budget)
        })
    }

    fn delta_uncached(
        terms: &TermStore,
        r: TermId,
        memo: &mut ReMemo<'_>,
        budget: &mut RegexWorkBudget,
    ) -> Option<bool> {
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
                    if !Self::delta_memo(terms, child, memo, budget)? {
                        return Some(false);
                    }
                }
                Some(true)
            }

            "re.union" if !args.is_empty() => {
                for &child in args {
                    if Self::delta_memo(terms, child, memo, budget)? {
                        return Some(true);
                    }
                }
                Some(false)
            }

            "re.inter" if !args.is_empty() => {
                for &child in args {
                    if !Self::delta_memo(terms, child, memo, budget)? {
                        return Some(false);
                    }
                }
                Some(true)
            }

            "re.*" | "re.opt" if args.len() == 1 => Some(true),
            "re.+" if args.len() == 1 => Self::delta_memo(terms, args[0], memo, budget),
            "re.comp" if args.len() == 1 => {
                Self::delta_memo(terms, args[0], memo, budget).map(|b| !b)
            }

            "re.diff" if args.len() == 2 => {
                let d1 = Self::delta_memo(terms, args[0], memo, budget)?;
                let d2 = Self::delta_memo(terms, args[1], memo, budget)?;
                Some(d1 && !d2)
            }

            // (_ re.loop n m) R: `⋃_{k=n}^{m} L(R)^k`, so nullable iff the union
            // is non-degenerate AND (n == 0 or R is nullable).
            //
            // SMT-LIB: `n > m` makes the index set EMPTY, so the regex denotes
            // the EMPTY language, which is NOT nullable. Missing that check made
            // `delta` answer `true` for `""` in the empty language, which is
            // unsound in BOTH directions on the UNSAT path:
            //   * `evaluate` uses it for `re.+`/`re.loop` over `""`, so a
            //     `(not (str.in_re "" R))` assertion was refuted by a bogus
            //     "yes it matches" — a wrong theory conflict;
            //   * `is_nullable` is the core solver's positive-length guard, and
            //     a complemented degenerate loop (`(re.comp ((_ re.loop 4 2) R))`
            //     = `Σ*`) was reported NON-nullable, i.e. a bogus `|x| > 0`.
            // `evaluate`, `accepted_lengths` and `WeRegex::loop_bounded` all
            // already fold `n > m` to the empty language; only `delta` did not
            // (#regex-loop-degenerate-bounds).
            "re.loop" if args.len() == 1 => {
                let Symbol::Indexed(_, indices) = sym else {
                    return None;
                };
                if indices.len() != 2 {
                    return None;
                }
                if indices[0] > indices[1] {
                    return Some(false);
                }
                if indices[0] == 0 {
                    Some(true)
                } else {
                    Self::delta_memo(terms, args[0], memo, budget)
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
    ///
    /// The empty match is eligible, which is what `str.replace_re` wants: the
    /// SMT-LIB 2.6 Unicode Strings clause for `str.replace_re` decomposes
    /// `s = x ++ w ++ z` with `w` in `[[r]]`, `|x|` minimal and then `|w|`
    /// minimal, and carries **no** `w != ""` side condition. Use
    /// [`Self::find_first_nonempty_match_with_budget`] for `str.replace_re_all`,
    /// whose clause does carry it.
    pub(crate) fn find_first_match(terms: &TermStore, s: &str, r: TermId) -> MatchResult {
        let mut budget = RegexWorkBudget::unlimited();
        match Self::find_first_match_with_budget(terms, s, r, &mut budget) {
            Ok(result) => result,
            Err(_) => MatchResult::Incomplete,
        }
    }

    pub(crate) fn find_first_match_with_budget(
        terms: &TermStore,
        s: &str,
        r: TermId,
        budget: &mut RegexWorkBudget,
    ) -> Result<MatchResult, RegexWorkLimitExceeded> {
        Self::find_first_match_of_min_len(terms, s, r, 0, budget)
    }

    /// Find the leftmost, then shortest, **non-empty** match of `r` in `s`.
    ///
    /// This is the matcher required by the SMT-LIB 2.6 Unicode Strings clause
    /// for `str.replace_re_all`, which decomposes `s = x ++ w ++ z` with `w` in
    /// `[[r]]` **and `w != ""`**, `|x|` minimal and then `|w|` minimal. Using
    /// the empty-match-eligible [`Self::find_first_match_with_budget`] there is
    /// a soundness defect: for any nullable `r` the leftmost shortest match is
    /// the empty match at position 0, so no replacement ever happens and the
    /// operator degenerates to the identity.
    pub(crate) fn find_first_nonempty_match_with_budget(
        terms: &TermStore,
        s: &str,
        r: TermId,
        budget: &mut RegexWorkBudget,
    ) -> Result<MatchResult, RegexWorkLimitExceeded> {
        Self::find_first_match_of_min_len(terms, s, r, 1, budget)
    }

    /// Shared leftmost-then-shortest scan with a minimum match length in
    /// characters (`0` admits the empty match, `1` excludes it).
    fn find_first_match_of_min_len(
        terms: &TermStore,
        s: &str,
        r: TermId,
        min_chars: usize,
        budget: &mut RegexWorkBudget,
    ) -> Result<MatchResult, RegexWorkLimitExceeded> {
        let chars: Vec<char> = s.chars().collect();
        for start in 0..=chars.len() {
            let start_byte = chars[..start].iter().map(|c| c.len_utf8()).sum::<usize>();
            for end in (start + min_chars)..=chars.len() {
                let end_byte = chars[..end].iter().map(|c| c.len_utf8()).sum::<usize>();
                let substr = &s[start_byte..end_byte];
                match Self::evaluate_with_budget(terms, substr, r, budget)? {
                    Some(true) => return Ok(MatchResult::Found(start_byte, end_byte)),
                    Some(false) => {}
                    None => return Ok(MatchResult::Incomplete),
                }
            }
        }
        Ok(MatchResult::NoMatch)
    }
}

#[allow(clippy::panic)]
#[cfg(test)]
#[path = "regexp_tests.rs"]
mod tests;
