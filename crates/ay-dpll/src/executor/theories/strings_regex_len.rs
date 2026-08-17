// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bounded regex-membership × length-constraint decision pre-pass
//! (TARGET strings_regex_len).
//!
//! When a string variable `x` is constrained by a positive regex membership
//! `(str.in_re x R)` AND a derivable finite length window `[lo, hi]`, the set of
//! satisfying values of `x` over the regex's *accepted alphabet* is finite and
//! enumerable. We exploit this two ways, both sound-by-construction:
//!
//! * **UNSAT (e.g. S1).** If the regex `R` only accepts strings over a finite,
//!   statically-computable alphabet `A` (see [`Executor::regex_accepted_alphabet`])
//!   then *every* accepted string of length in `[lo, hi]` uses characters from
//!   `A`. Exhaustively enumerating `A^len` for `len ∈ [lo, hi]` and finding NO
//!   string accepted by all positive memberships (and rejected by all negative
//!   ones) proves the membership+length conjuncts are jointly unsatisfiable —
//!   independent of every other constraint, since the memberships and the length
//!   bound MUST hold. So we may soundly return `unsat`.
//!
//! * **SAT (e.g. S3).** Any concrete accepted string is a candidate witness. We
//!   hand the candidates to the existing validated-assumption machinery
//!   ([`Executor::try_string_var_witnesses`]): each is pinned as `x = "..."`,
//!   re-solved, and the *full model is validated* before SAT is trusted. A wrong
//!   guess (or a candidate ruled out by other constraints) simply fails
//!   validation and falls through to the normal pipeline. No unsound SAT can
//!   escape.
//!
//! Fail-closed everywhere: an unbounded length, an alphabet that is not a finite
//! computable superset (`re.all` / `re.allchar` / `re.comp` admit arbitrary
//! characters), an over-large search space, or "candidates exist but none
//! validated" all return `Ok(None)` so the caller runs the normal solver.

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::DetHashSet as HashSet;
use ay_core::term::{Constant, Symbol, TermData, TermId};
use ay_core::Sort;
use ay_strings::we_regex::{WeRegex, WitnessWorkBudget};

use crate::executor_types::{Result, SolveResult};

use super::super::model::string_witness::{
    str_witness_w1b, MAX_WITNESS_REGEXES, WITNESS_SEARCH_MAX_LEN,
};
use super::super::Executor;
use super::strings_analysis::{PrefixSuffixWitness, MAX_PIVOT_CANDIDATES};

/// Maximum length window we will enumerate for a regex×length decision.
/// Bounds the work to a finite search; longer windows fall closed to Unknown.
const MAX_REGEX_LEN: usize = 8;

/// Maximum number of distinct characters in the enumeration alphabet. A larger
/// alphabet (e.g. a wide `re.range`) blows up the search space, so we bail.
const MAX_REGEX_ALPHABET: usize = 16;

/// Maximum number of CONSTRUCTED candidates tried per variable (W1b). Each
/// candidate costs one bounded assumption re-solve, so the count is kept small.
const W1B_MAX_CANDIDATES: usize = 4;

/// A positive/negative regex membership constraint on a single variable.
struct Membership {
    /// The regex term `R`.
    regex: TermId,
    /// `true` for `(str.in_re x R)`, `false` for `(not (str.in_re x R))`.
    positive: bool,
}

impl Executor {
    /// Bounded regex-membership × length pre-pass. See module docs.
    ///
    /// Returns `Ok(Some(Unsat))` / `Ok(Some(Sat))` only on a sound decision,
    /// `Ok(None)` to fall through to the normal pipeline.
    pub(in crate::executor) fn try_regex_length_witnesses(
        &mut self,
    ) -> Result<Option<SolveResult>> {
        // Re-entry guard: the SAT path recurses through the solver with a pinned
        // candidate, which must NOT re-trigger this pre-pass.
        if self.pivot_enum_depth != 0 {
            return Ok(None);
        }

        // Collect, per string variable, its positive/negative regex memberships.
        let var_memberships = self.collect_var_memberships();
        if super::debug_auflia_enabled() {
            safe_eprintln!(
                "[REGEXLEN] try_regex_length_witnesses: {} vars with memberships",
                var_memberships.len()
            );
        }
        if var_memberships.is_empty() {
            return Ok(None);
        }

        // Unfiltered length bounds for all variables (no MAX_PIVOT_BOUND filter).
        let length_bounds = self.regex_var_length_bounds();

        for (var, memberships) in &var_memberships {
            // A length window for `var` is required to make the search finite.
            let Some(&(lo, hi)) = length_bounds.get(var) else {
                if super::debug_auflia_enabled() {
                    safe_eprintln!("[REGEXLEN] var={:?}: no length bound", var);
                }
                continue;
            };
            if super::debug_auflia_enabled() {
                safe_eprintln!("[REGEXLEN] var={:?}: len=[{}..={}]", var, lo, hi);
            }
            if hi == usize::MAX || hi > MAX_REGEX_LEN || lo > hi {
                continue;
            }

            // Compute a sound finite superset of every character that any string
            // accepted by a POSITIVE membership can contain. Each accepted value
            // must satisfy all positive memberships, so its characters lie in the
            // intersection of their alphabets; the union is a safe superset to
            // enumerate over (negative memberships only remove candidates). If
            // any positive membership has an open alphabet, bail.
            let mut alphabet: HashSet<char> = HashSet::default();
            let mut alphabet_ok = true;
            let mut has_positive = false;
            for m in memberships {
                if !m.positive {
                    continue;
                }
                has_positive = true;
                match self.regex_accepted_alphabet(m.regex) {
                    Some(chars) => alphabet.extend(chars),
                    None => {
                        alphabet_ok = false;
                        break;
                    }
                }
            }
            if !alphabet_ok || !has_positive {
                continue;
            }
            if alphabet.len() > MAX_REGEX_ALPHABET {
                continue;
            }

            let mut alphabet: Vec<char> = alphabet.into_iter().collect();
            alphabet.sort_unstable();

            // Enumerate every string over `alphabet` with length in [lo, hi] and
            // keep those satisfying ALL memberships (positive and negative). The
            // enumeration is exhaustive over the accepted-string space because
            // `alphabet` is a superset of every accepted string's characters.
            let Some(accepted) = self.enumerate_accepted_strings(&alphabet, lo, hi, memberships)
            else {
                // Search space too large or a membership became non-ground-
                // evaluable mid-enumeration: fall closed.
                continue;
            };

            if accepted.is_empty() {
                // No string of any feasible length is accepted by all positive
                // memberships. The membership + length conjuncts are jointly
                // unsatisfiable, regardless of other constraints. Sound UNSAT.
                return Ok(Some(SolveResult::unsat()));
            }

            // Some accepted strings exist: try each as a fully-validated witness.
            // A validated SAT is sound; otherwise fall through (other constraints
            // may rule them out, but we cannot conclude UNSAT from that here).
            let witness = PrefixSuffixWitness {
                var: *var,
                candidates: accepted,
            };
            if let Some(result @ SolveResult::Sat) = self.try_string_var_witnesses(vec![witness])? {
                return Ok(Some(result));
            }
        }

        Ok(None)
    }

    /// W1b: CONTENT-POSITIVE regex witness CONSTRUCTION, split out of
    /// [`Self::try_regex_length_witnesses`] so it can run LATE in the pre-pass
    /// cascade (TARGET strings_regex_len W1b-placement).
    ///
    /// PLACEMENT RATIONALE. This pass only ever produces SAT candidates — a
    /// failed search means "not found", never "no witness exists" — so nothing
    /// it computes can contribute to an UNSAT verdict. Running it before the
    /// exact passes therefore charged its full derivative product search to
    /// every file those passes decide outright: measured on
    /// `automatark-lu/instance13338` (UNSAT), the search exhausted 11 137
    /// product states / 64.7M derivative-node units in ~2.1 s, after which the
    /// Nielsen pre-pass proved UNSAT in 4.6 ms. Ordering it after the exact
    /// passes keeps every conversion (the candidate set, the pinning and the
    /// full model validation are unchanged) and pays for the search only on
    /// formulas nothing cheaper decides.
    /// Derivative-work budget for the CHEAP W1b probe (see
    /// [`Self::try_regex_construct_witnesses_cheap`]).
    ///
    /// The product-search per-state cost is UNIFORM across the automatark
    /// family (~8k units regardless of outcome), so a per-state or per-length
    /// cap cannot separate a real convergence from a doomed exhaust; only the
    /// TOTAL work does. Calibrated on the pair that pulls in opposite
    /// directions: `instance12580` (SAT) converges after ~1.6M units, while
    /// `instance13338` (UNSAT) exhausts for ~65M. This budget clears the
    /// former and caps the latter — and because the cheap probe runs AFTER the
    /// exact passes that already decide `instance13338` (Nielsen, 4.6 ms), the
    /// cap it hits there is never even reached. A budgeted `None` is
    /// indistinguishable from "not found": the unrestricted
    /// [`Self::try_regex_construct_witnesses`] retries every declined variable,
    /// so no candidate is lost — only its position in the cascade changes.
    const CHEAP_W1B_WORK_BUDGET: u64 = 3_000_000;

    /// W1b with a CHEAP per-variable work budget, for the fast conversions that
    /// should not be made to pay for the passes downstream of it. Everything it
    /// declines (budget hit) is retried unbudgeted by
    /// [`Self::try_regex_construct_witnesses`].
    pub(in crate::executor) fn try_regex_construct_witnesses_cheap(
        &mut self,
    ) -> Result<Option<SolveResult>> {
        self.regex_construct_witnesses(Some(Self::CHEAP_W1B_WORK_BUDGET))
    }

    pub(in crate::executor) fn try_regex_construct_witnesses(
        &mut self,
    ) -> Result<Option<SolveResult>> {
        self.regex_construct_witnesses(None)
    }

    fn regex_construct_witnesses(
        &mut self,
        work_budget: Option<u64>,
    ) -> Result<Option<SolveResult>> {
        if self.pivot_enum_depth != 0 {
            return Ok(None);
        }
        if !str_witness_w1b() {
            return Ok(None);
        }
        let var_memberships = self.collect_var_memberships();
        if var_memberships.is_empty() {
            return Ok(None);
        }
        let length_bounds = self.regex_var_length_bounds();

        // W1b (default ON, `--dpll-no-str-witness` kill switch): CONTENT-POSITIVE construction
        // for the variables the finite enumeration above had to skip.
        //
        // The enumeration is content-BLIND: it needs a derivable length window
        // `hi <= 8` AND a closed alphabet of at most 16 characters, then brute
        // forces `A^len`. Industrial regex chains (automatark, stringfuzz,
        // slog) satisfy neither — an `re.range`-heavy union has a wide
        // alphabet, and a `re.*`/`re.+` chain has no upper length bound — so
        // every one of them falls through, and no other AY path can emit a
        // character that is not a literal in the formula. The exact derivative
        // search DOES construct such a value directly.
        //
        // SOUNDNESS: unchanged from the enumeration path above. The
        // constructed string is a CANDIDATE handed to the same
        // `try_string_var_witnesses` machinery — pinned as the hard assumption
        // `x = "..."`, re-solved, and accepted only after FULL model
        // validation plus assumption validation. A wrong candidate falls
        // through to the normal pipeline; UNSAT is NEVER concluded from a
        // failed search (`find_witness` returning `None` means "not found",
        // never "no witness exists").
        {
            for (var, memberships) in &var_memberships {
                let Some(regexes) = self.translate_var_memberships(memberships) else {
                    continue;
                };
                let candidates = Self::construct_regex_witnesses(
                    &regexes,
                    length_bounds.get(var).copied().unwrap_or((0, usize::MAX)),
                    work_budget,
                );
                if candidates.is_empty() {
                    continue;
                }
                if super::debug_auflia_enabled() {
                    safe_eprintln!(
                        "[REGEXLEN] W1b constructed witnesses for var={:?}: {:?}",
                        var,
                        candidates
                    );
                }
                let witness = PrefixSuffixWitness {
                    var: *var,
                    candidates,
                };
                if let Some(result @ SolveResult::Sat) =
                    self.try_string_var_witnesses(vec![witness])?
                {
                    return Ok(Some(result));
                }
            }
        }

        Ok(None)
    }

    /// Construct up to [`W1B_MAX_CANDIDATES`] witnesses for the conjoined
    /// `regexes`, biased to the variable's derived length window `[lo, hi]`
    /// (W1b).
    ///
    /// The SHORTEST witness alone is usually wrong for a length-constrained
    /// variable — `(str.len x) >= 3` with `x ∈ (re.* R)` accepts `""`, which
    /// the search returns first and the assumption solve then refutes. So the
    /// window's lowest feasible lengths are probed EXACTLY as well. Every
    /// candidate is validated downstream; producing more of them can only
    /// convert (or cost bounded time), never mis-answer.
    fn construct_regex_witnesses(
        regexes: &[WeRegex],
        (lo, hi): (usize, usize),
        work_budget: Option<u64>,
    ) -> Vec<String> {
        let mut out: Vec<String> = Vec::new();
        let mut shared_budget = work_budget.map(WitnessWorkBudget::new);
        let mut push = |w: String| {
            if !out.contains(&w) && out.len() < W1B_MAX_CANDIDATES {
                out.push(w);
            }
        };
        // Exact-length probes from the bottom of the window up.
        let start = lo.min(WITNESS_SEARCH_MAX_LEN);
        let end = hi
            .min(start.saturating_add(W1B_MAX_CANDIDATES - 1))
            .min(WITNESS_SEARCH_MAX_LEN);
        for len in start..=end {
            let witness = match shared_budget.as_mut() {
                Some(budget) if budget.is_exhausted() => break,
                Some(budget) => ay_strings::we_regex::find_witness_with_work_budget(
                    regexes,
                    Some(len),
                    len,
                    budget,
                ),
                None => ay_strings::we_regex::find_witness_bounded(regexes, Some(len), len),
            };
            if let Some(w) = witness {
                push(w);
            }
        }
        // Shortest witness of ANY length, as the fallback for variables with
        // no usable length window (or whose window the probes above missed).
        let fallback = match shared_budget.as_mut() {
            Some(budget) if budget.is_exhausted() => None,
            Some(budget) => ay_strings::we_regex::find_witness_with_work_budget(
                regexes,
                None,
                WITNESS_SEARCH_MAX_LEN,
                budget,
            ),
            None => {
                ay_strings::we_regex::find_witness_bounded(regexes, None, WITNESS_SEARCH_MAX_LEN)
            }
        };
        if let Some(w) = fallback {
            push(w);
        }
        out
    }

    /// Translate a variable's memberships into [`WeRegex`] constraints
    /// (positive as-is, negative EXACTLY complemented), or `None` when any
    /// membership has no exact translation or the conjunction is too large for
    /// the bounded product search.
    ///
    /// Bailing is always safe here: the result only ever seeds a
    /// gate-validated candidate.
    fn translate_var_memberships(&self, memberships: &[Membership]) -> Option<Vec<WeRegex>> {
        if memberships.is_empty() || memberships.len() > MAX_WITNESS_REGEXES {
            return None;
        }
        let mut out = Vec::with_capacity(memberships.len());
        for m in memberships {
            let r = self.translate_we_regex(m.regex, 0)?;
            out.push(if m.positive { r } else { WeRegex::comp(r) });
        }
        Some(out)
    }

    /// Decide `(str.++ ... x ...) = const` with a single free variable.
    ///
    /// When a top-level equality has a `str.++` on one side, a string constant on
    /// the other, and exactly one `str.++` operand is a bare free string variable
    /// while every other operand resolves to a string constant, the free
    /// variable's value is uniquely determined by stripping the known prefix /
    /// suffix constants (TARGET strings_regex_len S2). The single candidate is
    /// tried via the validated-assumption machinery, so SAT is only trusted after
    /// full model validation and a wrong derivation (e.g. a length mismatch) falls
    /// closed to the normal pipeline. Never wrong.
    pub(in crate::executor) fn try_concat_constant_witnesses(
        &mut self,
    ) -> Result<Option<SolveResult>> {
        if self.pivot_enum_depth != 0 {
            return Ok(None);
        }

        let witnesses = self.detect_concat_constant_witnesses();
        if witnesses.is_empty() {
            return Ok(None);
        }
        if let Some(result @ SolveResult::Sat) = self.try_string_var_witnesses(witnesses)? {
            return Ok(Some(result));
        }
        Ok(None)
    }

    /// Detect `(str.++ ... x ...) = const` equalities with a single free string
    /// variable and otherwise constant operands; return the derived witness for
    /// each. The candidate value is the unique substring of `const` left after
    /// removing the known constant prefix and suffix lengths.
    fn detect_concat_constant_witnesses(&self) -> Vec<PrefixSuffixWitness> {
        let mut witnesses: Vec<PrefixSuffixWitness> = Vec::new();
        let mut seen: HashSet<TermId> = HashSet::default();

        for &assertion in &self.ctx.assertions {
            let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(assertion) else {
                continue;
            };
            if name != "=" || args.len() != 2 {
                continue;
            }
            let (concat_term, target) =
                match (self.ctx.terms.get(args[0]), self.ctx.terms.get(args[1])) {
                    (TermData::App(Symbol::Named(n), _), TermData::Const(Constant::String(s)))
                        if n == "str.++" =>
                    {
                        (args[0], s.clone())
                    }
                    (TermData::Const(Constant::String(s)), TermData::App(Symbol::Named(n), _))
                        if n == "str.++" =>
                    {
                        (args[1], s.clone())
                    }
                    _ => continue,
                };
            let TermData::App(_, concat_args) = self.ctx.terms.get(concat_term) else {
                continue;
            };
            let concat_args: Vec<TermId> = concat_args.clone();

            // Locate exactly one free string-variable operand; all others must be
            // string constants (so the witness is deterministic).
            let mut free_idx: Option<usize> = None;
            let mut ok = true;
            for (idx, &arg) in concat_args.iter().enumerate() {
                match self.ctx.terms.get(arg) {
                    TermData::Const(Constant::String(_)) => {}
                    TermData::Var(..)
                        if *self.ctx.terms.sort(arg) == Sort::String && free_idx.is_none() =>
                    {
                        free_idx = Some(idx);
                    }
                    _ => {
                        ok = false;
                        break;
                    }
                }
            }
            if !ok {
                continue;
            }
            let Some(free_idx) = free_idx else {
                continue;
            };
            let free_var = concat_args[free_idx];

            // Sum the known constant lengths before and after the free operand.
            let target_chars: Vec<char> = target.chars().collect();
            let mut prefix_len = 0usize;
            let mut suffix_len = 0usize;
            let mut consistent = true;
            for (idx, &arg) in concat_args.iter().enumerate() {
                if idx == free_idx {
                    continue;
                }
                let TermData::Const(Constant::String(s)) = self.ctx.terms.get(arg) else {
                    consistent = false;
                    break;
                };
                let clen = s.chars().count();
                if idx < free_idx {
                    prefix_len += clen;
                } else {
                    suffix_len += clen;
                }
            }
            if !consistent {
                continue;
            }
            let Some(mid_len) = target_chars.len().checked_sub(prefix_len + suffix_len) else {
                // Constants already overflow the target: length mismatch. Let the
                // normal pipeline derive UNSAT (we only emit SAT witnesses here).
                continue;
            };
            let value: String = target_chars[prefix_len..prefix_len + mid_len]
                .iter()
                .collect();

            if seen.insert(free_var) {
                witnesses.push(PrefixSuffixWitness {
                    var: free_var,
                    candidates: vec![value],
                });
            }
        }

        witnesses
    }

    /// Collect, per string variable, all top-level `(str.in_re x R)` membership
    /// literals (positive and negated). Only bare string-variable subjects are
    /// recorded; memberships over non-variable terms are ignored.
    fn collect_var_memberships(&self) -> Vec<(TermId, Vec<Membership>)> {
        use ay_core::kani_compat::DetHashMap as HashMap;
        let mut map: HashMap<TermId, Vec<Membership>> = HashMap::default();

        for &assertion in &self.ctx.assertions {
            let (atom, positive) = self.strip_negation(assertion);
            let TermData::App(sym, args) = self.ctx.terms.get(atom) else {
                continue;
            };
            if !matches!(sym.name(), "str.in_re" | "str.in.re") || args.len() != 2 {
                continue;
            }
            let subject = args[0];
            let regex = args[1];
            // Subject must be a bare string variable.
            if !matches!(self.ctx.terms.get(subject), TermData::Var(..))
                || *self.ctx.terms.sort(subject) != Sort::String
            {
                continue;
            }
            map.entry(subject)
                .or_default()
                .push(Membership { regex, positive });
        }

        map.into_iter().collect()
    }

    /// Strip a chain of `not` wrappers, returning `(atom, polarity)`.
    fn strip_negation(&self, term: TermId) -> (TermId, bool) {
        let mut t = term;
        let mut polarity = true;
        while let TermData::Not(inner) = self.ctx.terms.get(t) {
            t = *inner;
            polarity = !polarity;
        }
        (t, polarity)
    }

    /// Length window `[lo, hi]` (inclusive) per string variable, with `hi =
    /// usize::MAX` meaning "no upper bound". Mirrors the bound extraction used by
    /// the pivot machinery but without the `MAX_PIVOT_BOUND` filter.
    fn regex_var_length_bounds(&self) -> ay_core::kani_compat::DetHashMap<TermId, (usize, usize)> {
        self.detect_all_string_length_bounds_pub(&self.ctx.assertions)
    }

    /// Compute a sound, finite superset of every character that any string in the
    /// language of regex `r` can contain, or `None` when the language may contain
    /// arbitrary characters (`re.all` / `re.allchar` / `re.comp`) or the regex is
    /// not statically analysable.
    ///
    /// Soundness contract: if this returns `Some(A)`, then for every string `w`
    /// with `w ∈ L(r)`, every character of `w` is in `A`. This lets the caller
    /// enumerate `A^len` and treat "no accepted string found" as exhaustive.
    fn regex_accepted_alphabet(&self, r: TermId) -> Option<HashSet<char>> {
        let TermData::App(sym, args) = self.ctx.terms.get(r) else {
            return None;
        };

        match sym.name() {
            // Empty language: no accepted string ⇒ empty alphabet.
            "re.none" if args.is_empty() => Some(HashSet::default()),

            // str.to_re(c): exactly the characters of the constant c.
            "str.to_re" | "str.to.re" if args.len() == 1 => {
                let s = self.resolve_regex_string_const(args[0])?;
                Some(s.chars().collect())
            }

            // re.range(lo, hi): the closed character range. Per SMT-LIB this is
            // the EMPTY language whenever an endpoint is not a single character
            // or lo > hi — an empty accepted alphabet (nothing is accepted), NOT
            // an open one. Bail only if the (valid) range is too wide to
            // enumerate.
            "re.range" if args.len() == 2 => {
                let lo = self.resolve_regex_string_const(args[0])?;
                let hi = self.resolve_regex_string_const(args[1])?;
                if lo.chars().count() != 1 || hi.chars().count() != 1 {
                    // Non-singleton endpoint(s): empty language ⇒ empty alphabet.
                    return Some(HashSet::default());
                }
                let lo_c = lo.chars().next().unwrap();
                let hi_c = hi.chars().next().unwrap();
                if lo_c > hi_c {
                    // Reversed range: empty language ⇒ empty alphabet.
                    return Some(HashSet::default());
                }
                let span = (hi_c as u32).checked_sub(lo_c as u32)?;
                if span as usize + 1 > MAX_REGEX_ALPHABET {
                    return None;
                }
                let mut set = HashSet::default();
                for cp in (lo_c as u32)..=(hi_c as u32) {
                    set.insert(char::from_u32(cp)?);
                }
                Some(set)
            }

            // Composites: union the children's alphabets. For inter/diff a tighter
            // set exists, but the union is always a safe superset.
            "re.++" | "re.union" | "re.inter" if !args.is_empty() => {
                let mut set = HashSet::default();
                for &child in args {
                    set.extend(self.regex_accepted_alphabet(child)?);
                }
                Some(set)
            }

            // re.*, re.+, re.opt, re.loop: same alphabet as the body.
            "re.*" | "re.+" | "re.opt" | "re.loop" if args.len() == 1 => {
                self.regex_accepted_alphabet(args[0])
            }

            // re.diff(a, b): an accepted string is in L(a); its characters are
            // bounded by a's alphabet (b only removes strings).
            "re.diff" if args.len() == 2 => self.regex_accepted_alphabet(args[0]),

            // Open alphabets — a single accepted string may contain ANY character,
            // so no finite superset exists. Fall closed.
            // re.all, re.allchar, re.comp, and anything unrecognised.
            _ => None,
        }
    }

    /// Resolve a term to a concrete string constant for regex analysis.
    fn resolve_regex_string_const(&self, t: TermId) -> Option<String> {
        match self.ctx.terms.get(t) {
            TermData::Const(Constant::String(s)) => Some(s.clone()),
            _ => None,
        }
    }

    /// Enumerate every string over `alphabet` with character-length in
    /// `[lo, hi]` and return those satisfying *all* memberships (positive must
    /// match, negative must not). Returns `None` if the search space exceeds the
    /// candidate cap (the result would not be exhaustive) or a membership cannot
    /// be ground-evaluated on a candidate (regex not ground-evaluable).
    fn enumerate_accepted_strings(
        &self,
        alphabet: &[char],
        lo: usize,
        hi: usize,
        memberships: &[Membership],
    ) -> Option<Vec<String>> {
        // Bound total work: sum_{len=lo..=hi} |alphabet|^len must stay within the
        // candidate cap so the enumeration is exhaustive.
        let mut total: u64 = 0;
        for len in lo..=hi {
            let count = (alphabet.len() as u64).checked_pow(len as u32)?;
            total = total.checked_add(count)?;
            if total > MAX_PIVOT_CANDIDATES as u64 {
                return None;
            }
        }
        // The empty alphabet only produces the empty string (len 0).
        if alphabet.is_empty() && lo > 0 {
            return Some(Vec::new());
        }

        let mut accepted = Vec::new();
        for len in lo..=hi {
            if len == 0 {
                if self.string_satisfies_memberships("", memberships)? {
                    accepted.push(String::new());
                }
                continue;
            }
            if alphabet.is_empty() {
                continue;
            }
            // Odometer over alphabet indices.
            let mut indices = vec![0usize; len];
            loop {
                let s: String = indices.iter().map(|&i| alphabet[i]).collect();
                if self.string_satisfies_memberships(&s, memberships)? {
                    accepted.push(s);
                }
                // Increment odometer.
                let mut pos = len;
                let done = loop {
                    if pos == 0 {
                        break true;
                    }
                    pos -= 1;
                    indices[pos] += 1;
                    if indices[pos] < alphabet.len() {
                        break false;
                    }
                    indices[pos] = 0;
                };
                if done {
                    break;
                }
            }
        }
        Some(accepted)
    }

    /// Whether concrete string `s` satisfies every membership: each positive
    /// regex matches and each negative regex does not. Returns `None` if any
    /// membership's regex is not ground-evaluable (so the caller falls closed).
    fn string_satisfies_memberships(&self, s: &str, memberships: &[Membership]) -> Option<bool> {
        for m in memberships {
            let matches = ay_strings::ground_eval_in_re(&self.ctx.terms, s, m.regex)?;
            if matches != m.positive {
                return Some(false);
            }
        }
        Some(true)
    }
}

#[cfg(test)]
mod w1b_tests {
    use super::*;

    /// `[x-z]{3}` — no AY path other than derivative construction can emit
    /// these characters when the formula mentions no such literal.
    fn range3() -> WeRegex {
        WeRegex::concat(vec![WeRegex::range("x", "z"); 3])
    }

    #[test]
    fn constructs_exact_length_witness_inside_window() {
        let cands = Executor::construct_regex_witnesses(&[range3()], (3, 3), None);
        assert_eq!(cands.len(), 1, "one exact length in the window: {cands:?}");
        assert_eq!(cands[0].chars().count(), 3);
        assert_eq!(range3().matches(&cands[0]), Some(true));
    }

    #[test]
    fn probes_several_lengths_from_the_bottom_of_the_window() {
        // `[x-z]*` accepts every length; a `>= 2` lower bound must NOT yield
        // the shortest ("") witness alone — that is exactly the candidate the
        // length constraint refutes.
        let star = WeRegex::star(WeRegex::range("x", "z"));
        let cands = Executor::construct_regex_witnesses(&[star], (2, usize::MAX), None);
        assert!(!cands.is_empty());
        assert!(
            cands.iter().all(|c| c.chars().count() >= 2),
            "no candidate below the lower bound: {cands:?}"
        );
        assert!(cands.len() <= W1B_MAX_CANDIDATES);
    }

    #[test]
    fn negative_membership_is_carried_as_exact_complement() {
        // `x ∈ [a-z]{1}` ∧ `x ∉ [a-b]{1}` must construct a letter outside a-b.
        let pos = WeRegex::range("a", "z");
        let neg = WeRegex::comp(WeRegex::range("a", "b"));
        let cands = Executor::construct_regex_witnesses(&[pos.clone(), neg.clone()], (1, 1), None);
        assert!(!cands.is_empty(), "witness must exist");
        for c in &cands {
            assert_eq!(pos.matches(c), Some(true), "{c:?} ∈ [a-z]");
            assert_eq!(neg.matches(c), Some(true), "{c:?} ∉ [a-b]");
        }
    }

    #[test]
    fn empty_language_yields_no_candidate() {
        assert!(Executor::construct_regex_witnesses(&[WeRegex::None], (0, 4), None).is_empty());
    }

    #[test]
    fn deep_witness_beyond_the_default_feasibility_knob_is_reachable() {
        // A 90-character literal chain: far past the default
        // `AY_WE_WITNESS_MAX_LEN` (64 under S1), yet an ordinary witness.
        let lit: String = std::iter::repeat_n('q', 90).collect();
        let cands =
            Executor::construct_regex_witnesses(&[WeRegex::lit(&lit)], (0, usize::MAX), None);
        assert_eq!(cands, vec![lit]);
    }

    #[test]
    fn cheap_probe_shares_one_work_budget_across_lengths() {
        // `All` costs one derivative unit per character. A shared budget of
        // four therefore finds lengths one and two (1 + 2 units), then stops
        // during the length-three probe. Resetting four units for every probe
        // would incorrectly admit all four candidates.
        let cands = Executor::construct_regex_witnesses(&[WeRegex::All], (1, 4), Some(4));
        let lengths: Vec<usize> = cands.iter().map(|word| word.chars().count()).collect();
        assert_eq!(lengths, vec![1, 2]);
    }
}
