// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! String formula analysis helpers: length bounds, alphabet collection,
//! candidate generation, and decomposition concat collection.
//!
//! Extracted from `strings.rs` for code health (#5970). These helpers
//! are shared by both `strings.rs` (QF_S) and `strings_lia.rs` (QF_SLIA).

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::{Constant, Symbol, TermData, TermId};
use ay_core::Sort;

use super::super::Executor;

/// Allow a small number of repeated string lemma requests before declaring stall.
///
/// A single immediate repeat can still make progress after SAT explores the
/// updated search space from prior splits. We only treat the loop as stalled
/// after multiple consecutive repeats of the exact same lemma.
pub(super) const MAX_CONSECUTIVE_DUPLICATE_LEMMAS: usize = 5;

/// Maximum upper bound for a pivot variable to be eligible for enumeration.
/// Variables with len > this are too expensive to enumerate character by character.
const MAX_PIVOT_BOUND: usize = 3;

/// Maximum number of candidate values to enumerate before falling back.
pub(super) const MAX_PIVOT_CANDIDATES: usize = 200;

/// Detected length bound for a string variable.
pub(super) struct LengthBound {
    /// The variable's TermId
    pub(super) var: TermId,
    pub(super) lower: usize,
    pub(super) upper: usize,
}

/// A prefix/suffix-derived candidate witness for an unbounded string variable.
pub(super) struct PrefixSuffixWitness {
    /// The variable this witness assigns.
    pub(super) var: TermId,
    /// Candidate concrete values, minimal length first.
    pub(super) candidates: Vec<String>,
}

/// The positive string predicate a concat witness is being built for.
#[derive(Clone, Copy)]
enum PredKind {
    Contains,
    PrefixOf,
    SuffixOf,
}

impl Executor {
    /// Generate minimal-length witness candidates for string variables that are
    /// positively constrained by `str.prefixof(p, z)` and `str.suffixof(s, z)`
    /// with constant `p`, `s` but have NO upper length bound (so pivot
    /// enumeration cannot fire).
    ///
    /// The minimal models are the overlap-merges of `p` and `s`: for each
    /// overlap `o` (largest first) where the last `o` chars of `p` equal the
    /// first `o` chars of `s`, the merge `p ++ s[o..]` is a valid witness
    /// (prefix `p`, suffix `s`). These candidates are only *tried* — each is
    /// re-solved as a hard assumption and fully model-validated before any SAT
    /// is trusted, so this is a completeness heuristic with zero soundness risk
    /// (a wrong guess simply falls through to the normal CEGAR loop).
    ///
    /// Conservative gating: only variables whose sole positive occurrences are
    /// in `prefixof`/`suffixof` predicates are considered, to keep the witness
    /// list small. Any other constraint on `z` (equalities, lengths, contains,
    /// regex, ...) makes the variable ineligible here — the normal pipeline
    /// handles those.
    pub(super) fn detect_prefix_suffix_witnesses(&self) -> Vec<PrefixSuffixWitness> {
        let mut prefixes: HashMap<TermId, Vec<String>> = HashMap::default();
        let mut suffixes: HashMap<TermId, Vec<String>> = HashMap::default();
        // Variables that appear in any term we don't model as pure prefix/suffix.
        let mut ineligible: HashSet<TermId> = HashSet::default();

        for &assertion in &self.ctx.assertions {
            self.scan_prefix_suffix_term(
                assertion,
                true,
                &mut prefixes,
                &mut suffixes,
                &mut ineligible,
            );
        }

        let mut witnesses = Vec::new();
        for (&var, ps) in &prefixes {
            if ineligible.contains(&var) {
                continue;
            }
            let Some(ss) = suffixes.get(&var) else {
                continue;
            };
            let mut candidates: Vec<String> = Vec::new();
            for p in ps {
                for s in ss {
                    for cand in Self::overlap_merge_candidates(p, s) {
                        if !candidates.contains(&cand) {
                            candidates.push(cand);
                        }
                    }
                }
            }
            // Shortest candidates first (minimal witnesses).
            candidates.sort_by_key(|c| c.chars().count());
            candidates.truncate(MAX_PIVOT_CANDIDATES);
            if !candidates.is_empty() {
                witnesses.push(PrefixSuffixWitness { var, candidates });
            }
        }
        witnesses
    }

    /// Recursively classify a term, recording prefixof/suffixof constant edges
    /// and marking any string variable used in any *other* position as
    /// ineligible for the prefix/suffix witness heuristic.
    fn scan_prefix_suffix_term(
        &self,
        term: TermId,
        positive: bool,
        prefixes: &mut HashMap<TermId, Vec<String>>,
        suffixes: &mut HashMap<TermId, Vec<String>>,
        ineligible: &mut HashSet<TermId>,
    ) {
        match self.ctx.terms.get(term) {
            TermData::Not(inner) => {
                self.scan_prefix_suffix_term(*inner, !positive, prefixes, suffixes, ineligible);
            }
            TermData::App(Symbol::Named(name), args) => {
                // A positive prefixof/suffixof with a constant first arg and a
                // string-variable second arg is a recognised edge. The variable
                // is NOT marked ineligible by this occurrence.
                if positive && args.len() == 2 && (name == "str.prefixof" || name == "str.suffixof")
                {
                    if let (TermData::Const(Constant::String(c)), TermData::Var(..)) =
                        (self.ctx.terms.get(args[0]), self.ctx.terms.get(args[1]))
                    {
                        let c = c.clone();
                        if name == "str.prefixof" {
                            prefixes.entry(args[1]).or_default().push(c);
                        } else {
                            suffixes.entry(args[1]).or_default().push(c);
                        }
                        return;
                    }
                }
                // Any other occurrence: mark every string-variable descendant as
                // ineligible (it is constrained by something we don't model).
                for &arg in args {
                    self.mark_string_vars_ineligible(arg, ineligible);
                }
            }
            TermData::Ite(c, t, e) => {
                self.mark_string_vars_ineligible(*c, ineligible);
                self.mark_string_vars_ineligible(*t, ineligible);
                self.mark_string_vars_ineligible(*e, ineligible);
            }
            _ => {}
        }
    }

    /// Mark all string-sorted variables reachable from `term` as ineligible.
    fn mark_string_vars_ineligible(&self, term: TermId, ineligible: &mut HashSet<TermId>) {
        let mut stack = vec![term];
        let mut seen = HashSet::default();
        while let Some(t) = stack.pop() {
            if !seen.insert(t) {
                continue;
            }
            match self.ctx.terms.get(t) {
                TermData::Var(..) if *self.ctx.terms.sort(t) == Sort::String => {
                    ineligible.insert(t);
                }
                TermData::App(_, args) => stack.extend(args.iter().copied()),
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(c, th, e) => {
                    stack.push(*c);
                    stack.push(*th);
                    stack.push(*e);
                }
                _ => {}
            }
        }
    }

    /// Enumerate overlap-merge witnesses of `p` (prefix) and `s` (suffix).
    ///
    /// For each overlap `o` from `min(|p|,|s|)` down to 0 where `p`'s last `o`
    /// chars equal `s`'s first `o` chars, yield `p ++ s[o..]`. Larger overlap =
    /// shorter witness; the non-overlapping `o = 0` case is always included.
    fn overlap_merge_candidates(p: &str, s: &str) -> Vec<String> {
        let p_chars: Vec<char> = p.chars().collect();
        let s_chars: Vec<char> = s.chars().collect();
        let max_overlap = p_chars.len().min(s_chars.len());
        let mut out = Vec::new();
        for o in (0..=max_overlap).rev() {
            if p_chars[p_chars.len() - o..] == s_chars[..o] {
                let mut merged: String = p_chars.iter().collect();
                merged.extend(s_chars[o..].iter());
                out.push(merged);
            }
        }
        out
    }

    /// #ssl-residue B: pinned-length placement witnesses.
    ///
    /// When `(= (str.len x) N)` pins a concrete length for a string VARIABLE
    /// `x`, positional anchors constrain windows of `x` directly:
    /// * `(= (str.substr x i m) c)` — place `c` (|c| = m) at position `i`;
    /// * `(= (str.indexof x needle 0) k)`, `k >= 0` — place `needle` at `k`
    ///   (the needle-free prefix comes from the filler character);
    /// * `(str.contains x c)` (positive, top-level) — place `c` at each
    ///   feasible start position (floating anchor).
    ///
    /// Candidates fill every unconstrained position with a character absent
    /// from all anchor constants (so no accidental extra needle occurrence).
    /// PURELY heuristic — every candidate is re-solved as a hard assumption
    /// and fully model-validated before SAT is trusted (see
    /// `try_string_var_witnesses`), so a wrong guess falls through to the
    /// normal pipeline and genuinely-UNSAT cases stay UNSAT. Negated
    /// predicates are never anchors; conflicting fixed anchors yield no
    /// candidates (fall-through).
    pub(super) fn detect_pinned_length_placement_witnesses(&self) -> Vec<PrefixSuffixWitness> {
        use num_traits::ToPrimitive;
        const MAX_PIN_LEN: usize = 64;
        const MAX_PLACEMENT_CANDIDATES: usize = 24;

        let get_int = |t: TermId| -> Option<usize> {
            match self.ctx.terms.get(t) {
                TermData::Const(Constant::Int(n)) => n.to_usize(),
                _ => None,
            }
        };
        let get_str = |t: TermId| -> Option<String> {
            match self.ctx.terms.get(t) {
                TermData::Const(Constant::String(s)) => Some(s.clone()),
                _ => None,
            }
        };
        let is_str_var = |t: TermId| -> bool {
            matches!(self.ctx.terms.get(t), TermData::Var(..))
                && *self.ctx.terms.sort(t) == Sort::String
        };

        let mut pins: HashMap<TermId, usize> = HashMap::default();
        // (start, constant) placements that are forced at a fixed position.
        let mut fixed: HashMap<TermId, Vec<(usize, String)>> = HashMap::default();
        // Constants that must occur somewhere (start position free).
        let mut floating: HashMap<TermId, Vec<String>> = HashMap::default();

        for &assertion in &self.ctx.assertions {
            match self.ctx.terms.get(assertion) {
                TermData::App(Symbol::Named(name), args) if name == "=" && args.len() == 2 => {
                    for (l, r) in [(args[0], args[1]), (args[1], args[0])] {
                        let TermData::App(Symbol::Named(n2), a2) = self.ctx.terms.get(l) else {
                            continue;
                        };
                        if n2 == "str.len" && a2.len() == 1 && is_str_var(a2[0]) {
                            if let Some(n) = get_int(r) {
                                if n <= MAX_PIN_LEN {
                                    pins.entry(a2[0]).or_insert(n);
                                }
                            }
                        } else if n2 == "str.substr" && a2.len() == 3 && is_str_var(a2[0]) {
                            if let (Some(i), Some(m), Some(c)) =
                                (get_int(a2[1]), get_int(a2[2]), get_str(r))
                            {
                                if m >= 1 && c.chars().count() == m {
                                    fixed.entry(a2[0]).or_default().push((i, c));
                                }
                            }
                        } else if n2 == "str.indexof"
                            && a2.len() == 3
                            && is_str_var(a2[0])
                            && get_int(a2[2]) == Some(0)
                        {
                            if let (Some(needle), Some(k)) = (get_str(a2[1]), get_int(r)) {
                                if !needle.is_empty() {
                                    fixed.entry(a2[0]).or_default().push((k, needle));
                                }
                            }
                        }
                    }
                }
                TermData::App(Symbol::Named(name), args)
                    if name == "str.contains" && args.len() == 2 =>
                {
                    if is_str_var(args[0]) {
                        if let Some(c) = get_str(args[1]) {
                            if !c.is_empty() {
                                floating.entry(args[0]).or_default().push(c);
                            }
                        }
                    }
                }
                _ => {}
            }
        }

        let mut witnesses = Vec::new();
        for (&var, &n) in &pins {
            let fixed_a = fixed.get(&var).cloned().unwrap_or_default();
            let float_a = floating.get(&var).cloned().unwrap_or_default();
            if fixed_a.is_empty() && float_a.is_empty() {
                continue;
            }
            // Filler character absent from every anchor constant.
            let mut used: HashSet<char> = HashSet::default();
            for (_, c) in &fixed_a {
                used.extend(c.chars());
            }
            for c in &float_a {
                used.extend(c.chars());
            }
            let filler = ('a'..='z')
                .chain('A'..='Z')
                .chain('0'..='9')
                .find(|ch| !used.contains(ch))
                .unwrap_or('~');

            // Apply the fixed anchors to the position slots.
            let mut base: Vec<Option<char>> = vec![None; n];
            let mut ok = true;
            for (start, c) in &fixed_a {
                let cs: Vec<char> = c.chars().collect();
                if start + cs.len() > n {
                    ok = false;
                    break;
                }
                for (j, ch) in cs.iter().enumerate() {
                    match base[start + j] {
                        None => base[start + j] = Some(*ch),
                        Some(prev) if prev == *ch => {}
                        Some(_) => {
                            ok = false;
                            break;
                        }
                    }
                }
                if !ok {
                    break;
                }
            }
            if !ok {
                continue;
            }

            // Branch the floating anchors over feasible start positions.
            let mut partials: Vec<Vec<Option<char>>> = vec![base];
            for c in &float_a {
                let cs: Vec<char> = c.chars().collect();
                let mut next: Vec<Vec<Option<char>>> = Vec::new();
                if cs.len() > n {
                    partials.clear();
                    break;
                }
                'outer: for partial in &partials {
                    for p in 0..=(n - cs.len()) {
                        let mut cand = partial.clone();
                        let mut fits = true;
                        for (j, ch) in cs.iter().enumerate() {
                            match cand[p + j] {
                                None => cand[p + j] = Some(*ch),
                                Some(prev) if prev == *ch => {}
                                Some(_) => {
                                    fits = false;
                                    break;
                                }
                            }
                        }
                        if fits {
                            next.push(cand);
                        }
                        if next.len() >= MAX_PLACEMENT_CANDIDATES {
                            break 'outer;
                        }
                    }
                }
                partials = next;
            }

            let mut candidates: Vec<String> = Vec::new();
            for partial in partials {
                let s: String = partial.into_iter().map(|c| c.unwrap_or(filler)).collect();
                if !candidates.contains(&s) {
                    candidates.push(s);
                }
            }
            candidates.truncate(MAX_PLACEMENT_CANDIDATES);
            if !candidates.is_empty() {
                witnesses.push(PrefixSuffixWitness { var, candidates });
            }
        }
        witnesses
    }

    /// Resolve a string term to a concrete constant using literal string
    /// constants and explicit `(= var "const")` assignments.
    ///
    /// Returns `None` for any term that is not provably a single constant
    /// (free variable with no assignment, non-constant operand, nested
    /// concat with a free component). Used only to identify the *grounded*
    /// neighbours of a free component when constructing a witness; the
    /// witness is then validated by a full model solve, so a conservative
    /// `None` here only forgoes the heuristic — it is never unsound.
    fn resolve_string_const(
        &self,
        term: TermId,
        assignments: &HashMap<TermId, String>,
    ) -> Option<String> {
        match self.ctx.terms.get(term) {
            TermData::Const(Constant::String(s)) => Some(s.clone()),
            TermData::Var(..) => assignments.get(&term).cloned(),
            TermData::App(Symbol::Named(name), args) if name == "str.++" => {
                let args: Vec<TermId> = args.clone();
                let mut out = String::new();
                for arg in args {
                    out.push_str(&self.resolve_string_const(arg, assignments)?);
                }
                Some(out)
            }
            _ => None,
        }
    }

    /// Detect positive `str.contains`/`str.prefixof`/`str.suffixof` predicates
    /// over a partially-grounded `str.++` and construct concrete witnesses for
    /// the single free (string-variable) component that make the predicate true.
    ///
    /// Only POSITIVE predicates are considered: a witness for the free operand
    /// of a *negated* predicate could hide a genuine conflict, so negations are
    /// skipped entirely (`positive == false`). The free variable is set to a
    /// concrete value; every candidate is re-solved as a hard assumption and
    /// fully model-validated before any SAT is trusted (see
    /// `try_contains_prefix_suffix_concat_witnesses`), so a wrong guess is
    /// harmless — it simply falls through to the normal pipeline.
    ///
    /// A free variable that also appears in OTHER constraints is *not* excluded
    /// here; the validation gate (full model + assumption validation) rejects
    /// any candidate inconsistent with those constraints. We only require that
    /// the free component is a bare string variable and that all *other*
    /// components of the concat resolve to constants (so the witness can be
    /// computed deterministically).
    /// Detect `(= (str.replace_all v t u) c)` equalities (both orders) with
    /// a bare string-variable haystack `v` and ground `t`/`u`/`c`, and
    /// construct concrete witness candidates for `v` (extf wave 2):
    ///
    /// 1. the inverse image `replace_all(c, u, t)` — the value whose forward
    ///    replacement most plausibly yields `c` (exact when `u` occurrences
    ///    in `c` are exactly the images of the original `t` occurrences);
    /// 2. `c` itself — covers the no-match case (`v` has no occurrence of
    ///    `t`, so the result is `v` unchanged).
    ///
    /// Both are heuristic: every candidate is re-solved as a hard assumption
    /// and fully model-validated before SAT is trusted (see
    /// `try_string_var_witnesses`), so a wrong guess is harmless and an
    /// UNSAT candidate never concludes global UNSAT.
    pub(super) fn detect_replace_all_witnesses(&self) -> Vec<PrefixSuffixWitness> {
        let mut witnesses: Vec<PrefixSuffixWitness> = Vec::new();
        let mut seen_vars: HashSet<TermId> = HashSet::default();

        for &assertion in &self.ctx.assertions {
            let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(assertion) else {
                continue;
            };
            if name != "=" || args.len() != 2 {
                continue;
            }
            for (app_side, const_side) in [(args[0], args[1]), (args[1], args[0])] {
                let TermData::App(Symbol::Named(app_name), app_args) = self.ctx.terms.get(app_side)
                else {
                    continue;
                };
                if app_name != "str.replace_all" || app_args.len() != 3 {
                    continue;
                }
                let v = app_args[0];
                if !matches!(self.ctx.terms.get(v), TermData::Var(..)) {
                    continue;
                }
                let TermData::Const(Constant::String(c)) = self.ctx.terms.get(const_side) else {
                    continue;
                };
                let TermData::Const(Constant::String(t)) = self.ctx.terms.get(app_args[1]) else {
                    continue;
                };
                let TermData::Const(Constant::String(u)) = self.ctx.terms.get(app_args[2]) else {
                    continue;
                };
                if seen_vars.contains(&v) {
                    continue;
                }
                let mut cands: Vec<String> = Vec::new();
                if !u.is_empty() && !t.is_empty() {
                    let inverse = ay_strings::eval::eval_str_replace_all(c, u, t);
                    cands.push(inverse);
                }
                if !cands.contains(c) {
                    cands.push(c.clone());
                }
                if !cands.is_empty() {
                    seen_vars.insert(v);
                    witnesses.push(PrefixSuffixWitness {
                        var: v,
                        candidates: cands,
                    });
                }
            }
        }
        witnesses
    }

    pub(super) fn detect_concat_predicate_witnesses(&self) -> Vec<PrefixSuffixWitness> {
        let assignments = self.explicit_string_assignments(&self.ctx.assertions);
        let mut witnesses: Vec<PrefixSuffixWitness> = Vec::new();
        let mut seen_vars: HashSet<TermId> = HashSet::default();

        for &assertion in &self.ctx.assertions {
            // Only positive (non-negated) predicates are eligible. A negation
            // constrains the model; constructing a witness could hide a
            // conflict and produce a wrong SAT.
            let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(assertion) else {
                continue;
            };
            if args.len() != 2 {
                continue;
            }
            let name = name.clone();
            let args: Vec<TermId> = args.clone();
            let kind = match name.as_str() {
                "str.contains" => PredKind::Contains,
                "str.prefixof" => PredKind::PrefixOf,
                "str.suffixof" => PredKind::SuffixOf,
                _ => continue,
            };
            for (var, candidates) in
                self.concat_predicate_candidates(kind, args[0], args[1], &assignments)
            {
                if seen_vars.contains(&var) {
                    continue;
                }
                let mut cands: Vec<String> = Vec::new();
                for c in candidates {
                    if !cands.contains(&c) {
                        cands.push(c);
                    }
                }
                cands.sort_by_key(|c| c.chars().count());
                cands.truncate(MAX_PIVOT_CANDIDATES);
                if !cands.is_empty() {
                    seen_vars.insert(var);
                    witnesses.push(PrefixSuffixWitness {
                        var,
                        candidates: cands,
                    });
                }
            }
        }
        witnesses
    }

    /// Compute `(free_var, candidate_values)` witnesses for one positive
    /// predicate `pred(arg0, arg1)`.
    ///
    /// Handles each of `contains`/`prefixof`/`suffixof` in both argument
    /// orientations. Returns at most one `(var, values)` pair per eligible
    /// free component. The values are concrete strings; the caller validates
    /// them via a full model solve, so over-generation is sound.
    fn concat_predicate_candidates(
        &self,
        kind: PredKind,
        arg0: TermId,
        arg1: TermId,
        assignments: &HashMap<TermId, String>,
    ) -> Vec<(TermId, Vec<String>)> {
        let mut out: Vec<(TermId, Vec<String>)> = Vec::new();
        match kind {
            PredKind::Contains => {
                // contains(haystack, needle): place `needle` inside a free
                // component of the haystack concat. Needle must be a constant.
                let Some(needle) = self.resolve_string_const(arg1, assignments) else {
                    return out;
                };
                if needle.is_empty() {
                    return out; // Already trivially true.
                }
                // Single-free-component path: includes boundary-spanning
                // completions that straddle the grounded prefix neighbour.
                self.collect_concat_free_witnesses(
                    arg0,
                    assignments,
                    &mut out,
                    |prefix, _suffix| {
                        // Default: free := needle (needle wholly inside it).
                        let mut cands = vec![needle.clone()];
                        // Boundary completion: complete a match that straddles
                        // the grounded prefix neighbour. If `prefix` ends with a
                        // proper, non-empty prefix `α` of `needle`, set free so
                        // the remaining `needle[α..]` follows directly.
                        let pchars: Vec<char> = prefix.chars().collect();
                        let nchars: Vec<char> = needle.chars().collect();
                        let max = pchars.len().min(nchars.len().saturating_sub(1));
                        for a in (1..=max).rev() {
                            if pchars[pchars.len() - a..] == nchars[..a] {
                                let rest: String = nchars[a..].iter().collect();
                                if !cands.contains(&rest) {
                                    cands.push(rest);
                                }
                            }
                        }
                        cands
                    },
                );
                // Multi-free-component fallback: when the concat has more than
                // one free variable component, the single-free path above bails
                // (prefix/suffix are not determined). Placing the needle wholly
                // inside any one free component still makes contains true; the
                // other free components are assigned by the inner solver. Emit
                // `free := needle` for each free component. Validation gates SAT.
                if out.is_empty() {
                    for f in self.concat_free_var_components(arg0, assignments) {
                        out.push((f, vec![needle.clone()]));
                    }
                }
            }
            PredKind::PrefixOf => {
                // prefixof(p, s): p is a prefix of s.
                // Orientation A: s = str.++(g, free, ...), p constant.
                //   Need p to be a prefix of g++free++...  Set the free
                //   component so g++free starts with p (when p extends past g).
                if let Some(p) = self.resolve_string_const(arg0, assignments) {
                    let before = out.len();
                    self.collect_concat_free_witnesses(
                        arg1,
                        assignments,
                        &mut out,
                        |prefix, _suffix| {
                            // `prefix` = grounded part before the free component.
                            // free := p[len(prefix)..] when prefix is a prefix of p.
                            let pre: Vec<char> = prefix.chars().collect();
                            let pc: Vec<char> = p.chars().collect();
                            let mut cands = Vec::new();
                            if pc.len() >= pre.len() && pc[..pre.len()] == pre[..] {
                                let rest: String = pc[pre.len()..].iter().collect();
                                cands.push(rest);
                            }
                            // Also offer the empty witness (covers p shorter than
                            // the grounded prefix, e.g. p already a prefix).
                            cands.push(String::new());
                            cands
                        },
                    );
                    // Multi-free fallback: the single-free path bails when the
                    // haystack concat has more than one free component. Anchor
                    // `p` on the first free leaf (validation-gated).
                    if out.len() == before {
                        if let Some(w) = self.concat_prefix_anchor_witness(arg1, &p, assignments) {
                            out.push(w);
                        }
                    }
                }
                // Orientation B: p = str.++(g, free, ...), s constant.
                //   Need g++free++... to be a prefix of s. Set the free
                //   component to the slice of s after the grounded prefix.
                if let Some(s) = self.resolve_string_const(arg1, assignments) {
                    self.collect_concat_free_witnesses(
                        arg0,
                        assignments,
                        &mut out,
                        |prefix, suffix| {
                            // free occupies s[len(prefix) .. len(s)-len(suffix)].
                            let schars: Vec<char> = s.chars().collect();
                            let plen = prefix.chars().count();
                            let slen = suffix.chars().count();
                            let mut cands = Vec::new();
                            if plen + slen <= schars.len()
                                && prefix == &schars[..plen].iter().collect::<String>()
                            {
                                let mid: String =
                                    schars[plen..schars.len() - slen].iter().collect();
                                cands.push(mid);
                            }
                            cands.push(String::new());
                            cands
                        },
                    );
                }
            }
            PredKind::SuffixOf => {
                // suffixof(p, s): p is a suffix of s.
                // Orientation A: s = str.++(..., free, g), p constant.
                //   Need p to be a suffix of ...++free++g. Set free so
                //   free++g ends with p (when p extends past g).
                if let Some(p) = self.resolve_string_const(arg0, assignments) {
                    let before = out.len();
                    self.collect_concat_free_witnesses(
                        arg1,
                        assignments,
                        &mut out,
                        |_prefix, suffix| {
                            // `suffix` = grounded part after the free component.
                            // free := p[..len(p)-len(suffix)] when suffix is a
                            // suffix of p.
                            let suf: Vec<char> = suffix.chars().collect();
                            let pc: Vec<char> = p.chars().collect();
                            let mut cands = Vec::new();
                            if pc.len() >= suf.len() && pc[pc.len() - suf.len()..] == suf[..] {
                                let rest: String = pc[..pc.len() - suf.len()].iter().collect();
                                cands.push(rest);
                            }
                            cands.push(String::new());
                            cands
                        },
                    );
                    // Multi-free fallback: anchor `p` on the last free leaf.
                    if out.len() == before {
                        if let Some(w) = self.concat_suffix_anchor_witness(arg1, &p, assignments) {
                            out.push(w);
                        }
                    }
                }
                // Orientation B: p = str.++(..., free, g), s constant.
                //   Need ...++free++g to be a suffix of s. Set the free
                //   component to the slice of s between the grounded ends.
                if let Some(s) = self.resolve_string_const(arg1, assignments) {
                    self.collect_concat_free_witnesses(
                        arg0,
                        assignments,
                        &mut out,
                        |prefix, suffix| {
                            let schars: Vec<char> = s.chars().collect();
                            let plen = prefix.chars().count();
                            let slen = suffix.chars().count();
                            let mut cands = Vec::new();
                            if plen + slen <= schars.len()
                                && suffix
                                    == &schars[schars.len() - slen..].iter().collect::<String>()
                            {
                                let mid: String =
                                    schars[plen..schars.len() - slen].iter().collect();
                                cands.push(mid);
                            }
                            cands.push(String::new());
                            cands
                        },
                    );
                }
            }
        }
        out
    }

    /// Return the free (unassigned) string-variable leaf components of a
    /// `str.++` term, in order. Used for the multi-free `contains` fallback,
    /// where placing the needle in any one of them suffices.
    fn concat_free_var_components(
        &self,
        concat: TermId,
        assignments: &HashMap<TermId, String>,
    ) -> Vec<TermId> {
        let mut leaves = Vec::new();
        Self::collect_concat_leaves(&self.ctx.terms, concat, &mut leaves);
        // Only treat the concat as eligible when every non-free leaf resolves
        // to a constant; otherwise the placement reasoning is unreliable.
        let mut out = Vec::new();
        for leaf in leaves {
            let is_free_var = matches!(self.ctx.terms.get(leaf), TermData::Var(..))
                && *self.ctx.terms.sort(leaf) == Sort::String
                && !assignments.contains_key(&leaf);
            if is_free_var {
                if !out.contains(&leaf) {
                    out.push(leaf);
                }
            } else if self.resolve_string_const(leaf, assignments).is_none() {
                return Vec::new();
            }
        }
        out
    }

    /// Multi-free `prefixof(p, concat)` orientation-A witness.
    ///
    /// When the haystack concat has *more than one* free component (so the
    /// single-free [`Self::collect_concat_free_witnesses`] path bails), `p` is
    /// still a prefix of the concat as long as the leftmost characters spell
    /// `p`. We anchor on the FIRST free leaf: accumulate the grounded constant
    /// prefix of leaves before it; if that grounded prefix is itself a prefix of
    /// `p`, set the first free leaf to the remaining `p[grounded..]`. Trailing
    /// leaves (free or not) do not affect prefix-ness, so they are left to the
    /// inner solver. A leaf before the first free one that cannot be grounded,
    /// or a grounded prefix that diverges from `p`, yields no witness (the
    /// caller falls through). The candidate is validation-gated, so an
    /// over-eager guess is harmless.
    fn concat_prefix_anchor_witness(
        &self,
        concat: TermId,
        p: &str,
        assignments: &HashMap<TermId, String>,
    ) -> Option<(TermId, Vec<String>)> {
        let mut leaves = Vec::new();
        Self::collect_concat_leaves(&self.ctx.terms, concat, &mut leaves);
        let pc: Vec<char> = p.chars().collect();
        let mut grounded = 0usize; // chars of `p` matched by grounded leaves so far
        for leaf in leaves {
            let is_free_var = matches!(self.ctx.terms.get(leaf), TermData::Var(..))
                && *self.ctx.terms.sort(leaf) == Sort::String
                && !assignments.contains_key(&leaf);
            if is_free_var {
                // Anchor here: free := p[grounded..].
                let rest: String = pc[grounded.min(pc.len())..].iter().collect();
                return Some((leaf, vec![rest, String::new()]));
            }
            // Grounded leaf: it must continue spelling `p` (or, once `p` is fully
            // consumed, anything is fine since the prefix is already satisfied).
            let g = self.resolve_string_const(leaf, assignments)?;
            for ch in g.chars() {
                if grounded < pc.len() {
                    if pc[grounded] != ch {
                        return None; // Grounded prefix diverges from `p`.
                    }
                    grounded += 1;
                }
            }
        }
        None
    }

    /// Multi-free `suffixof(p, concat)` orientation-A witness (mirror of
    /// [`Self::concat_prefix_anchor_witness`]). Anchors on the LAST free leaf:
    /// accumulate the grounded constant suffix of leaves after it; if that
    /// grounded suffix is a suffix of `p`, set the last free leaf to the leading
    /// `p[..len(p)-grounded]`. Leading leaves do not affect suffix-ness.
    /// Validation-gated, so over-generation is sound.
    fn concat_suffix_anchor_witness(
        &self,
        concat: TermId,
        p: &str,
        assignments: &HashMap<TermId, String>,
    ) -> Option<(TermId, Vec<String>)> {
        let mut leaves = Vec::new();
        Self::collect_concat_leaves(&self.ctx.terms, concat, &mut leaves);
        let pc: Vec<char> = p.chars().collect();
        let mut grounded = 0usize; // chars of `p`'s tail matched by grounded leaves
        for leaf in leaves.into_iter().rev() {
            let is_free_var = matches!(self.ctx.terms.get(leaf), TermData::Var(..))
                && *self.ctx.terms.sort(leaf) == Sort::String
                && !assignments.contains_key(&leaf);
            if is_free_var {
                let keep = pc.len().saturating_sub(grounded);
                let rest: String = pc[..keep].iter().collect();
                return Some((leaf, vec![rest, String::new()]));
            }
            let g = self.resolve_string_const(leaf, assignments)?;
            for ch in g.chars().rev() {
                if grounded < pc.len() {
                    if pc[pc.len() - 1 - grounded] != ch {
                        return None; // Grounded suffix diverges from `p`.
                    }
                    grounded += 1;
                }
            }
        }
        None
    }

    /// For a `str.++` term, find a single free (string-variable) component
    /// whose grounded neighbours (everything strictly before / after it) all
    /// resolve to constants, and produce its witness values via `make`.
    ///
    /// `make(prefix, suffix)` receives the concatenation of the grounded
    /// components before the free component (`prefix`) and after it (`suffix`),
    /// and returns candidate concrete values for the free component.
    ///
    /// Only fires when the concat has exactly one free component (so prefix and
    /// suffix are fully determined). Multiple free components are left to the
    /// normal pipeline / single-needle placement handled by the caller.
    fn collect_concat_free_witnesses<F>(
        &self,
        concat: TermId,
        assignments: &HashMap<TermId, String>,
        out: &mut Vec<(TermId, Vec<String>)>,
        make: F,
    ) where
        F: Fn(&str, &str) -> Vec<String>,
    {
        let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(concat) else {
            return;
        };
        if name != "str.++" {
            return;
        }
        let args: Vec<TermId> = args.clone();
        // Identify free string-variable components vs grounded ones.
        let mut free_idx: Option<usize> = None;
        for (i, &a) in args.iter().enumerate() {
            let is_free_var = matches!(self.ctx.terms.get(a), TermData::Var(..))
                && *self.ctx.terms.sort(a) == Sort::String
                && !assignments.contains_key(&a);
            if is_free_var {
                if free_idx.is_some() {
                    return; // More than one free component — not handled here.
                }
                free_idx = Some(i);
            } else if self.resolve_string_const(a, assignments).is_none() {
                return; // A non-free component we cannot ground — bail.
            }
        }
        let Some(fi) = free_idx else {
            return; // Fully grounded — nothing to witness.
        };
        let free_var = args[fi];
        let mut prefix = String::new();
        for &a in &args[..fi] {
            match self.resolve_string_const(a, assignments) {
                Some(s) => prefix.push_str(&s),
                None => return,
            }
        }
        let mut suffix = String::new();
        for &a in &args[fi + 1..] {
            match self.resolve_string_const(a, assignments) {
                Some(s) => suffix.push_str(&s),
                None => return,
            }
        }
        let cands = make(&prefix, &suffix);
        if !cands.is_empty() {
            out.push((free_var, cands));
        }
    }

    fn known_exact_string_length(
        &self,
        term: TermId,
        exact_var_lengths: &HashMap<TermId, usize>,
        visiting: &mut HashSet<TermId>,
    ) -> Option<usize> {
        if let Some(&len) = exact_var_lengths.get(&term) {
            return Some(len);
        }

        if !visiting.insert(term) {
            return None;
        }

        let result = match self.ctx.terms.get(term) {
            TermData::Const(Constant::String(s)) => Some(s.chars().count()),
            TermData::App(Symbol::Named(name), args) if name == "str.++" => {
                let mut total = 0usize;
                for &arg in args {
                    let len = self.known_exact_string_length(arg, exact_var_lengths, visiting)?;
                    total = total.checked_add(len)?;
                }
                Some(total)
            }
            _ => None,
        };

        visiting.remove(&term);
        result
    }

    /// Extract all exact string length equalities from assertions without
    /// the `MAX_PIVOT_BOUND` filter.
    ///
    /// Unlike `detect_bounded_string_vars_in`, this returns exact lengths
    /// for ALL variables regardless of their bound magnitude. This is needed
    /// for `has_exact_string_length_contradiction` which should detect
    /// contradictions even when variable lengths exceed the pivot enumeration
    /// threshold (#7464).
    fn detect_exact_string_lengths(&self, assertions: &[TermId]) -> HashMap<TermId, usize> {
        let mut bounds: HashMap<TermId, (Option<usize>, Option<usize>)> = HashMap::default();

        for &assertion in assertions {
            self.extract_length_bound_from_term(assertion, &mut bounds);
        }

        bounds
            .into_iter()
            .filter_map(|(var, (lo, hi))| {
                let lower = lo.unwrap_or(0);
                let upper = hi?;
                if lower == upper {
                    Some((var, lower))
                } else {
                    None
                }
            })
            .collect()
    }

    /// Extract all string length bounds from assertions without the
    /// `MAX_PIVOT_BOUND` filter.
    ///
    /// Returns `(lower, upper)` for each variable. Upper may be `usize::MAX`
    /// if no upper bound was detected.
    /// Public wrapper over [`Self::detect_all_string_length_bounds`] for the
    /// regex×length pre-pass (a sibling theories module).
    pub(super) fn detect_all_string_length_bounds_pub(
        &self,
        assertions: &[TermId],
    ) -> HashMap<TermId, (usize, usize)> {
        self.detect_all_string_length_bounds(assertions)
    }

    fn detect_all_string_length_bounds(
        &self,
        assertions: &[TermId],
    ) -> HashMap<TermId, (usize, usize)> {
        // #8529: Use deterministic hash maps in all builds.
        use ay_core::kani_compat::DetHashMap as HashMap;
        let mut bounds: HashMap<TermId, (Option<usize>, Option<usize>)> = HashMap::default();

        for &assertion in assertions {
            self.extract_length_bound_from_term(assertion, &mut bounds);
        }

        bounds
            .into_iter()
            .map(|(var, (lo, hi))| {
                let lower = lo.unwrap_or(0);
                let upper = hi.unwrap_or(usize::MAX);
                (var, (lower, upper))
            })
            .collect()
    }

    /// Compute known min/max length for a term given variable length bounds.
    ///
    /// For constants, returns exact length. For str.++ concatenations,
    /// recursively sums operand bounds. For variables with known bounds,
    /// returns (lower, upper). Returns `None` if any operand has no bounds.
    fn known_length_range(
        &self,
        term: TermId,
        var_bounds: &HashMap<TermId, (usize, usize)>,
        visiting: &mut HashSet<TermId>,
    ) -> Option<(usize, usize)> {
        if let Some(&bounds) = var_bounds.get(&term) {
            return Some(bounds);
        }

        if !visiting.insert(term) {
            return None;
        }

        let result = match self.ctx.terms.get(term) {
            TermData::Const(Constant::String(s)) => {
                let len = s.chars().count();
                Some((len, len))
            }
            TermData::App(Symbol::Named(name), args) if name == "str.++" => {
                let mut total_min = 0usize;
                let mut total_max = 0usize;
                for &arg in args {
                    let (lo, hi) = self.known_length_range(arg, var_bounds, visiting)?;
                    total_min = total_min.saturating_add(lo);
                    total_max = total_max.saturating_add(hi);
                }
                Some((total_min, total_max))
            }
            _ => None,
        };

        visiting.remove(&term);
        result
    }

    /// Detect direct string equalities whose exact lengths already contradict.
    ///
    /// This catches formulas like `(= (str.++ x y) "abc")` together with
    /// exact length facts `len(x)=2` and `len(y)=2`, which are UNSAT even
    /// before the string normal-form solver starts splitting.
    ///
    /// Also catches range-based contradictions where the minimum sum of
    /// operand lengths exceeds the target, or the maximum sum is less than
    /// the target (#7464).
    ///
    /// Uses unfiltered length bounds (no `MAX_PIVOT_BOUND` filter) so that
    /// contradictions involving variables with large bounds are still caught
    /// early.
    pub(super) fn has_exact_string_length_contradiction(&self, assertions: &[TermId]) -> bool {
        let exact_var_lengths = self.detect_exact_string_lengths(assertions);
        let all_bounds = self.detect_all_string_length_bounds(assertions);

        // Per-variable bound contradiction: a single variable whose derived
        // length lower bound exceeds its upper bound is unsatisfiable, e.g.
        // `len(s)=0 ∧ len(s)=1` → lower=1 > upper=0, or `len(x)=5 ∧ len(x)=3`
        // (#927). `str.len` is total and non-negative, so an empty feasible
        // length interval means no model exists.
        if all_bounds.values().any(|&(lower, upper)| lower > upper) {
            return true;
        }

        assertions.iter().copied().any(|assertion| {
            let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(assertion) else {
                return false;
            };
            if name != "=" || args.len() != 2 {
                return false;
            }
            if *self.ctx.terms.sort(args[0]) != Sort::String
                || *self.ctx.terms.sort(args[1]) != Sort::String
            {
                return false;
            }

            // Check 1: exact length contradiction (both sides fully determined)
            let mut visiting = HashSet::default();
            let exact_contradiction = matches!(
                (
                    self.known_exact_string_length(args[0], &exact_var_lengths, &mut visiting),
                    {
                        visiting.clear();
                        self.known_exact_string_length(args[1], &exact_var_lengths, &mut visiting)
                    },
                ),
                (Some(lhs), Some(rhs)) if lhs != rhs
            );
            if exact_contradiction {
                return true;
            }

            // Check 2: range-based contradiction. If [min_lhs, max_lhs] and
            // [min_rhs, max_rhs] don't overlap, the equality is impossible.
            visiting.clear();
            if let (Some((min_l, max_l)), Some((min_r, max_r))) = (
                self.known_length_range(args[0], &all_bounds, &mut visiting),
                {
                    visiting.clear();
                    self.known_length_range(args[1], &all_bounds, &mut visiting)
                },
            ) {
                // Ranges [min_l, max_l] and [min_r, max_r] must overlap.
                if min_l > max_r || min_r > max_l {
                    return true;
                }
            }

            false
        })
    }

    /// Detect a positively-asserted `str.contains(H, N)` (or
    /// `str.prefixof`/`str.suffixof`) that is structurally UNSATISFIABLE: the
    /// haystack `H` is a concrete constant while the needle `N` is a
    /// `str.++` whose constant leaves already make any substring match
    /// impossible. Returns `true` when such a contradiction is found.
    ///
    /// Only TOP-LEVEL conjuncts are considered (the formula unconditionally
    /// requires them), so descending through `and` is sound but `or`/`ite`/
    /// `not` are not. The refutation conditions mirror
    /// `concat_needle_refutes_contains` in the model-validation oracle and are
    /// SOUND under-approximations (free leaves contribute >= 0 chars of
    /// unknown content):
    ///
    /// * `contains(H, N)`: false if the sum of the constant-leaf lengths of
    ///   `N` exceeds `|H|`, or if any non-empty constant leaf of `N` is not a
    ///   substring of `H`.
    /// * `prefixof(P, H)` / `suffixof(P, H)`: false if `P`'s constant-leaf
    ///   length sum exceeds `|H|`. (A constant block of `P` must also occur in
    ///   `H`, but only the length bound is needed for the in-scope cases and
    ///   the model-validation oracle covers the content case as a backstop.)
    ///
    /// This yields a precise `unsat` for the concat-needle contains class,
    /// rather than the `unknown` produced by the model-validation fallback.
    pub(super) fn has_unsatisfiable_positive_concat_predicate(
        &self,
        assertions: &[TermId],
    ) -> bool {
        // Flatten top-level conjunctions: every conjunct of a top-level `and`
        // is also unconditionally required, so both the length-bound detection
        // and the predicate scan must see the inner `(= (str.len s2) 5)` /
        // `str.contains` conjuncts, not just the enclosing `and` node. Do NOT
        // descend through or/ite/not (those conjuncts are conditional).
        let mut conjuncts: Vec<TermId> = Vec::new();
        let mut stack: Vec<TermId> = assertions.to_vec();
        while let Some(term) = stack.pop() {
            match self.ctx.terms.get(term) {
                TermData::App(Symbol::Named(name), args) if name == "and" => {
                    stack.extend(args.iter().copied());
                }
                _ => conjuncts.push(term),
            }
        }

        // Length bounds (with free-variable lower bounds, e.g. `len(s2)=5`)
        // tighten the needle's minimum length beyond what its constant leaves
        // alone give, so `contains("b", s2++s1) ∧ len(s2)=5` is refuted.
        let all_bounds = self.detect_all_string_length_bounds(&conjuncts);

        for &term in &conjuncts {
            let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(term) else {
                continue;
            };
            if args.len() != 2 {
                continue;
            }
            let (haystack, needle, is_contains) = match name.as_str() {
                // contains(H, N): N must be a substring of H.
                "str.contains" => (args[0], args[1], true),
                // prefixof(P, H) / suffixof(P, H): P must fit within H.
                "str.prefixof" | "str.suffixof" => (args[1], args[0], false),
                _ => continue,
            };
            if self.concat_predicate_refuted(haystack, needle, is_contains, &all_bounds) {
                return true;
            }
        }
        false
    }

    /// Sound refutation helper for [`Self::has_unsatisfiable_positive_concat_predicate`].
    /// `haystack` must resolve to a concrete string constant; `needle`/pattern
    /// is decomposed into concat leaves whose constant blocks impose the
    /// necessary conditions described on the caller. `is_contains` selects the
    /// content check (only meaningful for `str.contains`). `var_bounds` carries
    /// detected per-variable length bounds so free leaves with a known lower
    /// bound (e.g. `len(s2)=5`) contribute to the minimum-length refutation.
    fn concat_predicate_refuted(
        &self,
        haystack: TermId,
        needle: TermId,
        is_contains: bool,
        var_bounds: &HashMap<TermId, (usize, usize)>,
    ) -> bool {
        // Haystack must be a fully concrete constant; otherwise it could be
        // arbitrarily long / contain anything and no refutation is sound.
        let empty = HashMap::default();
        let Some(haystack_val) = self.resolve_string_const(haystack, &empty) else {
            return false;
        };
        if *self.ctx.terms.sort(needle) != Sort::String {
            return false;
        }
        let haystack_len = haystack_val.chars().count();

        let mut leaves = Vec::new();
        Self::collect_concat_leaves(&self.ctx.terms, needle, &mut leaves);

        // Summarize the needle as FORCED constant blocks (maximal runs of
        // directly adjacent constant leaves) separated by free gaps. Each gap
        // carries a minimum length = sum of the free leaves' detected lower
        // length bounds (0 when unbounded). `gaps[i]` is the minimum number of
        // free chars before `blocks[i]`; `trailing_gap` is the minimum after
        // the last block. Adjacent constants are merged (they are contiguous in
        // the needle's value); a variable breaks the run (it may be non-empty),
        // so blocks separated by a variable are NOT merged. This is a SOUND
        // under-approximation: free leaves are arbitrary-content wildcards of
        // at-least their minimum length, so a refutation never rejects a
        // satisfiable model.
        let mut min_len = 0usize;
        let mut blocks: Vec<String> = Vec::new();
        let mut gaps: Vec<usize> = Vec::new();
        let mut cur_block = String::new();
        let mut pending_gap = 0usize;
        let mut have_const_leaf = false;
        for &leaf in &leaves {
            match self.ctx.terms.get(leaf) {
                TermData::Const(Constant::String(s)) => {
                    have_const_leaf = true;
                    min_len = min_len.saturating_add(s.chars().count());
                    cur_block.push_str(s);
                }
                _ => {
                    if !cur_block.is_empty() {
                        blocks.push(std::mem::take(&mut cur_block));
                        gaps.push(pending_gap);
                        pending_gap = 0;
                    }
                    let lower = var_bounds.get(&leaf).map(|&(lo, _)| lo).unwrap_or(0);
                    min_len = min_len.saturating_add(lower);
                    pending_gap = pending_gap.saturating_add(lower);
                }
            }
        }
        if !cur_block.is_empty() {
            blocks.push(cur_block);
            gaps.push(pending_gap);
            pending_gap = 0;
        }
        let trailing_gap = pending_gap;

        // Length refutation: forced minimum needle length exceeds haystack.
        if min_len > haystack_len {
            return true;
        }

        // Content + ordering refutation (contains only): the forced blocks must
        // be placeable in order, non-overlapping, inside the haystack with the
        // required gaps. When no placement exists, contains is impossible.
        // (For prefixof/suffixof, only the length bound is applied here; the
        // model-validation oracle covers the boundary-content case.)
        if is_contains && have_const_leaf && !blocks.is_empty() {
            return !Self::blocks_placeable(&haystack_val, &blocks, &gaps, trailing_gap);
        }
        false
    }

    /// Can the forced constant `blocks` be placed IN ORDER, non-overlapping,
    /// inside `haystack`, with at least `gaps[i]` free chars before `blocks[i]`
    /// and `trailing_gap` free chars after the last? Greedy leftmost placement
    /// (optimal for feasibility — placing each block as early as possible never
    /// forecloses placing the remaining blocks).
    fn blocks_placeable(
        haystack: &str,
        blocks: &[String],
        gaps: &[usize],
        trailing_gap: usize,
    ) -> bool {
        let hay: Vec<char> = haystack.chars().collect();
        let hlen = hay.len();
        let mut cursor = 0usize;
        for (i, block) in blocks.iter().enumerate() {
            let bchars: Vec<char> = block.chars().collect();
            let blen = bchars.len();
            let mut start = cursor.saturating_add(gaps[i]);
            loop {
                if start + blen > hlen {
                    return false;
                }
                if hay[start..start + blen] == bchars[..] {
                    break;
                }
                start += 1;
            }
            cursor = start + blen;
        }
        cursor + trailing_gap <= hlen
    }

    /// Collect witness concat terms introduced by preregistered decomposition clauses.
    ///
    /// Contains/prefix/suffix preregistration emits implication clauses whose
    /// conclusions are equalities like `x = str.++(sk_pre, y, sk_post)`. These
    /// concat terms are branch-local witnesses, not user-level word equations,
    /// so normal-form checking must ignore them the same way it ignores extf
    /// reduction concats.
    pub(super) fn collect_decomposition_concat_terms(&self, assertions: &[TermId]) -> Vec<TermId> {
        let mut reduced = Vec::new();
        let mut seen_terms = HashSet::default();
        let mut visited = HashSet::default();
        let mut stack: Vec<TermId> = assertions.to_vec();

        while let Some(term) = stack.pop() {
            if !visited.insert(term) {
                continue;
            }
            match self.ctx.terms.get(term) {
                TermData::App(Symbol::Named(name), args) if name == "=" && args.len() == 2 => {
                    for &side in args {
                        if matches!(self.ctx.terms.get(side), TermData::App(sym, _) if sym.name() == "str.++")
                            && seen_terms.insert(side)
                        {
                            reduced.push(side);
                        }
                    }
                    stack.extend(args.iter().copied());
                }
                TermData::App(_, args) => stack.extend(args.iter().copied()),
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(c, t, e) => {
                    stack.push(*c);
                    stack.push(*t);
                    stack.push(*e);
                }
                TermData::Let(bindings, body) => {
                    for (_, value) in bindings {
                        stack.push(*value);
                    }
                    stack.push(*body);
                }
                TermData::Const(_)
                | TermData::Var(_, _)
                | TermData::Forall(_, _, _)
                | TermData::Exists(_, _, _)
                | _ => {}
            }
        }

        reduced
    }

    /// Detect string variables with bounded lengths from assertion constraints.
    ///
    /// Looks for patterns like `(<= (* (str.len X) k) c)` and
    /// `(>= (* (str.len X) k) c)` in the assertion set and extracts
    /// integer bounds on variable lengths.
    pub(super) fn detect_bounded_string_vars(&self) -> Vec<LengthBound> {
        self.detect_bounded_string_vars_in(&self.ctx.assertions)
    }

    /// Detect string variables with bounded lengths from an explicit assertion set.
    pub(super) fn detect_bounded_string_vars_in(&self, assertions: &[TermId]) -> Vec<LengthBound> {
        // Map: variable TermId → (lower_bound, upper_bound)
        let mut bounds: HashMap<TermId, (Option<usize>, Option<usize>)> = HashMap::default();

        for &assertion in assertions {
            self.extract_length_bound_from_term(assertion, &mut bounds);
        }

        bounds
            .into_iter()
            .filter_map(|(var, (lo, hi))| {
                let lower = lo.unwrap_or(0);
                let upper = hi?;
                // An infeasible bound (lower > upper) is a genuine length
                // contradiction, e.g. `len(s)=0 ∧ len(s)=1` yields lower=1,
                // upper=0 (#927). This is NOT enumerable — there is no string
                // of length in an empty interval. Skip it here so we do not
                // panic or fabricate candidates; the contradiction is reported
                // separately by `has_exact_string_length_contradiction`, which
                // turns it into a sound UNSAT.
                if lower > upper {
                    return None;
                }
                if upper <= MAX_PIVOT_BOUND {
                    Some(LengthBound { var, lower, upper })
                } else {
                    None
                }
            })
            .collect()
    }

    /// Extract a length bound from a single assertion term.
    ///
    /// Recognizes patterns:
    /// - `(<= (* (str.len X) k) c)` → len(X) <= c/k
    /// - `(>= (* (str.len X) k) c)` → len(X) >= ceil(c/k)
    /// - `(<= (str.len X) c)` → len(X) <= c
    /// - `(>= (str.len X) c)` → len(X) >= c
    fn extract_length_bound_from_term(
        &self,
        term: TermId,
        bounds: &mut HashMap<TermId, (Option<usize>, Option<usize>)>,
    ) {
        let terms = &self.ctx.terms;
        match terms.get(term) {
            TermData::App(Symbol::Named(op), args) if args.len() == 2 => {
                let is_le = op == "<=";
                let is_ge = op == ">=";
                let is_eq = op == "=";
                if !is_le && !is_ge && !is_eq {
                    return;
                }
                // Try to extract (str.len var, coefficient, rhs_constant).
                // First with str.len on the left (`(<= (str.len x) c)`); if that
                // fails, with str.len on the RIGHT (`(<= c (str.len x))` or the
                // canonicalized `(>= c (str.len x))`), in which case the
                // inequality direction flips relative to the variable. For `=`
                // direction is irrelevant. This reversed handling fixes lost
                // lower bounds, e.g. `(>= (str.len x) 1)` canonicalized to
                // `(<= 1 (str.len x))` previously dropped the lower bound and
                // left the pivot/regex enumeration searching from length 0
                // (TARGET strings_regex_len T11).
                let mut effective_is_le = is_le;
                let mut effective_is_ge = is_ge;
                let parsed = Self::parse_scaled_strlen(terms, args[0], args[1]).or_else(|| {
                    let rev = Self::parse_scaled_strlen(terms, args[1], args[0]);
                    if rev.is_some() && !is_eq {
                        // Variable is on the RHS: `c <= len` means `len >= c`,
                        // `c >= len` means `len <= c`. Flip the direction.
                        std::mem::swap(&mut effective_is_le, &mut effective_is_ge);
                    }
                    rev
                });
                if let Some((var, coeff, rhs)) = parsed {
                    if coeff == 0 {
                        return;
                    }
                    let entry = bounds.entry(var).or_insert((None, None));
                    if is_eq {
                        // len(var) = rhs/coeff — sets both bounds (#7460).
                        let bound = rhs / coeff;
                        entry.0 = Some(entry.0.map_or(bound, |prev: usize| prev.max(bound)));
                        entry.1 = Some(entry.1.map_or(bound, |prev: usize| prev.min(bound)));
                    } else if effective_is_le {
                        // coeff * len(var) <= rhs → len(var) <= rhs / coeff
                        let bound = rhs / coeff;
                        entry.1 = Some(entry.1.map_or(bound, |prev: usize| prev.min(bound)));
                    } else if effective_is_ge {
                        // coeff * len(var) >= rhs → len(var) >= ceil(rhs / coeff)
                        let bound = rhs.div_ceil(coeff);
                        entry.0 = Some(entry.0.map_or(bound, |prev: usize| prev.max(bound)));
                    }
                }
            }
            _ => {}
        }
    }

    /// Parse a term that represents `k * str.len(var)` or just `str.len(var)`.
    /// Returns `(var, coefficient, rhs_constant)` if recognized.
    fn parse_scaled_strlen(
        terms: &ay_core::term::TermStore,
        lhs: TermId,
        rhs: TermId,
    ) -> Option<(TermId, usize, usize)> {
        // rhs must be an integer constant
        let rhs_val = match terms.get(rhs) {
            TermData::Const(Constant::Int(n)) => usize::try_from(n).ok()?,
            _ => return None,
        };
        // lhs is either str.len(var) or (* (str.len var) k) or (* k (str.len var))
        match terms.get(lhs) {
            TermData::App(Symbol::Named(name), args) if name == "str.len" && args.len() == 1 => {
                // Simple: str.len(var)
                let var = args[0];
                if matches!(terms.get(var), TermData::Var(..)) {
                    Some((var, 1, rhs_val))
                } else {
                    None
                }
            }
            TermData::App(Symbol::Named(name), args) if name == "*" && args.len() == 2 => {
                // Scaled: (* (str.len var) k) or (* k (str.len var))
                let (strlen_arg, coeff_arg) = if Self::is_strlen_of_var(terms, args[0]) {
                    (args[0], args[1])
                } else if Self::is_strlen_of_var(terms, args[1]) {
                    (args[1], args[0])
                } else {
                    return None;
                };
                let coeff = match terms.get(coeff_arg) {
                    TermData::Const(Constant::Int(n)) => usize::try_from(n).ok()?,
                    _ => return None,
                };
                // Extract var from str.len(var)
                match terms.get(strlen_arg) {
                    TermData::App(_, args) if !args.is_empty() => Some((args[0], coeff, rhs_val)),
                    _ => None,
                }
            }
            _ => None,
        }
    }

    /// Check if a term is `str.len(var)` where var is a string variable.
    fn is_strlen_of_var(terms: &ay_core::term::TermStore, term: TermId) -> bool {
        matches!(terms.get(term),
            TermData::App(Symbol::Named(name), args)
                if name == "str.len" && args.len() == 1
                    && matches!(terms.get(args[0]), TermData::Var(..)))
    }

    /// P2: witness candidates for string variables whose
    /// polarity-decoded constraints include NEGATIVE content facts — negated
    /// `str.contains(H[x], "c")` (haystack may be any composite over `x`,
    /// e.g. the pyex `replace(substr(uri,..),..) ++ substr(uri,..)` chain),
    /// negated equalities against string literals, plus length atoms. Such a
    /// variable usually has trivial models built from a character OUTSIDE the
    /// formula's constant alphabet (a fresh char cannot create a forbidden
    /// needle occurrence, and it collapses `indexof` chains to `-1` /
    /// `substr` windows to degenerate cases), but the unguided CEGAR loop
    /// stalls on them: the negative predicates latch the extf pass
    /// `incomplete` because nothing ever forces a concrete value (the pyex
    /// `¬contains(v, ",") ∧ len(v) ≠ 0 ∧ at(v, len-1) ≠ <ws>` idiom,
    /// Reynolds CAV'17 benchmarks).
    ///
    /// SOUNDNESS: candidates are only *guessed and validated* through
    /// [`Self::try_negative_only_model_guesses`] — every joint assignment is
    /// checked by the full model-validation battery before any SAT is
    /// trusted, and guess failure never concludes UNSAT. A wrong guess costs
    /// a few model evaluations and falls through to the normal pipeline, so
    /// this pass cannot flip any verdict; it only finds models that already
    /// exist. Eligibility is therefore a COST heuristic, not a soundness
    /// gate:
    ///   - at least one negatively-decoded content atom must mention the var
    ///     (targets the class; the pyex `(= (ite C 1 0) 0)` integer idiom is
    ///     decoded to recover C's real polarity);
    ///   - a var positively pinned to a literal (`x = "c"` decoded true) is
    ///     excluded from FRESH-char candidates (the joint search still
    ///     assigns it its harvested literals);
    ///   - vars under `str.in_re` are excluded (regex membership needs
    ///     specific content — owned by the S1 machinery).
    pub(super) fn detect_negative_only_witnesses(&self) -> Vec<PrefixSuffixWitness> {
        const VAR_CAP: usize = 4;

        let is_str_var = |t: TermId| -> bool {
            matches!(self.ctx.terms.get(t), TermData::Var(..))
                && *self.ctx.terms.sort(t) == Sort::String
        };
        let str_const = |t: TermId| -> Option<String> {
            match self.ctx.terms.get(t) {
                TermData::Const(Constant::String(s)) => Some(s.clone()),
                _ => None,
            }
        };

        // Collect all string vars in a subtree.
        let collect_vars = |root: TermId, out: &mut HashSet<TermId>| {
            let mut stack = vec![root];
            let mut visited: HashSet<TermId> = HashSet::default();
            while let Some(t) = stack.pop() {
                if !visited.insert(t) {
                    continue;
                }
                match self.ctx.terms.get(t) {
                    TermData::Var(..) if *self.ctx.terms.sort(t) == Sort::String => {
                        out.insert(t);
                    }
                    TermData::App(_, args) => stack.extend(args.iter().copied()),
                    TermData::Not(i) => stack.push(*i),
                    TermData::Ite(c, a, b) => {
                        stack.push(*c);
                        stack.push(*a);
                        stack.push(*b);
                    }
                    _ => {}
                }
            }
        };

        let mut disqualified: HashSet<TermId> = HashSet::default();
        let mut saw_negative: HashSet<TermId> = HashSet::default();
        let mut all_vars: HashSet<TermId> = HashSet::default();

        // ---- Phase A: census. Only `str.in_re` is a hard context
        // disqualifier (regex membership needs specific content); everything
        // else — concats, indexof/replace/substr chains — is fine: a fresh
        // char merely collapses those chains, and validation decides.
        {
            let mut stack: Vec<TermId> = self.ctx.assertions.clone();
            let mut visited: HashSet<TermId> = HashSet::default();
            while let Some(t) = stack.pop() {
                if !visited.insert(t) {
                    continue;
                }
                match self.ctx.terms.get(t) {
                    TermData::Var(..) if *self.ctx.terms.sort(t) == Sort::String => {
                        all_vars.insert(t);
                    }
                    TermData::App(Symbol::Named(name), args) => {
                        if name == "str.in_re" {
                            for &a in args {
                                collect_vars(a, &mut disqualified);
                            }
                        }
                        stack.extend(args.iter().copied());
                    }
                    TermData::Not(i) => stack.push(*i),
                    TermData::Ite(c, a, b) => {
                        stack.push(*c);
                        stack.push(*a);
                        stack.push(*b);
                    }
                    TermData::Let(bindings, body) => {
                        for (_, v) in bindings {
                            stack.push(*v);
                        }
                        stack.push(*body);
                    }
                    _ => {}
                }
            }
        }

        // Decode the pyex integer idiom `(= (ite C a b) k)` (a, b, k int
        // literals): returns `(C, same_polarity)` — `same_polarity=true` when
        // the atom being TRUE forces C true.
        let decode_ite_int_eq = |a: TermId, b: TermId| -> Option<(TermId, bool)> {
            let int_const = |t: TermId| match self.ctx.terms.get(t) {
                TermData::Const(Constant::Int(k)) => Some(k.clone()),
                _ => None,
            };
            for (ite_side, k_side) in [(a, b), (b, a)] {
                let Some(k) = int_const(k_side) else { continue };
                if let TermData::Ite(c, tv, ev) = self.ctx.terms.get(ite_side) {
                    let (Some(tvc), Some(evc)) = (int_const(*tv), int_const(*ev)) else {
                        continue;
                    };
                    if tvc == k && evc != k {
                        return Some((*c, true));
                    }
                    if evc == k && tvc != k {
                        return Some((*c, false));
                    }
                }
            }
            None
        };

        // ---- Phase B: polarity-tracked atom classification.
        {
            let mut stack: Vec<(TermId, bool)> =
                self.ctx.assertions.iter().map(|&t| (t, true)).collect();
            let mut visited: HashSet<(TermId, bool)> = HashSet::default();
            while let Some((t, pol)) = stack.pop() {
                if !visited.insert((t, pol)) {
                    continue;
                }
                match self.ctx.terms.get(t).clone() {
                    TermData::Not(i) => stack.push((i, !pol)),
                    TermData::Ite(c, a, b) => {
                        stack.push((c, true));
                        stack.push((c, false));
                        stack.push((a, pol));
                        stack.push((b, pol));
                    }
                    TermData::App(Symbol::Named(name), args) if name == "and" || name == "or" => {
                        for &a in &args {
                            stack.push((a, pol));
                        }
                    }
                    TermData::App(Symbol::Named(name), args) if name == "=>" && args.len() == 2 => {
                        stack.push((args[0], !pol));
                        stack.push((args[1], pol));
                    }
                    TermData::App(Symbol::Named(name), args) if name == "=" && args.len() == 2 => {
                        // pyex idiom decode first: recover C's real polarity.
                        if let Some((c, same)) = decode_ite_int_eq(args[0], args[1]) {
                            stack.push((c, if same { pol } else { !pol }));
                            continue;
                        }
                        let s0 = self.ctx.terms.sort(args[0]).clone();
                        if s0 == Sort::Bool {
                            // Boolean equality: children polarity-ambiguous.
                            for &a in &args {
                                stack.push((a, true));
                                stack.push((a, false));
                            }
                        } else if s0 == Sort::String {
                            for (lhs, rhs) in [(args[0], args[1]), (args[1], args[0])] {
                                let Some(_c) = str_const(rhs) else { continue };
                                if pol {
                                    // Positively pinned literal on a BARE var:
                                    // fresh-char candidates would fight it (the
                                    // joint search assigns its harvested
                                    // literals instead).
                                    if is_str_var(lhs) {
                                        disqualified.insert(lhs);
                                    }
                                } else {
                                    // Negated equality against a literal:
                                    // every var inside the other side gains a
                                    // negative content atom.
                                    collect_vars(lhs, &mut saw_negative);
                                }
                            }
                        }
                        // Int equality (non-idiom): len atoms are neutral.
                    }
                    TermData::App(Symbol::Named(name), args)
                        if name == "str.contains" && args.len() == 2 =>
                    {
                        let (h, n) = (args[0], args[1]);
                        if !pol {
                            if let Some(c) = str_const(n) {
                                if !c.is_empty() {
                                    // Negated contains with a literal needle:
                                    // haystack may be ANY composite over the
                                    // vars (pyex mongoclient chains).
                                    collect_vars(h, &mut saw_negative);
                                }
                            }
                        }
                    }
                    _ => {}
                }
            }
        }

        // Fresh witness character: outside the formula's constant alphabet, a
        // fresh char can never create a forbidden needle occurrence.
        let alphabet: HashSet<char> = self.collect_alphabet().into_iter().collect();
        let fresh: Option<char> = ('a'..='z')
            .chain('A'..='Z')
            .chain('0'..='9')
            .find(|c| !alphabet.contains(c));
        let Some(c) = fresh else {
            return Vec::new();
        };

        let mut eligible: Vec<TermId> = all_vars
            .into_iter()
            .filter(|v| saw_negative.contains(v) && !disqualified.contains(v))
            .collect();
        // Deterministic order (hash-set iteration order is already
        // deterministic via DetHashSet, but sort for stability anyway).
        eligible.sort_unstable_by_key(|t| t.0);
        eligible.truncate(VAR_CAP);

        eligible
            .into_iter()
            .map(|var| PrefixSuffixWitness {
                var,
                candidates: vec![
                    c.to_string(),
                    String::new(),
                    std::iter::repeat_n(c, 2).collect(),
                    std::iter::repeat_n(c, 3).collect(),
                ],
            })
            .collect()
    }

    pub(super) fn collect_alphabet(&self) -> Vec<char> {
        let mut chars = HashSet::default();
        let mut stack: Vec<TermId> = self.ctx.assertions.clone();
        let mut visited = HashSet::default();
        while let Some(tid) = stack.pop() {
            if !visited.insert(tid) {
                continue;
            }
            match self.ctx.terms.get(tid) {
                TermData::Const(Constant::String(s)) => {
                    chars.extend(s.chars());
                }
                TermData::App(_, args) => stack.extend(args.iter().copied()),
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(c, t, e) => {
                    stack.push(*c);
                    stack.push(*t);
                    stack.push(*e);
                }
                _ => {}
            }
        }
        let mut result: Vec<char> = chars.into_iter().collect();
        result.sort_unstable();
        result
    }

    /// Generate all candidate strings of a given length from an alphabet.
    ///
    /// Returns `(candidates, exhaustive)`. `exhaustive` is `true` only when the
    /// returned vector contains *every* string over `alphabet` with length in
    /// `[lower, upper]` — i.e. the enumeration was not cut short by the
    /// [`MAX_PIVOT_CANDIDATES`] cap. This flag is **soundness-critical**: the
    /// pivot-enumeration caller may only conclude UNSAT from "every candidate is
    /// UNSAT" when the candidate set is exhaustive over the search space.
    /// Truncated enumerations skip values (#927: the satisfying witness can be
    /// past the cap), so they must never drive an UNSAT verdict.
    pub(super) fn generate_candidates(
        alphabet: &[char],
        lower: usize,
        upper: usize,
    ) -> (Vec<String>, bool) {
        let mut candidates = Vec::new();
        for len in lower..=upper {
            if len == 0 {
                candidates.push(String::new());
                continue;
            }
            // Generate all strings of exactly `len` characters from alphabet
            let mut indices = vec![0usize; len];
            loop {
                let s: String = indices.iter().map(|&i| alphabet[i]).collect();
                candidates.push(s);
                if candidates.len() >= MAX_PIVOT_CANDIDATES {
                    // Hit the cap: the space may still have unenumerated
                    // values, so the result is NOT exhaustive.
                    return (candidates, false);
                }
                // Increment indices (odometer-style)
                let mut pos = len - 1;
                loop {
                    indices[pos] += 1;
                    if indices[pos] < alphabet.len() {
                        break;
                    }
                    indices[pos] = 0;
                    if pos == 0 {
                        // Done with this length
                        break;
                    }
                    pos -= 1;
                }
                if pos == 0 && indices[0] == 0 {
                    break; // All strings of this length generated
                }
            }
        }
        debug_assert!(
            candidates.iter().all(|s| {
                let len = s.chars().count();
                len >= lower && len <= upper
            }),
            "BUG: generate_candidates produced string with length outside [{lower}, {upper}]"
        );
        // Reaching here means the loop ran to completion for every length
        // without tripping the cap: the enumeration is exhaustive.
        (candidates, true)
    }
}
