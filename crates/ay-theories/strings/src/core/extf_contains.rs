// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Contains-related helpers, concat structural analysis, integer term resolution,
//! and regex replace evaluation.
//!
//! Extracted from `extf_eval.rs` as part of code-health module split.
//! The primary evaluation and resolution methods remain in `extf_eval.rs`.

use super::*;

impl CoreSolver {
    /// Check if a concat term structurally contains a constant substring.
    ///
    /// Walks the concat structure of `haystack` looking for any constant
    /// component (or adjacent constants) that contain `needle`. Returns true
    /// if the needle is found without requiring the full haystack to be ground.
    ///
    /// This enables `str.contains(str.++(x, "world"), "world")` to evaluate
    /// to true even when `x` is unresolved.
    pub(super) fn concat_contains_constant(
        terms: &TermStore,
        state: &SolverState,
        haystack: TermId,
        needle: &str,
    ) -> bool {
        if needle.is_empty() {
            return true;
        }
        // Collect the concat components (flattening nested concats).
        let mut components = Vec::new();
        Self::flatten_concat(terms, state, haystack, &mut components);

        // Check individual constant components.
        for comp in &components {
            if let Some(s) = Self::resolve_string_term(terms, state, *comp, 0) {
                if s.contains(needle) {
                    return true;
                }
            }
        }

        // Check adjacent constant pairs (needle may span two components).
        for window in components.windows(2) {
            if let (Some(a), Some(b)) = (
                Self::resolve_string_term(terms, state, window[0], 0),
                Self::resolve_string_term(terms, state, window[1], 0),
            ) {
                let combined = format!("{a}{b}");
                if combined.contains(needle) {
                    return true;
                }
            }
        }

        false
    }

    /// #ssl-residue C: prove `str.contains(haystack, needle)` TRUE independent
    /// of skolem content. Applies when the needle resolves to a non-empty
    /// constant `w` and a concat equal to the haystack (the haystack itself or
    /// a concat term in its EQC) has ONE component with a constant value `C`
    /// such that `w` is a substring of `C`: `contains(a ++ C ++ b, w)` holds
    /// for ALL `a`, `b`, so the entailment never depends on skolem values.
    /// Needles spanning component boundaries are deliberately NOT handled
    /// (skolem-dependent — they stay fail-closed).
    ///
    /// Returns the extra explanation literals justifying the entailment
    /// (haystack ≃ concat, component ≃ constant, needle ≃ constant — all EQC
    /// merges voiced via `state.explain`), or `None` when not entailed or when
    /// any required justification cannot be voiced (fail-closed).
    pub(super) fn contains_segment_entailment(
        terms: &TermStore,
        state: &SolverState,
        atom: TermId,
    ) -> Option<Vec<TheoryLit>> {
        let TermData::App(sym, args) = terms.get(atom) else {
            return None;
        };
        if sym.name() != "str.contains" || args.len() != 2 {
            return None;
        }
        let (haystack, needle) = (args[0], args[1]);

        // Needle constant: syntactic, or an explainable EQC constant term.
        let (needle_expl_id, needle_str) = match terms.get(needle) {
            TermData::Const(Constant::String(s)) => (None, s.clone()),
            _ => {
                let cid = state.find_constant_term_id(terms, needle)?;
                let TermData::Const(Constant::String(s)) = terms.get(cid) else {
                    return None;
                };
                (Some(cid), s.clone())
            }
        };
        if needle_str.is_empty() {
            // Trivially true for every haystack; leave to the normal paths.
            return None;
        }

        // Candidate concats: the haystack itself plus its EQC concat terms.
        let mut candidates: Vec<TermId> = vec![haystack];
        let haystack_rep = state.find(haystack);
        if let Some(eqc) = state.get_eqc(&haystack_rep) {
            candidates.extend(eqc.concat_terms.iter().copied());
        }

        for ct in candidates {
            let mut components = Vec::new();
            Self::flatten_concat(terms, state, ct, &mut components);
            for &comp in &components {
                // Constant value of this SINGLE component: syntactic, or an
                // explainable EQC constant term (fail-closed otherwise).
                let (comp_expl_id, comp_val) = match terms.get(comp) {
                    TermData::Const(Constant::String(s)) => (None, s.clone()),
                    _ => {
                        let Some(cid) = state.find_constant_term_id(terms, comp) else {
                            continue;
                        };
                        let TermData::Const(Constant::String(s)) = terms.get(cid) else {
                            continue;
                        };
                        (Some(cid), s.clone())
                    }
                };
                if !comp_val.contains(needle_str.as_str()) {
                    continue;
                }
                // Entailed. Voice every EQC merge the argument relies on.
                let mut extra: Vec<TheoryLit> = Vec::new();
                if ct != haystack {
                    extra.extend(state.explain(haystack, ct));
                }
                if let Some(cid) = comp_expl_id {
                    if cid != comp {
                        extra.extend(state.explain(comp, cid));
                    }
                }
                if let Some(nid) = needle_expl_id {
                    if nid != needle {
                        extra.extend(state.explain(needle, nid));
                    }
                }
                return Some(extra);
            }
        }
        None
    }

    /// Flatten a concat term into its leaf components (syntactic only).
    ///
    /// Only walks the syntactic `str.++` structure of the term itself.
    /// Does NOT follow EQC representatives or members — doing so is unsound
    /// because EQC members may include Skolem decomposition terms that
    /// circularly assume the predicate being evaluated (e.g., the contains
    /// Skolem `x = str.++(sk, needle, sk2)` would always make
    /// `concat_contains_constant` return true, masking real contradictions
    /// like `x = "goodbye"` ∧ `str.contains(x, "hello")`).
    pub(super) fn flatten_concat(
        terms: &TermStore,
        _state: &SolverState,
        t: TermId,
        out: &mut Vec<TermId>,
    ) {
        if let TermData::App(sym, args) = terms.get(t) {
            if sym.name() == "str.++" {
                for &arg in args {
                    Self::flatten_concat(terms, _state, arg, out);
                }
                return;
            }
        }
        out.push(t);
    }

    /// Check whether the needle's minimum length strictly exceeds the
    /// haystack's maximum length, using structural analysis of concat
    /// components. Returns true when `str.contains(haystack, needle)` must
    /// be false due to length.
    ///
    /// Handles patterns like `str.contains(x, str.++(x, y))` when `y` is
    /// provably non-empty: the needle includes `x` plus extra, so its
    /// length exceeds `len(x)`.
    ///
    /// CVC5 reference: sequences_rewriter.cpp:2986 CTN_LEN_INEQ
    pub(super) fn needle_strictly_longer(
        terms: &TermStore,
        state: &SolverState,
        haystack: TermId,
        needle: TermId,
    ) -> bool {
        let mut components = Vec::new();
        Self::flatten_concat(terms, state, needle, &mut components);
        if components.len() < 2 {
            return false;
        }

        let haystack_rep = state.find(haystack);

        // Check if any component of the needle is in the same EQC as haystack.
        // If so, the remaining components represent "extra" length that must be
        // accounted for. If any remaining component has provably positive min
        // length, the needle is strictly longer.
        let mut found_haystack = false;
        let mut has_positive_extra = false;
        for &comp in &components {
            let comp_rep = state.find(comp);
            if comp_rep == haystack_rep && !found_haystack {
                found_haystack = true;
                continue;
            }
            // Check if this "extra" component has provably positive min length.
            if Self::has_positive_min_length(terms, state, comp) {
                has_positive_extra = true;
            }
        }

        found_haystack && has_positive_extra
    }

    /// Check whether the needle's concat components, after removing
    /// empty-EQC components, reduce to a single term in the same EQC as
    /// the haystack.
    ///
    /// For example: `str.contains(x, str.++(x, y))` with `y` in the
    /// empty-EQC → needle reduces to `x` → true (reflexive containment).
    pub(super) fn needle_reduces_to_haystack(
        terms: &TermStore,
        state: &SolverState,
        haystack: TermId,
        needle: TermId,
    ) -> bool {
        let mut components = Vec::new();
        Self::flatten_concat(terms, state, needle, &mut components);
        if components.len() < 2 {
            return false;
        }

        let haystack_rep = state.find(haystack);

        // Filter out empty-EQC components.
        let non_empty: Vec<_> = components
            .iter()
            .filter(|&&c| !state.is_empty_string(terms, c))
            .collect();

        // After removing empty components, the needle should reduce to
        // a single term in the same EQC as haystack.
        non_empty.len() == 1 && state.find(*non_empty[0]) == haystack_rep
    }

    /// Whether a string term has a provably positive minimum length.
    ///
    /// Returns true if the term is a known non-empty constant, or is in an
    /// EQC with a non-empty constant. Variables with unknown value return
    /// false (they might be "").
    pub(super) fn has_positive_min_length(
        terms: &TermStore,
        state: &SolverState,
        t: TermId,
    ) -> bool {
        // Check EQC constant.
        let rep = state.find(t);
        if let Some(info) = state.get_eqc(&rep) {
            if let Some(c) = info.constant.as_deref() {
                return !c.is_empty();
            }
        }
        // Check syntactic constant.
        if let TermData::Const(Constant::String(s)) = terms.get(t) {
            return !s.is_empty();
        }
        // Concat: all components must have positive min length for the whole
        // to have positive min length — but even one component with positive
        // min length suffices to contribute positive extra in the caller.
        // Here we just need any positive contribution.
        if let TermData::App(sym, args) = terms.get(t) {
            if sym.name() == "str.++" {
                return args
                    .iter()
                    .any(|&a| Self::has_positive_min_length(terms, state, a));
            }
        }
        false
    }

    /// For a positive `str.contains(haystack, needle)` where the needle is
    /// a concat that includes the haystack as a component, infer that all
    /// extra components must equal the empty string.
    ///
    /// `str.contains(x, str.++(x, y))` is true → `len(x) >= len(x) + len(y)`
    /// → `len(y) = 0` → `y = ""`. Emits `y = ""` as an internal equality.
    ///
    /// CVC5 reference: strings_entail.cpp:945 inferEqsFromContains
    pub(super) fn infer_eqs_from_contains(
        terms: &TermStore,
        state: &SolverState,
        atom: TermId,
        contains_lit: TheoryLit,
        infer: &mut InferenceManager,
    ) {
        let TermData::App(sym, args) = terms.get(atom) else {
            return;
        };
        if sym.name() != "str.contains" || args.len() != 2 {
            return;
        }
        let Some(empty_id) = state.empty_string_id() else {
            return;
        };

        let haystack = args[0];
        let needle = args[1];
        let haystack_rep = state.find(haystack);

        let mut components = Vec::new();
        Self::flatten_concat(terms, state, needle, &mut components);
        if components.len() < 2 {
            return;
        }

        // Check if any component is in the same EQC as haystack.
        let mut found_haystack = false;
        let mut haystack_comp = None;
        let mut extra = Vec::new();
        for &comp in &components {
            if state.find(comp) == haystack_rep && !found_haystack {
                found_haystack = true;
                haystack_comp = Some(comp);
            } else {
                extra.push(comp);
            }
        }

        if !found_haystack || extra.is_empty() {
            return;
        }

        // Explain: the contains assertion + why the component equals haystack.
        let mut explanation = vec![contains_lit];
        if let Some(hc) = haystack_comp {
            if hc != haystack {
                explanation.extend(state.explain(hc, haystack));
            }
        }
        for comp in extra {
            if !state.is_empty_string(terms, comp) {
                infer.add_internal_equality(
                    InferenceKind::EndpointEq,
                    comp,
                    empty_id,
                    explanation.clone(),
                );
            }
        }
    }

    /// CTN_LHS_EMPTYSTR: for positive str.contains("", x), infer x = "".
    ///
    /// The empty string only contains the empty string, so
    /// `str.contains("", x)` being true forces `x = ""`.
    /// CVC5 handles this in strings_entail.cpp and via reduction lemmas.
    pub(super) fn infer_contains_empty_haystack(
        terms: &TermStore,
        state: &SolverState,
        atom: TermId,
        contains_lit: TheoryLit,
        infer: &mut InferenceManager,
    ) {
        let TermData::App(sym, args) = terms.get(atom) else {
            return;
        };
        if sym.name() != "str.contains" || args.len() != 2 {
            return;
        }
        let Some(empty_id) = state.empty_string_id() else {
            return;
        };

        let haystack = args[0];
        let needle = args[1];

        // Only applies when haystack is known to be "".
        if !state.is_empty_string(terms, haystack) {
            return;
        }
        // If needle is already known empty, nothing to infer.
        if state.is_empty_string(terms, needle) {
            return;
        }

        // Explain: the contains assertion + why haystack is "".
        let mut explanation = vec![contains_lit];
        if haystack != empty_id && state.find(haystack) == state.find(empty_id) {
            explanation.extend(state.explain(haystack, empty_id));
        }
        infer.add_internal_equality(InferenceKind::EndpointEq, needle, empty_id, explanation);
    }

    /// Resolve an integer term to a concrete BigInt when possible.
    ///
    /// Resolution order:
    /// 1. Syntactic integer constant
    /// 2. `str.indexof(s, t, i)` with resolved arguments
    /// 3. `str.len(s)` with resolved string argument
    /// 4. `str.to_int(s)` with resolved string argument
    pub(super) fn resolve_int_term(
        terms: &TermStore,
        state: &SolverState,
        t: TermId,
        depth: usize,
    ) -> Option<BigInt> {
        if depth > Self::MAX_RESOLVE_DEPTH {
            return None;
        }

        let rep = state.find(t);
        // Check via EQC representative first, then direct term.
        if let TermData::Const(Constant::Int(n)) = terms.get(rep) {
            return Some(n.clone());
        }
        match terms.get(t) {
            TermData::Const(Constant::Int(n)) => Some(n.clone()),
            TermData::App(sym, args) => match sym.name() {
                "str.indexof" if args.len() == 3 => {
                    let s = Self::resolve_string_term(terms, state, args[0], depth + 1)?;
                    let pat = Self::resolve_string_term(terms, state, args[1], depth + 1)?;
                    let start = Self::resolve_int_term(terms, state, args[2], depth + 1)?;
                    crate::eval::eval_str_indexof(&s, &pat, &start)
                }
                "str.len" if args.len() == 1 => {
                    let s = Self::resolve_string_term(terms, state, args[0], depth + 1)?;
                    Some(BigInt::from(s.chars().count()))
                }
                "str.to_int" | "str.to.int" if args.len() == 1 => {
                    let s = Self::resolve_string_term(terms, state, args[0], depth + 1)?;
                    Some(crate::eval::eval_str_to_int(&s))
                }
                "str.to_code" if args.len() == 1 => {
                    let s = Self::resolve_string_term(terms, state, args[0], depth + 1)?;
                    Some(crate::eval::eval_str_to_code(&s))
                }
                _ => None,
            },
            _ => None,
        }
    }

    /// Evaluate `str.replace_re(s, r, t)`: replace first regex match in s with t.
    ///
    /// If no match, returns s unchanged.
    pub(super) fn eval_str_replace_re(
        terms: &TermStore,
        s: &str,
        r: TermId,
        t: &str,
    ) -> Option<String> {
        match RegExpSolver::find_first_match(terms, s, r) {
            MatchResult::Found(start, end) => {
                let mut result = s[..start].to_string();
                result.push_str(t);
                result.push_str(&s[end..]);
                Some(result)
            }
            MatchResult::NoMatch => Some(s.to_string()),
            MatchResult::Incomplete => None,
        }
    }

    /// Evaluate `str.replace_re_all(s, r, t)`: replace all regex matches in s with t.
    ///
    /// SMT-LIB 2.6 semantics: each replaced match must be NON-EMPTY (the
    /// theory's recursive clause carries the `w != ""` side condition), so a
    /// nullable regex still replaces its shortest non-empty matches. This
    /// delegates to the single crate-level implementation
    /// (`crate::ground_eval_replace_re_all`) so the two entry points cannot
    /// drift apart again.
    pub(super) fn eval_str_replace_re_all(
        terms: &TermStore,
        s: &str,
        r: TermId,
        t: &str,
    ) -> Option<String> {
        crate::ground_eval_replace_re_all(terms, s, r, t)
    }
}
