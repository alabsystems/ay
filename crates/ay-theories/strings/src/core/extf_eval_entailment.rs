// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Structural entailment for string containment, prefix, and suffix predicates.
//!
//! These methods use EQC structure (concat terms, empty string checks, length
//! comparisons) to determine truth values without full constant resolution.
//! Extracted from extf_eval.rs as part of #5970 code-health splits.
//!
//! CVC5 reference: sequences_rewriter.cpp rewriteContains

use super::*;

impl CoreSolver {
    /// Evaluate `str.contains(haystack, needle)` with structural entailment.
    ///
    /// CVC5 reference: sequences_rewriter.cpp rewriteContains
    pub(super) fn eval_contains(
        terms: &TermStore,
        state: &SolverState,
        haystack: TermId,
        needle: TermId,
    ) -> Option<bool> {
        // Reflexive: x contains x.
        if state.find(haystack) == state.find(needle) {
            return Some(true);
        }
        // Everything contains "".
        if state.is_empty_string(terms, needle) {
            return Some(true);
        }
        // CTN_LHS_EMPTYSTR: str.contains("", x) ↔ x = "".
        if state.is_empty_string(terms, haystack) {
            if state.is_empty_string(terms, needle) {
                return Some(true);
            }
            if Self::has_positive_min_length(terms, state, needle) {
                return Some(false);
            }
            // Unknown whether needle is empty.
            return None;
        }
        // CTN_LEN_INEQ: needle strictly longer than haystack → false.
        if Self::needle_strictly_longer(terms, state, haystack, needle) {
            return Some(false);
        }
        // CTN_LEN_INEQ_NSTRICT: needle reduces to haystack after empty removal.
        if Self::needle_reduces_to_haystack(terms, state, haystack, needle) {
            return Some(true);
        }
        // Structural: constant needle found in a constant concat component.
        if let Some(needle_str) = Self::resolve_string_term(terms, state, needle, 0) {
            if Self::concat_contains_constant(terms, state, haystack, &needle_str) {
                return Some(true);
            }
            // CTN_COMPONENT: check haystack's EQC concat terms.
            //
            // When the haystack is a variable y with y = str.++(x, "world"),
            // the syntactic check above misses it because y itself is not
            // a concat. Check the EQC's concat terms directly.
            //
            // Safety: this only returns Some(true), never Some(false).
            // For positive contains assertions, this is sound because the
            // EQC concat equation provides a structural witness. For negative
            // assertions, the caller detects actual != expected as a conflict
            // with proper explanation.
            //
            // CVC5 reference: sequences_rewriter.cpp:2925 CTN_COMPONENT
            let haystack_rep = state.find(haystack);
            if let Some(eqc) = state.get_eqc(&haystack_rep) {
                if *DEBUG_STRING_CORE {
                    eprintln!(
                        "[STRING_CORE] CTN_COMPONENT: haystack={:?} rep={:?} needle=\"{}\" concat_terms={:?}",
                        haystack, haystack_rep, needle_str, eqc.concat_terms
                    );
                }
                for &ct in &eqc.concat_terms {
                    if Self::concat_contains_constant(terms, state, ct, &needle_str) {
                        if *DEBUG_STRING_CORE {
                            eprintln!(
                                "[STRING_CORE] CTN_COMPONENT: found needle in concat term {ct:?}"
                            );
                        }
                        return Some(true);
                    }
                }
            }
        }
        // Full resolution: both args resolve to constants.
        let h = Self::resolve_string_term(terms, state, haystack, 0)?;
        let n = Self::resolve_string_term(terms, state, needle, 0)?;
        Some(h.contains(n.as_str()))
    }

    /// Evaluate `str.prefixof(prefix, s)`.
    pub(super) fn eval_prefixof(
        terms: &TermStore,
        state: &SolverState,
        prefix: TermId,
        s: TermId,
    ) -> Option<bool> {
        if state.find(prefix) == state.find(s) {
            return Some(true);
        }
        if state.is_empty_string(terms, prefix) {
            return Some(true);
        }
        // EQC component check: if s's EQC has a concat starting
        // with a component in the same EQC as prefix, return true.
        let prefix_rep = state.find(prefix);
        let s_rep = state.find(s);
        if let Some(eqc) = state.get_eqc(&s_rep) {
            for &ct in &eqc.concat_terms {
                if let Some(children) = state.get_concat_children(terms, ct) {
                    for &child in children {
                        if state.is_empty_string(terms, child) {
                            continue;
                        }
                        if state.find(child) == prefix_rep {
                            return Some(true);
                        }
                        break;
                    }
                }
            }
        }
        let prefix_str = Self::resolve_string_term(terms, state, prefix, 0)?;
        let s_str = Self::resolve_string_term(terms, state, s, 0)?;
        Some(s_str.starts_with(prefix_str.as_str()))
    }

    /// Evaluate str.suffixof(suffix, s).
    pub(super) fn eval_suffixof(
        terms: &TermStore,
        state: &SolverState,
        suffix: TermId,
        s: TermId,
    ) -> Option<bool> {
        if state.find(suffix) == state.find(s) {
            return Some(true);
        }
        if state.is_empty_string(terms, suffix) {
            return Some(true);
        }
        // EQC component check: if s's EQC has a concat ending
        // with a component in the same EQC as suffix, return true.
        let suffix_rep = state.find(suffix);
        let s_rep = state.find(s);
        if let Some(eqc) = state.get_eqc(&s_rep) {
            for &ct in &eqc.concat_terms {
                if let Some(children) = state.get_concat_children(terms, ct) {
                    for &child in children.iter().rev() {
                        if state.is_empty_string(terms, child) {
                            continue;
                        }
                        if state.find(child) == suffix_rep {
                            return Some(true);
                        }
                        break;
                    }
                }
            }
        }
        let suffix_str = Self::resolve_string_term(terms, state, suffix, 0)?;
        let s_str = Self::resolve_string_term(terms, state, s, 0)?;
        Some(s_str.ends_with(suffix_str.as_str()))
    }
}
