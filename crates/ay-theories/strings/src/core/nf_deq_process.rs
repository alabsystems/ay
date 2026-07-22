// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! NF disequality processing: component-wise deq walk and DISL case analysis.
//!
//! Contains `process_simple_deq` (CVC5 processSimpleDeq) and `process_deq_disl`
//! (CVC5 processDeq fallback). Called from `check_normal_forms_deq` in
//! `nf_disequality.rs`.
//!
//! Extracted from nf_disequality.rs as part of #5970 code-health splits.

use super::*;

impl CoreSolver {
    /// Disequality-oriented component comparison (CVC5 processSimpleDeq style).
    ///
    /// This is intentionally narrower than `process_simple_neq`:
    /// - no N_UNIFY/internal equalities,
    /// - no ConstSplit/VarSplit synthesis in the deq path.
    ///
    /// It performs a reverse suffix trim, then scans left-to-right. If it cannot
    /// certify the disequality directly, it may request a guarded `LengthSplit`
    /// on reduced components (when both sides have length metadata).
    pub(super) fn process_simple_deq(
        terms: &TermStore,
        state: &SolverState,
        nf1: &NormalForm,
        nf2: &NormalForm,
        diseq_lit: TheoryLit,
        _skolems: &mut SkolemCache,
    ) -> NfCheckResult {
        // Reverse reduction: strip matching suffix components first.
        let mut rproc = 0usize;
        while rproc < nf1.base.len() && rproc < nf2.base.len() {
            let i1 = nf1.base.len() - 1 - rproc;
            let i2 = nf2.base.len() - 1 - rproc;
            if state.find(nf1.base[i1]) == state.find(nf2.base[i2]) {
                rproc += 1;
            } else {
                break;
            }
        }

        let len1 = nf1.base.len().saturating_sub(rproc);
        let len2 = nf2.base.len().saturating_sub(rproc);

        let mut i = 0usize;
        let mut j = 0usize;
        let mut off1 = 0usize;
        let mut off2 = 0usize;

        while i < len1 && j < len2 {
            let c1 = nf1.base[i];
            let c2 = nf2.base[j];
            let r1 = state.find(c1);
            let r2 = state.find(c2);

            if r1 == r2 && off1 == 0 && off2 == 0 {
                i += 1;
                j += 1;
                continue;
            }

            let s1 = Self::component_constant_owned(terms, state, c1);
            let s2 = Self::component_constant_owned(terms, state, c2);

            match (&s1, &s2) {
                (Some(cs1), Some(cs2)) => {
                    let chars1: Vec<char> = cs1.chars().skip(off1).collect();
                    let chars2: Vec<char> = cs2.chars().skip(off2).collect();
                    let common = chars1
                        .iter()
                        .zip(chars2.iter())
                        .take_while(|(a, b)| a == b)
                        .count();

                    let l1 = chars1.len();
                    let l2 = chars2.len();

                    // Direct character mismatch witnesses disequality.
                    if common < l1 && common < l2 {
                        return NfCheckResult::Ok;
                    }

                    if common == l1 && common == l2 {
                        i += 1;
                        j += 1;
                        off1 = 0;
                        off2 = 0;
                    } else if common == l1 {
                        i += 1;
                        off1 = 0;
                        off2 += common;
                    } else {
                        j += 1;
                        off2 = 0;
                        off1 += common;
                    }
                }
                _ if off1 == 0 && off2 == 0 => {
                    // CVC5 Simple Case 2: if components have equal length
                    // and are already known disequal, the overall disequality
                    // is satisfied without any inference.
                    //
                    // Reference: CVC5 processSimpleDeq lines 2400-2416
                    if Self::are_lengths_equal_with_entail(terms, state, c1, c2)
                        && state.are_disequal(c1, c2)
                    {
                        return NfCheckResult::Ok;
                    }
                    // Reduced components differ but are not concretely comparable.
                    // Request a safe length split only when both components have
                    // length metadata and relation is genuinely unknown.
                    if Self::has_length_info(terms, state, c1)
                        && Self::has_length_info(terms, state, c2)
                        && !Self::are_lengths_equal_with_entail(terms, state, c1, c2)
                        && !state.are_lengths_disequal(terms, c1, c2)
                    {
                        return NfCheckResult::NeedLemma(StringLemma {
                            kind: StringLemmaKind::LengthSplit,
                            x: c1,
                            y: c2,
                            char_offset: 0,
                            start_offset: 0,
                            reason: vec![diseq_lit],
                        });
                    }
                    // Guard: if either component is an unresolved string
                    // application (e.g., str.replace with variable args), the
                    // solver cannot reason about it — return Incomplete so the
                    // caller propagates Unknown rather than emitting a useless
                    // split lemma on an opaque term.
                    if Self::is_unresolved_string_application(terms, state, c1)
                        || Self::is_unresolved_string_application(terms, state, c2)
                    {
                        return NfCheckResult::Incomplete;
                    }
                    // Two non-constant components with different representatives
                    // and equal lengths. CVC5 returns false from processSimpleDeq
                    // and the caller emits an equality split (x = y v x != y).
                    //
                    // If x = y, the disequality may still hold via other NF
                    // components. If x != y, the disequality is directly
                    // satisfied at this position.
                    //
                    // Ref: CVC5 core_solver.cpp:2280-2300 (DEQ_STRINGS_EQ /
                    //      DEQ_LENS_EQ fallback in caller).
                    return NfCheckResult::NeedLemma(StringLemma {
                        kind: StringLemmaKind::EqualitySplit,
                        x: c1,
                        y: c2,
                        char_offset: 0,
                        start_offset: 0,
                        reason: vec![diseq_lit],
                    });
                }
                _ => {
                    // Partial offset with unresolved components: cannot certify
                    // the disequality. Signal Incomplete so the check loop
                    // propagates Unknown rather than silently dropping.
                    return NfCheckResult::Incomplete;
                }
            }
        }

        // If one side is exhausted but the other has leftover concrete
        // characters, disequality is immediately satisfied.
        if (off1 > 0 && j >= len2) || (off2 > 0 && i >= len1) {
            return NfCheckResult::Ok;
        }

        // All components matched pairwise — the normal forms look identical,
        // so we cannot certify the disequality. Return Incomplete so the
        // caller propagates Unknown instead of silently dropping it.
        NfCheckResult::Incomplete
    }

    /// Active disequality reasoning when `process_simple_deq` cannot resolve.
    ///
    /// Walks NF components pairwise and applies CVC5's DEQ_DISL case analysis
    /// for positions where the simple deq scanner bails out. Emits split lemmas
    /// to guide the SAT solver toward resolving the disequality.
    ///
    /// Currently handles:
    /// - `DEQ_DISL_EMP_SPLIT` (CVC5 line 2157-2167): non-constant may be empty
    /// - `DEQ_DISL_FIRST_CHAR_EQ_SPLIT` (CVC5 line 2192-2198): len=1 vs first char
    ///
    /// Reference: CVC5 `core_solver.cpp:2112-2306` (processDeq main loop).
    pub(super) fn process_deq_disl(
        terms: &TermStore,
        state: &SolverState,
        nf1: &NormalForm,
        nf2: &NormalForm,
        diseq_lit: TheoryLit,
    ) -> NfCheckResult {
        // Reverse suffix trim (same as process_simple_deq).
        let mut rproc = 0usize;
        while rproc < nf1.base.len() && rproc < nf2.base.len() {
            let i1 = nf1.base.len() - 1 - rproc;
            let i2 = nf2.base.len() - 1 - rproc;
            if state.find(nf1.base[i1]) == state.find(nf2.base[i2]) {
                rproc += 1;
            } else {
                break;
            }
        }

        let len1 = nf1.base.len().saturating_sub(rproc);
        let len2 = nf2.base.len().saturating_sub(rproc);

        for i in 0..len1.min(len2) {
            let c1 = nf1.base[i];
            let c2 = nf2.base[i];
            let r1 = state.find(c1);
            let r2 = state.find(c2);

            if r1 == r2 {
                continue;
            }

            let c1_is_const = Self::component_constant_owned(terms, state, c1).is_some();
            let c2_is_const = Self::component_constant_owned(terms, state, c2).is_some();

            // Only handle the mixed constant/non-constant case for now.
            if !(c1_is_const ^ c2_is_const) {
                continue;
            }

            let (ck, nck) = if c1_is_const { (c1, c2) } else { (c2, c1) };

            // Case A1: Non-constant may be empty → DEQ_DISL_EMP_SPLIT.
            // CVC5 core_solver.cpp:2157-2167.
            if !state.is_known_nonempty(terms, nck) {
                return NfCheckResult::NeedLemma(StringLemma {
                    kind: StringLemmaKind::DeqEmptySplit,
                    x: nck,
                    y: nck,
                    char_offset: 0,
                    start_offset: 0,
                    reason: vec![diseq_lit],
                });
            }

            // Non-constant is known non-empty. Check if length is 1.
            if state.known_length_full(terms, nck) == Some(1) {
                // Resolve to a concrete constant TermId for the DPLL executor.
                if let Some(ck_term) = Self::constant_term_for_component(terms, state, ck) {
                    if let Some(ck_str) = Self::component_constant_owned(terms, state, ck) {
                        if let Some(first_char) = ck_str.chars().next() {
                            // If nck is already known disequal to the first char,
                            // the disequality is satisfied at this position.
                            if let Some(nck_val) = Self::component_constant_owned(terms, state, nck)
                            {
                                if nck_val != first_char.to_string() {
                                    return NfCheckResult::Ok;
                                }
                            }

                            // Case A2: DEQ_DISL_FIRST_CHAR_EQ_SPLIT.
                            // Pass the concrete constant TermId in y; the DPLL
                            // executor extracts the first character.
                            // CVC5 core_solver.cpp:2192-2198.
                            return NfCheckResult::NeedLemma(StringLemma {
                                kind: StringLemmaKind::DeqFirstCharEqSplit,
                                x: nck,
                                y: ck_term,
                                char_offset: 0,
                                start_offset: 0,
                                reason: vec![diseq_lit],
                            });
                        }
                    }
                }
            }

            // Cases A3 and A4 require Skolem decomposition (Wave 2 Step 2).
            // Fall through to Incomplete for now.
        }

        NfCheckResult::Incomplete
    }
}
