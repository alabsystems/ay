// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Normal form disequality checking for the string core solver.
//!
//! Extracted from `core/mod.rs` (#4817 code-quality split).
//!
//! Implements CVC5's `checkNormalFormsDeq`, `processSimpleDeq`, and
//! `processDeq` (DEQ_DISL case analysis).
//!
//! Reference: `reference/cvc5/src/theory/strings/core_solver.cpp`

use crate::arith_entail::ArithEntail;
use crate::infer::{InferenceKind, InferenceManager};
use crate::normal_form::NormalForm;
use crate::skolem::SkolemCache;
use crate::state::SolverState;
use ay_core::term::{Constant, TermData, TermId, TermStore};
use ay_core::{StringLemma, StringLemmaKind, TheoryLit};

use super::{CoreSolver, NfCheckResult, DEBUG_STRING_CORE};

impl CoreSolver {
    /// Check normal form disequalities (#4070).
    ///
    /// Two-phase approach following CVC5's `checkNormalFormsDeq`:
    ///
    /// **Phase 1 — Conflict detection + length triage:**
    /// For each disequality (a != b), first check for conflicts (both sides
    /// provably equal). Then classify by length relationship:
    /// - Lengths disequal: deq trivially satisfied (different-length strings
    ///   cannot be equal).
    /// - Lengths unknown (with length info): emit `LengthSplit` to force the
    ///   SAT solver to decide.
    /// - Lengths equal: fall through (Phase 2 not yet implemented).
    ///
    /// Length triage is gated on `has_length_info` — in pure QF_S problems
    /// without `str.len`, emitting `LengthSplit` would create orphaned atoms
    /// that no arithmetic solver interprets.
    ///
    /// **Phase 2 — Deq component reduction (Wave 1 partial):**
    /// For equal-length deqs with computed NFs, run a deq-specific component
    /// walk (suffix trim + forward scan). This Wave 1 pass emits only guarded
    /// `LengthSplit` lemmas on reduced components and never emits internal
    /// equalities (N_UNIFY). Full CVC5 `processDeq` decomposition is not yet implemented.
    ///
    /// Reference: `reference/cvc5/src/theory/strings/core_solver.cpp`
    ///   checkNormalFormsDeq (lines 2552-2639) + processDeq (lines 2004-2307)
    pub(super) fn check_normal_forms_deq(
        &self,
        terms: &TermStore,
        state: &SolverState,
        infer: &mut InferenceManager,
        skolems: &mut SkolemCache,
    ) -> NfCheckResult {
        let mut saw_incomplete = false;

        // Phase 1: Conflict detection + length triage.
        for &(t1, t2, lit) in state.disequalities() {
            let r1 = state.find(t1);
            let r2 = state.find(t2);

            // Check 1: Same EQC -> disequality violated.
            if r1 == r2 {
                if *DEBUG_STRING_CORE {
                    eprintln!(
                        "[STRING_CORE] check_normal_forms_deq conflict(same-eqc): t1={:?} data1={:?} t2={:?} data2={:?} lit={:?} rep={:?}",
                        t1,
                        terms.get(t1),
                        t2,
                        terms.get(t2),
                        lit,
                        r1
                    );
                }
                let explanation = Self::build_deq_explanation(t1, t2, lit, state);
                infer.add_conflict(InferenceKind::DisequalityViolation, explanation);
                return NfCheckResult::Conflict;
            }

            let nf1 = self.normal_forms.get(&r1);
            let nf2 = self.normal_forms.get(&r2);
            if let (Some(a), Some(b)) = (nf1, nf2) {
                // Check 2: NFs structurally identical (EQC-aware comparison).
                if self.nfs_equal(state, a, b) {
                    if *DEBUG_STRING_CORE {
                        eprintln!(
                            "[STRING_CORE] check_normal_forms_deq conflict(nf-equal): t1={:?} data1={:?} t2={:?} data2={:?} lit={:?}",
                            t1,
                            terms.get(t1),
                            t2,
                            terms.get(t2),
                            lit
                        );
                    }
                    let explanation = Self::build_deq_explanation(t1, t2, lit, state);
                    infer.add_conflict(InferenceKind::ConstantSplit, explanation);
                    return NfCheckResult::Conflict;
                }

                // Check 3: Both NFs resolve to the same constant string.
                if let (Some(s1), Some(s2)) = (
                    self.nf_to_constant(terms, state, a),
                    self.nf_to_constant(terms, state, b),
                ) {
                    if s1 == s2 {
                        if *DEBUG_STRING_CORE {
                            eprintln!(
                                "[STRING_CORE] check_normal_forms_deq conflict(nf-const-equal): t1={t1:?} t2={t2:?} lit={lit:?} value={s1:?}"
                            );
                        }
                        let explanation = Self::build_deq_explanation(t1, t2, lit, state);
                        infer.add_conflict(InferenceKind::ConstantSplit, explanation);
                        return NfCheckResult::Conflict;
                    }
                }
            }

            // Check 4: Both sides resolve to the same concrete string via
            // function evaluation (e.g., str.at("hello",0) ≠ "h" where
            // str.at evaluates to "h"). nf_to_constant misses these because
            // it only checks EQC constants and syntactic string literals,
            // not evaluated function applications.
            if let (Some(s1), Some(s2)) = (
                Self::resolve_string_term(terms, state, t1, 0),
                Self::resolve_string_term(terms, state, t2, 0),
            ) {
                if s1 == s2 {
                    if *DEBUG_STRING_CORE {
                        eprintln!(
                            "[STRING_CORE] check_normal_forms_deq conflict(eval-equal): t1={:?} data1={:?} t2={:?} data2={:?} lit={:?} value={:?}",
                            t1,
                            terms.get(t1),
                            t2,
                            terms.get(t2),
                            lit,
                            s1
                        );
                    }
                    let explanation = Self::build_deq_explanation(t1, t2, lit, state);
                    infer.add_conflict(InferenceKind::PredicateConflict, explanation);
                    return NfCheckResult::Conflict;
                }
            }

            // Split-generated branch literals can produce disequalities that are
            // already settled by shape facts, e.g. `x = ""` and
            // `x != str.++("b", k)`. Treat those as resolved instead of forcing
            // incomplete on unresolved applications.
            if Self::disequality_is_trivially_satisfied(terms, state, t1, t2) {
                continue;
            }

            // Length triage (#4070): classify by length relationship.
            //
            // Only enter triage when both sides have length information
            // (known constant length or a registered str.len term). In pure
            // QF_S problems without str.len, length terms don't exist and
            // emitting LengthSplit would create orphaned atoms that no
            // arithmetic solver interprets.
            //
            // CVC5 reference: checkNormalFormsDeq lines 2576-2598
            if Self::has_length_info(terms, state, r1) && Self::has_length_info(terms, state, r2) {
                if state.are_lengths_disequal(terms, r1, r2) {
                    // Lengths are different — the disequality is trivially satisfied.
                    // Strings of different lengths cannot be equal.
                    continue;
                }

                if !Self::are_lengths_equal_with_entail(terms, state, r1, r2) {
                    // Length relationship unknown — emit a LengthSplit to force
                    // the SAT solver to decide len(r1) = len(r2) vs len(r1) != len(r2).
                    //
                    // CVC5 reference: sendSplit(lt[0], lt[1], STRINGS_DEQ_LENGTH_SP)
                    return NfCheckResult::NeedLemma(StringLemma {
                        kind: StringLemmaKind::LengthSplit,
                        x: r1,
                        y: r2,
                        char_offset: 0,
                        start_offset: 0,
                        reason: vec![lit],
                    });
                }
                // Lengths known equal — fall through to component-wise deq reduction.
            }

            // Phase 2 (#4070 Wave 1): deq-specific component walk over
            // equal-length normal forms. Unlike process_simple_neq, this path
            // never emits internal equalities (N_UNIFY). It only:
            //   - certifies deq as satisfied when a concrete mismatch is found
            //   - requests a guarded split lemma on reduced components
            //
            // Reference: CVC5 core_solver.cpp:2328-2479 (processSimpleDeq)
            if let (Some(a), Some(b)) = (nf1, nf2) {
                match Self::process_simple_deq(terms, state, a, b, lit, skolems) {
                    NfCheckResult::NeedLemma(lemma) => return NfCheckResult::NeedLemma(lemma),
                    NfCheckResult::Conflict => return NfCheckResult::Conflict,
                    NfCheckResult::Incomplete => {
                        // process_simple_deq bailed — try DEQ_DISL case analysis.
                        // CVC5 core_solver.cpp:2112-2306 (processDeq fallback).
                        match Self::process_deq_disl(terms, state, a, b, lit) {
                            NfCheckResult::NeedLemma(lemma) => {
                                return NfCheckResult::NeedLemma(lemma);
                            }
                            NfCheckResult::Conflict => return NfCheckResult::Conflict,
                            NfCheckResult::Ok => {}
                            NfCheckResult::Incomplete => saw_incomplete = true,
                        }
                    }
                    NfCheckResult::Ok => {}
                }
            }

            if Self::is_unresolved_string_application(terms, state, t1)
                || Self::is_unresolved_string_application(terms, state, t2)
            {
                saw_incomplete = true;
            }
        }

        if infer.has_conflict() {
            return NfCheckResult::Conflict;
        }

        if saw_incomplete {
            NfCheckResult::Incomplete
        } else {
            NfCheckResult::Ok
        }
    }

    /// Whether a term has enough length metadata for safe LengthSplit emission.
    ///
    /// We require either a known constant length or a registered `str.len` term.
    /// This prevents orphaned `str.len` split atoms in pure QF_S contexts where
    /// no arithmetic solver interprets them.
    fn has_length_info(terms: &TermStore, state: &SolverState, t: TermId) -> bool {
        let rep = state.find(t);
        state.known_length(terms, rep).is_some() || state.get_length_term(&rep).is_some()
    }

    /// Length-equality check with arithmetic entailment fallback.
    ///
    /// Primary path uses the existing EQC metadata check.
    /// Fallback path asks ArithEntail to compare registered length terms,
    /// which handles exact structural cases like `str.unit(_)` lengths.
    pub(super) fn are_lengths_equal_with_entail(
        terms: &TermStore,
        state: &SolverState,
        a: TermId,
        b: TermId,
    ) -> bool {
        if state.are_lengths_equal(terms, a, b) {
            return true;
        }

        let ra = state.find(a);
        let rb = state.find(b);
        let (Some(len_a), Some(len_b)) = (state.get_length_term(&ra), state.get_length_term(&rb))
        else {
            return false;
        };

        ArithEntail::new(terms, state).check_eq(len_a, len_b)
    }

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
    fn process_deq_disl(
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

    /// Whether this term is a string function application that cannot currently be resolved.
    ///
    /// Only flags applications that need evaluation to a concrete value
    /// (str.at, str.substr, str.replace, str.from_int, str.to_int, etc.).
    /// Concat (`str.++`) and equality (`=`) terms are handled by the normal
    /// form machinery and should NOT trigger Unknown.
    fn is_unresolved_string_application(terms: &TermStore, state: &SolverState, t: TermId) -> bool {
        let TermData::App(sym, _) = terms.get(t) else {
            return false;
        };
        // Concat, equality, and str.len are not string-returning — handled
        // by NF comparison (concat/equality) or LIA solver (str.len).
        match sym.name() {
            "str.++" | "=" | "str.len" => return false,
            _ => {}
        }
        Self::resolve_string_term(terms, state, t, 0).is_none()
    }

    /// Check if a disequality is already satisfied by obvious shape facts.
    ///
    /// Handles split-branch disequalities like `x != str.++("b", k)` when
    /// `x = ""` is known.
    fn disequality_is_trivially_satisfied(
        terms: &TermStore,
        state: &SolverState,
        t1: TermId,
        t2: TermId,
    ) -> bool {
        // Concrete constants with different values are already disequal.
        if let (Some(s1), Some(s2)) = (
            Self::resolve_string_term(terms, state, t1, 0),
            Self::resolve_string_term(terms, state, t2, 0),
        ) {
            if s1 != s2 {
                return true;
            }
        }

        let t1_empty = state.is_empty_string(terms, t1);
        let t2_empty = state.is_empty_string(terms, t2);
        (t1_empty && Self::is_guaranteed_nonempty(terms, state, t2))
            || (t2_empty && Self::is_guaranteed_nonempty(terms, state, t1))
    }

    /// Conservative non-emptiness check for shape reasoning.
    fn is_guaranteed_nonempty(terms: &TermStore, state: &SolverState, t: TermId) -> bool {
        if state.is_known_nonempty(terms, t) {
            return true;
        }
        match terms.get(t) {
            TermData::Const(Constant::String(s)) => !s.is_empty(),
            TermData::App(sym, args) if sym.name() == "str.++" => args
                .iter()
                .any(|&arg| Self::is_guaranteed_nonempty(terms, state, arg)),
            _ => false,
        }
    }

    /// Build a conflict explanation for a disequality violation.
    ///
    /// Uses proof-forest explain() to collect only the merge reasons on
    /// the path between the two disequal terms, plus the disequality
    /// literal itself. If no proof path exists, this returns just the
    /// disequality literal and the conflict remains explainable but targeted.
    fn build_deq_explanation(
        t1: TermId,
        t2: TermId,
        deq_lit: TheoryLit,
        state: &SolverState,
    ) -> Vec<TheoryLit> {
        let mut explanation = state.explain(t1, t2);
        if !explanation.contains(&deq_lit) {
            explanation.push(deq_lit);
        }
        explanation
    }

    /// Compare two normal forms for structural equality under EQC representatives.
    ///
    /// Two NFs are equal if they have the same length and each pair of
    /// corresponding components shares the same EQC representative.
    pub(super) fn nfs_equal(&self, state: &SolverState, a: &NormalForm, b: &NormalForm) -> bool {
        if a.base.len() != b.base.len() {
            return false;
        }
        a.base
            .iter()
            .zip(b.base.iter())
            .all(|(&x, &y)| state.find(x) == state.find(y))
    }

    /// Try to resolve a normal form to a concrete constant string.
    ///
    /// Returns `Some(string)` if every component in the NF has a known
    /// constant value (via its EQC or syntactically). Returns `None` if
    /// any component is a variable with no known constant.
    pub(super) fn nf_to_constant(
        &self,
        terms: &TermStore,
        state: &SolverState,
        nf: &NormalForm,
    ) -> Option<String> {
        let mut result = String::new();
        for &component in &nf.base {
            let comp_rep = state.find(component);
            let comp_const = state
                .get_eqc(&comp_rep)
                .and_then(|e| e.constant.as_deref())
                .or_else(|| Self::get_string_constant(terms, component));
            match comp_const {
                Some(s) => result.push_str(s),
                None => return None,
            }
        }
        Some(result)
    }
}
