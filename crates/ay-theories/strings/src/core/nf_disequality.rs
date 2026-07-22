// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! NF disequality checking and component-wise deq analysis.
//!
//! Extracted from `core/mod.rs` per design
//! the development design notes.

use super::*;

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
    pub(super) fn has_length_info(terms: &TermStore, state: &SolverState, t: TermId) -> bool {
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

    // process_simple_deq, process_deq_disl extracted to nf_deq_process.rs

    /// Whether this term is a string function application that cannot currently be resolved.
    ///
    /// Only flags applications that need evaluation to a concrete value
    /// (str.at, str.substr, str.replace, str.from_int, str.to_int, etc.).
    /// Concat (`str.++`) and equality (`=`) terms are handled by the normal
    /// form machinery and should NOT trigger Unknown.
    pub(super) fn is_unresolved_string_application(
        terms: &TermStore,
        state: &SolverState,
        t: TermId,
    ) -> bool {
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
    pub(super) fn disequality_is_trivially_satisfied(
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
    pub(super) fn is_guaranteed_nonempty(
        terms: &TermStore,
        state: &SolverState,
        t: TermId,
    ) -> bool {
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
}

#[cfg(test)]
#[path = "nf_disequality_tests.rs"]
mod tests;
