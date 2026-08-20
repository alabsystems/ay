// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! NF equality checking: propagation-only pass and constant comparison.
//!
//! The word equation solver (`process_simple_neq`) is in `nf_equality_simpleq`.
//!
//! Extracted from `core/mod.rs` per design
//! the development design notes.

use super::*;

impl CoreSolver {
    /// Propagation-only NF equality check (CVC5's `checkNormalFormsEqProp`).
    ///
    /// Runs the NF equality checking pipeline but **buffers** split lemma
    /// requests instead of returning them immediately. This allows:
    /// 1. Detecting identical NFs across different EQCs and merging them
    ///    (free propagation via `nf_to_eqc` deduplication).
    /// 2. Running `check_extf_eval_effort1` between propagation and splitting,
    ///    which may resolve things without needing the split.
    ///
    /// Returns `Conflict` on conflict, `Ok` or `Incomplete` otherwise.
    /// Buffered lemmas are retrieved later by `check_normal_forms_eq`.
    ///
    /// Reference: `reference/cvc5/src/theory/strings/core_solver.cpp:551-609`
    pub(super) fn check_normal_forms_eq_prop(
        &mut self,
        terms: &TermStore,
        state: &SolverState,
        infer: &mut InferenceManager,
        skolems: &mut SkolemCache,
    ) -> NfCheckResult {
        self.buffered_lemmas.clear();
        self.nf_to_eqc.clear();
        let mut saw_incomplete = false;
        let reps = state.eqc_representatives();
        for &rep in &reps {
            let eqc = match state.get_eqc(&rep) {
                Some(eqc) => eqc,
                None => continue,
            };
            // Active concat terms: non-reduced, used for primary NF computation
            // and Case A (constant comparison).
            let active_concat_terms: Vec<TermId> = eqc
                .concat_terms
                .iter()
                .copied()
                .filter(|ct| !self.reduced_terms.contains(ct))
                .collect();
            // All concat terms including reduced: used for Case B pairwise
            // NF comparison (#6326). Prefix/suffix Skolem decomposition
            // concat terms are marked reduced (their extf semantics are
            // captured by SAT-level implications), but their NFs must still
            // be compared pairwise to detect conflicts like
            // str.++("ac", sk1) vs str.++("ab", sk2) in the same EQC.
            let all_concat_terms: &[TermId] = &eqc.concat_terms;

            if active_concat_terms.is_empty() && all_concat_terms.len() < 2 {
                // Non-concat EQC: check for nf_to_eqc deduplication.
                // Its NF is the singleton [rep].
                if let Some(nf) = self.normal_forms.get(&rep) {
                    let nf_key: Vec<TermId> = nf.base.iter().map(|&t| state.find(t)).collect();
                    if let Some(&other_rep) = self.nf_to_eqc.get(&nf_key) {
                        if other_rep != rep {
                            // Two EQCs have identical NFs — merge them.
                            let explanation = Self::build_explanation(nf, state);
                            if !explanation.is_empty() {
                                infer.add_internal_equality(
                                    InferenceKind::Unify,
                                    rep,
                                    other_rep,
                                    explanation,
                                );
                                if infer.has_conflict() {
                                    return NfCheckResult::Conflict;
                                }
                            } else {
                                saw_incomplete = true;
                            }
                        }
                    } else {
                        self.nf_to_eqc.insert(nf_key, rep);
                    }
                }
                continue;
            }

            // Case A: EQC has constant — compare each concat NF against it.
            if let Some(ref eqc_const) = eqc.constant {
                let eqc_const = eqc_const.clone();
                if *DEBUG_STRING_CORE {
                    eprintln!(
                        "[STRING_CORE] Case A: rep={:?} constant=\"{}\" concats(active/total)={}/{}",
                        rep,
                        eqc_const,
                        active_concat_terms.len(),
                        eqc.concat_terms.len()
                    );
                }
                for &ct in &active_concat_terms {
                    if let Some(concat_nf) = self.try_compute_concat_nf(terms, state, rep, ct) {
                        if *DEBUG_STRING_CORE {
                            eprintln!("[STRING_CORE]   NF for {:?}: {:?}", ct, concat_nf.base);
                        }
                        match self.process_nf_against_constant(
                            terms, state, &concat_nf, &eqc_const, infer,
                        ) {
                            NfCheckResult::Conflict => {
                                if *DEBUG_STRING_CORE {
                                    eprintln!(
                                        "[STRING_CORE]   CONFLICT from process_nf_against_constant for ct={:?} data={:?} const={:?} rep={:?}",
                                        ct,
                                        terms.get(ct),
                                        eqc_const,
                                        rep
                                    );
                                }
                                return NfCheckResult::Conflict;
                            }
                            NfCheckResult::NeedLemma(lemma) => {
                                // Buffer instead of returning immediately.
                                self.buffered_lemmas.push(lemma);
                                return if saw_incomplete {
                                    NfCheckResult::Incomplete
                                } else {
                                    NfCheckResult::Ok
                                };
                            }
                            NfCheckResult::Incomplete => {
                                // process_nf_against_constant bailed on a variable.
                                // Fall through to process_simple_neq.
                                if let Some(const_nf) = self.normal_forms.get(&rep) {
                                    match Self::process_simple_neq(
                                        terms, state, &concat_nf, const_nf, infer, skolems,
                                    ) {
                                        NfCheckResult::Conflict => return NfCheckResult::Conflict,
                                        NfCheckResult::NeedLemma(lemma) => {
                                            self.buffered_lemmas.push(lemma);
                                            return if saw_incomplete {
                                                NfCheckResult::Incomplete
                                            } else {
                                                NfCheckResult::Ok
                                            };
                                        }
                                        NfCheckResult::Incomplete => saw_incomplete = true,
                                        NfCheckResult::Ok => {}
                                    }
                                } else {
                                    saw_incomplete = true;
                                }
                            }
                            NfCheckResult::Ok => {}
                        }
                    }
                }
                // Register this EQC's NF in nf_to_eqc for dedup.
                if let Some(nf) = self.normal_forms.get(&rep) {
                    let nf_key: Vec<TermId> = nf.base.iter().map(|&t| state.find(t)).collect();
                    if let Some(&other_rep) = self.nf_to_eqc.get(&nf_key) {
                        if other_rep != rep {
                            let explanation = Self::build_explanation(nf, state);
                            if !explanation.is_empty() {
                                infer.add_internal_equality(
                                    InferenceKind::Unify,
                                    rep,
                                    other_rep,
                                    explanation,
                                );
                                if infer.has_conflict() {
                                    return NfCheckResult::Conflict;
                                }
                            } else {
                                saw_incomplete = true;
                            }
                        }
                    } else {
                        self.nf_to_eqc.insert(nf_key, rep);
                    }
                }
                continue;
            }

            // Case B: 2+ concat terms (including reduced) — compare NFs pairwise.
            // Use all_concat_terms (#6326): reduced concat terms from prefix/suffix
            // decompositions must participate in pairwise comparison to detect
            // conflicts like str.++("ac",sk1) vs str.++("ab",sk2).
            if all_concat_terms.len() >= 2 {
                let mut nfs: Vec<NormalForm> = Vec::new();
                for &ct in all_concat_terms {
                    if let Some(nf) = self.try_compute_concat_nf(terms, state, rep, ct) {
                        nfs.push(nf);
                    }
                }
                if *DEBUG_STRING_CORE {
                    eprintln!(
                        "[STRING_CORE] Case B: rep={:?} {} all concat terms ({} active), {} NFs",
                        rep,
                        all_concat_terms.len(),
                        active_concat_terms.len(),
                        nfs.len()
                    );
                    for (k, nf) in nfs.iter().enumerate() {
                        eprintln!("[STRING_CORE]   NF[{}]: {:?}", k, nf.base);
                    }
                }
                for i in 0..nfs.len() {
                    for j in (i + 1)..nfs.len() {
                        match Self::process_simple_neq(
                            terms, state, &nfs[i], &nfs[j], infer, skolems,
                        ) {
                            NfCheckResult::Conflict => {
                                if *DEBUG_STRING_CORE {
                                    eprintln!("[STRING_CORE]   CONFLICT from process_simple_neq for NF[{i}] vs NF[{j}]");
                                }
                                return NfCheckResult::Conflict;
                            }
                            NfCheckResult::NeedLemma(lemma) => {
                                self.buffered_lemmas.push(lemma);
                                return if saw_incomplete {
                                    NfCheckResult::Incomplete
                                } else {
                                    NfCheckResult::Ok
                                };
                            }
                            NfCheckResult::Incomplete => saw_incomplete = true,
                            NfCheckResult::Ok => {}
                        }
                    }
                }
            }

            // Register this EQC's NF in nf_to_eqc for dedup.
            if let Some(nf) = self.normal_forms.get(&rep) {
                let nf_key: Vec<TermId> = nf.base.iter().map(|&t| state.find(t)).collect();
                if let Some(&other_rep) = self.nf_to_eqc.get(&nf_key) {
                    if other_rep != rep {
                        let explanation = Self::build_explanation(nf, state);
                        if !explanation.is_empty() {
                            infer.add_internal_equality(
                                InferenceKind::Unify,
                                rep,
                                other_rep,
                                explanation,
                            );
                            if infer.has_conflict() {
                                return NfCheckResult::Conflict;
                            }
                        } else {
                            saw_incomplete = true;
                        }
                    }
                } else {
                    self.nf_to_eqc.insert(nf_key, rep);
                }
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

    /// Emit one buffered split lemma from the propagation-only pass.
    ///
    /// CVC5's `checkNormalFormsEq` picks the best inference from `d_pinfers`.
    /// We pick the first buffered lemma (simplest heuristic; CVC5 picks by
    /// minimum inference ID which is effectively the same for our usage).
    ///
    /// Reference: `reference/cvc5/src/theory/strings/core_solver.cpp:2755-2787`
    pub(super) fn check_normal_forms_eq(&mut self) -> NfCheckResult {
        let Some(lemma) = self.buffered_lemmas.pop() else {
            return NfCheckResult::Ok;
        };
        // Closure 3 (`--str-nf`, sub-flag 3): de-serialized emission.
        // Every remaining DISTINCT buffered lemma rides along in the same
        // round instead of costing one CEGAR round-trip each. Each buffered
        // lemma is independently guarded (its own NF explanation), so
        // emitting several at once is exactly as sound as emitting them one
        // per round — only faster.
        if crate::str_nf_closure_enabled(3) {
            let rest = std::mem::take(&mut self.buffered_lemmas);
            for extra in rest {
                if extra != lemma && !self.extra_lemmas.contains(&extra) {
                    self.extra_lemmas.push(extra);
                }
            }
        }
        NfCheckResult::NeedLemma(lemma)
    }

    /// Compare a multi-component NF against a known constant value.
    ///
    /// Walks the NF left-to-right, consuming characters from the constant.
    /// Implements Cases 0, 1, 2, 5 of processSimpleNEq for the special
    /// case where one side is a known constant.
    pub(super) fn process_nf_against_constant(
        &self,
        terms: &TermStore,
        state: &SolverState,
        nf: &NormalForm,
        target: &str,
        infer: &mut InferenceManager,
    ) -> NfCheckResult {
        let mut offset = 0; // How far into `target` we've consumed.

        for &component in &nf.base {
            let comp_rep = state.find(component);

            // Get the constant value for this NF component (via EQC).
            let comp_const = state
                .get_eqc(&comp_rep)
                .and_then(|e| e.constant.as_deref())
                .or_else(|| Self::get_string_constant(terms, component));

            match comp_const {
                Some(s) => {
                    // Case 5: const-const comparison.
                    if offset + s.len() > target.len() {
                        // Component is too long — conflict.
                        let Some(explanation) =
                            Self::build_nf_vs_constant_explanation(terms, nf, state)
                        else {
                            return NfCheckResult::Incomplete;
                        };
                        infer.add_conflict(InferenceKind::ConstantSplit, explanation);
                        return NfCheckResult::Conflict;
                    }
                    let target_slice = &target[offset..offset + s.len()];
                    if s != target_slice {
                        // Mismatch — conflict.
                        let Some(explanation) =
                            Self::build_nf_vs_constant_explanation(terms, nf, state)
                        else {
                            return NfCheckResult::Incomplete;
                        };
                        infer.add_conflict(InferenceKind::ConstantSplit, explanation);
                        return NfCheckResult::Conflict;
                    }
                    offset += s.len();
                }
                None => {
                    // Variable component — can't determine its value statically.
                    // Cases 6-9 (splits) would handle this; for now, bail out.
                    return NfCheckResult::Incomplete;
                }
            }
        }

        // Case 0/1: All NF components consumed. Check remaining.
        if offset != target.len() {
            // NF resolves to a shorter string than the constant — conflict.
            let Some(explanation) = Self::build_nf_vs_constant_explanation(terms, nf, state) else {
                return NfCheckResult::Incomplete;
            };
            infer.add_conflict(InferenceKind::EndpointEmpty, explanation);
            return NfCheckResult::Conflict;
        }

        NfCheckResult::Ok
    }
}
