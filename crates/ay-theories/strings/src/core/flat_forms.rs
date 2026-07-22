// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Flat-form construction and comparison.
//!
//! Flat forms are lightweight representations of concat terms that enable
//! quick mismatch detection before the more expensive normal-form computation.
//!
//! Reference: CVC5 `core_solver.cpp:492-495`, `core_solver.cpp:580-640`

use super::*;

impl CoreSolver {
    /// Build flat forms for all concat terms in all EQCs.
    ///
    /// A flat form of `str.++(t1, t2, ..., tn)` is `[r1, r2, ..., rm]` where
    /// each `ri` is the EQC representative of `ti` and empty-string reps are
    /// dropped. This is a single-level flattening (no recursive expansion).
    ///
    /// Reference: CVC5 `core_solver.cpp:492-495` (built during checkCycles DFS)
    pub(super) fn build_flat_forms(&mut self, terms: &TermStore, state: &SolverState) {
        self.flat_forms.clear();
        let reps = state.eqc_representatives();
        for &rep in &reps {
            let Some(eqc) = state.get_eqc(&rep) else {
                continue;
            };
            for &concat_term in &eqc.concat_terms {
                let Some(children) = state.get_concat_children(terms, concat_term) else {
                    continue;
                };
                let mut ff = Vec::new();
                for &child in children {
                    let child_rep = state.find(child);
                    if !state.is_empty_string(terms, child_rep) {
                        ff.push(child_rep);
                    }
                }
                self.flat_forms.insert(concat_term, ff);
            }
        }
    }

    /// Check flat forms for conflicts and equality inferences.
    ///
    /// Two sub-checks:
    /// 1. Constant containment: if an EQC has a constant, verify that constant
    ///    components in flat forms appear in order within it.
    /// 2. Pairwise comparison: compare flat forms of concat terms in the same
    ///    EQC for endpoint-empty, endpoint-eq, and unify inferences.
    ///
    /// Reference: CVC5 `core_solver.cpp:128-371` (`checkFlatForms`)
    pub(super) fn check_flat_forms(
        &self,
        terms: &TermStore,
        state: &SolverState,
        infer: &mut InferenceManager,
    ) -> bool {
        let reps = state.eqc_representatives();
        for &rep in &reps {
            let Some(eqc) = state.get_eqc(&rep) else {
                continue;
            };

            // Phase 1: Constant containment check.
            // If the EQC has a known constant, verify that constant components
            // from each concat's flat form appear in order within it.
            if let Some(ref eqc_const) = eqc.constant {
                for &concat_term in &eqc.concat_terms {
                    let Some(ff) = self.flat_forms.get(&concat_term) else {
                        continue;
                    };
                    let mut search_pos = 0;
                    for &comp in ff {
                        let comp_rep = state.find(comp);
                        let Some(comp_const) = state.get_constant(&comp_rep) else {
                            continue;
                        };
                        if let Some(pos) = eqc_const[search_pos..].find(comp_const) {
                            search_pos += pos + comp_const.len();
                        } else {
                            // Flat forms are a lightweight pre-pass only. A mismatch
                            // here can be spurious when component boundaries are still
                            // underconstrained; defer conflicts to full NF checks.
                            break;
                        }
                    }
                }
            }

            // Phase 2: Pairwise flat form comparison.
            let concats = &eqc.concat_terms;
            if concats.len() < 2 {
                continue;
            }
            // Precompute reversed flat forms once per concat term (#4061).
            // Previously reversed inside the O(C^2) pair loop, allocating
            // O(C^2 * F) reversed copies instead of O(C * F).
            let rev_forms: HashMap<TermId, Vec<TermId>> = concats
                .iter()
                .filter_map(|&ct| {
                    self.flat_forms
                        .get(&ct)
                        .map(|ff| (ct, ff.iter().copied().rev().collect()))
                })
                .collect();
            for i in 0..concats.len() {
                for j in (i + 1)..concats.len() {
                    let ff_a = self.flat_forms.get(&concats[i]);
                    let ff_b = self.flat_forms.get(&concats[j]);
                    if let (Some(a), Some(b)) = (ff_a, ff_b) {
                        // Forward pass.
                        if self
                            .compare_flat_forms(terms, state, infer, concats[i], concats[j], a, b)
                        {
                            return true;
                        }
                        if infer.has_conflict() || infer.has_internal_equalities() {
                            return infer.has_conflict();
                        }
                        // Reverse pass (using precomputed reversed forms).
                        if let (Some(a_rev), Some(b_rev)) =
                            (rev_forms.get(&concats[i]), rev_forms.get(&concats[j]))
                        {
                            if self.compare_flat_forms(
                                terms, state, infer, concats[i], concats[j], a_rev, b_rev,
                            ) {
                                return true;
                            }
                            if infer.has_conflict() || infer.has_internal_equalities() {
                                return infer.has_conflict();
                            }
                        }
                    }
                }
            }
        }
        false
    }

    /// Compare two flat forms component by component.
    ///
    /// Walks both flat forms in parallel:
    /// - Same rep at index: advance both.
    /// - One exhausted: remaining components must be empty (F_ENDPOINT_EMP).
    /// - Both at last with different reps: must be equal (F_ENDPOINT_EQ).
    /// - Different but known equal length: must be equal (F_UNIFY).
    /// - Both constants with incompatible prefixes: conflict (F_CONST).
    ///
    /// Returns `true` only if a **conflict** was found. Internal equalities
    /// are added to `infer` but do not cause early return — they are processed
    /// by the lib.rs internal fact loop after core.check() completes.
    ///
    /// Reference: CVC5 `core_solver.cpp:216-371` (`checkFlatForm`)
    #[allow(clippy::too_many_arguments)]
    pub(super) fn compare_flat_forms(
        &self,
        terms: &TermStore,
        state: &SolverState,
        infer: &mut InferenceManager,
        concat_a: TermId,
        concat_b: TermId,
        ff_a: &[TermId],
        ff_b: &[TermId],
    ) -> bool {
        // Base explanation: why the two concat terms are in the same EQC.
        let mut base_explanation = state.explain_or_all(concat_a, concat_b);

        // Endpoint-empty premise completeness (#flat-forms-empty-premise).
        // `build_flat_forms` DROPS children whose representative is the empty
        // string without recording the dependency, so every inference below
        // (F_ENDPOINT_EQ / F_UNIFY / F_ENDPOINT_EMP) implicitly assumes those
        // children are empty. Fold each such emptiness premise
        // `explain(child, "")` into the base explanation; otherwise conflicts
        // later built from these proof edges (extf_effort1 explanation chains)
        // are INCOMPLETE and become spurious few-literal conflicts → false
        // UNSAT. If a premise has no proof path, FAIL CLOSED by skipping the
        // inference entirely (mirrors the strict-explanation policy in
        // nf_equality_simpleq.rs #6273): adding premises only strengthens
        // explanations; skipping only loses an optional propagation.
        for &concat in &[concat_a, concat_b] {
            let Some(children) = state.get_concat_children(terms, concat) else {
                continue;
            };
            for &child in children {
                if !state.is_empty_string(terms, state.find(child)) {
                    // Kept in the flat form — not a hidden premise.
                    continue;
                }
                if matches!(
                    terms.get(child),
                    TermData::Const(Constant::String(s)) if s.is_empty()
                ) {
                    // Literally the empty-string constant: no premise needed.
                    continue;
                }
                // The empty-string term inside child's EQC to explain against.
                let target = state.find_constant_term_id(terms, child).or_else(|| {
                    state
                        .empty_string_id()
                        .filter(|&e| state.find(e) == state.find(child))
                });
                let premise = target.map(|t| state.explain(child, t)).unwrap_or_default();
                if premise.is_empty() {
                    // No proof path for a non-literal emptiness premise: any
                    // explanation built from this comparison would be
                    // incomplete. Fail closed — skip all inferences here.
                    return false;
                }
                for lit in premise {
                    if !base_explanation.contains(&lit) {
                        base_explanation.push(lit);
                    }
                }
            }
        }

        let mut ia = 0;
        let mut ib = 0;
        while ia < ff_a.len() && ib < ff_b.len() {
            let ra = state.find(ff_a[ia]);
            let rb = state.find(ff_b[ib]);

            if ra == rb {
                // Same representative: advance both.
                ia += 1;
                ib += 1;
                continue;
            }

            // Both are constants: check prefix compatibility.
            if let (Some(ca), Some(cb)) = (state.get_constant(&ra), state.get_constant(&rb)) {
                if !ca.starts_with(cb) && !cb.starts_with(ca) {
                    // Flat-form constant mismatch is heuristic only; the full NF
                    // pass performs sound conflict checks with split lemmas.
                    return false;
                }
                // One is a prefix of the other: can't resolve at flat form level.
                // Fall through to NF computation for the full picture.
                return false;
            }

            // Both at their last component with different reps: must be equal
            // (F_ENDPOINT_EQ). CVC5 reference: core_solver.cpp:337
            if ia == ff_a.len() - 1 && ib == ff_b.len() - 1 {
                infer.add_internal_equality(
                    InferenceKind::EndpointEq,
                    ff_a[ia],
                    ff_b[ib],
                    base_explanation,
                );
                // Internal equality, not a conflict — let pipeline continue.
                return false;
            }

            // Known equal length: infer equality (F_UNIFY).
            if Self::are_lengths_equal_with_entail(terms, state, ra, rb) {
                infer.add_internal_equality(
                    InferenceKind::Unify,
                    ff_a[ia],
                    ff_b[ib],
                    base_explanation,
                );
                // Internal equality, not a conflict — let pipeline continue.
                return false;
            }

            // Can't resolve this pair at flat form level.
            return false;
        }

        // One or both exhausted. Check remaining components.
        if ia < ff_a.len() || ib < ff_b.len() {
            // The shorter form is exhausted. Remaining components of the longer
            // form must all be empty strings.
            let remaining = if ia < ff_a.len() {
                &ff_a[ia..]
            } else {
                &ff_b[ib..]
            };

            if let Some(empty_id) = state.empty_string_id() {
                for &comp in remaining {
                    if !state.is_empty_string(terms, comp) {
                        infer.add_internal_equality(
                            InferenceKind::EndpointEmpty,
                            comp,
                            empty_id,
                            base_explanation.clone(),
                        );
                    }
                }
            }
        }

        // No conflict found (internal equalities may have been added).
        false
    }
}
