// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
//
// Explanation building for the string core solver.
//
// Constructs targeted explanations from normal form dependencies for
// conflict/split lemmas. Sound explanation generation is critical for
// CDCL correctness — empty or over-approximate explanations cause
// false-UNSAT (#3826, #6273).

// #8529: Use deterministic hash sets in all builds.
use ay_core::kani_compat::DetHashSet as HashSet;
use ay_core::{Constant, TermData, TermId, TermStore, TheoryLit};

use crate::normal_form::NormalForm;
use crate::state::SolverState;

use super::{CoreSolver, DEBUG_STRING_CORE};

impl CoreSolver {
    /// Get the string constant value for a component (owned copy).
    pub(super) fn component_constant_owned(
        terms: &TermStore,
        state: &SolverState,
        t: TermId,
    ) -> Option<String> {
        if let Some(const_tid) = state.find_constant_term_id(terms, t) {
            if let Some(s) = Self::get_string_constant(terms, const_tid) {
                return Some(s.to_owned());
            }
        }
        let rep = state.find(t);
        if let Some(s) = state.get_eqc(&rep).and_then(|e| e.constant.as_deref()) {
            return Some(s.to_owned());
        }
        Self::get_string_constant(terms, t).map(str::to_owned)
    }

    /// Resolve a component with known constant value to the concrete constant term.
    ///
    /// `process_simple_neq` may discover that a component is constant via EQC
    /// metadata even when the component term itself is a variable/concat.
    /// ConstSplit lowering needs the concrete constant `TermId` to extract
    /// characters; otherwise the executor degrades to EmptySplit and can stall.
    pub(super) fn constant_term_for_component(
        terms: &TermStore,
        state: &SolverState,
        t: TermId,
    ) -> Option<TermId> {
        match terms.get(t) {
            TermData::Const(Constant::String(_)) => Some(t),
            _ => state.find_constant_term_id(terms, t),
        }
    }

    /// Extend `explanation` with `lits`, skipping duplicates in O(1) per
    /// literal via the companion `seen` set. Previously used
    /// `Vec::contains()` which is O(n) per literal, making explanation
    /// construction O(n²). (#4061)
    pub(super) fn extend_dedup(
        explanation: &mut Vec<TheoryLit>,
        seen: &mut HashSet<TheoryLit>,
        lits: Vec<TheoryLit>,
    ) {
        for lit in lits {
            if seen.insert(lit) {
                explanation.push(lit);
            }
        }
    }

    /// Build a conflict explanation from NF dependencies.
    ///
    /// Uses `state.explain(dep.lhs, dep.rhs)` for each dependency to produce
    /// a targeted explanation via BFS over the proof forest.
    ///
    /// Returns an empty Vec when all deps are trivial (lhs==rhs at explain
    /// time). Callers must handle this: conflict-reporting callers should
    /// return `NfCheckResult::Incomplete`, internal-equality callers should
    /// skip the merge. An empty explanation would produce a vacuously-true
    /// blocking clause leading to false UNSAT (#3826).
    ///
    /// Previously fell back to `state.assertions().to_vec()`, but that
    /// over-approximation creates blocking clauses so strong they eliminate
    /// valid assignments in CEGAR loops, causing false UNSAT.
    pub(super) fn build_explanation(nf: &NormalForm, state: &SolverState) -> Vec<TheoryLit> {
        let mut explanation = Vec::new();
        let mut seen = HashSet::default();
        for dep in &nf.deps {
            Self::extend_dedup(&mut explanation, &mut seen, state.explain(dep.lhs, dep.rhs));
        }
        explanation
    }

    /// Like `build_explanation`, but returns `None` if any non-trivial dep
    /// (lhs ≠ rhs) has an empty explain — the proof forest can't justify
    /// that merge. Using an incomplete explanation in a conflict clause
    /// would cause false UNSAT (#3826).
    ///
    /// Also augments with component/rep-to-constant equalities: when a
    /// variable's EQC contains a concrete string, the constant witness is
    /// still relevant conflict context even if the structural NF deps are
    /// trivial.
    fn build_explanation_strict(
        terms: &TermStore,
        nf: &NormalForm,
        state: &SolverState,
    ) -> Option<Vec<TheoryLit>> {
        let mut explanation = Vec::new();
        let mut seen = HashSet::default();
        for dep in &nf.deps {
            if dep.lhs == dep.rhs {
                continue;
            }
            let dep_expl = state.explain(dep.lhs, dep.rhs);
            if dep_expl.is_empty() {
                return None;
            }
            Self::extend_dedup(&mut explanation, &mut seen, dep_expl);
        }

        for &component in &nf.base {
            // Augment 1 (#6273): component → string constant.
            // When a variable's EQC contains a constant, the merge equality
            // is essential for conflict clause soundness. Without it,
            // `process_simple_neq` Case 5 produces empty explanations for
            // conflicts involving variable-resolved constants → false-UNSAT.
            if let Some(const_tid) = state.find_constant_term_id(terms, component) {
                if component != const_tid {
                    Self::extend_dedup(
                        &mut explanation,
                        &mut seen,
                        state.explain(component, const_tid),
                    );
                }
            }
        }
        if let Some(rep) = nf.rep {
            if let Some(const_tid) = state.find_constant_term_id(terms, rep) {
                if rep != const_tid {
                    Self::extend_dedup(&mut explanation, &mut seen, state.explain(rep, const_tid));
                }
            }
        }
        Some(explanation)
    }

    /// Strict version of `build_pair_explanation`: returns `None` when
    /// either NF has an unexplainable non-trivial dep, or when the combined
    /// explanation is empty (no guards → vacuously-blocking → false-UNSAT).
    ///
    /// When `allow_one_sided` is false, also returns `None` for one-sided
    /// explanations where only one NF contributes literals. Those clauses are
    /// often too narrow (e.g. a single VarSplit literal) and can cause false
    /// UNSAT; treat them as incomplete so the solver can continue searching for
    /// a complete explanation.
    ///
    /// For conflict callers only (#3826, #4025).
    pub(super) fn build_pair_explanation_strict(
        terms: &TermStore,
        nf1: &NormalForm,
        nf2: &NormalForm,
        state: &SolverState,
        allow_one_sided: bool,
    ) -> Option<Vec<TheoryLit>> {
        let mut explanation = Self::build_explanation_strict(terms, nf1, state)?;
        let other = Self::build_explanation_strict(terms, nf2, state)?;
        if !allow_one_sided && explanation.is_empty() != other.is_empty() {
            return None;
        }
        let mut seen: HashSet<TheoryLit> = explanation.iter().copied().collect();
        Self::extend_dedup(&mut explanation, &mut seen, other);
        // Reject empty explanations (#6273): without any guard literals,
        // the conflict clause would block valid assignments → false-UNSAT.
        // Variable-heavy NFs can produce empty explanations when all deps
        // are trivial and augmentation finds nothing.
        if explanation.is_empty() {
            return None;
        }
        Some(explanation)
    }

    /// Build the explanation contributed by one NF for guarded lemmas.
    ///
    /// This is the per-side building block for
    /// `build_pair_explanation_for_lemma`: it validates non-trivial deps
    /// strictly, then augments with component/rep-to-constant equalities so
    /// trivial deps still pick up the SAT-level literals that justified the
    /// current NF alignment.
    fn build_nf_explanation_for_lemma_side(
        terms: &TermStore,
        nf: &NormalForm,
        state: &SolverState,
    ) -> Option<Vec<TheoryLit>> {
        let mut explanation = Vec::new();
        let mut seen = HashSet::default();
        for dep in &nf.deps {
            if dep.lhs == dep.rhs {
                continue;
            }
            let dep_expl = state.explain(dep.lhs, dep.rhs);
            // Strict: if a non-trivial dep is unexplainable, the NF alignment
            // context can't be properly guarded. Return None to block lemma
            // emission and avoid under-guarded clauses → false-UNSAT (#6273).
            if dep_expl.is_empty() {
                return None;
            }
            Self::extend_dedup(&mut explanation, &mut seen, dep_expl);
        }

        for &component in &nf.base {
            // Augment 1: component → string constant (existing)
            if let Some(const_tid) = state.find_constant_term_id(terms, component) {
                if component != const_tid {
                    Self::extend_dedup(
                        &mut explanation,
                        &mut seen,
                        state.explain(component, const_tid),
                    );
                }
            }
            // Augment 2 (#6273): component → EQC representative.
            // When the NF computation flattened through this component's EQC,
            // the merge equalities are essential guards. Without them, variable-
            // heavy formulas produce vacuous lemma guards → false-UNSAT.
            let comp_rep = state.find(component);
            if comp_rep != component {
                let rep_expl = state.explain(component, comp_rep);
                if !rep_expl.is_empty() {
                    Self::extend_dedup(&mut explanation, &mut seen, rep_expl);
                }
            }
        }
        if let Some(rep) = nf.rep {
            if let Some(const_tid) = state.find_constant_term_id(terms, rep) {
                if rep != const_tid {
                    Self::extend_dedup(&mut explanation, &mut seen, state.explain(rep, const_tid));
                }
            }
            // Augment 2 for rep (#6273): same pattern.
            let rep_rep = state.find(rep);
            if rep_rep != rep {
                let rr_expl = state.explain(rep, rep_rep);
                if !rr_expl.is_empty() {
                    Self::extend_dedup(&mut explanation, &mut seen, rr_expl);
                }
            }
        }

        Some(explanation)
    }

    /// Build a guarded explanation for lemma clauses (ConstSplit, VarSplit,
    /// LengthSplit, ConstUnify).
    ///
    /// Like `build_pair_explanation_strict`, this validates that all non-trivial
    /// NF deps are explainable. Additionally, it augments with component→constant
    /// equalities from the proof forest (like `build_pair_explanation`). This
    /// ensures that even when NF structural deps are trivial (lhs==rhs), the
    /// explanation includes the decision-level literals that justify the NF
    /// alignment.
    ///
    /// Returns `None` when:
    /// - Any non-trivial dep has an empty explanation (proof forest gap)
    /// - The final explanation is empty after augmentation and the NF pair is
    ///   not dependency-free (no guards → vacuously true lemma → false-UNSAT,
    ///   #6273)
    pub(super) fn build_pair_explanation_for_lemma(
        terms: &TermStore,
        nf1: &NormalForm,
        nf2: &NormalForm,
        state: &SolverState,
    ) -> Option<Vec<TheoryLit>> {
        let mut explanation = Self::build_nf_explanation_for_lemma_side(terms, nf1, state)?;
        let other = Self::build_nf_explanation_for_lemma_side(terms, nf2, state)?;
        let mut seen: HashSet<TheoryLit> = explanation.iter().copied().collect();
        Self::extend_dedup(&mut explanation, &mut seen, other);

        // When structural deps contributed nothing, try the main equality
        // between the NF source terms before falling back to empty guards.
        // This matches cvc5's "base term equality" explanation pattern for NF
        // alignment and keeps #6273 guarded when an actual merge trail exists.
        if explanation.is_empty() {
            if let (Some(src1), Some(src2)) = (nf1.source, nf2.source) {
                if src1 != src2 && state.find(src1) == state.find(src2) {
                    if let Some(eq_tid) = terms.find_eq(src1, src2) {
                        let guard = TheoryLit::new(eq_tid, true);
                        if seen.insert(guard) {
                            explanation.push(guard);
                        }
                    }
                }
            }
            // Some NF pairs are structurally dependency-free: the NF was built
            // without any EQC merges, so there is nothing to guard. Keep the
            // #6273 rejection for all other empty-explanation cases.
            if explanation.is_empty() && !(nf1.deps.is_empty() && nf2.deps.is_empty()) {
                return None;
            }
        }

        Some(explanation)
    }

    /// Build an enriched explanation for NF-vs-constant conflicts.
    ///
    /// `build_explanation` only collects NF structural deps (concat→rep
    /// equalities). When those deps are trivial (lhs==rhs), it falls back to
    /// `state.assertions()` — a sound but overly broad over-approximation.
    /// This function instead augments with targeted component→constant
    /// equalities from the proof forest, which produce more discriminating
    /// conflict clauses.
    ///
    /// Returns `None` if the enriched explanation is still empty (caller
    /// should return `NfCheckResult::Incomplete` to avoid false UNSAT).
    pub(super) fn build_nf_vs_constant_explanation(
        terms: &TermStore,
        nf: &NormalForm,
        state: &SolverState,
    ) -> Option<Vec<TheoryLit>> {
        let mut explanation = Vec::new();
        let mut seen = HashSet::default();
        for dep in &nf.deps {
            Self::extend_dedup(&mut explanation, &mut seen, state.explain(dep.lhs, dep.rhs));
        }

        // Augment with component→constant equalities from the proof forest.
        for &component in &nf.base {
            if let Some(const_tid) = state.find_constant_term_id(terms, component) {
                if component != const_tid {
                    Self::extend_dedup(
                        &mut explanation,
                        &mut seen,
                        state.explain(component, const_tid),
                    );
                }
            }
        }

        // Also explain why the rep equals its constant (if applicable).
        if let Some(rep) = nf.rep {
            if let Some(const_tid) = state.find_constant_term_id(terms, rep) {
                if rep != const_tid {
                    Self::extend_dedup(&mut explanation, &mut seen, state.explain(rep, const_tid));
                }
            }
        }

        if *DEBUG_STRING_CORE {
            eprintln!("[STRING_CORE] build_nf_vs_constant_explanation: deps={} base={} explanation_len={} rep={:?}",
                nf.deps.len(), nf.base.len(), explanation.len(), nf.rep);
            if let Some(rep) = nf.rep {
                let const_tid = state.find_constant_term_id(terms, rep);
                eprintln!(
                    "[STRING_CORE]   rep_const_tid={:?} rep_eq_const={}",
                    const_tid,
                    const_tid.is_none_or(|c| rep == c)
                );
                if let Some(c) = const_tid {
                    if rep != c {
                        let rep_expl = state.explain(rep, c);
                        eprintln!("[STRING_CORE]   rep_explain_len={}", rep_expl.len());
                    }
                }
            }
            for (i, dep) in nf.deps.iter().enumerate() {
                let dep_expl = state.explain(dep.lhs, dep.rhs);
                eprintln!(
                    "[STRING_CORE]   dep[{}]: {:?} -> {:?} (explain_len={})",
                    i,
                    dep.lhs,
                    dep.rhs,
                    dep_expl.len()
                );
            }
        }
        if explanation.is_empty() {
            None
        } else {
            Some(explanation)
        }
    }

    /// Extract a string constant value from a term directly.
    pub(super) fn get_string_constant(terms: &TermStore, t: TermId) -> Option<&str> {
        match terms.get(t) {
            TermData::Const(Constant::String(s)) => Some(s.as_str()),
            _ => None,
        }
    }
}
