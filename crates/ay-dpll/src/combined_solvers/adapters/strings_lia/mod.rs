// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// #8529: Use deterministic hash sets in all builds.
use ay_core::kani_compat::DetHashSet as HashSet;
use ay_core::{Sort, TermId, TermStore, TheoryLit, TheoryPropagation, TheoryResult, TheorySolver};
use ay_euf::{EufModel, EufSolver};
use ay_lia::{LiaModel, LiaSolver};
use ay_strings::StringModel;

use crate::combined_solvers::check_loops::{
    assert_fixpoint_convergence, debug_nelson_oppen, defer_non_local_result,
};
use crate::combined_solvers::interface_bridge::{lia_get_int_value_with_reasons, InterfaceBridge};
use crate::term_helpers::contains_arithmetic_ops;

/// Combined Strings + EUF + LIA theory solver for QF_SLIA.
///
/// Wraps `StringSolver`, `EufSolver`, and `LiaSolver` with Nelson-Oppen
/// style theory combination. The StringSolver handles string equalities
/// and disequalities. LIA handles integer arithmetic including `str.len`
/// terms (which LIA treats as opaque Int variables). EUF handles
/// congruence reasoning. Length axioms are injected by the executor
/// before Tseitin encoding.
pub(crate) struct StringsLiaSolver<'a> {
    terms: &'a TermStore,
    strings: ay_strings::StringSolver<'a>,
    euf: EufSolver<'a>,
    lia: LiaSolver<'a>,
    /// Shared Nelson-Oppen interface term tracking (#3788).
    interface: InterfaceBridge,
    /// Scope depth counter for push/pop symmetry checking (#4995).
    scope_depth: usize,
}

fn equality_propagation_conflict_result(
    conflict: Vec<TheoryLit>,
    label: &'static str,
) -> TheoryResult {
    if !conflict.is_empty() {
        return TheoryResult::Unsat(conflict);
    }

    // A theory reported a conflict but with zero reasons. Treat this as
    // incomplete rather than silently dropping the conflict.
    tracing::warn!(
        "BUG: {label} propagate_equalities returned conflict with 0 reasons — \
         returning Unknown instead of silently dropping"
    );
    TheoryResult::Unknown
}

impl<'a> StringsLiaSolver<'a> {
    pub(crate) fn new(terms: &'a TermStore) -> Self {
        let mut lia = LiaSolver::new(terms);
        lia.set_combined_theory_mode(true);
        Self {
            terms,
            strings: ay_strings::StringSolver::new(terms),
            euf: EufSolver::new(terms),
            lia,
            interface: InterfaceBridge::new(),
            scope_depth: 0,
        }
    }

    /// Pre-register the empty string term in the inner string solver.
    pub(crate) fn set_empty_string_id(&mut self, id: TermId) {
        self.strings.set_empty_string_id(id);
    }

    /// Mark a term as having been reduced via DPLL-level reduction lemmas.
    pub(crate) fn mark_reduced(&mut self, term: TermId) {
        self.strings.mark_reduced(term);
    }

    /// Extract EUF, LIA, and String models for model generation.
    pub(crate) fn extract_all_models(&mut self) -> (EufModel, Option<LiaModel>, StringModel) {
        let euf_model = self.euf.extract_model();
        let lia_model = self.lia.extract_model();
        let string_model = self.strings.extract_model();
        (euf_model, lia_model, string_model)
    }

    #[cfg(test)]
    pub(crate) fn has_interface_term(&self, term: TermId) -> bool {
        self.interface.contains_arith_term(&term)
    }

    #[cfg(test)]
    pub(crate) fn sorted_interface_terms(&self) -> Vec<TermId> {
        self.interface.sorted_arith_terms()
    }

    /// Replay learned LIA cuts into the freshly-created theory.
    pub(crate) fn replay_learned_cuts(&mut self) {
        self.lia.replay_learned_cuts();
    }

    /// Extract warm state from the inner string solver for cross-iteration
    /// preservation (#3762). This captures statistics and reduced-term markers.
    pub(crate) fn take_string_warm_state(&self) -> ay_strings::StringSolverWarmState {
        self.strings.take_warm_state()
    }

    /// Import warm state into the inner string solver from a previous
    /// CEGAR iteration (#3762).
    pub(crate) fn import_string_warm_state(&mut self, state: &ay_strings::StringSolverWarmState) {
        self.strings.import_warm_state(state);
    }

    /// Identity accessor for macro compatibility (mirrors LiraSolver/AufLiraSolver pattern).
    #[expect(dead_code, reason = "used by incremental split-loop conflict macros")]
    pub(crate) fn lra_solver(&self) -> &Self {
        self
    }

    /// Collect all bound conflicts from the inner LIA solver.
    #[expect(dead_code, reason = "used by incremental split-loop conflict macros")]
    pub(crate) fn collect_all_bound_conflicts(
        &self,
        skip_first: bool,
    ) -> Vec<ay_core::TheoryConflict> {
        self.lia.collect_all_bound_conflicts(skip_first)
    }

    /// Export learned LIA state (Gomory cuts, HNF cuts) for cross-iteration persistence.
    pub(crate) fn take_learned_state(
        &mut self,
    ) -> (Vec<ay_lia::StoredCut>, HashSet<ay_lia::HnfCutKey>) {
        self.lia.take_learned_state()
    }

    /// Import learned LIA state from a previous iteration.
    pub(crate) fn import_learned_state(
        &mut self,
        cuts: Vec<ay_lia::StoredCut>,
        seen: HashSet<ay_lia::HnfCutKey>,
    ) {
        self.lia.import_learned_state(cuts, seen);
    }

    /// Export Diophantine solver state for cross-iteration persistence.
    pub(crate) fn take_dioph_state(&mut self) -> ay_lia::DiophState {
        self.lia.take_dioph_state()
    }

    /// Import Diophantine solver state from a previous iteration.
    pub(crate) fn import_dioph_state(&mut self, state: ay_lia::DiophState) {
        self.lia.import_dioph_state(state);
    }

    /// Drop model-equality requests over non-arithmetic terms.
    ///
    /// `LiaSolver` treats every term it sees — including String-sorted
    /// concat/variable terms reached via `str.len` interface bridging — as an
    /// opaque rational. When two such opaque terms happen to share an internal
    /// value, the arithmetic solver emits a `NeedModelEqualities` request asking
    /// the DPLL layer to `assume_eq` them. For String-sorted terms this is
    /// spurious: their equality/disequality is *owned* by the string theory,
    /// whose EQC partition is already propagated to LIA as shared
    /// (dis)equalities. Echoing those equalities back into the SAT/assume-eq
    /// machinery just spins the model-equality loop until its round budget is
    /// exhausted, downgrading genuinely-SAT instances (e.g. `x++y="ab"` with a
    /// length bound) to `unknown`.
    ///
    /// Soundness: keeping only `Int`/`Real`-sorted requests cannot mask a real
    /// disagreement. Non-arithmetic equalities that matter for the combined
    /// model are decided by EUF/strings and propagated through
    /// `assert_shared_equality`; LIA never needs to branch on them. Arithmetic
    /// model equalities (the only ones relevant to LIA's own convexity) are
    /// preserved unchanged.
    /// Whether an expression-split disequality term compares String-sorted
    /// operands (extf wave 2). Such disequalities are owned by the string
    /// theory's NF disequality machinery; the LIA layer sees the operands as
    /// opaque constants with default-equal values and would request a
    /// numeric `<`/`>` split that cannot be built for strings (the DPLL(T)
    /// layer would fail closed to Unknown).
    fn string_sorted_disequality(&self, disequality_term: TermId) -> bool {
        let atom = match self.terms.get(disequality_term) {
            ay_core::term::TermData::Not(inner) => *inner,
            _ => disequality_term,
        };
        match self.terms.get(atom) {
            ay_core::term::TermData::App(sym, args)
                if (sym.name() == "=" || sym.name() == "distinct") && args.len() == 2 =>
            {
                *self.terms.sort(args[0]) == Sort::String
                    || *self.terms.sort(args[1]) == Sort::String
            }
            _ => false,
        }
    }

    /// Whether a single-variable disequality-split request targets a
    /// String-sorted term (see [`Self::string_sorted_disequality`]).
    fn string_sorted_split_variable(&self, variable: TermId) -> bool {
        *self.terms.sort(variable) == Sort::String
    }

    fn arithmetic_model_equalities(
        &self,
        eqs: &[ay_core::ModelEqualityRequest],
    ) -> Vec<ay_core::ModelEqualityRequest> {
        eqs.iter()
            .filter(|eq| {
                matches!(self.terms.sort(eq.lhs), Sort::Int | Sort::Real)
                    && matches!(self.terms.sort(eq.rhs), Sort::Int | Sort::Real)
            })
            .cloned()
            .collect()
    }
}

impl TheorySolver for StringsLiaSolver<'_> {
    fn register_atom(&mut self, atom: TermId) {
        self.lia.register_atom(atom);
    }

    fn assert_literal(&mut self, literal: TermId, value: bool) {
        self.euf.assert_literal(literal, value);
        self.strings.assert_literal(literal, value);
        if contains_arithmetic_ops(self.terms, literal)
            || crate::term_helpers::contains_string_ops(self.terms, literal)
        {
            self.lia.assert_literal(literal, value);
        }
        // Track interface terms from all literals, including negated equalities (#4767).
        self.interface.track_interface_term(self.terms, literal);
        self.interface.collect_int_constants(self.terms, literal);
    }

    fn check(&mut self) -> TheoryResult {
        let debug = debug_nelson_oppen();

        #[cfg(debug_assertions)]
        if crate::theory_debug_flags::debug_lia_only() {
            return self.lia.check();
        }

        // Check strings first for string-level conflicts.
        let str_result = self.strings.check();
        let mut strings_incomplete = matches!(&str_result, TheoryResult::Unknown);
        if debug {
            safe_eprintln!(
                "[SLIA check] strings.check() => {:?}",
                match &str_result {
                    TheoryResult::Sat => "Sat".to_string(),
                    TheoryResult::Unsat(r) => format!("Unsat({} reasons)", r.len()),
                    TheoryResult::Unknown => "Unknown".to_string(),
                    TheoryResult::NeedStringLemma(l) => format!("NeedStringLemma({:?})", l.kind),
                    TheoryResult::NeedLemmas(_) => "NeedLemmas".to_string(),
                    TheoryResult::NeedSplit(_) => "NeedSplit".to_string(),
                    TheoryResult::NeedDisequalitySplit(_) => "NeedDisequalitySplit".to_string(),
                    TheoryResult::NeedExpressionSplit(_) => "NeedExpressionSplit".to_string(),
                    TheoryResult::NeedExpressionSplits(_) => "NeedExpressionSplits".to_string(),
                    TheoryResult::UnsatWithFarkas(_) => "UnsatWithFarkas".to_string(),
                    TheoryResult::NeedModelEquality(_) | TheoryResult::NeedModelEqualities(_) =>
                        "NeedModelEquality".to_string(),
                    // All current TheoryResult variants handled above (#4906, #6149).
                    // Wildcard covers future variants from #[non_exhaustive].
                    _ => unreachable!("unhandled TheoryResult variant — update this match"),
                }
            );
        }
        match &str_result {
            TheoryResult::Unsat(reasons) => {
                if self.strings.is_ground_conflict() || self.strings.is_cycle_based_conflict() {
                    // Ground conflicts (constant mismatches, extf predicate
                    // evaluation) and cycle-based conflicts (I_CYCLE: x=y++x
                    // → y="") are always trustworthy — return immediately.
                    // Cycle detection is a sound inference rule (CVC5
                    // STRINGS_I_CYCLE), so NF conflicts derived from
                    // cycle-inferred equalities are reliable (#3875).
                    return TheoryResult::Unsat(reasons.clone());
                }
                // Soundness guard (#6261, #6275): NF-dependent conflicts from
                // process_simple_neq can be spurious on multi-variable word
                // equations. Treat as Unknown so the CEGAR loop adds split
                // lemmas until the conflict is provable at the SAT level.
                strings_incomplete = true;
            }
            TheoryResult::Unknown | TheoryResult::Sat => {}
            TheoryResult::NeedStringLemma(_) => {
                let lia_result = self.lia.check();
                match &lia_result {
                    TheoryResult::Unsat(reasons) => return TheoryResult::Unsat(reasons.clone()),
                    TheoryResult::UnsatWithFarkas(conflict) => {
                        return TheoryResult::UnsatWithFarkas(conflict.clone())
                    }
                    TheoryResult::Sat
                    | TheoryResult::Unknown
                    | TheoryResult::NeedSplit(_)
                    | TheoryResult::NeedDisequalitySplit(_)
                    | TheoryResult::NeedExpressionSplit(_)
                    | TheoryResult::NeedExpressionSplits(_)
                    | TheoryResult::NeedStringLemma(_)
                    | TheoryResult::NeedLemmas(_)
                    | TheoryResult::NeedModelEquality(_)
                    | TheoryResult::NeedModelEqualities(_) => return str_result,
                    // All current TheoryResult variants handled above (#4906, #6149, #6303).
                    // Wildcard covers future variants from #[non_exhaustive].
                    _ => unreachable!("unhandled TheoryResult variant — update this match"),
                }
            }
            TheoryResult::NeedSplit(_)
            | TheoryResult::NeedDisequalitySplit(_)
            | TheoryResult::NeedExpressionSplit(_)
            | TheoryResult::NeedExpressionSplits(_)
            | TheoryResult::NeedLemmas(_)
            | TheoryResult::UnsatWithFarkas(_)
            | TheoryResult::NeedModelEquality(_)
            | TheoryResult::NeedModelEqualities(_) => return str_result,
            // All current TheoryResult variants handled above (#4906, #6149, #6303).
            // Wildcard covers future variants from #[non_exhaustive].
            _ => unreachable!("unhandled TheoryResult variant — update this match"),
        }

        const MAX_ITERATIONS: usize = 100;
        // #8319: AY_MAX_FIXPOINT_ROUNDS caps the N-O loop for debugging.
        let max_iters = crate::theory_debug_flags::max_fixpoint_rounds()
            .unwrap_or(MAX_ITERATIONS)
            .min(MAX_ITERATIONS);

        for iteration in 0..max_iters {
            let lia_result = self.lia.check();
            let lia_is_unknown = matches!(&lia_result, TheoryResult::Unknown);
            if debug {
                safe_eprintln!(
                    "[SLIA check] N-O iter {}: lia.check() => {:?}",
                    iteration,
                    match &lia_result {
                        TheoryResult::Sat => "Sat".to_string(),
                        TheoryResult::Unsat(r) => format!("Unsat({} reasons)", r.len()),
                        TheoryResult::Unknown => "Unknown".to_string(),
                        TheoryResult::UnsatWithFarkas(_) => "UnsatWithFarkas".to_string(),
                        _ => format!("{:?}", "other"),
                    }
                );
            }
            match &lia_result {
                TheoryResult::Unsat(reasons) => return TheoryResult::Unsat(reasons.clone()),
                TheoryResult::UnsatWithFarkas(conflict) => {
                    return TheoryResult::UnsatWithFarkas(conflict.clone())
                }
                TheoryResult::Unknown => {}
                TheoryResult::NeedSplit(split) => return TheoryResult::NeedSplit(split.clone()),
                TheoryResult::NeedDisequalitySplit(split) => {
                    // Drop splits over String-sorted variables — string
                    // disequalities are owned by the string theory (NF deq
                    // checking); the LIA layer only sees them as opaque
                    // constants with default-equal values, so its split
                    // request is spurious (mirrors the NeedModelEquality
                    // filtering below; extf wave 2).
                    if !self.string_sorted_split_variable(split.variable) {
                        return TheoryResult::NeedDisequalitySplit(split.clone());
                    }
                }
                TheoryResult::NeedExpressionSplit(split) => {
                    if !self.string_sorted_disequality(split.disequality_term) {
                        return TheoryResult::NeedExpressionSplit(split.clone());
                    }
                    // String-sorted disequality — owned by the string theory.
                    // Treat LIA as Sat for this round and continue N-O.
                }
                TheoryResult::NeedExpressionSplits(splits) => {
                    let filtered: Vec<_> = splits
                        .iter()
                        .filter(|s| !self.string_sorted_disequality(s.disequality_term))
                        .cloned()
                        .collect();
                    if !filtered.is_empty() {
                        return TheoryResult::NeedExpressionSplits(filtered);
                    }
                    // All requests were String-sorted — owned by the string
                    // theory. Continue the N-O loop.
                }
                TheoryResult::NeedStringLemma(lemma) => {
                    return TheoryResult::NeedStringLemma(lemma.clone())
                }
                TheoryResult::NeedLemmas(lemmas) => {
                    return TheoryResult::NeedLemmas(lemmas.clone())
                }
                TheoryResult::NeedModelEquality(eq) => {
                    // Drop model equalities over non-arithmetic (String) terms
                    // owned by the string theory; only arithmetic ones need a
                    // SAT-level assume_eq decision (see arithmetic_model_equalities).
                    let filtered = self.arithmetic_model_equalities(std::slice::from_ref(eq));
                    if let Some(arith_eq) = filtered.into_iter().next() {
                        return TheoryResult::NeedModelEquality(arith_eq);
                    }
                    // String-sorted request — already decided by the string
                    // theory. Treat LIA as Sat for this round and continue N-O.
                }
                TheoryResult::NeedModelEqualities(eqs) => {
                    let filtered = self.arithmetic_model_equalities(eqs);
                    if !filtered.is_empty() {
                        return TheoryResult::NeedModelEqualities(filtered);
                    }
                    // All requests were String-sorted — owned by the string
                    // theory. Continue the N-O loop instead of spinning the
                    // model-equality budget on spurious opaque-real equalities.
                }
                TheoryResult::Sat => {}
                // All current TheoryResult variants handled above (#4906, #6149).
                // Wildcard covers future variants from #[non_exhaustive].
                _ => unreachable!("unhandled TheoryResult variant — update this match"),
            }

            // Propagate equalities from LIA to EUF and Strings.
            let eq_result = self.lia.propagate_equalities();
            if let Some(conflict) = eq_result.conflict {
                return equality_propagation_conflict_result(conflict, "SLIA LIA");
            }
            let mut has_new_equalities = !eq_result.equalities.is_empty();
            if debug && has_new_equalities {
                safe_eprintln!(
                    "[SLIA N-O] Iteration {}: LIA discovered {} equalities",
                    iteration,
                    eq_result.equalities.len()
                );
            }
            for eq in eq_result.equalities {
                // Self-equality guard: propagate_equalities_to() checks this
                // centrally, but SLIA propagates directly to multiple targets.
                debug_assert!(
                    eq.lhs != eq.rhs,
                    "BUG: SLIA LIA propagated trivial self-equality ({:?} = {:?})",
                    eq.lhs,
                    eq.rhs
                );
                self.euf.assert_shared_equality(eq.lhs, eq.rhs, &eq.reason);
                self.strings
                    .assert_shared_equality(eq.lhs, eq.rhs, &eq.reason);
            }

            // Evaluate interface terms and propagate to EUF and Strings (#4068).
            // Bridge equalities now carry LIA tight-bound reasons when
            // available, improving proof provenance for conflict explanations.
            let lia = &self.lia;
            let (new_eqs, _speculative) = self.interface.evaluate_and_propagate(
                self.terms,
                &|t| lia_get_int_value_with_reasons(lia, t),
                debug,
                "SLIA",
            );
            for eq in &new_eqs {
                self.euf.assert_shared_equality(eq.lhs, eq.rhs, &eq.reason);
                self.strings
                    .assert_shared_equality(eq.lhs, eq.rhs, &eq.reason);
            }
            has_new_equalities |= !new_eqs.is_empty();

            // Check EUF.
            let euf_result = self.euf.check();
            match &euf_result {
                TheoryResult::Unsat(reasons) => return TheoryResult::Unsat(reasons.clone()),
                TheoryResult::Unknown => return TheoryResult::Unknown,
                TheoryResult::Sat => {}
                TheoryResult::NeedSplit(_)
                | TheoryResult::NeedDisequalitySplit(_)
                | TheoryResult::NeedExpressionSplit(_)
                | TheoryResult::NeedExpressionSplits(_)
                | TheoryResult::UnsatWithFarkas(_)
                | TheoryResult::NeedStringLemma(_)
                | TheoryResult::NeedLemmas(_)
                | TheoryResult::NeedModelEquality(_)
                | TheoryResult::NeedModelEqualities(_) => return euf_result,
                // All current TheoryResult variants handled above (#4906, #6149, #6303).
                // Wildcard covers future variants from #[non_exhaustive].
                _ => unreachable!("unhandled TheoryResult variant — update this match"),
            }

            // Propagate equalities from EUF to LIA and Strings.
            let euf_eq_result = self.euf.propagate_equalities();
            if let Some(conflict) = euf_eq_result.conflict {
                return equality_propagation_conflict_result(conflict, "SLIA EUF");
            }
            let has_euf_equalities = !euf_eq_result.equalities.is_empty();
            if debug && has_euf_equalities {
                safe_eprintln!(
                    "[SLIA N-O] Iteration {}: EUF discovered {} equalities",
                    iteration,
                    euf_eq_result.equalities.len()
                );
            }
            for eq in euf_eq_result.equalities {
                // Self-equality guard: matches propagate_equalities_to() invariant.
                debug_assert!(
                    eq.lhs != eq.rhs,
                    "BUG: SLIA EUF propagated trivial self-equality ({:?} = {:?})",
                    eq.lhs,
                    eq.rhs
                );
                // #7451: Sort-filter EUF→LIA propagation. EUF is sort-agnostic
                // and can discover equalities between terms of any sort (e.g.,
                // String = String from congruence closure). Sending these to LIA
                // causes LIA to misinterpret non-arithmetic terms as opaque
                // variables with value 0, producing spurious cross-sort
                // equalities (e.g., x:String = 0:Int) that cause false UNSAT.
                // Only propagate Int/Real-sorted equalities to LIA.
                let lhs_sort = self.terms.sort(eq.lhs);
                if matches!(lhs_sort, Sort::Int | Sort::Real) {
                    self.lia.assert_shared_equality(eq.lhs, eq.rhs, &eq.reason);
                }
                self.strings
                    .assert_shared_equality(eq.lhs, eq.rhs, &eq.reason);
            }

            // Re-check strings after N-O equality propagation.
            if has_new_equalities || has_euf_equalities {
                let str_recheck = self.strings.check();
                if debug {
                    safe_eprintln!(
                        "[SLIA check] strings re-check => {:?}",
                        match &str_recheck {
                            TheoryResult::Sat => "Sat".to_string(),
                            TheoryResult::Unsat(r) => format!("Unsat({} reasons)", r.len()),
                            TheoryResult::Unknown => "Unknown".to_string(),
                            TheoryResult::NeedStringLemma(l) =>
                                format!("NeedStringLemma({:?})", l.kind),
                            TheoryResult::NeedLemmas(_) => "NeedLemmas".to_string(),
                            TheoryResult::NeedSplit(_) => "NeedSplit".to_string(),
                            TheoryResult::NeedDisequalitySplit(_) =>
                                "NeedDisequalitySplit".to_string(),
                            TheoryResult::NeedExpressionSplit(_) =>
                                "NeedExpressionSplit".to_string(),
                            TheoryResult::NeedExpressionSplits(_) =>
                                "NeedExpressionSplits".to_string(),
                            TheoryResult::UnsatWithFarkas(_) => "UnsatWithFarkas".to_string(),
                            TheoryResult::NeedModelEquality(_)
                            | TheoryResult::NeedModelEqualities(_) =>
                                "NeedModelEquality".to_string(),
                            // All current TheoryResult variants handled above (#4906, #6149).
                            // Wildcard covers future variants from #[non_exhaustive].
                            _ => unreachable!("unhandled TheoryResult variant — update this match"),
                        }
                    );
                }
                match &str_recheck {
                    TheoryResult::Unsat(reasons) => {
                        if self.strings.is_ground_conflict()
                            || self.strings.is_cycle_based_conflict()
                        {
                            // Ground and cycle-based conflicts after N-O
                            // propagation are trustworthy (#3875).
                            return TheoryResult::Unsat(reasons.clone());
                        }
                        // Soundness guard (#3826, #4068, #6275): NF-dependent
                        // string conflicts after N-O propagation may be spurious.
                        // Bridge-derived EQC merges can cause incorrect NF
                        // conflicts. Treat as Unknown; the CEGAR loop will add
                        // split lemmas until the conflict is provable.
                        strings_incomplete = true;
                    }
                    TheoryResult::Unknown => {
                        strings_incomplete = true;
                    }
                    TheoryResult::Sat => {
                        strings_incomplete = false;
                    }
                    TheoryResult::NeedStringLemma(lemma) => {
                        return TheoryResult::NeedStringLemma(lemma.clone())
                    }
                    TheoryResult::NeedLemmas(lemmas) => {
                        return TheoryResult::NeedLemmas(lemmas.clone())
                    }
                    TheoryResult::NeedSplit(_)
                    | TheoryResult::NeedDisequalitySplit(_)
                    | TheoryResult::NeedExpressionSplit(_)
                    | TheoryResult::NeedExpressionSplits(_)
                    | TheoryResult::UnsatWithFarkas(_)
                    | TheoryResult::NeedModelEquality(_)
                    | TheoryResult::NeedModelEqualities(_) => return str_recheck,
                    // All current TheoryResult variants handled above (#4906, #6149, #6303).
                    // Wildcard covers future variants from #[non_exhaustive].
                    _ => unreachable!("unhandled TheoryResult variant — update this match"),
                }
            }

            if !has_new_equalities && !has_euf_equalities {
                if debug && iteration > 0 {
                    safe_eprintln!("[SLIA N-O] Fixpoint after {} iterations", iteration + 1);
                }
                if strings_incomplete || lia_is_unknown {
                    return TheoryResult::Unknown;
                }
                assert_fixpoint_convergence("SLIA", &mut [&mut self.lia, &mut self.euf]);
                return TheoryResult::Sat;
            }

            // Monotonicity: non-fixpoint iterations must discover new equalities
            debug_assert!(
                has_new_equalities || has_euf_equalities,
                "BUG: SLIA N-O iteration {iteration} continued past fixpoint with 0 new equalities"
            );

            // Non-convergence is a solver bug — assert in all build modes.
            // Non-convergence within the fixpoint bound is a SOUND fallback, not
            // a crash: the loop ends and returns `TheoryResult::Unknown` below.
            // (Formerly a `did not converge` panic — an abort on a legitimate, if
            // pathological, instance; `unknown` is always sound. #8319: a capped
            // `--max-fixpoint-rounds` reaches the same fallback.)
        }

        TheoryResult::Unknown
    }

    /// BCP-time lightweight check: run each sub-theory's cheap check
    /// individually WITHOUT the Nelson-Oppen fixpoint loop (#8404).
    ///
    /// The full N-O loop (up to 100 iterations of Strings+EUF+LIA with
    /// cross-theory equality propagation and interface bridge evaluation)
    /// is deferred to `check()`, which runs at decision time and during
    /// the final SAT check. During BCP, only per-theory consistency
    /// checks are needed -- these catch contradictory bounds (LIA simplex
    /// with tight budget), ground string conflicts (constant mismatches),
    /// and congruence conflicts (EUF) without the expensive cross-theory
    /// equality propagation.
    ///
    /// Without this override, the default `check_during_propagate`
    /// delegates to `check()`, running the full N-O fixpoint on every
    /// BCP theory check. This is the same pattern fixed in UfSeqLiaSolver,
    /// UfSeqSolver, UfNiaSolver, and UfNraSolver (commit 5366c834c).
    fn check_during_propagate(&mut self) -> TheoryResult {
        // LIA: runs simplex with tight propagation budget + GCD test.
        let lia_result = defer_non_local_result(self.lia.check_during_propagate());
        if !matches!(lia_result, TheoryResult::Sat) {
            return lia_result;
        }

        // EUF: runs congruence closure check.
        let euf_result = defer_non_local_result(self.euf.check_during_propagate());
        if !matches!(euf_result, TheoryResult::Sat) {
            return euf_result;
        }

        // Strings.
        //
        // SOUNDNESS (#6261/#6275 parity with `check()`): `StringSolver` does
        // NOT override `check_during_propagate`, so the trait default runs the
        // FULL `check()` — normal-form computation included. The pre-existing
        // comment here claimed "ground conflict detection ... without full
        // normal-form computation"; that was false, and it meant this lane
        // returned NF-dependent conflicts UNGATED at BCP time while `check()`
        // (above) distrusts exactly those conflicts as potentially spurious on
        // multi-variable word equations. Same solver, same conflicts,
        // contradictory trust — a wrong-UNSAT vector, since a BCP-time theory
        // conflict becomes a conflict clause directly.
        //
        // Fail closed: only ground/cycle conflicts (always trustworthy, per
        // the `check()` rationale) may propagate from here. An untrusted
        // conflict degrades to `Sat` = "no conflict found at BCP time", which
        // is sound because `check_during_propagate` is permitted to be weaker
        // than `check()` and `needs_final_check_after_sat` is `true` (below):
        // the full, gated `check()` always runs before any SAT is accepted, so
        // a genuine conflict is still caught there — completeness of THIS
        // lane's early conflict detection is the only thing given up.
        let str_result = defer_non_local_result(self.strings.check_during_propagate());
        // NF-engine closure 5 precondition (now UNCONDITIONAL on main, and
        // strictly stronger than the closure-5 form: it also covers
        // `UnsatWithFarkas`): an NF-dependent string conflict found during BCP
        // must NOT become a learned SAT clause, because `check()` (lines
        // 267-283) would refuse to trust it — otherwise a propositional UNSAT
        // could rest on a conflict the solver itself distrusts. Degrading to
        // `Sat` here loses nothing: `needs_final_check_after_sat` forces a
        // full, gated `check()` before any SAT is accepted.
        match &str_result {
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
                if !(self.strings.is_ground_conflict()
                    || self.strings.is_cycle_based_conflict()) => {}
            _ if !matches!(str_result, TheoryResult::Sat) => return str_result,
            _ => {}
        }

        TheoryResult::Sat
    }

    /// Since `check_during_propagate` skips the Nelson-Oppen fixpoint, the
    /// eager path must run one final full `check()` before accepting SAT.
    fn needs_final_check_after_sat(&self) -> bool {
        true
    }

    fn propagate(&mut self) -> Vec<TheoryPropagation> {
        let mut props = self.strings.propagate();
        props.extend(self.euf.propagate());
        props.extend(self.lia.propagate());
        props
    }

    /// Forward the string theory's batched lemma queue (NF-engine closure 3).
    /// Only the string sub-solver produces string lemmas.
    fn take_pending_string_lemmas(&mut self) -> Vec<ay_core::StringLemma> {
        self.strings.take_pending_string_lemmas()
    }

    fn has_pending_propagations(&self) -> bool {
        self.strings.has_pending_propagations()
            || self.euf.has_pending_propagations()
            || self.lia.has_pending_propagations()
    }

    fn has_pending_analysis(&self) -> bool {
        self.strings.has_pending_analysis()
            || self.euf.has_pending_analysis()
            || self.lia.has_pending_analysis()
    }

    fn drain_pending_propagations(&mut self) -> Vec<TheoryPropagation> {
        let mut props = self.strings.drain_pending_propagations();
        props.extend(self.euf.drain_pending_propagations());
        props.extend(self.lia.drain_pending_propagations());
        props
    }

    fn supports_theory_aware_branching(&self) -> bool {
        self.lia.supports_theory_aware_branching()
    }

    fn suggest_phase(&self, atom: TermId) -> Option<bool> {
        self.lia.suggest_phase(atom)
    }

    fn sort_atom_index(&mut self) {
        self.lia.sort_atom_index();
    }

    fn generate_bound_axiom_terms(&self) -> Vec<(TermId, bool, TermId, bool)> {
        self.lia.generate_bound_axiom_terms()
    }

    fn generate_incremental_bound_axioms(&self, atom: TermId) -> Vec<(TermId, bool, TermId, bool)> {
        self.lia.generate_incremental_bound_axioms(atom)
    }

    fn push(&mut self) {
        self.scope_depth += 1;
        self.strings.push();
        self.euf.push();
        self.lia.push();
        self.interface.push();
    }

    fn pop(&mut self) {
        if self.scope_depth == 0 {
            // Graceful no-op: pop at depth 0 is a caller error but not fatal.
            return;
        }
        self.scope_depth -= 1;
        self.strings.pop();
        self.euf.pop();
        self.lia.pop();
        self.interface.pop();
    }

    fn reset(&mut self) {
        assert!(
            self.scope_depth == 0,
            "BUG: StringsLiaSolver::reset() called with non-zero scope depth {} (unbalanced push/pop)",
            self.scope_depth,
        );
        self.strings.reset();
        self.euf.reset();
        self.lia.reset();
        self.interface.reset();
    }

    fn soft_reset(&mut self) {
        assert!(
            self.scope_depth == 0,
            "BUG: StringsLiaSolver::soft_reset() called with non-zero scope depth {} (unbalanced push/pop)",
            self.scope_depth,
        );
        self.strings.soft_reset();
        self.euf.soft_reset();
        self.lia.soft_reset();
        self.interface.reset();
    }

    fn soft_reset_warm(&mut self) {
        assert!(
            self.scope_depth == 0,
            "BUG: StringsLiaSolver::soft_reset_warm() called with non-zero scope depth {} (unbalanced push/pop)",
            self.scope_depth,
        );
        self.strings.soft_reset();
        self.euf.soft_reset();
        self.lia.soft_reset_warm();
        self.interface.reset();
    }
}

#[allow(clippy::panic)]
#[cfg(test)]
mod tests;
