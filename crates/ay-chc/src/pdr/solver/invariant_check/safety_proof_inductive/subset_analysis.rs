// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Trust-sensitive analysis stages for the inductive-subset fast path.

use super::super::inductive_accept_core::lemma_admitted_inductive;
use super::*;
use ay_core::kani_compat::DetHashSet;

type CandidateLemma = (PredicateId, ChcExpr, bool);
type AdmittedLemma = (PredicateId, ChcExpr);

struct InductiveEvidence {
    inductive: Vec<AdmittedLemma>,
    strictly_inductive: Vec<AdmittedLemma>,
    all_inductive: bool,
    all_strictly_inductive: bool,
    any_sample_tainted: bool,
}

impl InductiveEvidence {
    fn new() -> Self {
        Self {
            inductive: Vec::new(),
            strictly_inductive: Vec::new(),
            all_inductive: true,
            all_strictly_inductive: true,
            any_sample_tainted: false,
        }
    }

    fn admit(&mut self, pred: PredicateId, formula: ChcExpr, strict: bool, tainted: bool) {
        self.inductive.push((pred, formula.clone()));
        if strict {
            self.strictly_inductive.push((pred, formula));
        }
        self.any_sample_tainted |= tainted;
    }
}

struct LemmaChecks {
    blocking: ChcExpr,
    strict: bool,
    inductive: bool,
    init_valid: bool,
    entry_inductive: bool,
}

impl PdrSolver {
    pub(super) fn evaluate_inductive_subset(
        &mut self,
        queries: &[HornClause],
        model: InvariantModel,
    ) -> InductiveSubsetOutcome {
        let is_multi_pred = self.problem.predicates().len() > 1;
        let lemmas = self.non_algebraic_candidates();
        if lemmas.is_empty() {
            return InductiveSubsetOutcome::Cascade(model);
        }

        let inconsistent = self.inconsistent_frame_predicates(&lemmas);
        let evidence = self.collect_inductive_evidence(&lemmas, &inconsistent, is_multi_pred);
        let no_bv_sorts = !self.problem.has_bv_sorts();

        if evidence.all_inductive {
            return self.all_inductive_outcome(model, lemmas.len(), no_bv_sorts, &evidence);
        }
        if let Some(outcome) =
            self.inductive_subset_outcome(queries, is_multi_pred, no_bv_sorts, &evidence)
        {
            return outcome;
        }
        Self::full_model_cascade(model)
    }

    fn non_algebraic_candidates(&self) -> Vec<CandidateLemma> {
        // The Boolean tag prevents relative-induction-only hints from being
        // mistaken for strict self-inductive evidence, independently of the
        // #8578 anti-vacuous guard in the underlying oracles.
        self.frames[1]
            .lemmas
            .iter()
            .filter(|lemma| !lemma.algebraically_verified)
            .map(|lemma| {
                (
                    lemma.predicate,
                    lemma.formula.clone(),
                    lemma.relative_induction_only,
                )
            })
            .collect()
    }

    fn inconsistent_frame_predicates(
        &mut self,
        lemmas: &[CandidateLemma],
    ) -> DetHashSet<PredicateId> {
        let mut inconsistent = DetHashSet::default();
        let mut checked = DetHashSet::default();
        for (pred, _, _) in lemmas {
            if !checked.insert(*pred) || !self.frame_predicate_is_inconsistent(*pred) {
                continue;
            }
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: check_invariants_prove_safety: frame[1] for pred {} is INCONSISTENT, using strict self-inductiveness",
                    pred.index()
                );
            }
            inconsistent.insert(*pred);
        }
        inconsistent
    }

    fn frame_predicate_is_inconsistent(&mut self, pred: PredicateId) -> bool {
        let frame_lemmas: Vec<ChcExpr> = self.frames[1]
            .lemmas
            .iter()
            .filter(|lemma| lemma.predicate == pred)
            .map(|lemma| lemma.formula.clone())
            .collect();
        if frame_lemmas.len() < 2 {
            return false;
        }

        // ROW-expand select/store so array lemmas with symbolic store indices
        // can be discharged through LIA+ITE reasoning (#8660 Phase 2b).
        let bounded = self
            .bound_int_vars(ChcExpr::and_all(frame_lemmas))
            .expand_select_store_symbolic();
        self.smt.reset();
        matches!(
            self.smt
                .check_sat_with_timeout(&bounded, std::time::Duration::from_millis(200)),
            SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_)
        )
    }

    fn collect_inductive_evidence(
        &mut self,
        lemmas: &[CandidateLemma],
        inconsistent: &DetHashSet<PredicateId>,
        is_multi_pred: bool,
    ) -> InductiveEvidence {
        let mut evidence = InductiveEvidence::new();
        for (pred, formula, relative_only) in lemmas {
            let checks =
                self.check_candidate(*pred, formula, *relative_only, inconsistent, is_multi_pred);
            evidence.all_strictly_inductive &= checks.strict;
            if lemma_admitted_inductive(checks.inductive, checks.init_valid, checks.entry_inductive)
            {
                let tainted = !checks.strict && self.lemma_sample_tainted(*pred, &checks.blocking);
                evidence.admit(*pred, formula.clone(), checks.strict, tainted);
                continue;
            }

            evidence.all_inductive = false;
            if let Some((candidate, strict, tainted)) =
                self.try_disequality_repair(*pred, formula, &checks, inconsistent, is_multi_pred)
            {
                evidence.admit(*pred, candidate, strict, tainted);
            } else {
                self.log_rejected_candidate(*pred, formula, &checks);
            }
        }
        evidence
    }

    fn check_candidate(
        &mut self,
        pred: PredicateId,
        formula: &ChcExpr,
        relative_only: bool,
        inconsistent: &DetHashSet<PredicateId>,
        is_multi_pred: bool,
    ) -> LemmaChecks {
        let blocking = ChcExpr::not(formula.clone());
        let strict = !relative_only && self.is_strictly_self_inductive_blocking(&blocking, pred);
        let inductive = if relative_only {
            false
        } else if strict {
            true
        } else if !inconsistent.contains(&pred) {
            self.is_self_inductive_blocking(&blocking, pred)
        } else {
            false
        };
        let init_valid =
            !self.predicate_has_facts(pred) || self.blocks_initial_states(pred, &blocking);
        let entry_inductive = !is_multi_pred || self.is_entry_inductive(formula, pred, 1);
        LemmaChecks {
            blocking,
            strict,
            inductive,
            init_valid,
            entry_inductive,
        }
    }

    fn try_disequality_repair(
        &mut self,
        pred: PredicateId,
        formula: &ChcExpr,
        checks: &LemmaChecks,
        inconsistent: &DetHashSet<PredicateId>,
        is_multi_pred: bool,
    ) -> Option<(ChcExpr, bool, bool)> {
        if !crate::pdr::solver::diseq_swap::diseq_swap_enabled()
            || !checks.init_valid
            || !checks.entry_inductive
            || checks.inductive
        {
            return None;
        }
        for candidate in crate::pdr::solver::diseq_swap::strict_disequality_repairs(formula) {
            let blocking = ChcExpr::not(candidate.clone());
            let strict = self.is_strictly_self_inductive_blocking(&blocking, pred);
            let inductive = strict
                || (!inconsistent.contains(&pred)
                    && self.is_self_inductive_blocking(&blocking, pred));
            let init_valid =
                !self.predicate_has_facts(pred) || self.blocks_initial_states(pred, &blocking);
            let entry_inductive = !is_multi_pred || self.is_entry_inductive(&candidate, pred, 1);
            if !inductive || !init_valid || !entry_inductive {
                continue;
            }

            self.add_lemma_to_frame(Lemma::new(pred, candidate.clone(), 1), 1);
            let tainted = !strict && self.lemma_sample_tainted(pred, &blocking);
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: diseq-swap repair recovered self-inductive variant for pred {}: {} (from {})",
                    pred.index(), candidate, formula
                );
            }
            return Some((candidate, strict, tainted));
        }
        None
    }

    fn log_rejected_candidate(&self, pred: PredicateId, formula: &ChcExpr, checks: &LemmaChecks) {
        if !self.config.verbose {
            return;
        }
        let reason = if !checks.inductive {
            "not self-inductive"
        } else if !checks.init_valid {
            "not init-valid"
        } else {
            "not entry-inductive"
        };
        safe_eprintln!(
            "PDR: check_invariants_prove_safety: non-algebraic lemma {} for pred {} {}",
            formula,
            pred.index(),
            reason
        );
    }

    fn all_inductive_outcome(
        &self,
        mut model: InvariantModel,
        lemma_count: usize,
        no_bv_sorts: bool,
        evidence: &InductiveEvidence,
    ) -> InductiveSubsetOutcome {
        // Sample-backed non-strict acceptance is heuristic evidence, so only
        // strict or complete Bool+Int reasoning may skip whole-model validation.
        model.individually_inductive =
            (evidence.all_strictly_inductive || no_bv_sorts) && !evidence.any_sample_tainted;
        if self.config.verbose {
            safe_eprintln!(
                "PDR: check_invariants_prove_safety: all {} non-algebraic lemmas individually inductive ({}-predicate, strictly_inductive={}, sample_tainted={}, individually_inductive={})",
                lemma_count,
                self.problem.predicates().len(),
                evidence.all_strictly_inductive,
                evidence.any_sample_tainted,
                model.individually_inductive,
            );
        }
        InductiveSubsetOutcome::Proven(model)
    }

    fn inductive_subset_outcome(
        &mut self,
        queries: &[HornClause],
        is_multi_pred: bool,
        no_bv_sorts: bool,
        evidence: &InductiveEvidence,
    ) -> Option<InductiveSubsetOutcome> {
        if evidence.inductive.is_empty() {
            return None;
        }
        let subset_model = self.build_model_from_algebraic_plus_inductive(1, &evidence.inductive);
        let subset_blocks = self.algebraic_model_blocks_all_errors(&subset_model, queries);
        if self.config.verbose {
            safe_eprintln!(
                "PDR: check_invariants_prove_safety: inductive-subset model ({} algebraic + {} inductive) blocks errors: {}",
                self.frames[1].lemmas.iter().filter(|lemma| lemma.algebraically_verified).count(),
                evidence.inductive.len(),
                subset_blocks
            );
        }

        if is_multi_pred && !evidence.all_strictly_inductive {
            if let Some(model) =
                self.try_error_guided_discovery(queries, &evidence.strictly_inductive)
            {
                return Some(InductiveSubsetOutcome::Proven(model));
            }
        }
        if !subset_blocks {
            return None;
        }
        if let Some(model) = self.strict_subset_model(queries, evidence) {
            return Some(InductiveSubsetOutcome::Proven(model));
        }
        Some(self.non_strict_subset_outcome(subset_model, is_multi_pred, no_bv_sorts, evidence))
    }

    fn strict_subset_model(
        &mut self,
        queries: &[HornClause],
        evidence: &InductiveEvidence,
    ) -> Option<InvariantModel> {
        if evidence.strictly_inductive.is_empty() {
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: no strictly-inductive lemmas found; cannot build strict subset"
                );
            }
            return None;
        }
        let all_strict = evidence.strictly_inductive.len() == evidence.inductive.len();
        let mut model =
            self.build_model_from_algebraic_plus_inductive(1, &evidence.strictly_inductive);
        let blocks = all_strict || self.algebraic_model_blocks_all_errors(&model, queries);
        if self.config.verbose {
            safe_eprintln!(
                "PDR: strictly-inductive-only subset ({} lemmas, all_strict={}) blocks errors: {}",
                evidence.strictly_inductive.len(),
                all_strict,
                blocks
            );
        }
        if !blocks {
            return None;
        }
        model.individually_inductive = true;
        Some(model)
    }

    fn non_strict_subset_outcome(
        &self,
        mut model: InvariantModel,
        is_multi_pred: bool,
        no_bv_sorts: bool,
        evidence: &InductiveEvidence,
    ) -> InductiveSubsetOutcome {
        let needs_bv_cascade = self.problem.has_bv_sorts()
            && self.problem.predicates().len() == 1
            && !evidence.all_strictly_inductive;
        if needs_bv_cascade {
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: single-predicate BV inductive-subset candidate is non-strict; forcing verification cascade (#7964)"
                );
            }
            return InductiveSubsetOutcome::Cascade(model);
        }
        // Multi-predicate LIA has cross-predicate entry-inductiveness as an
        // additional proof signal. Sample-tainted evidence still requires the
        // whole-model verification cascade (#8827).
        if no_bv_sorts && is_multi_pred && !evidence.any_sample_tainted {
            model.individually_inductive = true;
            return InductiveSubsetOutcome::Proven(model);
        }
        InductiveSubsetOutcome::Cascade(model)
    }

    /// The per-lemma subset can fail even when its conjunction is inductive:
    /// conjuncts may rely on each other for preservation. Passing the full
    /// frame model onward only widens what the bounded verification cascade
    /// attempts; it does not accept anything without checking every original
    /// clause, including cross-predicate edges.
    fn full_model_cascade(model: InvariantModel) -> InductiveSubsetOutcome {
        InductiveSubsetOutcome::Cascade(model)
    }
}
