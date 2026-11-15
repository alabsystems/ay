// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Step (4) of the deferred-trust discharge over the authored ground core
//! (#ground-core-corroboration).
//!
//! # The defect
//!
//! `authored_ground_core_refutes` accepts a quantified query's refutation when
//! the AUTHORED quantifier-free conjuncts refute on their own, then hands the
//! verdict to the ordinary publication funnel. When the ground refutation's
//! proof ends in a `trust` step (datatype and nested-array reasoning have no
//! strict rules), that funnel reaches step (4): re-decide the authored
//! obligation in a fresh `Executor`. The obligation it re-decided was the WHOLE
//! authored scope, universal included, so the fresh solve walked straight back
//! into `quantified_semantic_unsat_or_unknown`, whose ground-core probe then
//! needs a deferred-trust discharge of its own at depth 1 — which
//! `TRUST_DISCHARGE_DEPTH` refuses by design. The nested verdict downgraded,
//! step (4) declined, and a query that a fresh solve of its seven ground roots
//! refutes in milliseconds published `unknown(SelfCheckRejected)`. Measured on
//! `model_checker_consumer_quantified_counterexample/nested_query_false_unsat`.
//!
//! That row's core keeps arrays inside the datatype fields of an outer array's
//! elements, which is nested array state: once `StaticFeatures` resolved
//! declared carriers, the nested-array quarantine withholds its trust-only
//! refutation before step (4) is reached (#nested-array-quarantine-datatype-fields).
//! Step (4) still serves every nested-array-free core.
//!
//! # The repair, and why it only ever strengthens the evidence asked for
//!
//! When the ground-core leg refuted a core in THIS public solve, step (4)
//! re-decides that core first, and falls back to the ordinary scope unchanged
//! if the core does not reconfirm. Nothing else in the funnel moves: the
//! forged-UNSAT guard still re-decides the EXACT whole problem, every non-trust
//! step of the proof is still strict-validated, the per-clause discharge still
//! runs first, `unsat` from a fresh executor is still the only accepting
//! verdict, and the structural proof screen is the same one.
//!
//! Soundness does not depend on where the recorded core came from. It is used
//! only when every term is literally a premise of the strict-proof `problem`
//! the publication claims, so it is a SUBSET of that problem, and an
//! unsatisfiable subset refutes every superset (dropping hypotheses only
//! weakens). A stale, recycled or wrong core can therefore at worst fail to
//! reconfirm; it cannot make step (4) accept a satisfiable problem.
//!
//! It is also not the self-corroboration `#qsu-downgrade-is-load-bearing`
//! forbids. That concern is a nested solve re-running the same instantiation
//! heuristic on the same quantified problem. The core is required to be
//! quantifier-free, so the fresh solve instantiates nothing: it is exactly the
//! re-decision step (4) already performs for every ground trust-bearing proof.

use ay_core::{ProofId, TermId};

use super::{probe_cert_reject, Executor, WHOLE_PROBLEM_RECONFIRMATION_LIMITS};
use crate::api::proofs::TrustClauseDischargeControls;
use crate::ematching::contains_quantifier;
use crate::executor::UnsatCorroboration;

impl Executor {
    /// Step (4)'s fresh re-decisions, cheapest question first: the recorded
    /// authored ground core (when it is a quantifier-free subset of
    /// `problem`), then step (4a)'s entailment of the `deferred` clauses by
    /// `corroboration_scope` (`trust_clause_entailment`), then the ordinary
    /// `corroboration_scope` exactly as before. Names the arm that accepted.
    ///
    /// NOT an UNSAT reconfirmation of the scope on its own:
    /// `Some` of an [`UnsatCorroboration::entailment`] says only that the scope entails the
    /// `deferred` clauses, which a SATISFIABLE scope can do. It is evidence for
    /// the verdict only after step (2)'s collecting check validated every other
    /// step of the proof, which is why its one caller runs it there and
    /// nowhere else.
    ///
    /// Every re-decision runs under the certification's `controls`.
    pub(super) fn fresh_executor_corroboration(
        &self,
        problem: &[TermId],
        corroboration_scope: &[TermId],
        deferred: &[(ProofId, Vec<TermId>)],
        controls: &TrustClauseDischargeControls,
    ) -> Option<UnsatCorroboration> {
        if let Some(core) = self.ground_core_corroboration_scope(problem) {
            if self.reconfirms_unsat_under(&core, WHOLE_PROBLEM_RECONFIRMATION_LIMITS, controls) {
                probe_cert_reject(|| {
                    format!(
                        "RECONFIRM(4): the {}-root authored ground core re-decided UNSAT",
                        core.len()
                    )
                });
                return Some(UnsatCorroboration::resolve(self.strengthenings_applied()));
            }
        }
        if self.reconfirms_deferred_clause_entailment(corroboration_scope, deferred, controls) {
            return Some(UnsatCorroboration::entailment(
                self.strengthenings_applied(),
            ));
        }
        self.reconfirms_unsat_under(
            corroboration_scope,
            WHOLE_PROBLEM_RECONFIRMATION_LIMITS,
            controls,
        )
        .then(|| UnsatCorroboration::resolve(self.strengthenings_applied()))
    }

    /// The ground core `authored_ground_core_refutes` refuted in this public
    /// solve, when it is non-empty, quantifier-free, and every member is a
    /// premise of `problem` (or the export-stripped authored `false`, which
    /// `authored_corroboration_scope` readmits on the same terms).
    pub(super) fn ground_core_corroboration_scope(
        &self,
        problem: &[TermId],
    ) -> Option<Vec<TermId>> {
        let core = self.authored_ground_core_refutation.as_deref()?;
        let readmitted = self.export_stripped_authored_false();
        let claimed = |term: &TermId| problem.contains(term) || readmitted == Some(*term);
        let quantifier_free = |term: &TermId| !contains_quantifier(&self.ctx.terms, *term);
        (!core.is_empty() && core.iter().all(claimed) && core.iter().all(quantifier_free))
            .then(|| core.to_vec())
    }
}

#[cfg(test)]
#[path = "ground_core_corroboration/tests.rs"]
mod tests;
