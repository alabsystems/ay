// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Proof-producing `PropagateValues` replay (#ppp-provenance, slices 1-2).
//!
//! Preprocessing rewrites assertions IN PLACE with no proof record, so a
//! solver proof that assumes the REWRITTEN assertion cannot be strictly
//! certified against the authored obligation: the assume is demoted to an
//! undischargeable `trust` step and a correct refutation publishes `unknown`
//! ("no exact proof authority" / "assumes term outside the supplied problem
//! obligation").
//!
//! This module consumes the producer provenance minted by the
//! `PropagateValues` pass ([`crate::preprocess::PropagationRecords`]) and
//! REPLAYS each recorded rewrite into proof steps the UNTOUCHED strict
//! checker re-derives: `cong`/`trans`/`evaluate` equality chains for
//! substitution-plus-constant-fold, `or`-clausification plus per-disjunct
//! refutation for disjunct elimination, and `equiv_pos` bridges from the
//! derived equality to the asserted unit. The records are HINTS ONLY: the
//! replay independently re-derives every step from the licensing defining
//! equalities (themselves derived from authored roots), and any mismatch
//! DECLINES the derivation, leaving today's fail-closed demotion behaviour
//! unchanged. No checker rule is added or widened; UNSAT direction only.
//!
//! L2 (#ppp-c7): the SAME plan machinery now also serves the exact-fragment
//! c7 unit channel in `sat_proof_manager`, which runs against `TermStore`
//! only. [`PropagationChainPlanner`] is therefore parameterized on the term
//! store; the L1 rebuild lane wraps it with `&mut executor.ctx.terms` and
//! emits byte-identical chains. Two L2-only extensions, both INERT for the
//! rebuild lane (empty instance-root slice; `closed_bv_bitblast_bridge`
//! false):
//!  * an instance-root base case deriving `(cl I)` for a sealed qpf
//!    premise-forced instance via the strict `forall_inst` chain, plus
//!    closed-disjunct elimination to its unique survivor and `=`-swap
//!    bridges for canonicalized conjunct respellings;
//!  * a closed-fold bridge variant emitting one closed `BvBitBlast` lemma
//!    (re-validated by the strict exhaustive bounded evaluator; zero
//!    assignment bits) instead of the `BvLiaTautology`+`BoolTautology`
//!    pair, because each `BvLiaTautology` lemma carries a fixed 100M-work
//!    admission precharge against the checked-refutation 250M envelope —
//!    the known P3b duplicate-fold blowout mode (measured 300,000,991).
//!
//! L3 (#ppp-l3): the AUFLIA `FlattenAnd`+`PropagateValues` fixpoint in
//! `solve_harness` now drains its pass records into the same executor store
//! (`extend_propagated_value_provenance_direct`), so the rebuild lane and the
//! c7 channel serve that HIGH-TRAFFIC route too. Two replay extensions cover
//! the fold shapes that route produces, both fail-closed and re-derived by
//! the untouched strict checker:
//!  * and-headed conjunct elimination at the record-bridge level
//!    (`and_bridge`): changed conjuncts must replay to literal `true` and
//!    the canonical rebuild must reproduce the recorded survivor set;
//!  * Bool `(= x true/false)` folds (`plan_bool_eq_const_fold`): a
//!    `cong` + `equiv_pos`/`equiv_neg` + `true`/`false`-tautology chain
//!    closing the `mk_eq` Boolean simplification as a term equality, valid
//!    for arbitrary theory atoms `x`.
//!
//! Kill switch: `--no-quant-unit-authority` (the existing campaign switch)
//! disables both record minting and this consumption, reproducing the
//! pristine baseline.

use std::sync::{Arc, Mutex};

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::{
    AletheRule, Constant, Proof, ProofId, ProofStep, Sort, Symbol, TermData, TermId, TermStore,
    TheoryLemmaKind,
};

use super::Executor;
use crate::preprocess::{PropagateValues, PropagationRecords};
use crate::sat_proof_manager::FragmentInstanceRootDerivation;

mod and_bridge;
mod clause;
mod equality;
mod or_bridge;
mod splice;
#[cfg(test)]
mod tests;

/// Merged-store cap; mirrors the pass-side cap. Overflow clears the store
/// (fail-closed: no partial licensing environment may drive a replay).
const MAX_STORED_PROPAGATION_RECORDS: usize = 4096;

/// Total term-node budget for one derivation plan. Exceeding it fails the
/// plan (the assume falls back to today's demotion path).
pub(crate) const PLAN_NODE_BUDGET: usize = 20_000;

/// Result of replaying the pass's `rewrite` on one term.
#[derive(Clone, Copy)]
enum EqRes {
    /// The pass leaves this term unchanged under the stamped environment.
    Unchanged,
    /// The pass rewrites the term to `to`; `id` concludes `(cl eq_term)`
    /// where `eq_term` is an equality between the term and `to` (orientation
    /// as stored in `eq_term`'s argument order).
    Changed {
        to: TermId,
        eq_term: TermId,
        id: ProofId,
    },
}

pub(crate) struct PlanCx<'a> {
    problem_set: &'a HashSet<TermId>,
    problem_roots: &'a [TermId],
    /// after -> (before, stamp), first record wins.
    record_by_after: &'a HashMap<TermId, (TermId, u32)>,
    /// expr -> (value, source assertion, stamp), first harvest wins.
    entry_by_expr: &'a HashMap<TermId, (TermId, TermId, u32)>,
    /// Sealed qpf premise-forced instance roots (#ppp-c7). Empty for the
    /// rebuild lane, so every L1 plan is unchanged.
    instance_roots: &'a [FragmentInstanceRootDerivation],
    /// Emit closed collapsing-fold bridges as one exhaustive-bounded-eval
    /// `BvBitBlast` lemma instead of the `BvLiaTautology`+`BoolTautology`
    /// pair (#ppp-c7 metering; see module docs). False for the rebuild lane.
    closed_bv_bitblast_bridge: bool,
    /// Self-contained chain under construction.
    pub(crate) chain: Proof,
    /// (cl t) memo.
    clause_memo: HashMap<TermId, ProofId>,
    /// Replay memo, keyed by (term, stamp).
    eq_memo: HashMap<(TermId, u32), Option<EqRes>>,
    /// Cycle guard for record chains.
    in_progress: HashSet<TermId>,
    /// Shared `(cl (not false))` tautology.
    false_taut: Option<ProofId>,
    /// Remaining node budget; exhaustion fails the plan.
    budget: usize,
}

impl<'a> PlanCx<'a> {
    pub(crate) fn new(
        problem_set: &'a HashSet<TermId>,
        problem_roots: &'a [TermId],
        record_by_after: &'a HashMap<TermId, (TermId, u32)>,
        entry_by_expr: &'a HashMap<TermId, (TermId, TermId, u32)>,
        instance_roots: &'a [FragmentInstanceRootDerivation],
        closed_bv_bitblast_bridge: bool,
    ) -> Self {
        Self {
            problem_set,
            problem_roots,
            record_by_after,
            entry_by_expr,
            instance_roots,
            closed_bv_bitblast_bridge,
            chain: Proof::new(),
            clause_memo: HashMap::default(),
            eq_memo: HashMap::default(),
            in_progress: HashSet::default(),
            false_taut: None,
            budget: PLAN_NODE_BUDGET,
        }
    }

    fn spend(&mut self, nodes: usize) -> Option<()> {
        self.budget = self.budget.checked_sub(nodes)?;
        Some(())
    }
}

impl Executor {
    /// Drain `PropagateValues` producer provenance from a preprocessor run
    /// into the executor store, offsetting stamps so successive runs stay
    /// ordered. Minting is gated on the campaign kill switch: with the
    /// switch off no record is ever stored and behaviour is byte-identical
    /// to baseline.
    pub(in crate::executor) fn extend_propagated_value_provenance(
        &mut self,
        handle: &Arc<Mutex<PropagateValues>>,
    ) {
        if !crate::quant_unit_authority::quant_unit_authority_enabled() {
            return;
        }
        let Ok(mut pass) = handle.lock() else {
            return;
        };
        let Some(records) = pass.take_propagation_records() else {
            return;
        };
        drop(pass);
        self.merge_propagation_records(records);
    }

    /// L3 sibling of [`Self::extend_propagated_value_provenance`] for a pass
    /// owned DIRECTLY by a preprocessing loop (the AUFLIA
    /// `FlattenAnd`+`PropagateValues` fixpoint in `solve_harness`) rather
    /// than behind the shared-pass mutex. Same kill-switch gate, same
    /// merged-store cap: with the switch off nothing is ever stored and the
    /// pass's internal records are simply dropped with the pass.
    pub(in crate::executor) fn extend_propagated_value_provenance_direct(
        &mut self,
        pass: &mut PropagateValues,
    ) {
        if !crate::quant_unit_authority::quant_unit_authority_enabled() {
            return;
        }
        let Some(records) = pass.take_propagation_records() else {
            return;
        };
        self.merge_propagation_records(records);
    }

    fn merge_propagation_records(&mut self, records: PropagationRecords) {
        let store = &mut self.propagated_value_provenance;
        let offset = store
            .rewrites
            .iter()
            .map(|record| record.stamp)
            .chain(store.entries.iter().map(|entry| entry.stamp))
            .max()
            .unwrap_or(0);
        store
            .rewrites
            .extend(records.rewrites.into_iter().map(|mut record| {
                record.stamp = record.stamp.saturating_add(offset);
                record
            }));
        store
            .entries
            .extend(records.entries.into_iter().map(|mut entry| {
                entry.stamp = entry.stamp.saturating_add(offset);
                entry
            }));
        tracing::debug!(
            rewrites = store.rewrites.len(),
            entries = store.entries.len(),
            "#ppp-provenance merged store size"
        );
        if store.rewrites.len() > MAX_STORED_PROPAGATION_RECORDS
            || store.entries.len() > MAX_STORED_PROPAGATION_RECORDS
        {
            // Fail-closed L1 precedent: an over-cap store is dropped WHOLE —
            // no partial licensing environment may drive a replay. Traced so
            // cap pressure on real fixtures is measurable (#ppp-l3).
            tracing::debug!(
                rewrites = store.rewrites.len(),
                entries = store.entries.len(),
                cap = MAX_STORED_PROPAGATION_RECORDS,
                "#ppp-provenance merged store over cap; withholding all records"
            );
            *store = PropagationRecords::default();
        }
    }

    /// Derive propagation-rewritten assumptions from their authored roots
    /// before the demotion pass turns unsupported assumptions into `trust`.
    pub(in crate::executor) fn derive_propagated_value_assumptions(
        &mut self,
        proof: &mut Proof,
        problem_assertions: &[TermId],
    ) {
        if !crate::quant_unit_authority::quant_unit_authority_enabled()
            || self.propagated_value_provenance.rewrites.is_empty()
        {
            return;
        }
        let problem_set = problem_assertions.iter().copied().collect();
        let (record_by_after, entry_by_expr) = self.propagation_replay_indexes();
        let candidates = Self::propagation_replay_candidates(proof, &problem_set, &record_by_after);
        if candidates.is_empty() {
            return;
        }
        let planned = self.plan_propagation_candidates(
            candidates,
            &problem_set,
            problem_assertions,
            &record_by_after,
            &entry_by_expr,
        );
        if !planned.is_empty() {
            splice::splice_propagated_plans(proof, planned);
        }
    }

    fn propagation_replay_indexes(
        &self,
    ) -> (
        HashMap<TermId, (TermId, u32)>,
        HashMap<TermId, (TermId, TermId, u32)>,
    ) {
        let mut record_by_after = HashMap::default();
        for record in &self.propagated_value_provenance.rewrites {
            if record.before != record.after {
                record_by_after
                    .entry(record.after)
                    .or_insert((record.before, record.stamp));
            }
        }
        let mut entry_by_expr = HashMap::default();
        for entry in &self.propagated_value_provenance.entries {
            entry_by_expr.entry(entry.expr).or_insert((
                entry.value,
                entry.source_assertion,
                entry.stamp,
            ));
        }
        (record_by_after, entry_by_expr)
    }

    fn propagation_replay_candidates(
        proof: &Proof,
        problem_set: &HashSet<TermId>,
        record_by_after: &HashMap<TermId, (TermId, u32)>,
    ) -> Vec<(usize, TermId)> {
        proof
            .steps
            .iter()
            .enumerate()
            .filter_map(|(index, step)| {
                let ProofStep::Assume(term) = step else {
                    return None;
                };
                if problem_set.contains(term) || !record_by_after.contains_key(term) {
                    return None;
                }
                Some((index, *term))
            })
            .collect()
    }

    fn plan_propagation_candidates(
        &mut self,
        candidates: Vec<(usize, TermId)>,
        problem_set: &HashSet<TermId>,
        problem_roots: &[TermId],
        record_by_after: &HashMap<TermId, (TermId, u32)>,
        entry_by_expr: &HashMap<TermId, (TermId, TermId, u32)>,
    ) -> HashMap<usize, (Proof, ProofId)> {
        let mut planned = HashMap::default();
        for (index, term) in candidates {
            let mut cx = PlanCx::new(
                problem_set,
                problem_roots,
                record_by_after,
                entry_by_expr,
                &[],
                false,
            );
            let mut planner = PropagationChainPlanner {
                terms: &mut self.ctx.terms,
            };
            if let Some(conclusion) = planner.plan_derive_clause(&mut cx, term) {
                planned.insert(index, (cx.chain, conclusion));
            }
        }
        planned
    }
}

/// Term-store-parameterized propagation replay planner shared by the L1
/// rebuild lane (`derive_propagated_value_assumptions`) and the L2 c7
/// exact-fragment unit channel (`sat_proof_manager`). Every emitted step is
/// re-derived by the untouched strict checker; the planner carries no
/// authority of its own.
pub(crate) struct PropagationChainPlanner<'t> {
    pub(crate) terms: &'t mut TermStore,
}
