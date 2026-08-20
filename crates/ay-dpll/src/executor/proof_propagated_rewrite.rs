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
    /// The literal Boolean constant this plan's TARGET is, if it is one
    /// (#4751). An assume that preprocessing folded all the way to
    /// `true`/`false` is not a rewritten problem assertion to reconstruct —
    /// it is a preprocessing-time refutation, and
    /// `rebuild_trust_leaf_proof_from_original_assertions` already rebuilds
    /// it from the authored roots WITH its theory certificates. The
    /// constant-fold bridges therefore refuse to conclude it; every other
    /// route to a constant target is untouched.
    constant_target: Option<TermId>,
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
            constant_target: None,
            budget: PLAN_NODE_BUDGET,
        }
    }

    /// Record that this plan's target is the literal Boolean constant
    /// `target` (#4751); see [`Self::constant_target`].
    pub(crate) fn with_constant_target(mut self, target: TermId) -> Self {
        self.constant_target = Some(target);
        self
    }

    /// Whether `candidate` is the literal Boolean constant this plan targets.
    pub(super) fn refuses_constant_conclusion(&self, candidate: TermId) -> bool {
        self.constant_target == Some(candidate)
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

    /// Mint `PropagateValues`-shaped provenance for the QF_LIA
    /// `VariableSubstitution` round (#4751).
    ///
    /// That pass rewrites assertions IN PLACE exactly like `PropagateValues`
    /// — its own call site notes it "detaches the reconstructed proof's
    /// leaves from the original assertions and forces Trust-step fallbacks"
    /// — but, unlike the BV and AUFLIA routes, it minted no records, so
    /// [`Self::derive_propagated_value_assumptions`] declined at its first
    /// guard and `demote_non_problem_assumptions` stamped the rewritten
    /// assume as a premiseless `trust`. Measured on the `dillig12_m` CHC
    /// benchmark: the depth-0 SingleLoop transition relation is substituted
    /// under its own init units (`v0 |-> 0`, `v1 |-> 0`) and constant-folded,
    /// so the proof assumes a term the authored stack does not contain.
    ///
    /// The records are HINTS ONLY, on the module's existing contract: the
    /// replay re-derives every step from the licensing defining equalities
    /// and declines on any mismatch. Fail-closed on each leg — a
    /// substitution with no recorded source assertion, or a replacement with
    /// no structurally-verified licensing equality, withholds the WHOLE run
    /// rather than seed a partial licensing environment, matching the
    /// over-cap policy in [`Self::merge_propagation_records`].
    ///
    /// #4751 `_mod_q` class — why a NON-CONSTANT replacement is admitted.
    /// The original leg demanded `TermData::Const(_)`, which withheld the
    /// whole run on the CHC route: `ChcExpr::eliminate_mod` asserts the
    /// Euclidean decomposition `(= x (+ (* k q) r))`, and substituting its
    /// dividend replaces `x` by a SUM, not a constant. Measured at the
    /// demotion site on `dillig12_m`, every `_mod_q_*` assume carried
    /// `rec=false` — i.e. no record at all — for exactly this reason.
    ///
    /// Constness was never what made the entry sound. The replay's entry arm
    /// (`plan_derive_eq_inner`) hands the entry's `source_assertion` back as
    /// the licensing EQUALITY and discharges it with `plan_derive_clause`, so
    /// what it actually needs is that the source really is spelled
    /// `(= expr value)` (either orientation). That is now checked
    /// STRUCTURALLY here for non-constant replacements — strictly more
    /// evidence than the constant leg ever required, and still only a hint:
    /// every emitted step is re-derived by the UNTOUCHED strict checker, and
    /// the reconstructed term must equal the recorded `after` before the
    /// bridge is taken.
    pub(in crate::executor) fn extend_propagated_value_provenance_from_var_subst(
        &mut self,
        before: &[TermId],
        after: &[TermId],
        var_subst: &crate::preprocess::VariableSubstitution,
    ) {
        if !crate::quant_unit_authority::quant_unit_authority_enabled() {
            return;
        }
        // A length mismatch means the caller re-shaped the stack between the
        // snapshots, so `before[i] -> after[i]` is not a rewrite pair.
        if before.len() != after.len() {
            return;
        }
        let substitutions = var_subst.substitutions();
        if substitutions.is_empty() {
            return;
        }
        let sources = var_subst.substitution_sources();

        // Entries are harvested at the same stamp as the rewrites they
        // license: "entries harvested in call k license rewrites of call
        // >= k", and this is a single `apply` round.
        let mut entries = Vec::with_capacity(substitutions.len());
        for (&expr, &value) in substitutions {
            let Some(&source_assertion) = sources.get(&expr) else {
                return;
            };
            // A LITERAL-CONSTANT replacement is the `PropagateValues` shape
            // this store was minted for; the replay's entry arm reads the
            // recorded `source_assertion` as the licensing equality directly.
            //
            // A NON-CONSTANT replacement is the DOMINANT QF_LIA shape and was
            // withheld outright by the first cut of this mint (#4751 measured
            // on dillig12_m: every substitution of every minting round is
            // non-constant, so the store stayed empty and every rewritten
            // assume demoted to `trust`). Admit it, but only when the recorded
            // source is spelled EXACTLY `(= expr value)` / `(= value expr)` --
            // that is precisely the claim the entry arm makes when it hands
            // `source` back as the licensing equality. `find_substitution`
            // also harvests from `ite`-encoded equalities, whose source term
            // is NOT that equality; those still withhold the WHOLE run rather
            // than seed an entry the replay would spell as an `equiv_pos` over
            // a non-equality (the live defect a95cec3469's negative test
            // found, there guarded only for `value == false`).
            //
            // Nothing else changes: records stay HINTS, every emitted step is
            // re-derived by the untouched strict checker, and a chain that
            // cannot reach the recorded `after` still declines to today's
            // demotion. The constant leg is untouched, so the existing
            // derivations are byte-identical.
            if !matches!(self.ctx.terms.get(value), ay_core::TermData::Const(_))
                && !Self::is_recorded_defining_equality(
                    &self.ctx.terms,
                    source_assertion,
                    expr,
                    value,
                )
            {
                return;
            }
            entries.push(crate::preprocess::PropagatedEntrySource {
                expr,
                value,
                source_assertion,
                stamp: 1,
            });
        }

        let rewrites: Vec<crate::preprocess::PropagatedRewriteRecord> = before
            .iter()
            .zip(after.iter())
            .filter(|(before, after)| before != after)
            .map(
                |(&before, &after)| crate::preprocess::PropagatedRewriteRecord {
                    before,
                    after,
                    stamp: 1,
                },
            )
            .collect();
        if rewrites.is_empty() {
            return;
        }

        self.merge_propagation_records(PropagationRecords { rewrites, entries });
    }

    /// Whether `source` is spelled `(= expr value)` or `(= value expr)` — the
    /// only shape the replay's entry arm may hand back as its licensing
    /// equality. Mirrors the consumer-side `is_defining_equality` check in
    /// `proof_propagated_rewrite::equality`, applied at MINT time so a
    /// non-constant replacement can never seed an entry the consumer would
    /// have to take on faith.
    fn source_is_defining_equality(
        terms: &TermStore,
        source: TermId,
        expr: TermId,
        value: TermId,
    ) -> bool {
        match terms.get(source) {
            TermData::App(symbol, args) if symbol.name() == "=" && args.len() == 2 => {
                (args[0] == expr && args[1] == value) || (args[0] == value && args[1] == expr)
            }
            _ => false,
        }
    }

    /// Mint `PropagateValues`-shaped provenance for the top-level
    /// UNIT-PROPAGATION round in `preprocess_lia_artifacts` (#4751).
    ///
    /// That pass deletes falsified disjuncts and stores `assertions[i] =
    /// (or kept…)` IN PLACE, exactly like `PropagateValues` and
    /// `VariableSubstitution`, but minted no records — so
    /// [`Self::derive_propagated_value_assumptions`] never saw the rewrite
    /// and `demote_non_problem_assumptions` stamped the reduced `or` a
    /// premiseless `trust`. The designed replay
    /// (`plan_or_elimination_bridge`) is exactly the right mechanism: it
    /// clausifies the authored `or`, drives every deleted disjunct to
    /// `false`, and resolves the survivors.
    ///
    /// The difference from `PropagateValues` is the LICENSE: unit
    /// propagation deletes `dj` because a bare unit asserting `dj`'s
    /// COMPLEMENT is on the stack, not because a defining equality
    /// `(= dj false)` is. The entries therefore carry that unit as their
    /// `source_assertion`, and the planner bridges it to the equality with
    /// an `equiv_neg2` tautology (see `plan_unit_literal_false_eq`). The c7
    /// sealing lane re-derives entries through
    /// `PropagateValues::extract_value_equality` and so simply DROPS these
    /// (fail-closed), leaving that channel unchanged.
    ///
    /// Records are HINTS ONLY on the module's existing contract: the replay
    /// re-derives every step and declines on any mismatch. Fail-closed per
    /// leg — a deletion whose recorded unit is not the literal complement of
    /// the deleted disjunct withholds the WHOLE run rather than seed a
    /// partial licensing environment.
    pub(in crate::executor) fn extend_propagated_value_provenance_from_unit_prop(
        &mut self,
        before: &[TermId],
        after: &[TermId],
        deletions: &[(TermId, TermId)],
    ) {
        if !crate::quant_unit_authority::quant_unit_authority_enabled() {
            return;
        }
        // A length mismatch means the caller re-shaped the stack between the
        // snapshots, so `before[i] -> after[i]` is not a rewrite pair.
        if before.len() != after.len() || deletions.is_empty() {
            return;
        }
        let false_term = self.ctx.terms.mk_bool(false);
        let mut entries = Vec::with_capacity(deletions.len());
        for &(disjunct, unit) in deletions {
            // The recorded unit must assert exactly the complement of the
            // deleted disjunct; anything else is not a license this replay
            // can spell, so withhold the run.
            let complementary = match self.ctx.terms.get(disjunct) {
                TermData::Not(inner) => *inner == unit,
                _ => matches!(self.ctx.terms.get(unit), TermData::Not(inner) if *inner == disjunct),
            };
            if !complementary {
                return;
            }
            entries.push(crate::preprocess::PropagatedEntrySource {
                expr: disjunct,
                value: false_term,
                source_assertion: unit,
                stamp: 1,
            });
        }

        let rewrites: Vec<crate::preprocess::PropagatedRewriteRecord> = before
            .iter()
            .zip(after.iter())
            .filter(|(before, after)| before != after)
            .map(
                |(&before, &after)| crate::preprocess::PropagatedRewriteRecord {
                    before,
                    after,
                    stamp: 1,
                },
            )
            .collect();
        if rewrites.is_empty() {
            return;
        }

        self.merge_propagation_records(PropagationRecords { rewrites, entries });
    }

    /// Whether `source` is spelled exactly `(= expr value)` or
    /// `(= value expr)` -- the licensing shape the propagation replay's entry
    /// arm assumes when it returns `source` as the equality between `expr`
    /// and `value`.
    fn is_recorded_defining_equality(
        terms: &TermStore,
        source: TermId,
        expr: TermId,
        value: TermId,
    ) -> bool {
        match terms.get(source) {
            TermData::App(symbol, args) if symbol.name() == "=" && args.len() == 2 => {
                (args[0] == expr && args[1] == value) || (args[0] == value && args[1] == expr)
            }
            _ => false,
        }
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
            if matches!(self.ctx.terms.get(term), TermData::Const(Constant::Bool(_))) {
                cx = cx.with_constant_target(term);
            }
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
