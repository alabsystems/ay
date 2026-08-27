// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Relevance-ranked admission of E-matching instances (Side B, the middle gear).
//!
//! A raw E-matching call emits at most `EMatchingConfig::max_total` (10 000)
//! fresh instances. Merging prior carry can make the admission batch larger;
//! measured SQ Equality batches contain 7 500-16 300 candidates. Admitting the
//! whole batch before the next ground solve spends the budget inside the EUF
//! core. When ranking is authorized, this module admits a bounded top-K and
//! CARRIES the remainder in [`crate::quantifier_manager::QuantifierManager`]
//! instead of discarding it.
//!
//! Mandatory internal proof recording forces unfiltered admission even when
//! relevance is requested. The carry item does not retain enough provenance to
//! replay a strict `forall_inst`, so certified public solves preserve the whole
//! batch. Public ranking is currently limited to competition proof shedding.
//!
//! # Soundness argument (the only thing that matters here)
//!
//! Withholding an instance REMOVES a top-level conjunct. Removing conjuncts
//! weakens the problem, so:
//!
//! - a refutation can never be manufactured by this layer — every `unsat` is
//!   derived from a SUBSET of the conjuncts the unfiltered path would have
//!   asserted, hence from a subset of the original problem's consequences;
//! - a `sat` COULD be spurious if it were read off an assertion set that is
//!   missing withheld constraints, so that is blocked at the source: a
//!   non-empty carry queue makes `QuantifierManager::has_deferred` true, and
//!   `classify_quantifier_result` maps `Sat && has_deferred` to
//!   `Unknown(QuantifierDeferred)`. The interleaved seam additionally reports
//!   `reached_limit` for any round in which it withheld, which maps to
//!   `Unknown(QuantifierRoundLimit)`.
//!
//! Nothing here mints a term, changes a trigger, or admits an instance the
//! E-matcher did not already produce and authorize.

mod statistics;

use ay_core::kani_compat::DetHashSet as HashSet;
use ay_core::TermId;

use super::super::model::EvalValue;
use super::super::Executor;
use crate::ematching::{
    instance_features, relevance_config, score_instance, split_top_k, ModelStanding,
    RelevanceConfig, ScoredInstance,
};

/// Outcome of one ranked admission.
pub(in crate::executor) struct RelevanceAdmission {
    /// Instances to assert this round, in admission order (best-first when
    /// ranking engaged). Carries the `support_root` bit so a carry flush can
    /// register the producing round's conflict-verification support.
    pub admitted: Vec<ScoredInstance>,
    /// Instances still withheld after this round. Zero means admission was
    /// complete, not necessarily that no carried item was flushed or reordered.
    pub withheld: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum AdmissionAuthority {
    /// Preserve every instance while mandatory certificate provenance is live.
    PreserveProof,
    /// No proof tracker is live, so ranked search admission is authorized.
    SearchOnly,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum CarryState {
    Empty,
    Pending,
}

fn admit_all(novel: Vec<TermId>, support_roots: &HashSet<TermId>) -> RelevanceAdmission {
    let admitted = novel
        .into_iter()
        .map(|inst| ScoredInstance {
            inst,
            score: 0.0,
            support_root: support_roots.contains(&inst),
            age: 0,
        })
        .collect();
    RelevanceAdmission {
        admitted,
        withheld: 0,
    }
}

fn admission_is_unfiltered(
    config: RelevanceConfig,
    authority: AdmissionAuthority,
    novel_count: usize,
    carry: CarryState,
) -> bool {
    !config.enabled
        || authority == AdmissionAuthority::PreserveProof
        || (novel_count <= config.flood_threshold && carry == CarryState::Empty)
}

fn merge_ranked_candidates(mut candidates: Vec<ScoredInstance>) -> Vec<ScoredInstance> {
    candidates.sort_by(|a, b| {
        a.inst
            .0
            .cmp(&b.inst.0)
            .then_with(|| b.score.total_cmp(&a.score))
    });
    let mut merged: Vec<ScoredInstance> = Vec::with_capacity(candidates.len());
    for candidate in candidates {
        if let Some(previous) = merged
            .last_mut()
            .filter(|prior| prior.inst == candidate.inst)
        {
            // Score order retains the best candidate. Provenance is monotone:
            // one authenticated source makes the shared instance a support root,
            // and re-derivation cannot erase time already spent in carry.
            previous.support_root |= candidate.support_root;
            previous.age = previous.age.max(candidate.age);
        } else {
            merged.push(candidate);
        }
    }
    merged
}

impl Executor {
    fn relevance_admission_authority(&self) -> AdmissionAuthority {
        if self.produce_proofs_enabled() {
            AdmissionAuthority::PreserveProof
        } else {
            AdmissionAuthority::SearchOnly
        }
    }

    /// Rank one round's instances and admit a bounded top-K.
    ///
    /// `novel` is the round's instances after the caller's own duplicate
    /// filtering; `support_roots` is the round's sound support-axiom subset;
    /// `watermark` is `TermStore::len()` captured BEFORE the round, which is
    /// what makes "this subterm is new" a constant-time test.
    ///
    /// Rounds at or below the flood threshold are admitted in their original
    /// order when no carry is pending. Disabled or proof-authority paths admit
    /// the novel batch in its original order, although the wrapper and its
    /// bookkeeping still execute. Proof authority leaves any prior carry
    /// deferred rather than consuming an unauthenticated proof premise.
    pub(in crate::executor) fn relevance_admit_round(
        &mut self,
        novel: Vec<TermId>,
        support_roots: &HashSet<TermId>,
        watermark: u32,
    ) -> RelevanceAdmission {
        let cfg = *relevance_config();
        let carry = if self
            .quantifier_manager
            .as_ref()
            .is_some_and(|manager| manager.carry_len() > 0)
        {
            CarryState::Pending
        } else {
            CarryState::Empty
        };
        let authority = self.relevance_admission_authority();
        if admission_is_unfiltered(cfg, authority, novel.len(), carry) {
            return admit_all(novel, support_roots);
        }

        // Take the carry queue first (ageing each entry), so previously withheld
        // work competes in this round's ranking instead of starving behind it.
        let carried_prev = self
            .quantifier_manager
            .as_mut()
            .map(|qm| qm.carry_take(cfg.age_bonus))
            .unwrap_or_default();
        let flushable = carried_prev.len();

        // Generations come from the persisted tracker: a generation-N instance
        // is N instantiations away from the input problem.
        let generations: Vec<u32> = self.quantifier_manager.as_ref().map_or_else(
            || vec![0; novel.len()],
            |qm| novel.iter().map(|&t| qm.instance_generation(t)).collect(),
        );

        let mut candidates: Vec<ScoredInstance> =
            Vec::with_capacity(carried_prev.len() + novel.len());
        candidates.extend(carried_prev);
        for (idx, inst) in novel.iter().copied().enumerate() {
            let features = instance_features(&self.ctx.terms, inst, watermark, cfg.max_walk);
            let standing = if cfg.use_model_signal {
                self.model_standing(inst)
            } else {
                ModelStanding::Unknown
            };
            candidates.push(ScoredInstance {
                inst,
                score: score_instance(features, generations[idx], standing),
                support_root: support_roots.contains(&inst),
                age: 0,
            });
        }

        // Hash-consing can surface the same instance twice. Retain the best
        // score while OR-ing authenticated support provenance across copies.
        let candidates = merge_ranked_candidates(candidates);

        let total = candidates.len();
        let (admitted, carried) = split_top_k(candidates, cfg.admit_per_round);
        let withheld = carried.len();
        let flushed = admitted.iter().filter(|s| s.age > 0).count();
        if let Some(manager) = self.quantifier_manager.as_mut() {
            manager.carry_put(carried);
            manager.relevance_record_round(total as u64, admitted.len() as u64, flushed as u64);
        }
        if let Some(manager) = self.quantifier_manager.as_ref() {
            // Refresh after every admission, including interleaved rounds.
            manager.write_relevance_statistics(&mut self.last_statistics);
        }
        debug_assert_eq!(
            total,
            admitted.len() + withheld,
            "relevance admission must conserve instances: nothing is dropped, \
             everything is either admitted or carried"
        );
        if cfg.debug {
            eprintln!(
                "c relevance-round candidates={total} pending_carry={flushable} \
                 admitted={} flushed={flushed} withheld={withheld}",
                admitted.len(),
            );
        }
        RelevanceAdmission { admitted, withheld }
    }

    /// How the current model stands on `inst`.
    ///
    /// An instance the model FALSIFIES is the one that will actually move the
    /// ground solver (the same signal `promote_deferred_conflicts` promotes on);
    /// one it already satisfies adds nothing this round. With no model, every
    /// instance is ranked on structure alone.
    fn model_standing(&self, inst: TermId) -> ModelStanding {
        let Some(model) = self.last_model.as_ref() else {
            return ModelStanding::Unknown;
        };
        match self.evaluate_term(model, inst) {
            EvalValue::Bool(true) => ModelStanding::Satisfied,
            EvalValue::Bool(false) => ModelStanding::Violated,
            _ => ModelStanding::Unknown,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn scored(id: u32, score: f64, support_root: bool) -> ScoredInstance {
        ScoredInstance {
            inst: TermId::new(id),
            score,
            support_root,
            age: 0,
        }
    }

    #[test]
    fn proof_authority_bypasses_enabled_top_k() {
        let config = RelevanceConfig {
            enabled: true,
            admit_per_round: 1,
            flood_threshold: 0,
            ..RelevanceConfig::default()
        };
        assert!(admission_is_unfiltered(
            config,
            AdmissionAuthority::PreserveProof,
            3,
            CarryState::Empty,
        ));
        let admission = admit_all(
            vec![TermId::new(1), TermId::new(2), TermId::new(3)],
            &HashSet::default(),
        );
        assert_eq!(admission.admitted.len(), 3);
        assert_eq!(admission.withheld, 0);
        assert!(!admission_is_unfiltered(
            config,
            AdmissionAuthority::SearchOnly,
            3,
            CarryState::Empty,
        ));
    }

    #[test]
    fn internal_tracker_selects_proof_authority_without_output_demand() {
        let mut executor = Executor::new();
        let producing = executor.is_producing_proofs();
        assert!(!producing);
        assert_eq!(
            executor.relevance_admission_authority(),
            AdmissionAuthority::SearchOnly,
        );

        executor.proof_tracker.enable();
        let producing = executor.is_producing_proofs();
        assert!(!producing);
        assert_eq!(
            executor.relevance_admission_authority(),
            AdmissionAuthority::PreserveProof,
        );
    }

    #[test]
    fn duplicate_candidates_keep_best_score_and_any_support_root() {
        let merged = merge_ranked_candidates(vec![
            scored(7, 9.0, false),
            ScoredInstance {
                age: 4,
                ..scored(7, 2.0, true)
            },
            scored(8, 1.0, false),
        ]);
        assert_eq!(merged.len(), 2);
        assert_eq!(merged[0].inst, TermId::new(7));
        assert_eq!(merged[0].score, 9.0);
        assert!(merged[0].support_root);
        assert_eq!(merged[0].age, 4);
    }
}
