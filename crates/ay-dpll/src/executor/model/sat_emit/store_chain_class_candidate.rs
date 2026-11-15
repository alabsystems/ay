// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A second array candidate for one proposed `Sat`
//! (#store-chain-class-candidate).
//!
//! The array solver extracts its model in two ways when they differ: the
//! per-term construction (`ArrayModel::array_values`) and the same model with
//! every equivalence class that holds a store chain given one value
//! (`ArrayModel::store_chain_class_candidate`, built by
//! `reconcile_store_chain_classes`). Neither dominates. The reconciliation
//! honours every TRUE store-chain equality of the solver's assignment,
//! including those only the eager fixpoint's own lemmas mention and whose
//! written indices the lazy search never related, so it repairs some models
//! (the hunt's d4b_free_bases witness, fresh finstore) and breaks others
//! (fresh incr2_2809_0051's second query: `sat` on main, `unknown` with the
//! reconciled model as the only one).
//!
//! The funnel therefore gates the per-term model first and, only when the
//! gates refused it, gates the reconciled one. SOUND: both are complete models
//! of the same assignment and each goes through the unchanged gate sequence of
//! `emit_sat_verdict_once`; the second attempt can only turn a fail-closed
//! `unknown` into a `Sat` whose model every gate confirmed.

use ay_core::TermId;

use super::SatOwnerTransition;
use crate::executor::model::Model;
use crate::executor::optimization::OptimizationModelPublication;
use crate::executor::Executor;
use crate::executor_types::{Result, SolveResult};

impl Executor {
    /// The ordinary SAT-emission chokepoint (#sat-chokepoint): runs
    /// `emit_sat_verdict_once` (the full gate sequence and certificate mint,
    /// documented there) on the proposed model and, when the gates refused a
    /// model that carries a store-chain class candidate, once more on that
    /// candidate (module docs).
    pub(in crate::executor) fn emit_sat_verdict(
        &mut self,
        proposed: SolveResult,
        roots: &[TermId],
    ) -> Result<SolveResult> {
        self.emit_sat_verdict_with_owner(proposed, roots, SatOwnerTransition::CurrentQuery)
    }

    pub(in crate::executor) fn emit_optimization_sat_verdict(
        &mut self,
        publication: OptimizationModelPublication<'_>,
    ) -> Result<SolveResult> {
        let (model, obligations) = publication.into_parts();
        self.last_model = model;
        self.emit_sat_verdict_with_owner(
            SolveResult::Sat,
            obligations,
            SatOwnerTransition::RestoredOptimization,
        )
    }

    fn emit_sat_verdict_with_owner(
        &mut self,
        proposed: SolveResult,
        roots: &[TermId],
        transition: SatOwnerTransition,
    ) -> Result<SolveResult> {
        let candidate = if proposed == SolveResult::Sat {
            self.take_store_chain_class_candidate()
        } else {
            None
        };
        let first = self.emit_sat_verdict_once(proposed, roots, transition)?;
        let Some(candidate) = candidate else {
            return Ok(first);
        };
        if first != SolveResult::Unknown
            || self.publish_evaluation_stop()
            || self.solve_deadline.expired()
        {
            return Ok(first);
        }
        // `--stats-full` `model_validation.store_chain_class_candidate`: 1 =
        // tried after the first model was refused, 2 = published.
        self.last_statistics
            .set_int("model_validation.store_chain_class_candidate", 1);
        let first_reason = self.last_unknown_reason.take();
        self.last_model = Some(candidate);
        self.last_model_validated = false;
        let second = self.emit_sat_verdict_once(SolveResult::Sat, roots, transition)?;
        if second == SolveResult::Sat {
            self.last_statistics
                .set_int("model_validation.store_chain_class_candidate", 2);
        } else if self.last_unknown_reason.is_none() {
            self.last_unknown_reason = first_reason;
        }
        Ok(second)
    }

    /// Detach the store-chain class candidate from the proposed model and
    /// return the proposed model with it installed as the array model, or
    /// `None` when the model carries none. Detaching keeps a re-entry of the
    /// funnel on the same model from offering it twice.
    pub(in crate::executor) fn take_store_chain_class_candidate(&mut self) -> Option<Model> {
        let model = self.last_model.as_mut()?;
        let values = model
            .array_model
            .as_mut()?
            .store_chain_class_candidate
            .take()?;
        let mut candidate = model.clone();
        candidate.array_model.as_mut()?.array_values = values;
        Some(candidate)
    }
}
