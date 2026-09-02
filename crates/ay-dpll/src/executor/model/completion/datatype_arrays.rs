// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bounded datatype-array planning and post-carrier substitution replay.

use ay_core::kani_compat::DetHashSet as HashSet;
use ay_core::TermId;

use super::{checked_datatype_root_augmentation, EvalValue, Model};
use crate::executor::Executor;

/// Authenticated roots and carrier candidates for completion phases 3, 5, and
/// 6. Owned augmentations are retained only when the corresponding bounded
/// producer succeeds; otherwise `roots` falls back to the caller's slice.
pub(super) struct DatatypeArrayCompletionPlan<'a> {
    caller_roots: &'a [TermId],
    augmented_roots: Option<Vec<TermId>>,
    eligible_carriers: Option<HashSet<TermId>>,
}

impl DatatypeArrayCompletionPlan<'_> {
    pub(super) fn roots(&self) -> &[TermId] {
        self.augmented_roots.as_deref().unwrap_or(self.caller_roots)
    }

    pub(super) fn eligible_carriers(&self) -> Option<&HashSet<TermId>> {
        self.eligible_carriers.as_ref()
    }
}

impl Executor {
    /// Recover only canonical authored hard facts needed by the W6
    /// datatype/array producer before carrier completion. Preprocessing may
    /// have removed both `x = (mk a)` and `a = const/store`; the same exact
    /// bounded slice is replayed through phases 3, 5, and 6.
    pub(super) fn datatype_array_completion_plan<'a>(
        &self,
        extra_roots: &'a [TermId],
    ) -> DatatypeArrayCompletionPlan<'a> {
        let forced_dt_support = self.forced_datatype_array_support();
        let authored_cell_roots = self.authored_datatype_array_cell_equalities(extra_roots);
        let authored_pre_dt_roots =
            checked_datatype_root_augmentation(extra_roots, &authored_cell_roots);
        let forced_pre_dt_roots = forced_dt_support.as_ref().and_then(|support| {
            checked_datatype_root_augmentation(
                authored_pre_dt_roots.as_deref().unwrap_or(extra_roots),
                &support.roots,
            )
        });
        let forced_roots_available = forced_pre_dt_roots.is_some();
        let augmented_roots = forced_pre_dt_roots.or(authored_pre_dt_roots);
        let roots = augmented_roots.as_deref().unwrap_or(extra_roots);

        // Ordinary datatype-result UF/select applications are not covered by
        // the eager BV lane, but the bounded opaque preflight has already
        // authenticated their exact declaration, signature, sort, and query
        // reachability. Admit only those applications as carrier-allocation
        // candidates, together with the separately authenticated hard-source
        // terms. This is eligibility to receive a fresh EUF class—not W6
        // array-field authority; construction and the independent certificate
        // gate still recheck the complete class and every authored assertion.
        let mut eligible_carriers = self
            .preflight_opaque_dt_collection(roots)
            .map(|preflight| preflight.into_parts().2);
        if forced_roots_available {
            if let Some(support) = forced_dt_support.as_ref() {
                if let Some(eligible) = eligible_carriers.as_mut() {
                    eligible.extend(support.carrier_terms.iter().copied());
                } else {
                    eligible_carriers = Some(support.carrier_terms.clone());
                }
            }
        }

        DatatypeArrayCompletionPlan {
            caller_roots: extra_roots,
            augmented_roots,
            eligible_carriers,
        }
    }

    /// Re-derive substituted BV/Bool vars whose defining term reads a
    /// datatype/uninterpreted-element array (#g4-dt-ce-select).
    ///
    /// The first substitution fixpoint runs before equality-carrier completion
    /// pins each `select` congruence-class element into the EUF model. Replaying
    /// only the transitive datatype-array dependents replaces stale values with
    /// committed-model values. An unevaluable definition remains unchanged, so
    /// validation still fails closed.
    pub(super) fn replay_datatype_array_dependent_substitutions(&mut self, model: &mut Model) {
        let sub_pairs: Vec<(TermId, TermId)> = self
            .recorded_var_substitutions
            .iter()
            .map(|(&from, &to)| (from, to))
            .collect();

        // Closure: direct readers plus substituted vars whose definitions
        // reference an already-dependent variable. Restricting the replay to
        // this closure avoids disturbing correctly recovered scalar values.
        let mut datatype_dependents: HashSet<TermId> = sub_pairs
            .iter()
            .filter(|&&(_, to)| Self::target_reads_datatype_element_array(&self.ctx.terms, to))
            .map(|&(from, _)| from)
            .collect();
        loop {
            let mut added = false;
            for &(from, to) in &sub_pairs {
                if !datatype_dependents.contains(&from)
                    && Self::term_references_var_in_set(&self.ctx.terms, to, &datatype_dependents)
                {
                    datatype_dependents.insert(from);
                    added = true;
                }
            }
            if !added {
                break;
            }
        }
        let targets: Vec<(TermId, TermId)> = sub_pairs
            .into_iter()
            .filter(|&(from, _)| datatype_dependents.contains(&from))
            .collect();
        if targets.is_empty() {
            return;
        }

        // Re-derive to a chain-length-bounded fixpoint. Each successful insert
        // clears the evaluation memo, so later dependents observe the update.
        // Unknown leaves the existing value untouched.
        let max_passes = targets.len() + 1;
        for _ in 0..max_passes {
            let mut changed = false;
            for &(from, to) in &targets {
                let value = self.evaluate_term(model, to);
                if matches!(value, EvalValue::Unknown) || value == self.evaluate_term(model, from) {
                    continue;
                }
                if Self::insert_completed_value(&self.ctx.terms, model, from, &value) {
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }
    }
}
