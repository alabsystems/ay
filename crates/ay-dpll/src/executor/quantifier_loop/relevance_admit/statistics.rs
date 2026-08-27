// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Observation-only statistics export for a quantifier campaign.
//!
//! The initial export records preprocessing counts. The final refresh runs after
//! Phase 0 and result mapping so demand-lane state and interleaved activity match
//! the completed check-sat call. Relevance admission also refreshes its counters
//! after every ranked round.

use ay_core::TermId;
use std::collections::BTreeMap;

use super::super::super::Executor;
use super::super::family_classifier::FamilyClass;
use super::super::QuantifierProcessingResult;

impl Executor {
    /// Export preprocessing measurements and return their stable family classes.
    pub(in crate::executor) fn record_quantifier_processing_statistics(
        &mut self,
        result: &QuantifierProcessingResult,
        classifier_foralls: &[TermId],
    ) -> BTreeMap<TermId, FamilyClass> {
        let classifier_classes = self.classify_quantifier_families(classifier_foralls);
        self.last_statistics.ematching_rounds_completed = result.ematching_rounds_completed;
        self.last_statistics.ematching_instances_created = result.ematching_instances_created;

        self.refresh_quantifier_campaign_statistics(&classifier_classes);
        classifier_classes
    }

    /// Refresh cumulative observation counters from the live campaign state.
    ///
    /// This is intentionally idempotent: callers publish once after preprocessing
    /// and again after Phase 0/interleaved result mapping, before an incremental
    /// solve restores its parked outer quantifier manager.
    pub(in crate::executor) fn refresh_quantifier_campaign_statistics(
        &mut self,
        classifier_classes: &BTreeMap<TermId, FamilyClass>,
    ) {
        // Side B relevance is pure observation; nothing reads these values back.
        if let Some(manager) = self.quantifier_manager.as_ref() {
            manager.write_relevance_statistics(&mut self.last_statistics);
        }

        // Clone first so the immutable manager borrow ends before statistics is
        // borrowed mutably. Family classification reads only the term store.
        let demand_stats = self
            .quantifier_manager
            .as_ref()
            .map(crate::quantifier_manager::QuantifierManager::demand_stats_clone);
        if let Some(demand_stats) = demand_stats {
            demand_stats.write_statistics(&mut self.last_statistics);
            super::super::write_family_class_statistics(
                &demand_stats,
                classifier_classes,
                &mut self.last_statistics,
            );
        }

        // The writer is inert unless the demand lane armed.
        if let Some(manager) = self.quantifier_manager.as_ref() {
            manager.demand_write_statistics(&mut self.last_statistics);
        }
    }
}
