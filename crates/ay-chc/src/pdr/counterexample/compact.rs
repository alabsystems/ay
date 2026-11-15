// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::Counterexample;
use crate::ground_derivation::compact::CompactEvidence;

impl Counterexample {
    pub(crate) fn compact_evidence(&self) -> Option<&CompactEvidence> {
        self.compact_derivation.as_deref()
    }

    pub(crate) fn with_compact_ground_derivation(mut self, evidence: CompactEvidence) -> Self {
        self.compact_derivation = Some(std::sync::Arc::new(evidence));
        self
    }

    /// Whether complete compact ground evidence is carried. Presence alone is
    /// not verification; ground_checks_unsafe replays the supplied source.
    pub fn has_compact_ground_derivation(&self) -> bool {
        self.compact_derivation.is_some()
    }

    pub(super) fn compact_certificate(&self) -> String {
        let Some(evidence) = self.compact_evidence() else {
            return String::new();
        };
        format!(
            ";; AY CHC compact ground evidence summary\n\
             ;; This summary is not a standalone certificate.\n\
             ;; Complete source-bound DAG values are in the compact ground artifact.\n\
             ;; Original clause instances: {}\n\
             ;; Complete shared value nodes: {}\n\
             ;; Query derivation step: {}\n\
             ;; No expanded legacy state trace is claimed.\n",
            evidence.derivation().steps.len(),
            evidence.derivation().arena.nodes().len(),
            evidence.derivation().query_step,
        )
    }
}
