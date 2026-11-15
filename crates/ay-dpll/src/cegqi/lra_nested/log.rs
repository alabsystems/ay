// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Γ: the instance log with provenance (plan §3.2).

use ay_core::TermId;

/// One logged instance `ψ_A[k, t]` of node `node`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct QlraInstance {
    /// Index of the node in [`super::QlraTree::nodes`].
    pub(crate) node: usize,
    /// Positional binder values, over free (problem) constants only.
    pub(crate) tuple: Vec<TermId>,
    /// Exact raw substitution of the node's effective-∀ body at `tuple`.
    pub(crate) instance: TermId,
    /// Refinement round that produced it.
    pub(crate) round: usize,
}

/// Append-only Γ.
#[derive(Clone, Debug, Default)]
pub(crate) struct InstanceLog {
    entries: Vec<QlraInstance>,
}

impl InstanceLog {
    pub(crate) fn entries(&self) -> &[QlraInstance] {
        &self.entries
    }

    pub(crate) fn len(&self) -> usize {
        self.entries.len()
    }

    pub(crate) fn count_for(&self, node: usize) -> usize {
        self.entries
            .iter()
            .filter(|entry| entry.node == node)
            .count()
    }

    /// Whether `node` already logged exactly this instance term.
    pub(crate) fn contains(&self, node: usize, instance: TermId) -> bool {
        self.entries
            .iter()
            .any(|entry| entry.node == node && entry.instance == instance)
    }

    pub(crate) fn push(&mut self, entry: QlraInstance) {
        self.entries.push(entry);
    }

    /// Distinct instance terms, in log order.
    pub(crate) fn instance_terms(&self) -> Vec<TermId> {
        let mut out: Vec<TermId> = Vec::with_capacity(self.entries.len());
        for entry in &self.entries {
            if !out.contains(&entry.instance) {
                out.push(entry.instance);
            }
        }
        out
    }
}
