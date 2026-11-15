// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Exact source sharing with separately bounded traversal and elaboration work.

use ay_core::TermId;
use ay_frontend::{command::Term, Context, SharedSurfaceElaboration, SharedSurfaceLimits};

use super::ground;

/// Raw reconstruction and canonical typing have separate caches. The frontend
/// owns all typing, declaration identity and exact-source canonical sharing.
pub(super) struct Plan<'source> {
    typed: SharedSurfaceElaboration<'source>,
    cache: Vec<Option<TermId>>,
    pub(super) reads_array: bool,
}

impl<'source> Plan<'source> {
    pub(super) fn new(
        root: &'source Term,
        context: &mut Context,
        stopped: impl FnMut(&Context) -> bool,
    ) -> Option<Self> {
        use crate::executor::proof_repair::proof_trust_surgery_surface_audit::{
            surface_source_work_probe_as, SurfaceWorkModel,
        };
        surface_source_work_probe_as(root, SurfaceWorkModel::Traversal).ok()?;
        let typed = context.elaborate_shared_surface_reading_array(
            root,
            SharedSurfaceLimits {
                distinct_nodes: ground::MAX_NODES,
                depth: ground::MAX_DEPTH,
                node_visits: ground::MAX_NODE_VISITS,
                token_visits: ground::MAX_TOKEN_VISITS,
            },
            stopped,
        )?;
        Some(Self {
            cache: vec![None; typed.len()],
            reads_array: typed.reads_array(),
            typed,
        })
    }

    pub(super) fn canonical(&self, context: &Context, source: &Term) -> Option<TermId> {
        self.typed.canonical(context, source)
    }

    pub(super) fn cached(&self, context: &Context, source: &Term) -> Option<Option<TermId>> {
        self.cache
            .get(self.typed.node_index(context, source)?)
            .copied()
    }

    pub(super) fn record(&mut self, context: &Context, source: &Term, raw: TermId) -> Option<()> {
        let id = self.typed.node_index(context, source)?;
        *self.cache.get_mut(id)? = Some(raw);
        Some(())
    }
}

#[cfg(test)]
#[path = "proof_trust_surgery_surface_ground_dag_tests.rs"]
mod tests;
