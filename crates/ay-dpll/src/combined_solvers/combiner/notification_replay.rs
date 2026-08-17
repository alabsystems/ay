// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Cached replay of persistent EUF-to-array equality notifications.

use ay_core::{TermId, TheoryLit};

use super::TheoryCombiner;

impl TheoryCombiner<'_> {
    pub(super) fn euf_array_replay_capacity_exhausted(&self) -> bool {
        self.imported_euf_array_notify_replay_edges
            .capacity_exhausted()
            || self.euf_array_notify_replay_edges.capacity_exhausted()
    }

    pub(super) fn record_array_assignment(
        &mut self,
        direct_equality: Option<(TermId, TermId, TheoryLit)>,
        normalized_lit: TheoryLit,
        previous_assignment: Option<bool>,
    ) {
        if let Some((lhs, rhs, reason)) = direct_equality {
            self.record_euf_array_notify_parent_edge(lhs, rhs, vec![reason]);
        }
        match previous_assignment {
            None => {
                let Self {
                    euf_array_notify_replay_cache: cache,
                    imported_euf_array_notify_replay_edges: imported,
                    euf_array_notify_replay_edges: local,
                    euf_array_notify_parent: parent,
                    ..
                } = self;
                cache.assignment_added(normalized_lit, imported, local, parent);
            }
            Some(previous) if previous != normalized_lit.value => {
                // An already-applied array notification cannot be selectively
                // undone when a caller overwrites a SAT assignment in scope.
                self.euf_array_notify_parent.clear();
                self.euf_array_notify_replay_cache.contradictory_overwrite();
            }
            Some(_) => {}
        }
    }

    pub(crate) fn replay_valid_euf_array_notifications(&mut self) -> usize {
        if self.arrays.is_none()
            || (self.imported_euf_array_notify_replay_edges.is_empty()
                && self.euf_array_notify_replay_edges.is_empty())
        {
            return 0;
        }

        let notification_count = {
            let Self {
                imported_euf_array_notify_replay_edges: imported,
                euf_array_notify_replay_edges: local,
                euf_array_notify_replay_cache: cache,
                current_assignments: assignments,
                euf_array_notify_parent: parent,
                arrays,
                ..
            } = self;
            cache.ensure_forest(imported, local, assignments, parent);
            if !cache.needs_application() {
                return 0;
            }
            let notification_count = cache.unapplied_forest().len();
            if let Some(arrays) = arrays {
                for &(target, source) in cache.unapplied_forest() {
                    arrays.notify_equality(target, source);
                }
            }
            cache.mark_applied();
            notification_count
        };
        if notification_count > 0 {
            self.mark_arrays_dirty();
        }
        notification_count
    }
}
