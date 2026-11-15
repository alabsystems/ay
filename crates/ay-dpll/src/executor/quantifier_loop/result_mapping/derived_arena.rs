// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The one vetoed path to derived-arena compaction.

use super::checked_isolated_solve::carries_name_encoded_term_ids;

/// Rebuild a derived query's cloned arena around the roots it holds -- the one
/// path to [`ay_frontend::Context::compact_terms_for_derived_query`] in this
/// crate, so no caller can relabel an arena whose internal names spell
/// `TermId`s (A-UFA-g6-div0: the forged-UNSAT guard's rebuild arrived without
/// the veto the other callers carried, and g6_100167 panicked in its nested
/// solve). `None`: such an arena, left as the unpruned clone. `Some(false)`:
/// the compaction could not relabel every held id; abandon the context.
pub(in crate::executor) fn compact_derived_arena(ctx: &mut ay_frontend::Context) -> Option<bool> {
    if carries_name_encoded_term_ids(&ctx.terms) {
        return None;
    }
    Some(ctx.compact_terms_for_derived_query())
}
