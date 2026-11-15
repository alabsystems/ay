// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Seal canonical-row identity roots against the completed SOURCE override map.
//!
//! ONLY `ReachableAuthoredSource::Identity` roots reach here — the ones a
//! source row spells exactly as the Alethe printer renders them, so pinning
//! the canonical text pins what the problem wrote. A `RawIdentity` root must
//! never be passed in: its grant authenticates the root's TERM, and its
//! authored spelling lives in DESCENDANT overrides (an author-named binder, a
//! `(_ bvN W)` literal). Pinning one to its canonical rendering publishes an
//! `assume` the problem never wrote while every later step keeps spelling the
//! same subterm the other way — the document carcara refuses at its first
//! premise, and the one the printer's `and_pos` surface guard declines.
//!
//! The later datatype-field merge remains separate: its source-wins policy
//! preserves these whole-root pins and unrelated selector spellings. This pass
//! does not canonicalize datatype-only rewrites or later printer-owned channels;
//! replacing an invented field's selector spelling with its bare internal name
//! would require a different authored-surface contract.

use super::*;

impl Executor {
    /// Root authentication is already complete. This only restores its exact
    /// printed text; child spellings remain available at every other root.
    pub(in crate::executor::proof) fn seal_authored_identity_surfaces(
        &self,
        roots: &[TermId],
        overrides: &mut DetHashMap<TermId, String>,
    ) -> Option<bool> {
        if roots.is_empty() || overrides.is_empty() {
            return Some(false);
        }
        if !proof_surface_syntax::surface_override_map_is_bounded(overrides) {
            return None;
        }
        let (effective, canonical) =
            canonical_render::render_pair(&self.ctx.terms, roots.iter().copied(), overrides)?;
        let mut candidate = overrides.clone();
        let mut changed = false;
        for (root, surface) in canonical {
            if effective.get(&root)? != &surface {
                candidate.insert(root, surface);
                changed = true;
            }
        }
        if !proof_surface_syntax::surface_override_map_is_bounded(&candidate) {
            return None;
        }
        if changed {
            *overrides = candidate;
        }
        Some(changed)
    }
}

// EXPLICIT: this file is itself loaded through a `#[path]`, so a bare
// `mod tests;` resolves against `source_resolution/`, not against
// `source_resolution/identity_surfaces/` — it silently loaded the PARENT
// module's `tests.rs` (measured: three `source_resolution::tests` names ran
// twice and not one test below was compiled).
#[cfg(test)]
#[path = "identity_surfaces/tests.rs"]
mod tests;
