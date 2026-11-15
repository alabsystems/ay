// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Authored root spellings the restoring pass installs ONLY because the Alethe
//! printer confines them to their own `assume`.
//!
//! Three installs rest on that promise rather than on the pass's ordinary
//! guards: a single source row whose connective elaboration FOLDED away
//! (`ReachableAuthoredSource::Folded`, `(or (< x 3) false)` over `(< x 3)`),
//! a whole-assertion spelling on a VARIABLE root the atom-hijack guard
//! refuses document-wide (`(or p false)` over `p`), and a spelling that
//! overwrites a disagreeing earlier entry. Each is admitted per root by
//! [`ay_proof::folded_authored_assume_bridge_is_supported`], which cannot see
//! the rest of the document, and then re-judged once the map is final by the
//! printer's own planner over the proof that ships
//! ([`Executor::effective_wire_term_overrides_for_export`]): a term the planner
//! confines leaves the wire channel, a term it leaves document-wide stays.
//!
//! The planner declines a fold bridge whose root has a strict descendant or
//! ancestor another override re-spells (`alethe_printer/authored_assume/
//! boolean_fold/document_spelling.rs`), and only the finished map says which
//! terms those are. MEASURED with that printer guard but without this
//! re-judgement, on `(assert (not (or false (= x y))))` +
//! `(assert (xor (not false) (not (= x y))))` + `(assert (<= x 1))` +
//! `(assert p)`: the per-root admission passed the first row, whose root
//! `(not (= x y))` sits above the second row's root `(= x y)`, but the
//! planner, seeing the second row's spelling on that descendant, left the
//! first spelling document-wide and the printer refused the publication the
//! base had answered `unsat` (with a disclosed foreign `assume`); and
//! `(assert (or p false))` + `(assert (= p false))` went from the base's
//! `unknown` to a refused publication, the variable root's confined
//! `(or p false)` standing beside the second row's document-wide
//! `(= p false)` on its ancestor `(not p)`. Re-judged, both answer exactly as
//! the base does.
//!
//! A spelling the printer does not confine is withdrawn exactly as the pass
//! behaved before these installs existed: a folded row falls back to the
//! entry an earlier pass left (`Untouched`), and a variable-root or
//! overwriting spelling declines the whole map (the base suppression).

use super::*;

/// Rounds of re-judging. A withdrawn spelling can re-expose a document-wide
/// entry under another confined root; past this many rounds every folded
/// install is withdrawn and every other one declines the map.
const MAX_CONFINED_SPELLING_ROUNDS: usize = 4;

/// Why the pass installed a spelling on the strength of the printer's
/// confinement alone.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(super) enum ConfinedSpellingKind {
    /// A folded single-row spelling; withdrawn to the earlier entry.
    Folded,
    /// A spelling the atom guard or a disagreeing entry would have refused;
    /// withdrawn by declining the whole map, as the pass did before.
    Guarded,
}

/// One spelling installed because the printer confines it.
pub(super) struct ConfinedSpelling {
    pub(super) root: TermId,
    /// The entry the root carried before this install.
    pub(super) previous: Option<String>,
    pub(super) kind: ConfinedSpellingKind,
}

impl Executor {
    /// Whether the Alethe printer confines the authored root spelling
    /// `surface` of the single source row behind `root` to that row's
    /// `assume`, deriving the canonical unit with checked steps
    /// ([`ay_proof::folded_authored_assume_bridge_is_supported`], the
    /// printer's own admission) and printing the canonical term everywhere
    /// else. This is the per-root admission; [`Self::withdraw_unconfined_spellings`]
    /// re-judges it against the whole document.
    ///
    /// Such a spelling rides nowhere past its `assume`, which removes the two
    /// hazards the restoring pass otherwise guards against: an entry another
    /// row's descendant left on the root is stale for it (a single row's own
    /// text is the only assertion of the problem that elaborates to the root),
    /// and a VARIABLE root may carry it (the atom-hijack guard of
    /// `collect_root_surface_term_override` protects document-wide entries).
    /// A constant root stays refused: it is shared by every assertion that
    /// folds to it.
    ///
    /// MEASURED at `2c356fd15` on `(assert (or (< x 3) false))` +
    /// `(assert (>= x 5))`, and on the `(and ..)`, `(= .. true)`, `(xor ..
    /// false)` and `(distinct .. false)` siblings: the native SOS lane purged
    /// the collector's spelling, this pass left the root `Untouched`, and AY
    /// published `(assume t0 (< x 3))` under `foreign_assumes=yes`, which
    /// carcara 1.1.0 refused. The same happened on the ordinary lane whenever a
    /// later row's `(not (< x 3))` overwrote the root's spelling, and
    /// `(assert (or p false))` + `(assert (not p))` lost its whole proof
    /// (`unknown` under `--proof`) to the atom guard.
    pub(super) fn printer_confines_authored_spelling(&self, root: TermId, surface: &str) -> bool {
        !matches!(self.ctx.terms.get(root), TermData::Const(_))
            && ay_proof::folded_authored_assume_bridge_is_supported(&self.ctx.terms, root, surface)
    }

    /// The spelling a Parsed source row installs on `root`, and whether it
    /// rests on the printer's confinement alone; `None` declines the whole
    /// map.
    ///
    /// The collector's root entry is the ordinary spelling. The atom-hijack
    /// guard refuses a whole-assertion spelling on an atomic root, and a
    /// spelling that disagrees with the entry already on the root
    /// (`existing`, unless the row `replaces_stale`) declines the map; both
    /// stand unless the printer confines exactly this row's spelling to its
    /// `assume`.
    pub(super) fn parsed_root_spelling(
        &mut self,
        root: TermId,
        source: &FrontendTerm,
        existing: Option<&String>,
        replaces_stale: bool,
    ) -> Option<(String, bool)> {
        let mut root_override = DetHashMap::default();
        proof_surface_syntax::collect_root_surface_term_override(
            &mut self.ctx,
            root,
            source,
            &mut root_override,
        );
        let (surface, atom_guarded) = match root_override.remove(&root) {
            Some(surface) => (surface, false),
            None => (
                proof_surface_syntax::authored_root_surface(&mut self.ctx, source),
                true,
            ),
        };
        let conflicting = !atom_guarded
            && !replaces_stale
            && existing.is_some_and(|existing| existing != &surface);
        let guarded = atom_guarded || conflicting;
        if guarded && !self.printer_confines_authored_spelling(root, &surface) {
            return None;
        }
        Some((surface, guarded))
    }

    /// Install the spelling of a folded single source row when the printer
    /// confines it, recording the install for the final re-judgement.
    pub(super) fn install_folded_spelling(
        &mut self,
        root: TermId,
        source: &FrontendTerm,
        overrides: &mut DetHashMap<TermId, String>,
        confined: &mut Vec<ConfinedSpelling>,
    ) -> bool {
        let surface = proof_surface_syntax::authored_root_surface(&mut self.ctx, source);
        if overrides.get(&root) == Some(&surface)
            || !self.printer_confines_authored_spelling(root, &surface)
        {
            return false;
        }
        let previous = overrides.insert(root, surface);
        confined.push(ConfinedSpelling {
            root,
            previous,
            kind: ConfinedSpellingKind::Folded,
        });
        true
    }

    /// Re-judge every confined install against the FINAL map with the
    /// printer's own planner over `proof`, and withdraw each spelling it does
    /// not confine. `None` when a guarded spelling is withdrawn (the caller
    /// declines the map, as the pass did before such spellings existed);
    /// otherwise whether `overrides` changed.
    pub(super) fn withdraw_unconfined_spellings(
        &self,
        proof: &Proof,
        mut confined: Vec<ConfinedSpelling>,
        overrides: &mut DetHashMap<TermId, String>,
    ) -> Option<bool> {
        let mut changed = false;
        for _ in 0..MAX_CONFINED_SPELLING_ROUNDS {
            if confined.is_empty() {
                return Some(changed);
            }
            let wire = self
                .effective_wire_term_overrides_for_export(proof, Some(overrides))
                .ok()
                .flatten();
            let unconfined = |install: &ConfinedSpelling| {
                wire.as_ref()
                    .is_none_or(|wire| wire.contains_key(&install.root))
            };
            if !confined.iter().any(unconfined) {
                return Some(changed);
            }
            let (withdrawn, kept): (Vec<_>, Vec<_>) = confined.into_iter().partition(unconfined);
            for install in withdrawn {
                if install.kind == ConfinedSpellingKind::Guarded {
                    return None;
                }
                withdraw(install, overrides);
                changed = true;
            }
            confined = kept;
        }
        // Still withdrawing after the last round: withdraw every folded
        // install (the pass's behaviour before they existed) and decline any
        // guarded one.
        for install in confined {
            if install.kind == ConfinedSpellingKind::Guarded {
                return None;
            }
            withdraw(install, overrides);
            changed = true;
        }
        Some(changed)
    }
}

/// Put back the entry `install` replaced.
fn withdraw(install: ConfinedSpelling, overrides: &mut DetHashMap<TermId, String>) {
    match install.previous {
        Some(previous) => overrides.insert(install.root, previous),
        None => overrides.remove(&install.root),
    };
}

// This file is loaded through a `#[path]`, so the test module's path is
// relative to this directory.
#[cfg(test)]
#[path = "confined_spelling_tests.rs"]
mod tests;
