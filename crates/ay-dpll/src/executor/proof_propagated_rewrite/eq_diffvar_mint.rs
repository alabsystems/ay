// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Producer mint for the `EqDiffVar` atom-fold channel (#4751).
//!
//! The consumer lane is [`super::eq_diffvar_lane`]; the derivation it plans is
//! [`super::eq_diffvar_bridge`]. This module is only the recording side: what
//! the preprocessing pass hands over, which folds are dropped before they can
//! reach a bridge, and where the records sit on the store's stamp axis.

use super::*;
use crate::preprocess::EqDiffVarAtomRecord;

impl Executor {
    /// Mint provenance for the `EqDiffVar` atom-fold round (#4751).
    ///
    /// The pass rewrites assertions IN PLACE — `(or (not g) (= a b))` becomes
    /// `(or (not g) (= d 0))` — and APPENDS the definitional pair
    /// `(<= d lin)` / `(<= lin d)` for the fresh `d` it minted. Its own wiring
    /// site already records the residual gap this closes: the definitional
    /// pair is certifiable (`fresh_def_bound`, #eq-diffvar-uncertifiable) but
    /// the REWRITE is not, so `demote_non_problem_assumptions` stamps every
    /// rewritten assertion a premiseless `trust`. Measured on `dillig12_m`,
    /// that is the whole residual population: 111 such steps over 44 rejected
    /// proofs, every one mentioning a difference variable.
    ///
    /// Records are HINTS on this module's standing contract. The replay
    /// re-derives `(= atom replacement)` from the two definitional bounds by a
    /// rational combination the checker's OWN validator re-checks before any
    /// step is emitted, and declines on any mismatch.
    ///
    /// Fail-closed per leg: a fold whose definiendum is not an atomic variable
    /// at the definiens' sort, or whose atom is not a binary equality, is
    /// dropped; a `before`/`after` pair the pass did not produce positionally
    /// withholds the WHOLE run, matching the over-cap policy in
    /// [`Executor::merge_propagation_records`].
    pub(in crate::executor) fn extend_eq_diffvar_provenance(
        &mut self,
        before: &[TermId],
        after: &[TermId],
        folds: &[crate::preprocess::AtomFold],
    ) {
        if !crate::quant_unit_authority::quant_unit_authority_enabled() {
            return;
        }
        // `EqDiffVar` rewrites slots `0..before.len()` in place and APPENDS its
        // definitional pair, so `after` is at least as long. A shorter `after`
        // means the caller re-shaped the stack between the snapshots, and
        // `before[i] -> after[i]` is then not a rewrite pair.
        if after.len() < before.len() || folds.is_empty() {
            return;
        }
        let rewrites: Vec<crate::preprocess::PropagatedRewriteRecord> = before
            .iter()
            .zip(after.iter())
            .filter(|(before, after)| before != after)
            .map(
                |(&before, &after)| crate::preprocess::PropagatedRewriteRecord {
                    before,
                    after,
                    stamp: 1,
                },
            )
            .collect();
        if rewrites.is_empty() {
            return;
        }
        let atoms: Vec<EqDiffVarAtomRecord> = folds
            .iter()
            .filter(|fold| Self::is_eq_diffvar_fold_well_formed(&self.ctx.terms, fold))
            .map(|fold| EqDiffVarAtomRecord {
                atom: fold.atom,
                replacement: fold.replacement,
                definiendum: fold.definiendum,
                definiens: fold.definiens,
                stamp: 1,
            })
            .collect();
        if atoms.is_empty() {
            return;
        }
        self.store_eq_diffvar_provenance(rewrites, atoms);
    }

    /// File one complete EqDiffVar record set on the shared stamp axis and
    /// enforce this lane's independent fail-closed cap.
    fn store_eq_diffvar_provenance(
        &mut self,
        rewrites: Vec<crate::preprocess::PropagatedRewriteRecord>,
        atoms: Vec<EqDiffVarAtomRecord>,
    ) {
        // STAMP. The `EqDiffVar` round runs BETWEEN the top-level
        // unit-propagation round and the `VariableSubstitution` round, and the
        // replay decides eligibility by `stamp <= target stamp`, so it has to
        // land strictly ABOVE the unit-propagation round's stamp and strictly
        // BELOW the substitution round's. Both strictnesses are load-bearing
        // and each is measured on `dillig12_m`:
        //
        // * TIED WITH THE SUBSTITUTION ROUND (above), the substitution round's
        //   ENTRIES become eligible while this round's rewrite is being
        //   replayed, and rewriting a subterm the pass had not yet touched
        //   reconstructs a term it never wrote: 38 of 111 target assumes stay
        //   underived, and re-measured on the current tree that arm is 34-35
        //   rejected proofs / 76-78 premiseless `Trust` against a 19 / 53
        //   baseline.
        // * TIED WITH THE UNIT-PROPAGATION ROUND (below), the mirror image: THIS
        //   channel becomes eligible while a unit-propagation rewrite is being
        //   replayed, so a disjunct the unit round merely DELETED comes back
        //   atom-folded and the recorded `after` is never reached. Measured, that
        //   tie is the whole residual premiseless-`Trust` census on this
        //   benchmark: 53 steps over 9 rejected proofs, all of them either an
        //   `or` whose authored form lost a disjunct to unit propagation, or a
        //   definitional bound reached through one.
        //
        // Consecutive `merge_propagation_records` rounds are spaced
        // `PROPAGATE_VALUES_STAMP_SCALE` apart precisely so a value strictly
        // between them exists; the records are filed directly at
        // `watermark + 1` and the `PropagateValues` vectors are left untouched.
        // Going through `merge_propagation_records` instead would advance the
        // shared offset, and shifting the stamps that store hands the EXISTING
        // replay changes which assertions that lane derives, which changes which
        // UNSATs certify, and turns two ay-chc route fixtures red.
        let store = &mut self.propagated_value_provenance;
        let watermark = store
            .rewrites
            .iter()
            .map(|record| record.stamp)
            .chain(store.entries.iter().map(|entry| entry.stamp))
            .max()
            .unwrap_or(0);
        // (#4751) File ONE stamp above the watermark. Eligibility is
        // `entry.stamp <= target.stamp`, and `merge_propagation_records` now
        // spaces rounds two apart, so this lands strictly between the unit
        // round and the substitution round. Filing AT the watermark ties with
        // the unit round and its rewrites replay under this channel, which is
        // what left the residual trust steps.
        let filed = watermark.saturating_add(1);
        store
            .eq_diffvar_rewrites
            .extend(rewrites.into_iter().map(|mut record| {
                record.stamp = filed;
                record
            }));
        store
            .eq_diffvar_atoms
            .extend(atoms.into_iter().map(|mut atom| {
                atom.stamp = filed;
                atom
            }));
        // Capped SEPARATELY, and clearing only itself: folding this channel
        // into the shared cap would let records the `PropagateValues` replay
        // never reads wipe the records it depends on — a silent degradation of
        // the existing lane rather than a fail-closed decline of this one.
        if store.eq_diffvar_rewrites.len() > MAX_STORED_PROPAGATION_RECORDS
            || store.eq_diffvar_atoms.len() > MAX_STORED_PROPAGATION_RECORDS
        {
            tracing::debug!(
                eq_diffvar_rewrites = store.eq_diffvar_rewrites.len(),
                eq_diffvar_atoms = store.eq_diffvar_atoms.len(),
                cap = MAX_STORED_PROPAGATION_RECORDS,
                "#4751 EqDiffVar provenance over cap; withholding those records"
            );
            store.eq_diffvar_rewrites.clear();
            store.eq_diffvar_atoms.clear();
        }
    }

    /// The local shape conditions the bridge needs: a binary equality atom
    /// folded to a binary equality atom over an ATOMIC variable at the
    /// definiens' sort. Anything else is dropped here rather than carried to a
    /// bridge that would decline anyway.
    pub(super) fn is_eq_diffvar_fold_well_formed(
        terms: &TermStore,
        fold: &crate::preprocess::AtomFold,
    ) -> bool {
        let binary_equality = |term: TermId| {
            matches!(
                terms.get(term),
                TermData::App(symbol, args) if symbol.name() == "=" && args.len() == 2
            )
        };
        binary_equality(fold.atom)
            && binary_equality(fold.replacement)
            && fold.atom != fold.replacement
            && matches!(terms.get(fold.definiendum), TermData::Var(_, _))
            && terms.sort(fold.definiendum) == terms.sort(fold.definiens)
    }
}
