// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Atomic installation of original-source guarded-store consequences.

use super::*;
use crate::preprocess::guarded_store_batch::{discover, install::prepare};

impl Executor {
    /// Only the early, assumption-free array/BV owner calls this, before its
    /// first flattening pass. The captured original vector is never replaced
    /// by derived roots in source authority or later model restoration.
    pub(super) fn prepare_guarded_store_preprocessing(
        &mut self,
        originals: &[TermId],
        source_sets: &mut Vec<Vec<TermId>>,
    ) -> Option<Box<dyn FnMut(usize, usize) -> bool>> {
        self.last_statistics
            .set_int("smt.abv.guarded_store.definitions", 0);
        self.last_statistics
            .set_int("smt.abv.guarded_store.derived_units", 0);
        if !crate::quant_unit_authority::quant_unit_authority_enabled()
            || self.term_memory_exceeded()
            // Avoid the legacy positional/source-whitelist fallback while
            // working roots include derived units. Public solves install this
            // authority already; a private route without it keeps its old path.
            || self.proof_problem_assertion_provenance.is_none()
        {
            return None;
        }
        let mut progress = self.array_preprocessing_progress();
        if !progress(originals.len(), 0) || self.ctx.assertions != originals {
            return None;
        }
        let batch = discover(&mut self.ctx.terms, originals, progress.as_mut())?;
        let definitions = batch.definitions().len();
        if definitions == 0 && batch.activated_units().is_empty() {
            return Some(progress);
        }
        let prepared = prepare(
            &self.ctx.terms,
            originals,
            &self.ctx.assertions,
            source_sets,
            batch,
            progress.as_mut(),
        )?;
        if self.term_memory_exceeded() || !progress(0, 0) {
            return None;
        }
        let (assertions, prepared_sources, units) = prepared.into_parts();
        let count = units.len();
        if !self.retain_array_preprocessing_units(units, progress.as_mut()) {
            return None;
        }
        // Infallible moves after the last refusing boundary publish all three
        // outputs together. Derived rows retain empty authored-source sets.
        self.ctx.assertions = assertions;
        *source_sets = prepared_sources;
        self.last_statistics
            .set_int("smt.abv.guarded_store.definitions", definitions as u64);
        self.last_statistics
            .set_int("smt.abv.guarded_store.derived_units", count as u64);
        Some(progress)
    }
}

#[cfg(test)]
mod tests;
