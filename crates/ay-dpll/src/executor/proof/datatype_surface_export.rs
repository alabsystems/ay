// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! One optional canonical datatype proof/problem/surface presentation.
//!
//! Native proof quality and premise authority are unchanged. The only term
//! rewrite is an exact registered tester identity's standard SMT-LIB spelling.

use super::{Executor, DEFAULT_ALETHE_EMISSION_WORK_BUDGET};

const MAX_WORK: usize = 16 * 1024 * 1024;
const MAX_BYTES: usize = 4 * 1024 * 1024;

impl Executor {
    pub(crate) fn try_export_last_unsat_datatype_pair(
        &self,
    ) -> Option<(String, String, ay_proof::CarcaraSurface)> {
        if self.last_unsat_proof_reconstruction_suppressed
            || self.last_proof_has_finite_enum_sidecar()
            || self.ctx.proof_transport_datatype_capacity().is_none()
            // Invented field-variable surfaces require their separate exact
            // projection codec; never silently omit that semantic channel.
            || self.ctx.has_dt_field_surface_entries()
        {
            return None;
        }
        let proof = self.last_proof_with_authenticated_alethe_surface()?;
        let stop = self.make_strict_check_stop();
        let mut work = 0usize;
        let mut bytes = 0usize;
        let mut progress = |additional_work: usize, additional_bytes: usize| {
            let Some(next_work) = work.checked_add(additional_work) else {
                return false;
            };
            let Some(next_bytes) = bytes.checked_add(additional_bytes) else {
                return false;
            };
            work = next_work;
            bytes = next_bytes;
            !stop() && work <= MAX_WORK && bytes <= MAX_BYTES
        };
        super::external_support::preflight_presentation_payload(proof, &mut progress)?;
        // The existing scope merger copies and deduplicates these borrowed
        // source rows. Price its quadratic contains-work and Vec upper bound
        // before asking it to allocate, preserving its exact premise policy.
        let original = self.proof_original_problem_assertions_slice();
        let problem_len = self
            .proof_problem_assertion_provenance
            .as_ref()
            .map_or(original.len(), |source| source.problem_assertions.len());
        let upper = problem_len
            .checked_add(original.len())?
            .checked_add(self.last_proof_rebuild_originals.len())?
            .checked_add(self.last_assumptions.as_ref().map_or(0, Vec::len))?;
        if !progress(upper.checked_mul(upper)?, upper.checked_mul(8)?) {
            return None;
        }
        let scope = self.proof_export_scope_assertions_for(proof)?;
        let overrides =
            self.datatype_problem_spelling_overrides(self.last_proof_term_overrides.as_ref())?;
        let (problem, constructors) =
            self.alethe_datatype_problem_with_constructors(&scope, Some(&overrides))?;
        let (rendered, dialect) = ay_proof::capture_alethe_dialect_report(|| {
            self.in_alethe_dialect(|| {
                ay_proof::try_export_alethe_with_paired_datatype_constructors(
                    proof,
                    &self.ctx.terms,
                    &scope,
                    Some(&overrides),
                    &constructors,
                    Some(DEFAULT_ALETHE_EMISSION_WORK_BUDGET),
                )
            })
        });
        let rendered = rendered.ok()?;
        if rendered.len() > MAX_BYTES
            || rendered.contains(":rule hole")
            || rendered.contains(":rule trust")
            || stop()
        {
            return None;
        }
        let surface = self
            .problem_and_proof_surface(proof, Some(&overrides))
            .with_dialect_report(&dialect);
        Some((rendered, problem, surface))
    }
}
