// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::mem::size_of;

use ay_core::{Symbol, TermData, TermId, TheoryLemmaProof};
use ay_sat::{ClauseTrace, ResolutionValidationError, ResolutionValidationResource};

use super::{exact_checked_add, exact_checked_mul, exact_sort_work, EXACT_NEW_NOT_BYTES};
use crate::sat_proof_manager::SatProofManager;

impl SatProofManager<'_> {
    pub(in crate::sat_proof_manager) fn clausification_preflight(
        &self,
        source: TermId,
        traced_clause_len: usize,
    ) -> Result<(usize, usize), ResolutionValidationError> {
        let (source_arity, symbol_bytes) = match self.terms.get(source) {
            TermData::App(symbol, args) => {
                let index_bytes = match symbol {
                    Symbol::Indexed(_, indices) => exact_checked_mul(
                        indices.len(),
                        size_of::<u32>(),
                        ResolutionValidationResource::Bytes,
                    )?,
                    Symbol::Named(_) => 0,
                    _ => 0,
                };
                (
                    args.len(),
                    exact_checked_add(
                        symbol.name().len(),
                        index_bytes,
                        ResolutionValidationResource::Bytes,
                    )?,
                )
            }
            TermData::Ite(_, _, _) => (3, 3),
            _ => (0, 0),
        };
        let expected_len = exact_checked_add(source_arity, 1, ResolutionValidationResource::Work)?;
        let work = exact_checked_add(
            exact_checked_add(
                exact_checked_mul(source_arity, 6, ResolutionValidationResource::Work)?,
                exact_sort_work(expected_len)?,
                ResolutionValidationResource::Work,
            )?,
            exact_sort_work(traced_clause_len)?,
            ResolutionValidationResource::Work,
        )?;

        // `canonicalize_tautology_clause` clones the application head and full
        // argument vector even for indexed two-literal rules, and some rules
        // additionally build complements/expected vectors. This deliberately
        // generous per-argument envelope covers those simultaneous values and
        // possible newly interned `Not` terms.
        let argument_bytes =
            exact_checked_mul(source_arity, 512, ResolutionValidationResource::Bytes)?;
        let expected_bytes = exact_checked_mul(
            expected_len,
            exact_checked_mul(3, size_of::<TermId>(), ResolutionValidationResource::Bytes)?,
            ResolutionValidationResource::Bytes,
        )?;
        let bytes = exact_checked_add(
            exact_checked_add(
                argument_bytes,
                expected_bytes,
                ResolutionValidationResource::Bytes,
            )?,
            exact_checked_add(symbol_bytes, 1024, ResolutionValidationResource::Bytes)?,
            ResolutionValidationResource::Bytes,
        )?;
        Ok((work, bytes))
    }

    pub(in crate::sat_proof_manager) fn theory_annotation_preflight(
        annotation: &TheoryLemmaProof,
        traced_clause_len: usize,
    ) -> Result<(usize, usize), ResolutionValidationError> {
        let cutting_plane_coefficients = match annotation.lia.as_ref() {
            Some(ay_core::LiaAnnotation::CuttingPlane(cutting_plane)) => {
                cutting_plane.farkas.coefficients.len()
            }
            _ => 0,
        };
        let coefficient_count = exact_checked_add(
            annotation
                .farkas
                .as_ref()
                .map_or(0, |farkas| farkas.coefficients.len()),
            cutting_plane_coefficients,
            ResolutionValidationResource::Work,
        )?;
        let clause_sort_work = exact_checked_add(
            exact_sort_work(annotation.clause.len())?,
            exact_sort_work(traced_clause_len)?,
            ResolutionValidationResource::Work,
        )?;
        let work = exact_checked_add(
            exact_checked_mul(clause_sort_work, 3, ResolutionValidationResource::Work)?,
            exact_checked_mul(
                coefficient_count,
                exact_checked_add(
                    (usize::BITS - (annotation.clause.len().max(2) - 1).leading_zeros()) as usize,
                    4,
                    ResolutionValidationResource::Work,
                )?,
                ResolutionValidationResource::Work,
            )?,
            ResolutionValidationResource::Work,
        )?;
        let clause_terms = exact_checked_add(
            annotation.clause.len(),
            traced_clause_len,
            ResolutionValidationResource::Bytes,
        )?;
        let bytes = exact_checked_add(
            exact_checked_mul(clause_terms, 256, ResolutionValidationResource::Bytes)?,
            exact_checked_add(
                exact_checked_mul(coefficient_count, 128, ResolutionValidationResource::Bytes)?,
                2048,
                ResolutionValidationResource::Bytes,
            )?,
            ResolutionValidationResource::Bytes,
        )?;
        Ok((work, bytes))
    }

    pub(in crate::sat_proof_manager) fn precharge_term_store_growth(
        &self,
        trace: &ClauseTrace,
        progress: &mut dyn FnMut(usize, usize) -> Result<(), ResolutionValidationError>,
    ) -> Result<(usize, usize), ResolutionValidationError> {
        let mut potential_new_nots = 0usize;
        for (trace_index, entry) in trace.entries().iter().enumerate() {
            if trace_index % 1024 == 0 {
                progress(0, 0)?;
            }
            if !entry.is_original {
                continue;
            }

            // Charge the full literal scan before inspecting polarity.
            progress(entry.clause.len(), 0)?;
            for literal in entry.clause {
                if !literal.is_positive() {
                    potential_new_nots = exact_checked_add(
                        potential_new_nots,
                        1,
                        ResolutionValidationResource::Bytes,
                    )?;
                }
            }

            // `canonicalize_tautology_clause` materializes `not_source` and
            // may negate every immediate connective argument. Count the full
            // arity even though most rules use fewer terms, so later rule
            // additions cannot silently escape this envelope.
            if let Some(annotation) =
                Self::original_annotation_by_id(self.clausification_proofs, entry.id)
            {
                let source_arity = if annotation.source_term.index() < self.terms.len() {
                    match self.terms.get(annotation.source_term) {
                        TermData::App(_, args) => args.len(),
                        TermData::Ite(_, _, _) => 3,
                        _ => 0,
                    }
                } else {
                    0
                };
                potential_new_nots = exact_checked_add(
                    potential_new_nots,
                    exact_checked_add(source_arity, 1, ResolutionValidationResource::Bytes)?,
                    ResolutionValidationResource::Bytes,
                )?;
            }
        }

        let baseline = self.terms.true_memory_bytes();
        if potential_new_nots == 0 {
            progress(1, 0)?;
            return Ok((baseline, 0));
        }
        let new_term_bytes = exact_checked_mul(
            potential_new_nots,
            EXACT_NEW_NOT_BYTES,
            ResolutionValidationResource::Bytes,
        )?;
        let growth_allowance = exact_checked_add(
            baseline,
            new_term_bytes,
            ResolutionValidationResource::Bytes,
        )?;
        // Charge before the first possible `mk_not_raw`. One current
        // footprint covers a geometric reallocation of every pre-existing
        // TermStore container across the batch; the per-term allowance covers
        // newly retained entries and buckets.
        progress(1, growth_allowance)?;
        Ok((baseline, growth_allowance))
    }

    pub(in crate::sat_proof_manager) fn reconcile_term_store_growth(
        &self,
        baseline: usize,
        charged_growth: &mut usize,
        progress: &mut dyn FnMut(usize, usize) -> Result<(), ResolutionValidationError>,
    ) -> Result<(), ResolutionValidationError> {
        let current = self.terms.true_memory_bytes();
        let actual_growth =
            current
                .checked_sub(baseline)
                .ok_or(ResolutionValidationError::AccountingOverflow {
                    resource: ResolutionValidationResource::Bytes,
                })?;
        if actual_growth > *charged_growth {
            let excess = actual_growth.checked_sub(*charged_growth).ok_or(
                ResolutionValidationError::AccountingOverflow {
                    resource: ResolutionValidationResource::Bytes,
                },
            )?;
            progress(0, excess)?;
            *charged_growth = actual_growth;
        } else {
            progress(0, 0)?;
        }
        Ok(())
    }
}
