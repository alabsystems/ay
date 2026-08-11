// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact emitted-vector census for conjunctive provenance-OR transfer.

use ay_core::kani_compat::DetHashSet as HashSet;

use super::{ProvenanceOrAndTransferOutcome, ProvenanceOrAndTransferPlan};

fn add(total: &mut usize, amount: usize) -> Option<()> {
    *total = total.checked_add(amount)?;
    Some(())
}

fn decreasing(start: usize, removals: usize) -> Option<usize> {
    if removals > start {
        return None;
    }
    removals.checked_mul(start)?.checked_sub(
        removals
            .checked_mul(removals.checked_add(1)?)?
            .checked_div(2)?,
    )
}

impl ProvenanceOrAndTransferPlan {
    /// Count every generated clause, certificate vector, and rule argument
    /// before any replacement `Proof` is constructed.
    pub(in crate::executor::proof_repair) fn emitted_literal_volume(&self) -> Option<usize> {
        let mut total = 0usize;
        add(&mut total, self.authored_sources.len())?;
        add(&mut total, self.source_disjuncts.len())?;

        let mut current: HashSet<_> = self.source_disjuncts.iter().copied().collect();
        if current.len() != self.source_disjuncts.len() {
            return None;
        }
        let mut emitted_true = false;
        for outcome in &self.outcomes {
            match outcome {
                ProvenanceOrAndTransferOutcome::Refute(refutation) => {
                    let width = refutation.lemma.clause.len();
                    // Farkas clause + coefficients + authored-support chain.
                    add(&mut total, width)?;
                    add(&mut total, width)?;
                    add(
                        &mut total,
                        decreasing(width, refutation.lemma.supports.len())?,
                    )?;
                    // and_pos clause, its source argument, and unit resolution.
                    add(&mut total, 2)?;
                    add(&mut total, 1)?;
                    add(&mut total, 1)?;
                }
                ProvenanceOrAndTransferOutcome::Map(mapping) => {
                    let child_count = mapping.target_children.len();
                    // Full-multiplicity and_neg plus its exact source argument.
                    add(&mut total, child_count.checked_add(1)?)?;
                    add(&mut total, 1)?;
                    for _ in &mapping.projections {
                        // and_pos clause and source argument.
                        add(&mut total, 3)?;
                    }
                    let resolution_count = mapping
                        .projections
                        .len()
                        .checked_add(usize::from(mapping.has_true))?;
                    if resolution_count == 0 {
                        return None;
                    }
                    // The first resolution replaces a target-child blocker by
                    // not(source); later links share that blocker and shrink by
                    // one. Duplicate true children are checker-set-normalized
                    // and therefore consume one true-pivot resolution.
                    let unique_start = resolution_count.checked_add(1)?;
                    let resolution_volume =
                        resolution_count.checked_mul(unique_start)?.checked_sub(
                            resolution_count
                                .checked_mul(resolution_count.saturating_sub(1))?
                                .checked_div(2)?,
                        )?;
                    add(&mut total, resolution_volume)?;
                    if mapping.has_true {
                        if !emitted_true {
                            add(&mut total, 1)?; // true unit
                            emitted_true = true;
                        }
                        add(&mut total, 2)?; // weakening [true, not(source)]
                    }
                }
            }

            if !current.remove(&outcome.source()) {
                return None;
            }
            if let ProvenanceOrAndTransferOutcome::Map(mapping) = outcome {
                current.insert(mapping.target);
            }
            // The outer source-OR resolution conclusion.
            add(&mut total, current.len())?;
        }

        let mut remaining: Vec<_> = current.into_iter().collect();
        remaining.sort_unstable();
        if remaining != self.remaining_targets {
            return None;
        }
        if remaining.is_empty() {
            add(&mut total, 1)?; // weakening empty to the goal
            return Some(total);
        }
        for width in (1..=remaining.len()).rev() {
            add(&mut total, 2)?; // or_neg clause
            add(&mut total, 1)?; // exact goal source argument
            add(&mut total, width)?; // goal-link resolution
        }
        add(&mut total, 1)?; // final contraction [goal]
        Some(total)
    }
}
