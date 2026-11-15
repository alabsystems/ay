// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Saturation instances for the exists-bridge chain lane, split from
//! the producer so each file stays inside the size ratchet.

use super::*;

impl Executor {
    /// Saturation candidates for one binder position of one universal:
    /// fresh bridge witnesses of the sort first, then this decision's
    /// recorded binding values at that position, then hint/ground terms.
    fn bridge_candidate_column(
        &self,
        authored: &[TermId],
        quantifier: TermId,
        position: usize,
        sort: &Sort,
        bound_names: &ay_core::kani_compat::DetHashSet<String>,
        witnesses: &[(Sort, TermId)],
    ) -> Vec<TermId> {
        let mut column: Vec<TermId> = witnesses
            .iter()
            .filter(|(witness_sort, _)| witness_sort == sort)
            .map(|(_, witness)| *witness)
            .collect();
        for record in &self.ematching_proof_records {
            if record.quantifier == quantifier {
                if let Some(&value) = record.binding.get(position) {
                    if !column.contains(&value) && self.term_avoids_names(value, bound_names) {
                        column.push(value);
                    }
                }
            }
        }
        for candidate in self.negated_exists_witness_candidates(
            authored,
            sort,
            bound_names,
            &[],
            MAX_WITNESSES_PER_SORT,
        ) {
            if !column.contains(&candidate) {
                column.push(candidate);
            }
        }
        column.truncate(MAX_WITNESSES_PER_SORT);
        column
    }

    /// Bounded ground instances of every authored universal over
    /// witness-augmented candidate columns — the closing instances the
    /// ground probe refutes against the bridge consequences.
    pub(super) fn bridge_saturation_records(
        &mut self,
        authored: &[TermId],
        closure: &[TermId],
        bound_names: &ay_core::kani_compat::DetHashSet<String>,
        witnesses: &[(Sort, TermId)],
    ) -> Vec<crate::ematching::ForallInstantiationProvenance> {
        let mut records: Vec<crate::ematching::ForallInstantiationProvenance> = Vec::new();
        for &term in closure {
            if records.len() >= MAX_SATURATION_RECORDS {
                break;
            }
            let TermData::Forall(bindings, body, _) = self.ctx.terms.get(term).clone() else {
                continue;
            };
            if bindings.is_empty() || bindings.len() > MAX_BINDERS {
                continue;
            }
            let mut per_binder: Vec<Vec<TermId>> = Vec::with_capacity(bindings.len());
            for (position, (_, sort)) in bindings.iter().enumerate() {
                let column = self.bridge_candidate_column(
                    authored,
                    term,
                    position,
                    sort,
                    bound_names,
                    witnesses,
                );
                if column.is_empty() {
                    per_binder.clear();
                    break;
                }
                per_binder.push(column);
            }
            if per_binder.len() != bindings.len() {
                continue;
            }
            // Staircase first (binder i gets candidate i — the fresh
            // witnesses head same-sort columns in binder order).
            let mut tuples = bounded_tuples(&per_binder, MAX_SATURATION_RECORDS - records.len());
            if per_binder.len() > 1 && !tuples.is_empty() {
                let staircase: Vec<TermId> = per_binder
                    .iter()
                    .enumerate()
                    .map(|(index, column)| column.get(index).copied().unwrap_or(column[0]))
                    .collect();
                if let Some(position) = tuples.iter().position(|t| t == &staircase) {
                    tuples.remove(position);
                } else if tuples.len() >= MAX_SATURATION_RECORDS - records.len() {
                    tuples.pop();
                }
                tuples.insert(0, staircase);
            }
            for tuple in tuples {
                if records.len() >= MAX_SATURATION_RECORDS {
                    break;
                }
                let mut substitution: ay_core::kani_compat::DetHashMap<String, TermId> =
                    ay_core::kani_compat::DetHashMap::default();
                for ((name, _), &value) in bindings.iter().zip(&tuple) {
                    substitution.insert(name.clone(), value);
                }
                let Some(instance) =
                    crate::ematching::subst_vars_exact_qf(&mut self.ctx.terms, body, &substitution)
                else {
                    continue;
                };
                if crate::ematching::contains_quantifier(&self.ctx.terms, instance)
                    || records.iter().any(|r| r.instance == instance)
                    || self
                        .ematching_proof_records
                        .iter()
                        .any(|r| r.instance == instance)
                {
                    continue;
                }
                records.push(crate::ematching::ForallInstantiationProvenance {
                    quantifier: term,
                    binding: tuple,
                    instance,
                });
            }
        }
        records
    }

    /// Candidate tuples for one bridge universal: this decision's
    /// recorded bindings for it first (the tuples the refutation
    /// actually used), then bounded hint/ground tuples.
    pub(super) fn bridge_tuples(
        &self,
        authored: &[TermId],
        bridge: &BridgeRoot,
        bound_names: &ay_core::kani_compat::DetHashSet<String>,
    ) -> Vec<Vec<TermId>> {
        let mut tuples: Vec<Vec<TermId>> = Vec::new();
        for record in &self.ematching_proof_records {
            if record.quantifier == bridge.forall
                && !tuples.contains(&record.binding)
                && record
                    .binding
                    .iter()
                    .all(|&value| self.term_avoids_names(value, bound_names))
            {
                tuples.push(record.binding.clone());
            }
        }
        let mut per_binder: Vec<Vec<TermId>> = Vec::with_capacity(bridge.bindings.len());
        for (_, sort) in &bridge.bindings {
            let candidates = self.negated_exists_witness_candidates(
                authored,
                sort,
                bound_names,
                &[],
                MAX_WITNESSES_PER_SORT,
            );
            if candidates.is_empty() {
                per_binder.clear();
                break;
            }
            per_binder.push(candidates);
        }
        if per_binder.len() == bridge.bindings.len() {
            for tuple in bounded_tuples(&per_binder, MAX_TUPLES_PER_BRIDGE) {
                if !tuples.contains(&tuple) {
                    tuples.push(tuple);
                }
            }
        }
        tuples.truncate(MAX_TUPLES_PER_BRIDGE);
        tuples
    }
}
