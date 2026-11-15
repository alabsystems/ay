// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Fragment-scan results and finite domains for the finite-domain UF
//! certificate.

use super::*;

/// Result of the fragment scan: signatures, sorts, ground material.
#[derive(Default)]
pub(super) struct FragmentScan {
    pub(super) signatures: HashMap<String, UfSignature>,
    pub(super) sorts: HashSet<Sort>,
    pub(super) ground_subterms: Vec<TermId>,
    pub(super) ground_apps: Vec<TermId>,
    pub(super) work: usize,
}

/// Finite per-sort domains: element spellings in first-seen order with
/// one representative ground term each.
#[derive(Clone, Default)]
pub(super) struct UfDomains {
    pub(super) by_sort: HashMap<Sort, Vec<(String, TermId)>>,
}

impl UfDomains {
    pub(super) fn seed_bool(&mut self, terms: &ay_core::TermStore) {
        self.by_sort.insert(
            Sort::Bool,
            vec![
                ("false".to_string(), terms.false_term()),
                ("true".to_string(), terms.true_term()),
            ],
        );
    }

    /// Insert an element; `Some(true)` when it was new, `Some(false)`
    /// when already present, `None` over budget.
    pub(super) fn insert(&mut self, sort: Sort, value: String, rep: TermId) -> Option<bool> {
        let entries = self.by_sort.entry(sort).or_default();
        if entries.iter().any(|(existing, _)| existing == &value) {
            return Some(false);
        }
        if entries.len() >= MAX_DOMAIN_PER_SORT {
            return None;
        }
        entries.push((value, rep));
        Some(true)
    }

    pub(super) fn entries(&self, sort: &Sort) -> Vec<(String, TermId)> {
        self.by_sort.get(sort).cloned().unwrap_or_default()
    }

    pub(super) fn reps(&self, sort: &Sort) -> Vec<TermId> {
        self.entries(sort).into_iter().map(|(_, rep)| rep).collect()
    }

    pub(super) fn rep_for(&self, sort: &Sort, value: &str) -> Option<TermId> {
        self.by_sort
            .get(sort)?
            .iter()
            .find(|(existing, _)| existing == value)
            .map(|(_, rep)| *rep)
    }

    pub(super) fn default_rep(&self, sort: &Sort) -> Option<&TermId> {
        self.by_sort.get(sort)?.first().map(|(_, rep)| rep)
    }
}

impl Executor {
    /// Seed the per-sort domains from the candidate model's values on
    /// the snapshot's ground subterms (Bool's domain is fixed).
    pub(super) fn uf_domains(
        &mut self,
        candidate: &mut Model,
        scan: &FragmentScan,
    ) -> Option<UfDomains> {
        let mut domains = UfDomains::default();
        domains.seed_bool(&self.ctx.terms);
        let mut seen: HashSet<TermId> = HashSet::default();
        for &term in &scan.ground_subterms {
            if !seen.insert(term) {
                continue;
            }
            let sort = self.ctx.terms.sort(term).clone();
            if matches!(sort, Sort::Bool) {
                continue;
            }
            let value = self.evaluate_term(candidate, term);
            let EvalValue::Element(atom) = value else {
                return None;
            };
            domains.insert(sort, atom, term)?;
        }
        // A fragment sort with no ground term (e.g. an argument-only
        // sort) gets a singleton domain named by a fresh constant,
        // valued by the candidate model itself. The exhibited finite
        // structure is still verified in full below, so the choice is
        // a hint: a wrong one fails verification, never the verdict.
        for sort in &scan.sorts {
            if matches!(sort, Sort::Bool) || !domains.reps(sort).is_empty() {
                continue;
            }
            let Sort::Uninterpreted(name) = sort else {
                return None;
            };
            let fresh = self
                .ctx
                .terms
                .mk_fresh_var("ay_ufd_rep", Sort::Uninterpreted(name.clone()));
            // Name the singleton element and pin the fresh constant to
            // it in the candidate clone (carried into the emitted model
            // below), so closure/install/verification evaluations all
            // read the same value.
            let atom = format!("@ufd!{name}");
            candidate
                .completed_values
                .insert(fresh, EvalValue::Element(atom.clone()));
            domains.insert(sort.clone(), atom, fresh)?;
        }
        Some(domains)
    }
}
