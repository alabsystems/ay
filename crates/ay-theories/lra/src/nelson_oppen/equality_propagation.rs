// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

type TightBoundVar = (TermId, Rational, Vec<TheoryLit>);
type TightBoundGroup = Vec<(TermId, Vec<TheoryLit>)>;
type TightBoundGroups = HashMap<Rational, TightBoundGroup>;

impl LraSolver {
    pub(super) fn propagate_equalities_impl(&mut self) -> EqualityPropagationResult {
        let debug = self.debug_lra_nelson_oppen;
        let tight_bound_vars = self.collect_tight_bound_vars(debug);
        let vars_by_value = group_tight_bound_vars(tight_bound_vars);

        self.propagate_tight_bound_equalities(&vars_by_value, debug);
        let new_disequalities = self.discover_tight_bound_disequalities(&vars_by_value, debug);
        let new_equalities = std::mem::take(&mut self.pending_equalities);

        log_propagation_counts(&new_equalities, &new_disequalities);
        EqualityPropagationResult {
            equalities: new_equalities,
            disequalities: new_disequalities,
            ..Default::default()
        }
    }

    // Collect variables whose equal, non-strict bounds uniquely determine
    // their value. Rational keeps the common i64-sized path allocation-free.
    fn collect_tight_bound_vars(&self, debug: bool) -> Vec<TightBoundVar> {
        // Sort term_to_var entries by TermId for deterministic iteration (#2681).
        let mut sorted_term_vars: Vec<_> = self.term_to_var.iter().collect();
        sorted_term_vars.sort_by_key(|(&term, _)| term.0);

        let mut tight_bound_vars = Vec::new();
        for (&var_term, &var_id) in sorted_term_vars {
            let Some(info) = self.vars.get(var_id as usize) else {
                continue;
            };
            let (Some(lower), Some(upper)) = (&info.lower, &info.upper) else {
                continue;
            };
            if lower.value != upper.value || lower.strict || upper.strict {
                continue;
            }

            let reasons = tight_bound_reasons(lower, upper);
            if debug {
                safe_eprintln!(
                    "[LRA N-O] Tight bound: term {} = {} (reasons: {:?})",
                    var_term.0,
                    lower.value,
                    reasons
                );
            }

            // Zero-reason bounds only reflect simplex's default model. Sending
            // them to EUF would spuriously merge every default-zero variable.
            if reasons.is_empty() {
                if debug {
                    safe_eprintln!(
                        "[LRA N-O] Skipping zero-reason tight bound: term {} = {}",
                        var_term.0,
                        lower.value,
                    );
                }
                continue;
            }
            if debug {
                safe_eprintln!(
                    "[LRA N-O] KEEPING tight bound: term {} = {} ({} reasons)",
                    var_term.0,
                    lower.value,
                    reasons.len(),
                );
            }
            tight_bound_vars.push((var_term, lower.value.clone(), reasons));
        }
        tight_bound_vars
    }

    fn propagate_tight_bound_equalities(&mut self, vars_by_value: &TightBoundGroups, debug: bool) {
        // Sort groups by value for deterministic iteration (#2681).
        let mut sorted_groups: Vec<_> = vars_by_value.iter().collect();
        sorted_groups.sort_by_key(|(value, _)| *value);

        for (_value, vars) in sorted_groups {
            for i in 0..vars.len() {
                for j in (i + 1)..vars.len() {
                    let (lhs, lhs_reasons) = &vars[i];
                    let (rhs, rhs_reasons) = &vars[j];
                    self.propagate_tight_bound_equality(
                        *lhs,
                        lhs_reasons,
                        *rhs,
                        rhs_reasons,
                        debug,
                    );
                }
            }
        }
    }

    // Value grouping is sort-blind in mixed Int/Real solving. The sort guard
    // prevents an ill-sorted equality from merging unlike constants in EUF.
    fn propagate_tight_bound_equality(
        &mut self,
        lhs: TermId,
        lhs_reasons: &[TheoryLit],
        rhs: TermId,
        rhs_reasons: &[TheoryLit],
        debug: bool,
    ) {
        if self.terms().sort(lhs) != self.terms().sort(rhs) {
            return;
        }

        let pair = ordered_pair(lhs, rhs);
        if !self.propagated_equality_pairs.insert(pair) {
            return;
        }

        let combined_reasons = combine_reasons(lhs_reasons, rhs_reasons);
        if debug {
            safe_eprintln!(
                "[LRA N-O] Propagating equality: term {} = term {} (reasons: {:?})",
                lhs.0,
                rhs.0,
                combined_reasons
            );
        }
        self.pending_equalities
            .push(DiscoveredEquality::new(lhs, rhs, combined_reasons));
    }

    fn discover_tight_bound_disequalities(
        &mut self,
        vars_by_value: &TightBoundGroups,
        debug: bool,
    ) -> Vec<DiscoveredDisequality> {
        let mut sorted_groups: Vec<_> = vars_by_value.iter().collect();
        sorted_groups.sort_by_key(|(value, _)| *value);

        let mut new_disequalities = Vec::new();
        for i in 0..sorted_groups.len() {
            for j in (i + 1)..sorted_groups.len() {
                let (_, group_a) = &sorted_groups[i];
                let (_, group_b) = &sorted_groups[j];

                // One anchor per value group avoids O(n*m) pairs. Equality
                // transitivity makes the anchor disequality sufficient.
                for (term_a, reasons_a) in group_a.iter().take(1) {
                    if reasons_a.is_empty() {
                        continue;
                    }
                    for (term_b, reasons_b) in group_b.iter().take(1) {
                        if reasons_b.is_empty() {
                            continue;
                        }
                        if let Some(disequality) = self.discover_tight_bound_disequality(
                            *term_a, reasons_a, *term_b, reasons_b, debug,
                        ) {
                            new_disequalities.push(disequality);
                        }
                    }
                }
            }
        }
        new_disequalities
    }

    // Mirrors the equality sort guard: arithmetic must never emit an
    // ill-sorted disequality between terms from different theories.
    fn discover_tight_bound_disequality(
        &mut self,
        term_a: TermId,
        reasons_a: &[TheoryLit],
        term_b: TermId,
        reasons_b: &[TheoryLit],
        debug: bool,
    ) -> Option<DiscoveredDisequality> {
        if self.terms().sort(term_a) != self.terms().sort(term_b) {
            return None;
        }

        let pair = ordered_pair(term_a, term_b);
        if !self.propagated_disequality_pairs.insert(pair) {
            return None;
        }

        let combined_reasons = combine_reasons(reasons_a, reasons_b);
        if debug {
            safe_eprintln!(
                "[LRA N-O] Propagating disequality: term {} != term {} ({} reasons)",
                term_a.0,
                term_b.0,
                combined_reasons.len()
            );
        }
        Some(DiscoveredDisequality::new(term_a, term_b, combined_reasons))
    }
}

fn tight_bound_reasons(lower: &Bound, upper: &Bound) -> Vec<TheoryLit> {
    let mut reasons = Vec::new();
    for (term, value) in lower.reason_pairs() {
        if !term.is_sentinel() {
            reasons.push(TheoryLit::new(term, value));
        }
    }
    for (term, value) in upper.reason_pairs() {
        if !term.is_sentinel() && !reasons.iter().any(|reason| reason.term == term) {
            reasons.push(TheoryLit::new(term, value));
        }
    }
    reasons
}

fn group_tight_bound_vars(tight_bound_vars: Vec<TightBoundVar>) -> TightBoundGroups {
    let mut vars_by_value: TightBoundGroups = HashMap::default();
    for (term, value, reasons) in tight_bound_vars {
        vars_by_value
            .entry(value)
            .or_default()
            .push((term, reasons));
    }
    vars_by_value
}

fn ordered_pair(lhs: TermId, rhs: TermId) -> (TermId, TermId) {
    if lhs.0 < rhs.0 {
        (lhs, rhs)
    } else {
        (rhs, lhs)
    }
}

fn combine_reasons(lhs: &[TheoryLit], rhs: &[TheoryLit]) -> Vec<TheoryLit> {
    // Preserve lhs order and duplicates exactly; deduplicate only additions
    // from rhs, matching the original propagation explanation behavior.
    let mut reason_seen: HashSet<TheoryLit> = lhs.iter().copied().collect();
    let mut combined_reasons = lhs.to_vec();
    for reason in rhs {
        if reason_seen.insert(*reason) {
            combined_reasons.push(*reason);
        }
    }
    combined_reasons
}

fn log_propagation_counts(
    new_equalities: &[DiscoveredEquality],
    new_disequalities: &[DiscoveredDisequality],
) {
    if !new_equalities.is_empty() {
        info!(
            target: "ay::lra",
            propagated = new_equalities.len(),
            "Nelson-Oppen equality propagation"
        );
    }
    if !new_disequalities.is_empty() {
        info!(
            target: "ay::lra",
            propagated = new_disequalities.len(),
            "Nelson-Oppen disequality propagation"
        );
    }
}
