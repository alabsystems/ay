// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Relational-equality lemma generalization.
//!
//! This extracts two-variable relational equalities from a point cube (e.g. `x = k, y = j`)
//! to propose more general blocking formulas like `x = y + c` or (via double-negation) `x = y`.

use crate::pdr::solver::PdrSolver;
use crate::{ChcExpr, ChcOp, ChcVar, PredicateId};

use super::{build_conjunction, extract_equality};

fn try_relational_equality_generalization_with<F>(
    conjuncts: &[ChcExpr],
    level: usize,
    verbose: bool,
    mut is_inductive_blocking: F,
) -> Option<ChcExpr>
where
    F: FnMut(&ChcExpr) -> bool,
{
    // Step 1: Extract all (var, value) pairs from equality conjuncts
    let mut var_values: Vec<(ChcVar, i128, usize)> = Vec::new();
    for (idx, conj) in conjuncts.iter().enumerate() {
        if let Some((var, val)) = extract_equality(conj) {
            var_values.push((var, val, idx));
        }
    }

    // Need at least 2 variables to find relational equalities
    if var_values.len() < 2 {
        return None;
    }

    // Step 2: Try discovering invariant equalities FIRST (most general)
    //
    // When we have state (D=1, E=0) where D != E, the state satisfies (D != E).
    // To block states where D != E, we need:
    // - blocking_formula = (D != E) [what the state satisfies]
    // - lemma = NOT(D != E) = (D = E) [the invariant we want to establish]
    //
    // This discovers the INVARIANT D=E: states satisfying (D != E) should be blocked.
    // We try this BEFORE offset equalities because it's more general.
    for i in 0..var_values.len() {
        for j in (i + 1)..var_values.len() {
            let (v1, val1, idx1) = &var_values[i];
            let (v2, val2, idx2) = &var_values[j];

            if v1.name == v2.name {
                continue;
            }

            // If the values differ, this state satisfies v1 != v2.
            // Use blocking_formula = NOT(v1 = v2) to block states where v1 != v2.
            // This creates lemma = (v1 = v2), establishing the equality invariant.
            if *val1 != *val2 {
                // The disequality that this state satisfies - use as blocking formula
                let disequality = ChcExpr::not(ChcExpr::eq(
                    ChcExpr::var(v1.clone()),
                    ChcExpr::var(v2.clone()),
                ));

                // First, try the disequality ALONE as the blocking formula.
                // This creates lemma NOT(NOT(v1=v2)) = (v1 = v2) - the equality invariant.
                if is_inductive_blocking(&disequality) {
                    if verbose {
                        safe_eprintln!(
                            "PDR: Equality invariant discovered: {} = {} (blocking {} at level {})",
                            v1.name,
                            v2.name,
                            disequality,
                            level
                        );
                    }
                    return Some(disequality);
                }

                // If pure disequality doesn't work, try combining with other conjuncts.
                // Build formula with disequality replacing both point constraints.
                let mut new_conjuncts: Vec<ChcExpr> = Vec::new();
                for (idx, conj) in conjuncts.iter().enumerate() {
                    if idx != *idx1 && idx != *idx2 {
                        new_conjuncts.push(conj.clone());
                    }
                }
                if !new_conjuncts.is_empty() {
                    new_conjuncts.push(disequality.clone());

                    let generalized = build_conjunction(&new_conjuncts);

                    // Check if the combined formula is inductive.
                    if is_inductive_blocking(&generalized) {
                        if verbose {
                            safe_eprintln!(
                                "PDR: Equality invariant with context discovered: {} = {} (blocking {} at level {})",
                                v1.name, v2.name, generalized, level
                            );
                        }
                        return Some(generalized);
                    }
                }
            }
        }
    }

    // Step 3: Try (small) offset-based relational equalities (less general than Step 2)
    //
    // NOTE: Large offsets can explode into many point-like lemmas on CHC-COMP problems and
    // cause severe performance regressions. Restrict to small offsets only.
    let mut candidates: Vec<(ChcExpr, Vec<usize>)> = Vec::new();

    for i in 0..var_values.len() {
        for j in (i + 1)..var_values.len() {
            let (v1, val1, idx1) = &var_values[i];
            let (v2, val2, idx2) = &var_values[j];

            // Skip if same variable (shouldn't happen but be safe)
            if v1.name == v2.name {
                continue;
            }

            let diff = val1.saturating_sub(*val2);

            const MAX_OFFSET_ABS: i128 = 8;
            if diff != 0 && diff.saturating_abs() > MAX_OFFSET_ABS {
                continue;
            }

            // Create candidate relational equality
            let relational_eq = if diff == 0 {
                // v1 = v2
                ChcExpr::eq(ChcExpr::var(v1.clone()), ChcExpr::var(v2.clone()))
            } else {
                // v1 = v2 + diff (or equivalently v1 - v2 = diff)
                ChcExpr::eq(
                    ChcExpr::var(v1.clone()),
                    ChcExpr::add(ChcExpr::var(v2.clone()), ChcExpr::Int(diff)),
                )
            };

            // This replaces conjuncts at idx1 and idx2.
            candidates.push((relational_eq, vec![*idx1, *idx2]));
        }
    }

    // Sort candidates: prefer pure equalities (diff=0) first, then by replaced count.
    candidates.sort_by(|a, b| {
        // Pure equality (no constant term) is preferable.
        let a_is_pure = matches!(
            &a.0,
            ChcExpr::Op(ChcOp::Eq, args) if matches!(args[1].as_ref(), ChcExpr::Var(_))
        );
        let b_is_pure = matches!(
            &b.0,
            ChcExpr::Op(ChcOp::Eq, args) if matches!(args[1].as_ref(), ChcExpr::Var(_))
        );

        match (a_is_pure, b_is_pure) {
            (true, false) => std::cmp::Ordering::Less,
            (false, true) => std::cmp::Ordering::Greater,
            _ => std::cmp::Ordering::Equal,
        }
    });

    // Step 4: Try each candidate.
    for (relational_eq, replaced_indices) in candidates {
        // Build new conjuncts: keep conjuncts not being replaced, add relational eq.
        let mut new_conjuncts: Vec<ChcExpr> = Vec::new();
        for (idx, conj) in conjuncts.iter().enumerate() {
            if !replaced_indices.contains(&idx) {
                new_conjuncts.push(conj.clone());
            }
        }
        new_conjuncts.push(relational_eq.clone());

        let generalized = build_conjunction(&new_conjuncts);

        // Check if the generalized formula is inductive.
        if is_inductive_blocking(&generalized) {
            if verbose {
                safe_eprintln!(
                    "PDR: Relational equality generalization succeeded: {} (replaced {} conjuncts)",
                    relational_eq,
                    replaced_indices.len()
                );
            }
            return Some(generalized);
        }
    }

    // Step 5: Try adding relational equalities as additional constraints
    // (strengthening instead of replacing).
    //
    // This is useful when the equality itself isn't inductive but helps generalization.
    for i in 0..var_values.len() {
        for j in (i + 1)..var_values.len() {
            let (v1, val1, _) = &var_values[i];
            let (v2, val2, _) = &var_values[j];

            if v1.name == v2.name {
                continue;
            }

            let diff = val1.saturating_sub(*val2);
            if diff != 0 {
                continue; // Only try pure equalities for strengthening.
            }

            // Try adding v1 = v2 as an additional constraint.
            let relational_eq = ChcExpr::eq(ChcExpr::var(v1.clone()), ChcExpr::var(v2.clone()));
            let mut strengthened = conjuncts.to_vec();
            strengthened.push(relational_eq.clone());
            let strengthened_formula = build_conjunction(&strengthened);

            // Check if strengthened is inductive and then try dropping conjuncts.
            if is_inductive_blocking(&strengthened_formula) {
                // Now try dropping some of the original conjuncts.
                let mut best_conjuncts = strengthened;

                for drop_idx in (0..conjuncts.len()).rev() {
                    if best_conjuncts.len() <= 2 {
                        break;
                    }
                    let mut test = best_conjuncts.clone();
                    test.remove(drop_idx);
                    let test_formula = build_conjunction(&test);

                    if is_inductive_blocking(&test_formula) {
                        best_conjuncts = test;
                    }
                }

                if best_conjuncts.len() < conjuncts.len() + 1 {
                    if verbose {
                        safe_eprintln!(
                            "PDR: Relational equality {} enabled dropping {} conjuncts",
                            relational_eq,
                            conjuncts.len() + 1 - best_conjuncts.len()
                        );
                    }
                    return Some(build_conjunction(&best_conjuncts));
                }
            }
        }
    }

    None
}

impl PdrSolver {
    pub(in crate::pdr) fn try_relational_equality_generalization(
        &mut self,
        conjuncts: &[ChcExpr],
        predicate: PredicateId,
        level: usize,
    ) -> Option<ChcExpr> {
        let verbose = self.config.verbose;
        try_relational_equality_generalization_with(conjuncts, level, verbose, |expr| {
            self.is_inductive_blocking(expr, predicate, level)
        })
    }
}

#[allow(clippy::unwrap_used, clippy::panic)]
#[cfg(test)]
#[path = "relational_tests.rs"]
mod tests;
