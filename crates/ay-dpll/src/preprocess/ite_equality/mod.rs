// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! ITE-based equality derivation preprocessing pass
//!
//! Derives implicit equalities from ITE-based variable assignments.
//! When two variables are constrained by the same ITE condition to the
//! same values, they must be equal.
//!
//! # Problem
//!
//! Given:
//! ```smt2
//! (ite C (= x #b1) (= x #b0))
//! (ite C (= y #b1) (= y #b0))
//! ```
//!
//! The solver needs to know that `x = y`, but without explicit linking,
//! these are independent constraints that can have inconsistent assignments.
//!
//! # Algorithm
//!
//! 1. Collect all "ITE assignments" of the form:
//!    `(ite C (= var then_val) (= var else_val))`
//!
//! 2. Group by (condition, then_val, else_val) tuple
//!
//! 3. For each group with 2+ variables, assert all pairs are equal
//!
//! # Reference
//!
//! - Issue #1708: BV soundness bug requiring this fix
//! - Report: the development design notes

use super::PreprocessingPass;
// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::term::TermData;
use ay_core::{TermId, TermStore};

/// Preprocessing pass that derives equalities from ITE-based assignments.
pub(crate) struct IteEquality {
    /// Track which equalities we've already added to avoid duplicates
    added_equalities: Vec<(TermId, TermId)>,
}

impl IteEquality {
    /// Create a new IteEquality pass.
    pub(crate) fn new() -> Self {
        Self {
            added_equalities: Vec::new(),
        }
    }

    /// Try to extract ITE assignment patterns from an assertion.
    ///
    /// Matches:
    /// - Simple: `(ite C (= var then_val) (= var else_val))`
    /// - Compound: `(ite C (and (= var1 v1) (= var2 v2) ...) (and (= var1 w1) (= var2 w2) ...))`
    ///
    /// Returns a vector of `(condition, var, then_val, else_val)` tuples.
    fn extract_ite_assignments(
        terms: &TermStore,
        assertion: TermId,
    ) -> Vec<(TermId, TermId, TermId, TermId)> {
        match terms.get(assertion) {
            TermData::Ite(cond, then_branch, else_branch) => {
                // Try simple pattern first
                if let (Some((then_var, then_val)), Some((else_var, else_val))) = (
                    Self::extract_equality_var(terms, *then_branch),
                    Self::extract_equality_var(terms, *else_branch),
                ) {
                    if then_var == else_var {
                        return vec![(*cond, then_var, then_val, else_val)];
                    }
                }

                // Try compound AND pattern
                let then_eqs = Self::extract_equalities_from_and(terms, *then_branch);
                let else_eqs = Self::extract_equalities_from_and(terms, *else_branch);

                if !then_eqs.is_empty() && !else_eqs.is_empty() {
                    // Build map from var -> val for each branch
                    let then_map: HashMap<TermId, TermId> = then_eqs.into_iter().collect();
                    let else_map: HashMap<TermId, TermId> = else_eqs.into_iter().collect();

                    // Find matching variables in both branches
                    let mut results = Vec::new();
                    for (&var, &then_val) in &then_map {
                        if let Some(&else_val) = else_map.get(&var) {
                            results.push((*cond, var, then_val, else_val));
                        }
                    }
                    return results;
                }

                Vec::new()
            }
            _ => Vec::new(),
        }
    }

    /// Extract all (var, val) pairs from an AND expression.
    ///
    /// Matches: `(and (= var1 val1) (= var2 val2) ... other_terms)`
    /// Returns all equality pairs found.
    fn extract_equalities_from_and(terms: &TermStore, term: TermId) -> Vec<(TermId, TermId)> {
        match terms.get(term) {
            TermData::App(sym, args) if sym.name() == "and" => {
                let mut results = Vec::new();
                for &arg in args {
                    if let Some(eq_pair) = Self::extract_equality_var(terms, arg) {
                        results.push(eq_pair);
                    }
                }
                results
            }
            _ => Vec::new(),
        }
    }

    /// Extract (var, val) from `(= var val)` or `(= val var)`.
    ///
    /// Returns the variable and the value it's being assigned to.
    fn extract_equality_var(terms: &TermStore, eq_term: TermId) -> Option<(TermId, TermId)> {
        match terms.get(eq_term) {
            TermData::App(sym, args) if sym.name() == "=" && args.len() == 2 => {
                let (lhs, rhs) = (args[0], args[1]);

                // Check which side is a variable
                let lhs_is_var = matches!(terms.get(lhs), TermData::Var(_, _));
                let rhs_is_var = matches!(terms.get(rhs), TermData::Var(_, _));

                if lhs_is_var && !rhs_is_var {
                    Some((lhs, rhs))
                } else if rhs_is_var && !lhs_is_var {
                    Some((rhs, lhs))
                } else if lhs_is_var && rhs_is_var {
                    // Both are variables - pick one as "var", other as "val"
                    // Use ordering for consistency
                    if lhs > rhs {
                        Some((lhs, rhs))
                    } else {
                        Some((rhs, lhs))
                    }
                } else {
                    // Neither is a variable (e.g., both constants)
                    None
                }
            }
            _ => None,
        }
    }
}

impl Default for IteEquality {
    fn default() -> Self {
        Self::new()
    }
}

impl PreprocessingPass for IteEquality {
    fn apply(&mut self, terms: &mut TermStore, assertions: &mut Vec<TermId>) -> bool {
        let debug = crate::theory_debug_flags::debug_ite_eq();

        // Phase 1: Collect all ITE assignments
        // Key: (condition, then_val, else_val) -> Vec<var>
        let mut ite_groups: HashMap<(TermId, TermId, TermId), Vec<TermId>> = HashMap::default();

        for &assertion in assertions.iter() {
            for (cond, var, then_val, else_val) in Self::extract_ite_assignments(terms, assertion) {
                if debug {
                    let var_name = if let TermData::Var(n, _) = terms.get(var) {
                        n.clone()
                    } else {
                        format!("{var:?}")
                    };
                    safe_eprintln!(
                        "[ite_eq] Found ITE assignment: {} with cond={:?}, then={:?}, else={:?}",
                        var_name,
                        cond,
                        then_val,
                        else_val
                    );
                }

                ite_groups
                    .entry((cond, then_val, else_val))
                    .or_default()
                    .push(var);
            }
        }

        // Phase 2: For each group with 2+ variables, add equality assertions
        let mut new_assertions = Vec::new();

        for (key, vars) in &ite_groups {
            if vars.len() < 2 {
                continue;
            }

            if debug {
                safe_eprintln!(
                    "[ite_eq] Group {:?} has {} variables: {:?}",
                    key,
                    vars.len(),
                    vars
                );
            }

            // Add equalities between all pairs (only need to chain them)
            // e.g., for [a, b, c], add (= a b) and (= b c)
            for i in 0..vars.len() - 1 {
                let v1 = vars[i];
                let v2 = vars[i + 1];

                // Check if we've already added this equality
                let pair = if v1 < v2 { (v1, v2) } else { (v2, v1) };
                if self.added_equalities.contains(&pair) {
                    continue;
                }

                let eq = terms.mk_eq(v1, v2);
                new_assertions.push(eq);
                self.added_equalities.push(pair);

                if debug {
                    let v1_name = if let TermData::Var(n, _) = terms.get(v1) {
                        n.clone()
                    } else {
                        format!("{v1:?}")
                    };
                    let v2_name = if let TermData::Var(n, _) = terms.get(v2) {
                        n.clone()
                    } else {
                        format!("{v2:?}")
                    };
                    safe_eprintln!("[ite_eq] Adding equality: {} = {}", v1_name, v2_name);
                }
            }
        }

        if new_assertions.is_empty() {
            return false;
        }

        // Prepend new equalities to assertions so variable substitution sees them first.
        // This establishes cleaner substitution paths (e.g., dec_func_2 -> dec_func_1
        // directly rather than through intermediate variables).
        new_assertions.append(assertions);
        *assertions = new_assertions;
        true
    }

    fn apply_with_sources(
        &mut self,
        terms: &mut TermStore,
        assertions: &mut Vec<TermId>,
        source_sets: &mut Vec<Vec<TermId>>,
    ) -> bool {
        debug_assert_eq!(assertions.len(), source_sets.len());
        let old_source_sets = source_sets.clone();
        let old_len = assertions.len();
        let modified = self.apply(terms, assertions);
        if modified {
            let added = assertions.len().saturating_sub(old_len);
            let mut new_source_sets = Vec::with_capacity(assertions.len());
            new_source_sets.resize(added, Vec::new());
            new_source_sets.extend(old_source_sets);
            *source_sets = new_source_sets;
        }
        debug_assert_eq!(assertions.len(), source_sets.len());
        modified
    }

    fn reset(&mut self) {
        // Don't reset added_equalities - we don't want to add duplicates
        // across fixed-point iterations
    }
}

#[cfg(test)]
mod tests;
