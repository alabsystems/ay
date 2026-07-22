// Copyright 2026 Andrew Yates
// Author: Andrew Yates
//
// Licensed under the Apache License, Version 2.0

//! Relational equality generalizer: equality/disequality/offset patterns.

use crate::expr::{ChcExpr, ChcSort, ChcVar};
use crate::generalize::{LemmaGeneralizer, TransitionSystemRef};

/// Relational equality generalizer: discovers equality/disequality between variables.
///
/// For states with (v1 = c1, v2 = c2), tries to discover:
/// 1. Equality invariants: `v1 = v2` (when c1 ≠ c2 violates invariant)
/// 2. Offset equalities: `v1 = v2 + k` (when state satisfies `v1 - v2 = k`)
/// 3. Disequality invariants: `v1 != v2` (when c1 = c2 violates invariant)
///
/// # When to Use
///
/// Use this generalizer early in the pipeline (Phase 0) to discover relational
/// patterns before other phases weaken point constraints. Examples:
/// - Copy propagation: `D = E` after assignments
/// - Index relationships: `read_idx = write_idx`
/// - State machine invariants: `pc1 != pc2` (mutual exclusion)
///
/// # Examples
///
/// State: (D=1, E=0) - if `D = E` is invariant, block `D != E`
/// State: (x=5, y=3) - if `x = y + 2` is invariant, block `x - y != 2`
///
/// # Design Note
///
/// This generalizer should run BEFORE other weakening phases because:
/// 1. Relational patterns (D=E or D!=E) are more powerful than point constraints
/// 2. Other phases may weaken point constraints (D=1 → D>0), losing pattern info
/// 3. If D!=E is inductive, it blocks infinite states vs just one
///
/// Reference: PDR's Phase 0 (lines 6931-6949 in pdr.rs)
pub(crate) struct RelationalEqualityGeneralizer {
    /// Maximum offset magnitude to consider for offset equalities.
    /// Large offsets can cause performance issues on some benchmarks.
    max_offset: i64,
}

impl Default for RelationalEqualityGeneralizer {
    fn default() -> Self {
        Self::new()
    }
}

impl RelationalEqualityGeneralizer {
    /// Create a new relational equality generalizer with default settings.
    pub(crate) fn new() -> Self {
        Self { max_offset: 10 }
    }
}

impl LemmaGeneralizer for RelationalEqualityGeneralizer {
    fn generalize(&self, lemma: &ChcExpr, level: u32, ts: &mut dyn TransitionSystemRef) -> ChcExpr {
        let conjuncts = lemma.collect_conjuncts();

        // Need at least 2 conjuncts for relational patterns
        if conjuncts.len() < 2 {
            return lemma.clone();
        }

        // Extract all (var_name, value, index) from equalities
        let var_values: Vec<(String, i128, usize)> = conjuncts
            .iter()
            .enumerate()
            .filter_map(|(idx, c)| {
                c.extract_var_int_equality()
                    .map(|(v, val)| (v.name, val, idx))
            })
            .collect();

        if var_values.len() < 2 {
            return lemma.clone();
        }

        // Step 1: Try discovering equality invariants (most general)
        // When we have state (v1=c1, v2=c2) where c1 != c2, check if v1 = v2 is invariant
        for i in 0..var_values.len() {
            for j in (i + 1)..var_values.len() {
                let (v1, val1, idx1) = &var_values[i];
                let (v2, val2, idx2) = &var_values[j];

                if v1 == v2 {
                    continue;
                }

                // If values differ, state satisfies v1 != v2
                // Try blocking NOT(v1 = v2) to establish v1 = v2 as invariant
                if *val1 != *val2 {
                    // The disequality that this state satisfies
                    let disequality = ChcExpr::not(ChcExpr::eq(
                        ChcExpr::var(ChcVar::new(v1, ChcSort::Int)),
                        ChcExpr::var(ChcVar::new(v2, ChcSort::Int)),
                    ));

                    // Try disequality ALONE first
                    if ts.check_inductive(&disequality, level) {
                        return disequality;
                    }

                    // Try combining with other conjuncts
                    let mut new_conjuncts: Vec<ChcExpr> = Vec::new();
                    for (idx, conj) in conjuncts.iter().enumerate() {
                        if idx != *idx1 && idx != *idx2 {
                            new_conjuncts.push(conj.clone());
                        }
                    }
                    new_conjuncts.push(disequality.clone());

                    let generalized = ChcExpr::and_all(new_conjuncts.iter().cloned());
                    if ts.check_inductive(&generalized, level) {
                        return generalized;
                    }
                }
            }
        }

        // Step 2: Try offset-based relational equalities (less general)
        // v1 = v2 + offset where offset is small
        for i in 0..var_values.len() {
            for j in (i + 1)..var_values.len() {
                let (v1, val1, idx1) = &var_values[i];
                let (v2, val2, idx2) = &var_values[j];

                if v1 == v2 {
                    continue;
                }

                // Calculate offset: v1 - v2 in current state
                // Use checked_sub to avoid overflow on extreme values
                let Some(offset) = val1.checked_sub(*val2) else {
                    continue; // Overflow - values too far apart
                };

                // Skip if offset is too large or zero
                // Use unsigned_abs to safely handle i128::MIN (which would overflow with .abs())
                if offset.unsigned_abs() > u128::from(self.max_offset.unsigned_abs()) || offset == 0
                {
                    continue;
                }

                // State satisfies v1 = v2 + offset
                // To block states violating this, block (v1 - v2 != offset)
                // This is equivalent to blocking NOT(v1 = v2 + offset)
                let v1_var = ChcExpr::var(ChcVar::new(v1, ChcSort::Int));
                let v2_var = ChcExpr::var(ChcVar::new(v2, ChcSort::Int));
                let v2_plus_offset = ChcExpr::add(v2_var, ChcExpr::Int(offset));
                let offset_disequality = ChcExpr::not(ChcExpr::eq(v1_var, v2_plus_offset));

                // Try offset disequality ALONE
                if ts.check_inductive(&offset_disequality, level) {
                    return offset_disequality;
                }

                // Try combining with other conjuncts
                let mut new_conjuncts: Vec<ChcExpr> = Vec::new();
                for (idx, conj) in conjuncts.iter().enumerate() {
                    if idx != *idx1 && idx != *idx2 {
                        new_conjuncts.push(conj.clone());
                    }
                }
                new_conjuncts.push(offset_disequality.clone());

                let generalized = ChcExpr::and_all(new_conjuncts.iter().cloned());
                if ts.check_inductive(&generalized, level) {
                    return generalized;
                }
            }
        }

        lemma.clone()
    }

    fn name(&self) -> &'static str {
        "relational-equality"
    }
}
