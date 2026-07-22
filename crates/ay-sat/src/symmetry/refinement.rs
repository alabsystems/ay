// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Iterative color refinement (1-dim Weisfeiler-Leman) on the bipartite
//! clause-variable incidence graph of a CNF formula.
//!
//! Each round refines variable colors by incorporating the multiset of
//! incident clause colors (and vice versa) until a stable coloring is
//! reached. Variables in the same color class after stabilization are
//! candidate automorphisms.
//!
//! Reference: Devriendt, Bogaerts, Bruynooghe, Denecker. "Improved Static
//! Symmetry Breaking for SAT." (BreakID, SAT 2016), Section 3.1.

use std::collections::BTreeMap;

use crate::{Literal, Variable};

/// Maximum number of refinement rounds before declaring stable.
/// BreakID uses a similar bound; most formulas stabilize in 3-5 rounds.
const MAX_REFINEMENT_ROUNDS: usize = 20;

/// Compact clause color: integer ID assigned during refinement.
type ClauseColorId = u32;

/// Compact variable color: integer ID assigned during refinement.
pub(crate) type VarColorId = u32;

/// Signature key for variable color refinement.
type VarColorSigKey = (VarColorId, Vec<(ClauseColorId, bool, u32)>);

/// Refined graph state after iterative color stabilization.
///
/// Each variable and clause has been assigned a compact integer color ID.
/// Variables sharing the same final color are candidate automorphic images.
#[derive(Debug, Clone)]
pub(crate) struct RefinedColorGraph {
    /// Per-variable: `(Variable, final_color_id)`.
    pub(crate) var_colors: Vec<(Variable, VarColorId)>,
    /// Number of refinement rounds executed before stabilization.
    pub(crate) rounds: usize,
}

impl RefinedColorGraph {
    /// Group variables by their refined color.
    ///
    /// Only groups with >= 2 variables are useful for symmetry detection.
    pub(crate) fn candidate_groups(&self) -> BTreeMap<VarColorId, Vec<Variable>> {
        let mut groups: BTreeMap<VarColorId, Vec<Variable>> = BTreeMap::new();
        for &(var, color) in &self.var_colors {
            groups.entry(color).or_default().push(var);
        }
        groups
    }
}

/// Run iterative color refinement on a CNF formula.
///
/// This implements BreakID-style 1-dimensional Weisfeiler-Leman refinement:
///
/// 1. **Round 0**: Assign initial clause colors from `(len, pos, neg)` and
///    initial variable colors from multiset of incident clause colors (split
///    by positive/negative polarity).
///
/// 2. **Refinement loop**: In each round, recolor clauses by the sorted
///    multiset of their literal-variable colors (preserving polarity), then
///    recolor variables by the sorted multiset of their incident refined
///    clause colors. Stop when the partition does not change.
pub(crate) fn iterative_color_refinement(clauses: &[Vec<Literal>]) -> RefinedColorGraph {
    if clauses.is_empty() {
        return RefinedColorGraph {
            var_colors: Vec::new(),
            rounds: 0,
        };
    }

    // Collect all variables appearing in the formula.
    let mut all_vars: Vec<Variable> = Vec::new();
    {
        let mut seen = std::collections::BTreeSet::new();
        for clause in clauses {
            for &lit in clause {
                if seen.insert(lit.variable()) {
                    all_vars.push(lit.variable());
                }
            }
        }
    }

    // Build adjacency: for each variable, list of (clause_index, polarity).
    let mut var_to_clauses: BTreeMap<Variable, Vec<(usize, bool)>> = BTreeMap::new();
    for (ci, clause) in clauses.iter().enumerate() {
        for &lit in clause {
            var_to_clauses
                .entry(lit.variable())
                .or_default()
                .push((ci, lit.is_positive()));
        }
    }

    // --- Round 0: initial coloring ---
    // Clause colors: map coarse triple (len, pos_count, neg_count) -> id.
    let mut clause_class_count: usize;
    let mut clause_colors: Vec<ClauseColorId> = Vec::with_capacity(clauses.len());
    {
        let mut triple_map: BTreeMap<(u16, u16, u16), ClauseColorId> = BTreeMap::new();
        let mut next_id: ClauseColorId = 0;
        for clause in clauses {
            let pos_count = clause.iter().filter(|lit| lit.is_positive()).count() as u16;
            let len = clause.len() as u16;
            let key = (len, pos_count, len - pos_count);
            let id = *triple_map.entry(key).or_insert_with(|| {
                let id = next_id;
                next_id += 1;
                id
            });
            clause_colors.push(id);
        }
        clause_class_count = triple_map.len();
    }

    // Variable colors: multiset of (clause_color, polarity, count) -> id.
    let mut var_class_count: usize;
    let mut var_colors: Vec<VarColorId> = Vec::with_capacity(all_vars.len());
    let mut var_index: BTreeMap<Variable, usize> = BTreeMap::new();
    {
        let mut sig_map: BTreeMap<Vec<(ClauseColorId, bool, u32)>, VarColorId> = BTreeMap::new();
        let mut next_id: VarColorId = 0;
        for (vi, &var) in all_vars.iter().enumerate() {
            var_index.insert(var, vi);
            let sig = build_var_color_sig(var, &var_to_clauses, &clause_colors);
            let id = *sig_map.entry(sig).or_insert_with(|| {
                let id = next_id;
                next_id += 1;
                id
            });
            var_colors.push(id);
        }
        var_class_count = sig_map.len();
    }

    // --- Refinement loop ---
    let mut rounds = 0;
    for _ in 0..MAX_REFINEMENT_ROUNDS {
        rounds += 1;
        let prev_clause_classes = clause_class_count;
        let prev_var_classes = var_class_count;

        // Refine clause colors: signature = (old_color, sorted multiset of (var_color, polarity)).
        let mut new_clause_colors = Vec::with_capacity(clauses.len());
        {
            let mut sig_map: BTreeMap<(ClauseColorId, Vec<(VarColorId, bool)>), ClauseColorId> =
                BTreeMap::new();
            let mut next_id: ClauseColorId = 0;
            for (ci, clause) in clauses.iter().enumerate() {
                let mut sig: Vec<(VarColorId, bool)> = clause
                    .iter()
                    .map(|&lit| {
                        let vi = var_index[&lit.variable()];
                        (var_colors[vi], lit.is_positive())
                    })
                    .collect();
                sig.sort_unstable();
                let key = (clause_colors[ci], sig);
                let id = *sig_map.entry(key).or_insert_with(|| {
                    let id = next_id;
                    next_id += 1;
                    id
                });
                new_clause_colors.push(id);
            }
            clause_class_count = sig_map.len();
        }

        // Refine variable colors using the new clause colors.
        let mut new_var_colors = Vec::with_capacity(all_vars.len());
        {
            let mut sig_map: BTreeMap<VarColorSigKey, VarColorId> = BTreeMap::new();
            let mut next_id: VarColorId = 0;
            for (vi, &var) in all_vars.iter().enumerate() {
                let sig = build_var_color_sig(var, &var_to_clauses, &new_clause_colors);
                let key = (var_colors[vi], sig);
                let id = *sig_map.entry(key).or_insert_with(|| {
                    let id = next_id;
                    next_id += 1;
                    id
                });
                new_var_colors.push(id);
            }
            var_class_count = sig_map.len();
        }

        clause_colors = new_clause_colors;
        var_colors = new_var_colors;

        // Stable if the number of color classes did not increase.
        if clause_class_count == prev_clause_classes && var_class_count == prev_var_classes {
            break;
        }
    }

    let result_var_colors: Vec<(Variable, VarColorId)> = all_vars
        .iter()
        .zip(var_colors.iter())
        .map(|(&var, &color)| (var, color))
        .collect();

    RefinedColorGraph {
        var_colors: result_var_colors,
        rounds,
    }
}

/// Build a variable's color signature: sorted multiset of
/// `(clause_color_id, is_positive, count)` tuples.
fn build_var_color_sig(
    var: Variable,
    var_to_clauses: &BTreeMap<Variable, Vec<(usize, bool)>>,
    clause_colors: &[ClauseColorId],
) -> Vec<(ClauseColorId, bool, u32)> {
    let mut bucket: BTreeMap<(ClauseColorId, bool), u32> = BTreeMap::new();
    if let Some(incidents) = var_to_clauses.get(&var) {
        for &(ci, pol) in incidents {
            *bucket.entry((clause_colors[ci], pol)).or_insert(0) += 1;
        }
    }
    bucket
        .into_iter()
        .map(|((cc, pol), count)| (cc, pol, count))
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Literal, Variable};

    #[test]
    fn test_refinement_symmetric_formula() {
        // x0 and x1 are interchangeable in this formula:
        // (x0 \/ z), (x1 \/ z), (~x0 \/ ~z), (~x1 \/ ~z)
        let x0 = Variable(0);
        let x1 = Variable(1);
        let z = Variable(2);
        let clauses = vec![
            vec![Literal::positive(x0), Literal::positive(z)],
            vec![Literal::positive(x1), Literal::positive(z)],
            vec![Literal::negative(x0), Literal::negative(z)],
            vec![Literal::negative(x1), Literal::negative(z)],
        ];

        let refined = iterative_color_refinement(&clauses);
        assert!(refined.rounds > 0, "should perform at least one round");

        let groups = refined.candidate_groups();
        // x0 and x1 should be in the same color class.
        let mut found_x0x1_group = false;
        for vars in groups.values() {
            if vars.contains(&x0) && vars.contains(&x1) {
                found_x0x1_group = true;
                break;
            }
        }
        assert!(found_x0x1_group, "x0 and x1 should share a color class");

        // z should NOT be in the same class as x0/x1.
        for vars in groups.values() {
            if vars.contains(&z) {
                assert!(!vars.contains(&x0), "z should not share a class with x0");
            }
        }
    }

    #[test]
    fn test_refinement_asymmetric_formula() {
        // x0 appears only positively, x1 appears both ways -> different classes.
        let x0 = Variable(0);
        let x1 = Variable(1);
        let clauses = vec![
            vec![Literal::positive(x0), Literal::positive(x1)],
            vec![Literal::positive(x0), Literal::negative(x1)],
        ];

        let refined = iterative_color_refinement(&clauses);
        let groups = refined.candidate_groups();
        // x0 and x1 should be in different classes.
        for vars in groups.values() {
            assert!(
                !(vars.contains(&x0) && vars.contains(&x1)),
                "x0 and x1 should NOT share a color class"
            );
        }
    }

    #[test]
    fn test_refinement_empty_formula() {
        let refined = iterative_color_refinement(&[]);
        assert_eq!(refined.rounds, 0);
        assert!(refined.var_colors.is_empty());
    }
}
