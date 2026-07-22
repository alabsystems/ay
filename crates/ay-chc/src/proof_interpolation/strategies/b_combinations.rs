// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::super::*;

/// Try to extract an interpolant by combining only B-pure literals from a Farkas conflict.
pub(crate) fn try_b_pure_combination(
    conflict_terms: &[TermId],
    origins: &[Partition],
    polarities: &[bool],
    coefficients: &[Rational64],
    atom_to_expr: &FxHashMap<TermId, ChcExpr>,
    shared_vars: &FxHashSet<String>,
    a_atoms: &FxHashSet<TermId>,
) -> Option<ChcExpr> {
    use crate::farkas::parse_linear_constraint;

    let origins_available = if origins.is_empty() {
        false
    } else if origins.len() == conflict_terms.len() {
        true
    } else {
        iuc_trace!(
            "try_b_pure_combination: origins length mismatch (terms={}, origins={})",
            conflict_terms.len(),
            origins.len()
        );
        return None;
    };

    let mut b_pure_contribs: Vec<(Rational64, FxHashMap<String, Rational64>, Rational64, bool)> =
        Vec::new();

    for (idx, ((&atom, &polarity), &coeff)) in conflict_terms
        .iter()
        .zip(polarities.iter())
        .zip(coefficients.iter())
        .enumerate()
    {
        let weight = rational64_abs(coeff);
        if weight == Rational64::from_integer(0) {
            continue;
        }

        let Some(expr) = atom_to_expr.get(&atom) else {
            continue;
        };

        let is_b_pure = if origins_available {
            origins[idx] == Partition::B && vars_all_shared(expr, shared_vars)
        } else {
            a_atoms.contains(&atom) && classify_literal(expr, shared_vars) == LiteralClass::BPure
        };
        if !is_b_pure {
            continue;
        }

        let constraint_expr = if polarity {
            expr.clone()
        } else {
            ChcExpr::not(expr.clone())
        };

        let Some(lin) = parse_linear_constraint(&constraint_expr) else {
            continue;
        };

        b_pure_contribs.push((weight, lin.coeffs, lin.bound, lin.strict));
    }

    if b_pure_contribs.is_empty() {
        if origins_available {
            iuc_trace!("try_b_pure_combination: no B-origin shared-var literals found");
        } else {
            iuc_trace!("try_b_pure_combination: no A-origin shared-var literals found (legacy)");
        }
        return None;
    }

    let mut combined_coeffs: FxHashMap<String, Rational64> = FxHashMap::default();
    let mut combined_bound: Rational64 = Rational64::from_integer(0);
    let mut combined_strict = false;

    for (weight, coeffs, bound, strict) in &b_pure_contribs {
        combined_strict |= *strict;
        combined_bound += *weight * *bound;
        for (var, c) in coeffs {
            let entry = combined_coeffs
                .entry(var.clone())
                .or_insert(Rational64::from_integer(0));
            *entry += *weight * *c;
        }
    }

    combined_coeffs.retain(|_, c| *c != Rational64::from_integer(0));

    let non_shared: Vec<&String> = combined_coeffs
        .keys()
        .filter(|v| !shared_vars.contains(*v))
        .collect();
    if !non_shared.is_empty() {
        iuc_trace!(
            "try_b_pure_combination: unexpected non-shared vars in result: {:?}",
            non_shared
        );
        return None;
    }

    let combined = build_linear_inequality(&combined_coeffs, combined_bound, combined_strict)?;
    let candidate = if origins_available {
        ChcExpr::not(combined)
            .normalize_negations()
            .normalize_strict_int_comparisons()
            .simplify_constants()
    } else {
        combined
    };

    if matches!(candidate, ChcExpr::Bool(true | false)) {
        iuc_trace!("try_b_pure_combination: trivial constraint");
        return None;
    }

    iuc_trace!("try_b_pure_combination: candidate = {}", candidate);
    Some(candidate)
}

/// Strategy 1.1: Split-literals partitioned Farkas combination (#6484).
pub(crate) fn try_split_literals_combination(
    conflict_terms: &[TermId],
    origins: &[Partition],
    polarities: &[bool],
    coefficients: &[Rational64],
    atom_to_expr: &FxHashMap<TermId, ChcExpr>,
    shared_vars: &FxHashSet<String>,
    a_atoms: &FxHashSet<TermId>,
) -> Option<ChcExpr> {
    use crate::farkas::parse_linear_constraint;

    let origins_available = !origins.is_empty() && origins.len() == conflict_terms.len();

    struct BPureEntry {
        weight: Rational64,
        coeffs: FxHashMap<String, Rational64>,
        bound: Rational64,
        strict: bool,
    }
    let mut entries: Vec<BPureEntry> = Vec::new();

    for (idx, ((&atom, &polarity), &coeff)) in conflict_terms
        .iter()
        .zip(polarities.iter())
        .zip(coefficients.iter())
        .enumerate()
    {
        let weight = rational64_abs(coeff);
        if weight == Rational64::from_integer(0) {
            continue;
        }
        let Some(expr) = atom_to_expr.get(&atom) else {
            continue;
        };
        let is_b_pure = if origins_available {
            origins[idx] == Partition::B && vars_all_shared(expr, shared_vars)
        } else {
            a_atoms.contains(&atom) && classify_literal(expr, shared_vars) == LiteralClass::BPure
        };
        if !is_b_pure {
            continue;
        }
        let constraint_expr = if polarity {
            expr.clone()
        } else {
            ChcExpr::not(expr.clone())
        };
        let Some(lin) = parse_linear_constraint(&constraint_expr) else {
            continue;
        };
        entries.push(BPureEntry {
            weight,
            coeffs: lin.coeffs,
            bound: lin.bound,
            strict: lin.strict,
        });
    }

    if entries.len() < 2 {
        return None;
    }

    let n = entries.len();
    let mut parent: Vec<usize> = (0..n).collect();
    let mut rank: Vec<usize> = vec![0; n];

    fn find(parent: &mut [usize], i: usize) -> usize {
        if parent[i] != i {
            parent[i] = find(parent, parent[i]);
        }
        parent[i]
    }
    fn union(parent: &mut [usize], rank: &mut [usize], i: usize, j: usize) {
        let ri = find(parent, i);
        let rj = find(parent, j);
        if ri == rj {
            return;
        }
        if rank[ri] < rank[rj] {
            parent[ri] = rj;
        } else if rank[ri] > rank[rj] {
            parent[rj] = ri;
        } else {
            parent[rj] = ri;
            rank[ri] += 1;
        }
    }

    let mut var_to_first: FxHashMap<&str, usize> = FxHashMap::default();
    for (idx, entry) in entries.iter().enumerate() {
        for var in entry.coeffs.keys() {
            if let Some(&first_idx) = var_to_first.get(var.as_str()) {
                union(&mut parent, &mut rank, first_idx, idx);
            } else {
                var_to_first.insert(var.as_str(), idx);
            }
        }
    }

    let mut partitions: FxHashMap<usize, Vec<usize>> = FxHashMap::default();
    for i in 0..n {
        let root = find(&mut parent, i);
        partitions.entry(root).or_default().push(i);
    }

    if partitions.len() < 2 {
        return None;
    }

    let mut per_partition_results: Vec<ChcExpr> = Vec::new();
    for indices in partitions.values() {
        let mut combined_coeffs: FxHashMap<String, Rational64> = FxHashMap::default();
        let mut combined_bound = Rational64::from_integer(0);
        let mut combined_strict = false;

        for &idx in indices {
            let entry = &entries[idx];
            combined_strict |= entry.strict;
            combined_bound += entry.weight * entry.bound;
            for (var, c) in &entry.coeffs {
                let e = combined_coeffs
                    .entry(var.clone())
                    .or_insert(Rational64::from_integer(0));
                *e += entry.weight * *c;
            }
        }

        combined_coeffs.retain(|_, c| *c != Rational64::from_integer(0));
        if combined_coeffs.keys().any(|v| !shared_vars.contains(v)) || combined_coeffs.is_empty() {
            continue;
        }

        let Some(ineq) = build_linear_inequality(&combined_coeffs, combined_bound, combined_strict)
        else {
            continue;
        };
        per_partition_results.push(ineq);
    }

    if per_partition_results.is_empty() {
        return None;
    }

    let candidate = if per_partition_results.len() == 1 {
        let combined = per_partition_results
            .into_iter()
            .next()
            .expect("invariant: len == 1 checked above");
        if origins_available {
            ChcExpr::not(combined)
                .normalize_negations()
                .normalize_strict_int_comparisons()
                .simplify_constants()
        } else {
            combined
        }
    } else {
        let conjunction = ChcExpr::and_all(per_partition_results);
        if origins_available {
            ChcExpr::not(conjunction)
                .normalize_negations()
                .normalize_strict_int_comparisons()
                .simplify_constants()
        } else {
            conjunction
        }
    };

    if matches!(candidate, ChcExpr::Bool(true | false)) {
        return None;
    }

    iuc_trace!("try_split_literals_combination: candidate = {}", candidate);
    Some(candidate)
}
