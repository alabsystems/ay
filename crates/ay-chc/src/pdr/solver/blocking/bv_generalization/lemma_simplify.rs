// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

pub(super) fn try_simplify_bv_native_lemma(
    solver: &mut PdrSolver,
    blocking_formula: &ChcExpr,
    predicate: PredicateId,
    level: usize,
) -> Option<ChcExpr> {
    let lemma = match blocking_formula {
        ChcExpr::Op(ChcOp::Not, args) if args.len() == 1 => args[0].as_ref().clone(),
        _ => return None,
    };

    let clauses = lemma.collect_conjuncts();
    if clauses.is_empty() {
        return None;
    }

    if let Some(result) = try_bv_inequality_weakening(solver, &clauses, predicate, level) {
        return Some(result);
    }

    if let Some(result) = try_bv_drop_all(solver, &clauses, predicate, level) {
        return Some(result);
    }

    None
}

fn try_bv_drop_all(
    solver: &mut PdrSolver,
    clauses: &[ChcExpr],
    predicate: PredicateId,
    level: usize,
) -> Option<ChcExpr> {
    let mut simplified_clauses = Vec::with_capacity(clauses.len());
    let mut any_simplified = false;

    for clause in clauses {
        let disjuncts = collect_disjuncts(clause);
        if disjuncts.len() <= 1 {
            simplified_clauses.push(clause.clone());
            continue;
        }
        let mut bool_disjuncts = Vec::new();
        let mut has_bv = false;
        for d in &disjuncts {
            if atom_contains_bv_constant(d) {
                has_bv = true;
            } else {
                bool_disjuncts.push(d.clone());
            }
        }
        if has_bv && !bool_disjuncts.is_empty() {
            let simplified = if bool_disjuncts.len() == 1 {
                bool_disjuncts
                    .into_iter()
                    .next()
                    .expect("invariant: non-empty")
            } else {
                ChcExpr::or_all(bool_disjuncts)
            };
            simplified_clauses.push(simplified);
            any_simplified = true;
        } else {
            simplified_clauses.push(clause.clone());
        }
    }

    if !any_simplified {
        return None;
    }

    let simplified_lemma = ChcExpr::and_all(simplified_clauses);
    let simplified_blocking = ChcExpr::not(simplified_lemma);
    if solver.is_inductive_blocking(&simplified_blocking, predicate, level) {
        if solver.config.verbose {
            safe_eprintln!(
                "PDR: #5877 BV-native phase 2: dropped all BV disjuncts (inductive at level {})",
                level
            );
        }
        Some(simplified_blocking)
    } else {
        None
    }
}

fn try_bv_inequality_weakening(
    solver: &mut PdrSolver,
    clauses: &[ChcExpr],
    predicate: PredicateId,
    level: usize,
) -> Option<ChcExpr> {
    let best_clauses = if let Some(weakened) =
        try_bv_inequality_weakening_all_clauses(solver, clauses, predicate, level)
    {
        if solver.config.verbose {
            safe_eprintln!(
                "PDR: #5877 BV-native phase 1a: weakened ALL BV distinctions to bvsle (inductive at level {})",
                level
            );
        }
        weakened
    } else {
        let mut best_clauses: Vec<ChcExpr> = clauses.to_vec();
        let mut any_weakened = false;

        for clause_idx in 0..clauses.len() {
            let disjuncts = collect_disjuncts(&clauses[clause_idx]);
            if disjuncts.len() <= 1 {
                continue;
            }

            let mut bv_distinct_indices: Vec<(usize, ChcVar, u32)> = Vec::new();
            for (i, d) in disjuncts.iter().enumerate() {
                if let Some((var, width)) = extract_bv_distinct_var(d) {
                    bv_distinct_indices.push((i, var, width));
                }
            }

            if bv_distinct_indices.is_empty() {
                continue;
            }

            let mut current_disjuncts: Vec<ChcExpr> = disjuncts.clone();
            let mut weakened_any_in_clause = false;

            for (idx, var, width) in &bv_distinct_indices {
                let bv_one = ChcExpr::BitVec(1, *width);
                let var_expr = ChcExpr::Var(var.clone());
                let ineq = ChcExpr::Op(ChcOp::BvSLe, vec![Arc::new(bv_one), Arc::new(var_expr)]);
                let saved = current_disjuncts[*idx].clone();
                current_disjuncts[*idx] = ineq;

                let candidate_clause = ChcExpr::or_all(current_disjuncts.clone());
                let mut candidate_clauses = best_clauses.clone();
                candidate_clauses[clause_idx] = candidate_clause;
                let candidate_lemma = ChcExpr::and_all(candidate_clauses.clone());
                let candidate_blocking = ChcExpr::not(candidate_lemma);

                if solver.is_inductive_blocking(&candidate_blocking, predicate, level) {
                    best_clauses = candidate_clauses;
                    weakened_any_in_clause = true;
                } else {
                    current_disjuncts[*idx] = saved;
                }
            }

            if weakened_any_in_clause {
                any_weakened = true;
            }
        }

        if !any_weakened {
            return None;
        }

        if solver.config.verbose {
            safe_eprintln!(
                "PDR: #5877 BV-native phase 1b: weakened individual BV distinctions to bvsle (inductive at level {})",
                level
            );
        }
        best_clauses
    };

    let mut minimized_clauses = best_clauses;
    for i in 0..minimized_clauses.len() {
        let disjuncts = collect_disjuncts(&minimized_clauses[i]);
        if disjuncts.len() <= 2 {
            continue;
        }
        for j in (0..disjuncts.len()).rev() {
            let is_bv_disjunct = matches!(
                &disjuncts[j],
                ChcExpr::Op(ChcOp::BvSLe | ChcOp::BvSLt | ChcOp::BvULe | ChcOp::BvULt, _)
            );
            if is_bv_disjunct {
                continue;
            }
            let mut reduced = collect_disjuncts(&minimized_clauses[i]);
            if reduced.len() <= 2 {
                break;
            }
            reduced.remove(j);
            let reduced_clause = if reduced.len() == 1 {
                reduced.into_iter().next().expect("invariant: len == 1")
            } else {
                ChcExpr::or_all(reduced)
            };
            let mut test_clauses = minimized_clauses.clone();
            test_clauses[i] = reduced_clause.clone();
            let test_lemma = ChcExpr::and_all(test_clauses);
            let test_blocking = ChcExpr::not(test_lemma);
            if solver.is_inductive_blocking(&test_blocking, predicate, level) {
                minimized_clauses[i] = reduced_clause;
            }
        }
    }

    let mut split_clauses = Vec::new();
    for clause in &minimized_clauses {
        let disjuncts = collect_disjuncts(clause);
        let bv_disjuncts: Vec<_> = disjuncts
            .iter()
            .filter(|d| {
                matches!(
                    d,
                    ChcExpr::Op(ChcOp::BvSLe | ChcOp::BvSLt | ChcOp::BvULe | ChcOp::BvULt, _)
                )
            })
            .cloned()
            .collect();
        let bool_disjuncts: Vec<_> = disjuncts
            .iter()
            .filter(|d| {
                !matches!(
                    d,
                    ChcExpr::Op(ChcOp::BvSLe | ChcOp::BvSLt | ChcOp::BvULe | ChcOp::BvULt, _)
                )
            })
            .cloned()
            .collect();
        if bv_disjuncts.len() > 1 && !bool_disjuncts.is_empty() {
            for bv_d in &bv_disjuncts {
                let mut single = bool_disjuncts.clone();
                single.push(bv_d.clone());
                let single_clause = if single.len() == 1 {
                    single.into_iter().next().expect("invariant: len == 1")
                } else {
                    ChcExpr::or_all(single)
                };
                split_clauses.push(single_clause);
            }
        } else {
            split_clauses.push(clause.clone());
        }
    }

    let split_lemma = ChcExpr::and_all(split_clauses.clone());
    let split_blocking = ChcExpr::not(split_lemma);
    if solver.is_inductive_blocking(&split_blocking, predicate, level) {
        let mut final_split = split_clauses.clone();
        for i in 0..final_split.len() {
            let disjuncts = collect_disjuncts(&final_split[i]);
            if disjuncts.len() <= 2 {
                continue;
            }
            for j in (0..disjuncts.len()).rev() {
                let is_bv_disjunct = matches!(
                    &disjuncts[j],
                    ChcExpr::Op(ChcOp::BvSLe | ChcOp::BvSLt | ChcOp::BvULe | ChcOp::BvULt, _)
                );
                if is_bv_disjunct {
                    continue;
                }
                let mut reduced = collect_disjuncts(&final_split[i]);
                if reduced.len() <= 2 {
                    break;
                }
                reduced.remove(j);
                let reduced_clause = if reduced.len() == 1 {
                    reduced.into_iter().next().expect("invariant: len == 1")
                } else {
                    ChcExpr::or_all(reduced)
                };
                let mut test_clauses = final_split.clone();
                test_clauses[i] = reduced_clause.clone();
                let test_lemma = ChcExpr::and_all(test_clauses);
                let test_blocking = ChcExpr::not(test_lemma);
                if solver.is_inductive_blocking(&test_blocking, predicate, level) {
                    final_split[i] = reduced_clause;
                }
            }
        }
        if solver.config.verbose {
            safe_eprintln!(
                "PDR: #5877 BV split: {} clauses -> {} per-variable clauses (inductive)",
                minimized_clauses.len(),
                final_split.len()
            );
        }
        let final_lemma = ChcExpr::and_all(final_split);
        return Some(ChcExpr::not(final_lemma));
    }

    for i in (0..minimized_clauses.len()).rev() {
        if minimized_clauses.len() <= 1 {
            break;
        }
        let mut reduced = minimized_clauses.clone();
        reduced.remove(i);
        let test_lemma = ChcExpr::and_all(reduced.clone());
        let test_blocking = ChcExpr::not(test_lemma);
        if solver.is_inductive_blocking(&test_blocking, predicate, level) {
            minimized_clauses = reduced;
        }
    }

    let final_lemma = ChcExpr::and_all(minimized_clauses);
    Some(ChcExpr::not(final_lemma))
}

fn try_bv_inequality_weakening_all_clauses(
    solver: &mut PdrSolver,
    clauses: &[ChcExpr],
    predicate: PredicateId,
    level: usize,
) -> Option<Vec<ChcExpr>> {
    let mut weakened_clauses = Vec::with_capacity(clauses.len());
    let mut any_weakened = false;

    for clause in clauses {
        let disjuncts = collect_disjuncts(clause);
        if disjuncts.len() <= 1 {
            weakened_clauses.push(clause.clone());
            continue;
        }

        let mut bool_disjuncts = Vec::new();
        let mut bv_vars_seen: Vec<(ChcVar, u32)> = Vec::new();

        for d in &disjuncts {
            if let Some((var, width)) = extract_bv_distinct_var(d) {
                if !bv_vars_seen.iter().any(|(v, _)| v.name == var.name) {
                    bv_vars_seen.push((var, width));
                }
            } else if !atom_contains_bv_constant(d) {
                bool_disjuncts.push(d.clone());
            }
        }

        if bv_vars_seen.is_empty() {
            weakened_clauses.push(clause.clone());
            continue;
        }

        let mut new_disjuncts = bool_disjuncts;
        for (var, width) in &bv_vars_seen {
            let bv_one = ChcExpr::BitVec(1, *width);
            let var_expr = ChcExpr::Var(var.clone());
            let ineq = ChcExpr::Op(ChcOp::BvSLe, vec![Arc::new(bv_one), Arc::new(var_expr)]);
            new_disjuncts.push(ineq);
        }
        if new_disjuncts.is_empty() {
            weakened_clauses.push(clause.clone());
            continue;
        }
        let weakened_clause = if new_disjuncts.len() == 1 {
            new_disjuncts
                .into_iter()
                .next()
                .expect("invariant: non-empty")
        } else {
            ChcExpr::or_all(new_disjuncts)
        };
        weakened_clauses.push(weakened_clause);
        any_weakened = true;
    }

    if !any_weakened {
        return None;
    }

    let weakened_lemma = ChcExpr::and_all(weakened_clauses.clone());
    let weakened_blocking = ChcExpr::not(weakened_lemma);
    if solver.is_inductive_blocking(&weakened_blocking, predicate, level) {
        Some(weakened_clauses)
    } else {
        None
    }
}
