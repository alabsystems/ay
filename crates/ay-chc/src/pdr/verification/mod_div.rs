// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Mod/div fallback strategies for PDR model verification.
//!
//! Contains ITE case-splitting, mod/div conjunct filtering, mod-free fragment
//! checking, and mod equality substitution. These are fallback strategies used
//! when the main SMT query returns Unknown due to mod/div operations.
//!
//! Extracted from `model.rs` as part of the structural split (#5970).

use super::*;

/// Verify a clause case by splitting on ITE expressions.
///
/// Tries three strategies in order:
/// 1. Narrow split: ITE in equality context in body
/// 2. General split: ITE anywhere in the full query
/// 3. Recursive split: handles OR + disequality splitting
pub(super) fn verify_case_via_ite_case_split(
    smt: &mut SmtContext,
    verbose: bool,
    clause_idx: usize,
    case_idx: Option<usize>,
    case_body: &ChcExpr,
    head_filtered: &ChcExpr,
    verify_timeout: std::time::Duration,
) -> bool {
    let case_timeout = verify_timeout.min(VERIFY_CASE_SPLIT_TIMEOUT);

    // First try the narrow split (ITE in equality context in body)
    let ite_cases = PdrSolver::split_ite_in_constraint(case_body);
    if ite_cases.len() > 1 {
        let mut all_pass = true;
        for (ite_case_idx, ite_case_body) in ite_cases.iter().enumerate() {
            let ite_case_query =
                ChcExpr::and(ite_case_body.clone(), ChcExpr::not(head_filtered.clone()));
            smt.reset();
            let ite_result = smt.check_sat_with_timeout(&ite_case_query, case_timeout);
            let ite_result = match ite_result {
                SmtResult::Unknown => {
                    smt.reset();
                    smt.check_sat_with_timeout(&ite_case_query, case_timeout)
                }
                other => other,
            };

            match ite_result {
                SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {
                    if verbose {
                        match case_idx {
                            Some(case_idx) => safe_eprintln!(
                                "PDR: verify_model: clause {} case {} ITE-case {} passed",
                                clause_idx,
                                case_idx,
                                ite_case_idx
                            ),
                            None => safe_eprintln!(
                                "PDR: verify_model: clause {} ITE-case {} passed",
                                clause_idx,
                                ite_case_idx
                            ),
                        }
                    }
                }
                other => {
                    if verbose {
                        match case_idx {
                            Some(case_idx) => safe_eprintln!(
                                "PDR: verify_model: clause {} case {} ITE-case {} failed/unknown ({:?})",
                                clause_idx, case_idx, ite_case_idx, other
                            ),
                            None => safe_eprintln!(
                                "PDR: verify_model: clause {} ITE-case {} failed/unknown ({:?})",
                                clause_idx, ite_case_idx, other
                            ),
                        }
                        safe_eprintln!("  ite_case_body: {}", ite_case_body);
                        safe_eprintln!("  head_filtered: {}", head_filtered);
                    }
                    all_pass = false;
                    break;
                }
            }
        }

        if all_pass {
            if verbose {
                match case_idx {
                    Some(case_idx) => safe_eprintln!(
                        "PDR: verify_model: clause {} case {} passed via ITE case-split (all {} ITE-cases)",
                        clause_idx, case_idx, ite_cases.len()
                    ),
                    None => safe_eprintln!(
                        "PDR: verify_model: clause {} passed via ITE case-split (all {} ITE-cases)",
                        clause_idx, ite_cases.len()
                    ),
                }
            }
            return true;
        }
    }

    // Fallback: try the general split (ITE anywhere in the full query)
    // This handles ITEs that appear in head, or in nested positions in body
    let full_query = ChcExpr::and(case_body.clone(), ChcExpr::not(head_filtered.clone()));
    if let Some([then_case, else_case]) = PdrSolver::split_ite_cases_anywhere(&full_query) {
        let mut both_pass = true;
        for (ite_case_idx, ite_case_query) in [then_case, else_case].iter().enumerate() {
            smt.reset();
            let ite_result = smt.check_sat_with_timeout(ite_case_query, case_timeout);
            let ite_result = match ite_result {
                SmtResult::Unknown => {
                    smt.reset();
                    smt.check_sat_with_timeout(ite_case_query, case_timeout)
                }
                other => other,
            };

            match ite_result {
                SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {
                    if verbose {
                        match case_idx {
                            Some(case_idx) => {
                                safe_eprintln!(
                                "PDR: verify_model: clause {} case {} general-ITE-case {} passed",
                                clause_idx, case_idx, ite_case_idx
                            )
                            }
                            None => safe_eprintln!(
                                "PDR: verify_model: clause {} general-ITE-case {} passed",
                                clause_idx,
                                ite_case_idx
                            ),
                        }
                    }
                }
                other => {
                    if verbose {
                        match case_idx {
                            Some(case_idx) => safe_eprintln!(
                                "PDR: verify_model: clause {} case {} general-ITE-case {} failed/unknown ({:?})",
                                clause_idx, case_idx, ite_case_idx, other
                            ),
                            None => safe_eprintln!(
                                "PDR: verify_model: clause {} general-ITE-case {} failed/unknown ({:?})",
                                clause_idx, ite_case_idx, other
                            ),
                        }
                        safe_eprintln!("  ite_case_query: {}", ite_case_query);
                    }
                    both_pass = false;
                    break;
                }
            }
        }

        if both_pass {
            if verbose {
                match case_idx {
                    Some(case_idx) => safe_eprintln!(
                        "PDR: verify_model: clause {} case {} passed via general ITE case-split",
                        clause_idx,
                        case_idx
                    ),
                    None => safe_eprintln!(
                        "PDR: verify_model: clause {} passed via general ITE case-split",
                        clause_idx
                    ),
                }
            }
            return true;
        }
    }

    // Final fallback: use the recursive PDR SAT check (handles OR + disequality splitting).
    // This avoids spurious verification failures when `check_sat_with_timeout` returns Unknown
    // on disjunctive LIA queries (e.g., `three_dots_moving_2`).
    let result = PdrSolver::try_verification_case_split(smt, verbose, &full_query, case_timeout);
    if matches!(
        result,
        SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_)
    ) {
        if verbose {
            match case_idx {
                Some(case_idx) => safe_eprintln!(
                    "PDR: verify_model: clause {} case {} passed via recursive case-split",
                    clause_idx,
                    case_idx
                ),
                None => safe_eprintln!(
                    "PDR: verify_model: clause {} passed via recursive case-split",
                    clause_idx
                ),
            }
        }
        return true;
    }

    false
}

/// Drop conjuncts that contain mod or div operations.
pub(in crate::pdr) fn drop_mod_div_conjuncts(expr: &ChcExpr) -> ChcExpr {
    let filtered: Vec<_> = expr
        .collect_conjuncts()
        .into_iter()
        .filter(|c| !PdrSolver::contains_mod_or_div(c))
        .collect();
    ChcExpr::and_all(filtered)
}

/// Check if the mod-free fragment of an expression is UNSAT.
///
/// Strips mod/div conjuncts and checks if the remaining pure LIA fragment
/// is unsatisfiable. If so, the full expression is also UNSAT (since removing
/// conjuncts weakens the formula).
pub(in crate::pdr) fn mod_free_fragment_is_unsat(
    smt: &mut SmtContext,
    expr: &ChcExpr,
    verify_timeout: std::time::Duration,
) -> bool {
    if !PdrSolver::contains_mod_or_div(expr) {
        return false;
    }

    let mod_free = drop_mod_div_conjuncts(expr);
    if mod_free == ChcExpr::Bool(true) {
        return false;
    }

    smt.reset();
    let mut result = smt.check_sat_with_timeout(&mod_free, verify_timeout);
    if matches!(result, SmtResult::Unknown) && !mod_free.contains_array_ops() {
        smt.reset();
        result = smt.check_sat_with_timeout(&mod_free, VERIFY_RETRY_TIMEOUT);
    }

    matches!(
        result,
        SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_)
    )
}

/// Substitute mod equalities in a query clause body to help the SMT solver.
///
/// Finds conjuncts of the form `(= (mod X k) Y)` where Y is a variable,
/// replaces all occurrences of `(mod X k)` with `Y`, and adds the range
/// constraint `0 ≤ Y < k`. After substitution, `propagate_constants` and
/// `simplify_constants` can often resolve the formula to `false`.
///
/// Returns `None` if no mod equalities are found.
pub(super) fn substitute_mod_equalities_in_body(body: &ChcExpr) -> Option<ChcExpr> {
    let conjuncts = body.collect_conjuncts();
    let mut substitution_pairs: Vec<(ChcExpr, ChcExpr)> = Vec::new();
    let mut range_constraints: Vec<ChcExpr> = Vec::new();

    for conj in &conjuncts {
        if let ChcExpr::Op(ChcOp::Eq, args) = conj {
            if args.len() == 2 {
                // Match (= (mod X k) Y) where Y is a variable
                let (mod_expr, var_expr, modulus) =
                    if let ChcExpr::Op(ChcOp::Mod, mod_args) = args[0].as_ref() {
                        if mod_args.len() == 2 {
                            if let ChcExpr::Int(k) = mod_args[1].as_ref() {
                                if let ChcExpr::Var(_) = args[1].as_ref() {
                                    (args[0].as_ref().clone(), args[1].as_ref().clone(), *k)
                                } else {
                                    continue;
                                }
                            } else {
                                continue;
                            }
                        } else {
                            continue;
                        }
                    } else if let ChcExpr::Op(ChcOp::Mod, mod_args) = args[1].as_ref() {
                        if mod_args.len() == 2 {
                            if let ChcExpr::Int(k) = mod_args[1].as_ref() {
                                if let ChcExpr::Var(_) = args[0].as_ref() {
                                    (args[1].as_ref().clone(), args[0].as_ref().clone(), *k)
                                } else {
                                    continue;
                                }
                            } else {
                                continue;
                            }
                        } else {
                            continue;
                        }
                    } else {
                        continue;
                    };

                // Soundness guard: skip substitution for non-positive modulus.
                // For k > 0, (mod X k) ∈ [0, k), so range 0 ≤ Y < k is correct.
                // For k ≤ 0, the range would be empty (false) or undefined, which
                // would make the substituted body trivially UNSAT — unsound if the
                // original body is satisfiable.
                if modulus <= 0 {
                    continue;
                }
                substitution_pairs.push((mod_expr, var_expr.clone()));
                // Range constraint: 0 ≤ Y < k (valid only for k > 0)
                range_constraints.push(ChcExpr::ge(var_expr.clone(), ChcExpr::Int(0)));
                range_constraints.push(ChcExpr::lt(var_expr, ChcExpr::Int(modulus)));
            }
        }
    }

    if substitution_pairs.is_empty() {
        return None;
    }

    // Apply substitution: replace (mod X k) with Y
    let mut result = body.substitute_expr_pairs(&substitution_pairs);

    // Add range constraints
    for rc in range_constraints {
        result = ChcExpr::and(result, rc);
    }

    // Propagate constants and simplify
    let result = result.propagate_constants().simplify_constants();
    Some(result)
}

#[cfg(test)]
#[path = "mod_div_tests.rs"]
mod tests;
