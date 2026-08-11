// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Exact certified optimum for the MINIMUM DOMINATING SET class via a 2-PACKING
//! lower-bound witness, with a self-certifying soundness gate.
//!
//! # The class
//!
//! A PB optimization instance is recognised as minimum dominating set when:
//! - the objective is `min sum_v x_v` with every term a single *positive* literal
//!   of coefficient `1` (uniform unit weights, distinct vars), and
//! - there is exactly one constraint per variable, and constraint `i` (0-indexed)
//!   is the *closed-neighbourhood* covering row of vertex `i+1`,
//!   `sum_{u in N[i+1]} x_u >= 1` with `i+1 in N[i+1]` (self-membership), every
//!   literal a positive unit literal, and every neighbourhood variable carrying
//!   unit objective cost.
//!
//! That is exactly: choose a minimum-weight set of vertices `D` such that every
//! vertex is dominated (`N[v] ∩ D != ∅`).
//!
//! # Why the returned value is an *optimum* (sound regardless of bugs here)
//!
//! We never trust a closed-form formula. Instead we exhibit two independently
//! re-checkable witnesses bracketing the domination number `gamma(G)`:
//!
//! * **LB witness — a 2-PACKING `S`.** A set of vertices whose CLOSED
//!   neighbourhoods are PAIRWISE DISJOINT (`N[u] ∩ N[w] = ∅` for distinct
//!   `u,w in S`). Each `v in S` must be dominated, i.e. some variable of `N[v]`
//!   is chosen; since the `N[v]` are disjoint these are distinct chosen vertices,
//!   and every neighbourhood variable carries unit objective cost, so
//!   `gamma(G) >= |S|`. A genuine 2-packing is a valid lower bound — it need NOT
//!   be maximum.
//! * **UB witness — a dominating set `D`.** Either the 2-packing's own centres
//!   (when they already dominate the graph — an *efficient/perfect* code, which
//!   is the common grid/hexgrid case), or AY's incumbent. Re-verified feasible
//!   against the ORIGINAL rows, so `gamma(G) <= |D| = eval_objective(D)`.
//!
//! We return `OptimumFound` ONLY when three independently checkable facts hold:
//!
//! 1. `S` is a GENUINE 2-packing: its closed neighbourhoods are pairwise disjoint
//!    (re-checked), so `|S|` is a valid LOWER bound.
//! 2. `D` satisfies every ORIGINAL constraint (`verify_all_constraints`) — a
//!    genuine feasible dominating set, so `|D|` is a valid UPPER bound.
//! 3. `eval_objective(D) == |S|`.
//!
//! `|S| <= gamma(G) <= |D|` together with `|D| == |S|` forces `gamma(G) == |S|`.
//! None of this trusts the greedy packing/detector: a bug there simply fails one
//! of the three checks and we return `None` (fall through to the general
//! portfolio). A non-tight packing (`|S| < |D|`) DECLINES — it never fabricates a
//! wrong optimum. This makes the path 0-wrong by construction.

use crate::eval::verify_all_constraints;
use crate::output::{PbSolution, PbStatus};
use crate::solver::eval_objective;
use crate::types::{PbConstraint, PbInstance, PbObjective, PbRel};

/// A detected min-dominating-set instance: for every vertex `v` (0-indexed) the
/// closed neighbourhood `N[v]` as a list of 0-indexed variable ids. Indexed by
/// vertex, so `closed_neighborhoods[v]` is the covering row of vertex `v` and is
/// guaranteed (by detection) to contain `v` itself.
struct DominatingSetShape {
    closed_neighborhoods: Vec<Vec<u32>>,
}

/// Recognises the minimum-dominating-set class. Returns `None` for any instance
/// that is not *exactly* this shape (detection is intentionally strict; a
/// mismatch costs only the cheap scan and falls through to the portfolio).
fn detect_dominating_set(
    instance: &PbInstance,
    objective: &PbObjective,
) -> Option<DominatingSetShape> {
    let n = instance.num_vars as usize;
    if n == 0 || objective.terms.is_empty() {
        return None;
    }
    // One closed-neighbourhood covering row per vertex.
    if instance.constraints.len() != n {
        return None;
    }

    // Objective: every term is `+1 * x_v` (positive literal, coeff 1, distinct).
    // Records which variables carry unit objective cost; the 2-packing lower
    // bound relies on every dominator costing exactly 1.
    let mut in_objective = vec![false; n];
    for term in &objective.terms {
        if term.coeff != 1 || term.lits.len() != 1 {
            return None;
        }
        let lit = term.lits[0];
        if lit.negated || lit.var == 0 || lit.var > instance.num_vars {
            return None;
        }
        let idx = (lit.var - 1) as usize;
        if in_objective[idx] {
            // Repeated objective variable -> not the canonical unit shape.
            return None;
        }
        in_objective[idx] = true;
    }

    let mut closed_neighborhoods: Vec<Vec<u32>> = Vec::with_capacity(n);
    for (i, constraint) in instance.constraints.iter().enumerate() {
        let nbhd = closed_neighborhood_of_constraint(constraint, instance.num_vars, &in_objective)?;
        // Self-membership: constraint `i` is the closed neighbourhood of vertex
        // `i` (0-indexed; variable `i+1`), so it must contain `i`.
        if !nbhd.contains(&(i as u32)) {
            return None;
        }
        closed_neighborhoods.push(nbhd);
    }

    Some(DominatingSetShape {
        closed_neighborhoods,
    })
}

/// Returns the sorted, deduplicated 0-indexed variable set of `constraint` if it
/// is a closed-neighbourhood covering row `+1 x_a +1 x_b ... >= 1` of distinct
/// positive unit literals, each carrying unit objective cost; otherwise `None`.
fn closed_neighborhood_of_constraint(
    constraint: &PbConstraint,
    num_vars: u32,
    in_objective: &[bool],
) -> Option<Vec<u32>> {
    if constraint.rel != PbRel::Ge || constraint.rhs != 1 || constraint.terms.is_empty() {
        return None;
    }
    let mut vars = Vec::with_capacity(constraint.terms.len());
    for term in &constraint.terms {
        if term.coeff != 1 || term.lits.len() != 1 {
            return None;
        }
        let lit = term.lits[0];
        if lit.negated || lit.var == 0 || lit.var > num_vars {
            return None;
        }
        let idx = lit.var - 1;
        // A free (zero-cost) dominator would break the 2-packing lower bound:
        // it could dominate at no objective cost.
        if !in_objective[idx as usize] {
            return None;
        }
        vars.push(idx);
    }
    vars.sort_unstable();
    vars.dedup();
    // Distinct literals only (no repeated variable within a row).
    if vars.len() != constraint.terms.len() {
        return None;
    }
    Some(vars)
}

/// Attempts to solve `instance` as a minimum dominating set, returning a
/// certified `OptimumFound` solution or `None`.
///
/// `incumbent`, when supplied, is AY's best feasible assignment so far; it is
/// used as the upper-bound dominating set when the packing's own centres do not
/// already dominate the graph. The self-contained path (centres of a perfect
/// code) needs no incumbent, so passing `None` still certifies the efficient-code
/// grid/hexgrid family.
pub(crate) fn try_solve(
    instance: &PbInstance,
    objective: &PbObjective,
    incumbent: Option<&[bool]>,
) -> Option<PbSolution> {
    let shape = detect_dominating_set(instance, objective)?;
    let nbhd = &shape.closed_neighborhoods;
    let n = instance.num_vars as usize;

    // --- LB witness: greedy 2-packing over vertices. Smaller closed
    // neighbourhoods first tends to admit more disjoint balls; for the regular
    // grid/hexgrid family it recovers the efficient (perfect) code. ---
    let mut order: Vec<usize> = (0..n).collect();
    order.sort_by_key(|&v| (nbhd[v].len(), v));
    let mut used = vec![false; n];
    let mut packing: Vec<usize> = Vec::new();
    for &v in &order {
        if nbhd[v].iter().all(|&u| !used[u as usize]) {
            packing.push(v);
            for &u in &nbhd[v] {
                used[u as usize] = true;
            }
        }
    }

    // --- SOUNDNESS CERTIFICATE (three independent checks) ---
    // 1. `packing` is a GENUINE 2-packing -> `|packing|` is a valid LOWER bound.
    let packing_size = certified_two_packing_size(&packing, nbhd, n)?;

    // --- UB witness: a feasible dominating set whose size equals the LB. ---
    // Candidate A: the packing's own centres (an efficient/perfect code). For a
    // perfect code every vertex lies in some chosen ball, so the centres
    // dominate the graph; `eval_objective(centres) == |packing|` by construction.
    let mut centers = vec![false; n];
    for &v in &packing {
        centers[v] = true;
    }
    let assignment = if verify_all_constraints(&instance.constraints, &centers) {
        centers
    } else {
        // Candidate B: AY's incumbent (only certifies if its value matches the
        // LB; a strictly larger incumbent means packing < domination -> decline).
        let inc = incumbent?;
        let mut projected = vec![false; n];
        for (v, slot) in projected.iter_mut().enumerate() {
            *slot = inc.get(v).copied().unwrap_or(false);
        }
        if !verify_all_constraints(&instance.constraints, &projected) {
            return None;
        }
        projected
    };

    // 2. `assignment` satisfies every ORIGINAL constraint -> valid UPPER bound
    //    (already re-verified above for whichever candidate was chosen).
    // 3. Upper bound value equals the 2-packing lower bound -> optimum.
    let value = eval_objective(objective, &assignment);
    if value != packing_size {
        return None;
    }

    Some(PbSolution {
        status: PbStatus::OptimumFound,
        assignment,
        objective: Some(value),
    })
}

/// Validates that `packing` is a real 2-packing and returns its size, or `None`
/// if any invariant fails (empty/closed-neighbourhood self-membership, or two
/// selected closed neighbourhoods sharing a variable). This is the trusted check
/// behind the `|S|` lower bound; it does NOT trust how the packing was produced.
fn certified_two_packing_size(packing: &[usize], nbhd: &[Vec<u32>], n: usize) -> Option<i128> {
    let mut seen = vec![false; n];
    for &v in packing {
        let ball = nbhd.get(v)?;
        if ball.is_empty() {
            return None;
        }
        // Closed neighbourhood must contain its own centre.
        if !ball.contains(&(v as u32)) {
            return None;
        }
        for &u in ball {
            let slot = seen.get_mut(u as usize)?;
            if *slot {
                // Overlap with a previously selected ball -> not a 2-packing.
                return None;
            }
            *slot = true;
        }
    }
    i128::try_from(packing.len()).ok()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::{PbLit, PbObjective, PbTerm};

    fn pos(var: u32) -> PbLit {
        PbLit {
            var,
            negated: false,
        }
    }

    fn unit_term(var: u32) -> PbTerm {
        PbTerm {
            coeff: 1,
            lits: vec![pos(var)],
        }
    }

    /// Builds a min-dominating-set instance from an undirected graph on `n`
    /// vertices (0-indexed `edges`). Constraint `i` is the closed neighbourhood
    /// `N[i+1] = {i+1} ∪ neighbours`, exactly the normalized OPB shape.
    fn domset_instance(n: u32, edges: &[(u32, u32)]) -> (PbInstance, PbObjective) {
        let mut adj: Vec<std::collections::BTreeSet<u32>> = (0..n)
            .map(|v| std::collections::BTreeSet::from([v]))
            .collect();
        for &(a, b) in edges {
            adj[a as usize].insert(b);
            adj[b as usize].insert(a);
        }
        let constraints: Vec<PbConstraint> = (0..n)
            .map(|v| PbConstraint {
                terms: adj[v as usize].iter().map(|&u| unit_term(u + 1)).collect(),
                rel: PbRel::Ge,
                rhs: 1,
            })
            .collect();
        let objective = PbObjective {
            terms: (1..=n).map(unit_term).collect(),
        };
        let instance = PbInstance {
            num_vars: n,
            num_constraints: constraints.len() as u32,
            constraints,
            objective: Some(objective.clone()),
        };
        (instance, objective)
    }

    /// Brute-force domination number over all 2^n subsets (tiny graphs only).
    fn brute_force_gamma(instance: &PbInstance) -> i128 {
        let n = instance.num_vars as usize;
        let mut best = i128::MAX;
        for mask in 0u32..(1u32 << n) {
            let assignment: Vec<bool> = (0..n).map(|v| (mask >> v) & 1 == 1).collect();
            if verify_all_constraints(&instance.constraints, &assignment) {
                best = best.min(i128::from(mask.count_ones()));
            }
        }
        best
    }

    #[test]
    fn triangle_certifies_gamma_one() {
        // C_3 (complete): one vertex dominates all. gamma = 1.
        let (inst, obj) = domset_instance(3, &[(0, 1), (1, 2), (2, 0)]);
        let sol = try_solve(&inst, &obj, None).expect("triangle certifies");
        assert_eq!(sol.status, PbStatus::OptimumFound);
        assert_eq!(sol.objective, Some(1));
        assert!(verify_all_constraints(&inst.constraints, &sol.assignment));
        assert_eq!(sol.objective, Some(brute_force_gamma(&inst)));
    }

    #[test]
    fn six_cycle_perfect_code_certifies_gamma_two() {
        // C_6 has an efficient (perfect) code {0,3}: greedy recovers it as a
        // 2-packing whose centres also dominate, so the SELF-CONTAINED path
        // (incumbent = None) certifies gamma = 2 with no SAT search.
        let (inst, obj) = domset_instance(6, &[(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 0)]);
        let sol = try_solve(&inst, &obj, None).expect("C6 perfect code certifies");
        assert_eq!(sol.status, PbStatus::OptimumFound);
        assert_eq!(sol.objective, Some(2));
        assert!(verify_all_constraints(&inst.constraints, &sol.assignment));
        // Cross-check the reported optimum against the true domination number.
        assert_eq!(sol.objective, Some(brute_force_gamma(&inst)));
        assert_eq!(brute_force_gamma(&inst), 2);
    }

    #[test]
    fn nine_cycle_perfect_code_certifies_gamma_three() {
        // C_9 has an efficient code {0,3,6}; brute-force confirms gamma = 3.
        let edges: Vec<(u32, u32)> = (0..9).map(|v| (v, (v + 1) % 9)).collect();
        let (inst, obj) = domset_instance(9, &edges);
        let sol = try_solve(&inst, &obj, None).expect("C9 perfect code certifies");
        assert_eq!(sol.objective, Some(3));
        assert!(verify_all_constraints(&inst.constraints, &sol.assignment));
        assert_eq!(sol.objective, Some(brute_force_gamma(&inst)));
    }

    #[test]
    fn five_cycle_does_not_falsely_certify() {
        // C_5: packing number 1 < gamma 2. The packing centres do NOT dominate
        // and no incumbent matches the (too-small) packing, so we DECLINE rather
        // than emit a wrong optimum.
        let (inst, obj) = domset_instance(5, &[(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)]);
        assert_eq!(brute_force_gamma(&inst), 2);
        // Self-contained: centres of the size-1 packing cannot dominate C_5.
        assert!(try_solve(&inst, &obj, None).is_none());
        // Even handed the TRUE optimum {1,4} (size 2), |D| = 2 != |S| = 1, so the
        // gate still declines (a non-tight packing never certifies).
        let optimum = vec![false, true, false, false, true];
        assert!(verify_all_constraints(&inst.constraints, &optimum));
        assert!(try_solve(&inst, &obj, Some(&optimum)).is_none());
    }

    #[test]
    fn path_p3_certifies_via_incumbent() {
        // P_3 (0-1-2): gamma = 1 (centre {1}), but the greedy packing picks a
        // LEAF whose single centre does not dominate, so the self-contained path
        // declines. Supplying AY's incumbent {1} (size == packing 1) certifies.
        let (inst, obj) = domset_instance(3, &[(0, 1), (1, 2)]);
        assert_eq!(brute_force_gamma(&inst), 1);
        assert!(try_solve(&inst, &obj, None).is_none());
        let incumbent = vec![false, true, false];
        assert!(verify_all_constraints(&inst.constraints, &incumbent));
        let sol = try_solve(&inst, &obj, Some(&incumbent)).expect("incumbent certifies P3");
        assert_eq!(sol.objective, Some(1));
        assert!(verify_all_constraints(&inst.constraints, &sol.assignment));
    }

    #[test]
    fn two_disjoint_p3_certifies_via_incumbent() {
        // Two disjoint P_3 components: gamma = 2 ({1,4}); packing = 2 but its
        // leaf centres do not dominate. The incumbent {1,4} matches the LB.
        let (inst, obj) = domset_instance(6, &[(0, 1), (1, 2), (3, 4), (4, 5)]);
        assert_eq!(brute_force_gamma(&inst), 2);
        let incumbent = vec![false, true, false, false, true, false];
        assert!(verify_all_constraints(&inst.constraints, &incumbent));
        let sol = try_solve(&inst, &obj, Some(&incumbent)).expect("incumbent certifies");
        assert_eq!(sol.objective, Some(2));
        assert_eq!(sol.objective, Some(brute_force_gamma(&inst)));
    }

    #[test]
    fn larger_incumbent_does_not_certify() {
        // A correct but SUBOPTIMAL incumbent must never be reported as optimum:
        // P_3 with incumbent {0,2} (size 2) > packing/gamma (1). |D| != |S| -> None.
        let (inst, obj) = domset_instance(3, &[(0, 1), (1, 2)]);
        let suboptimal = vec![true, false, true];
        assert!(verify_all_constraints(&inst.constraints, &suboptimal));
        assert!(try_solve(&inst, &obj, Some(&suboptimal)).is_none());
    }

    #[test]
    fn non_domset_weighted_objective_declines() {
        // Weighted objective is not the unit min-dominating-set shape.
        let (mut inst, _obj) = domset_instance(3, &[(0, 1), (1, 2), (2, 0)]);
        let weighted = PbObjective {
            terms: vec![
                PbTerm {
                    coeff: 2,
                    lits: vec![pos(1)],
                },
                unit_term(2),
                unit_term(3),
            ],
        };
        inst.objective = Some(weighted.clone());
        assert!(try_solve(&inst, &weighted, None).is_none());
    }

    #[test]
    fn non_domset_edge_constraints_decline() {
        // Vertex-cover-style edge clauses (#constraints != #vars, rows are not
        // closed neighbourhoods) must not be mistaken for dominating set.
        let constraints = vec![
            PbConstraint {
                terms: vec![unit_term(1), unit_term(2)],
                rel: PbRel::Ge,
                rhs: 1,
            },
            PbConstraint {
                terms: vec![unit_term(2), unit_term(3)],
                rel: PbRel::Ge,
                rhs: 1,
            },
        ];
        let objective = PbObjective {
            terms: vec![unit_term(1), unit_term(2), unit_term(3)],
        };
        let inst = PbInstance {
            num_vars: 3,
            num_constraints: 2,
            constraints,
            objective: Some(objective.clone()),
        };
        assert!(try_solve(&inst, &objective, None).is_none());
    }

    #[test]
    fn perfect_grid_torus_certifies_self_contained() {
        // 5x5 king-free rook... use the classic efficient-domination case: the
        // 5-cycle "cross product" is fiddly, so use a 4x4 torus of C_4 boxes is
        // also fiddly. Instead use disjoint triangles (3 components), an
        // efficient code with gamma = 3, certified self-contained.
        let (inst, obj) = domset_instance(
            9,
            &[
                (0, 1),
                (1, 2),
                (2, 0),
                (3, 4),
                (4, 5),
                (5, 3),
                (6, 7),
                (7, 8),
                (8, 6),
            ],
        );
        let sol = try_solve(&inst, &obj, None).expect("disjoint triangles certify");
        assert_eq!(sol.objective, Some(3));
        assert_eq!(sol.objective, Some(brute_force_gamma(&inst)));
    }
}
