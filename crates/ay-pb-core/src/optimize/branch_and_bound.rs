// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Sound LP-based branch-and-bound (B&B) optimizer for linear pseudo-Boolean
//! minimization.
//!
//! # What this closes
//!
//! The exact-rational LP relaxation ([`crate::optimize::lp_bound`]) gives a SOUND
//! lower bound `ceil(LP*) <= IntOpt`, and the portfolio upgrades a feasible
//! incumbent to `OptimumFound` whenever the incumbent value already meets that
//! floor. But on small **LP-gap** instances (e.g. `2club`, `knapsack`,
//! `dominating_set_hexgrid`, `clique-coloring`, `injcomp`) the LP floor is
//! strictly below the integer optimum, so the floor alone cannot certify the
//! incumbent. Branch-and-bound closes that gap: it splits the search on a
//! fractional variable and re-solves the LP on each child, until **every** leaf is
//! either pruned by a valid LP lower bound or resolved to a feasible integral
//! point. When the whole tree is explored, the best incumbent is the proven
//! integer optimum.
//!
//! # Soundness (the entire point)
//!
//! A `proven_optimal == true` result is a competition-disqualifying claim if it is
//! ever wrong, so the optimality proof rests on exactly one fact:
//!
//! > The recorded incumbent is the minimum objective over **all** integer-feasible
//! > assignments, because the DFS visited the entire `{0,1}^n` tree and at every
//! > leaf either (a) pruned a subtree whose SOUND LP lower bound was already
//! > `>=` the incumbent (so no strictly-better assignment lives there), or
//! > (b) resolved an integral, re-verified-feasible point whose objective updated
//! > the incumbent.
//!
//! The proof can only hold if the tree is exhausted. Therefore:
//!
//! - We **never** prune on a `None` LP bound (an absent bound proves nothing); we
//!   branch instead, keeping the subtree in the search.
//! - We prune **only** when `lb >= incumbent_value` with `lb` the sound LP bound on
//!   the augmented constraint set (original constraints + the unit-fixings on the
//!   path). The LP bound is a lower bound on the integer minimum of that
//!   subproblem, so `lb >= incumbent` means every assignment in the subtree has
//!   objective `>= lb >= incumbent` — none is strictly better, pruning is sound.
//! - The incumbent is only ever updated from an assignment that
//!   [`verify_all_constraints`] accepts, with its value taken from `eval_objective`
//!   of that exact assignment — never from the (fractional, advisory) LP point.
//! - `proven_optimal` is set **only** when the stack empties without ever hitting
//!   the node budget or the external stop. Any node left unexplored (budget, stop,
//!   or — defensively — an oversized fixing path) flips `proven_optimal` to false,
//!   so a cut-off search can only ever report `Satisfiable`-grade information.
//!
//! Because the LP bound is exact-rational (no float trust) and the unit-fixings are
//! exact integer constraints, the prune test is exact. A wrong optimum would
//! require the LP bound to over-estimate the integer minimum of a subproblem —
//! which [`crate::optimize::lp_bound`] proves it never does — or the tree to be
//! reported exhausted while a node was skipped, which the `completed` flag prevents.

use crate::eval::verify_all_constraints;
use crate::optimize::safe_lp_bound::safe_lp_bound_and_point;
use crate::solver::eval_objective;
use crate::types::{PbConstraint, PbInstance, PbLit, PbObjective, PbRel, PbTerm};

/// How close a fractional coordinate must be to 0 or 1 to count as integral.
const INTEGRALITY_TOL: f64 = 1e-6;

/// Max cutting-plane rounds per B&B node (branch-and-cut). Bounded so a single
/// node cannot spin: each round separates valid cuts violated by the LP point and
/// re-solves. Cuts only tighten the (sound) bound; they never affect correctness.
const BNB_NODE_CUT_ROUNDS: u32 = 8;

/// Result of a branch-and-bound solve.
pub(crate) struct BnbResult {
    /// Best feasible assignment found (index `v` is PB variable `v + 1`).
    /// Always satisfies [`verify_all_constraints`] with value == [`Self::value`].
    pub assignment: Vec<bool>,
    /// Objective value of [`Self::assignment`] (`eval_objective`).
    pub value: i128,
    /// `true` iff the whole `{0,1}^n` tree was explored and `value` is therefore
    /// the proven integer optimum. `false` if the search was cut off (node budget,
    /// external stop, or a defensive guard) — then `value`/`assignment` are merely a
    /// valid incumbent, not a certified optimum.
    pub proven_optimal: bool,
}

/// A single search node: the list of variable fixings on the path from the root.
struct Node {
    /// `(var, value)` fixings; `var` is 1-indexed, `value` true = fix to 1.
    fixings: Vec<(u32, bool)>,
}

/// Runs LP-based branch-and-bound for `min objective` over `instance.constraints`,
/// all variables Boolean.
///
/// `seed_incumbent` optionally provides a starting feasible assignment + value to
/// prune against from the first node (it is re-verified before use, so a bad seed is
/// simply ignored). `node_budget` caps the number of nodes explored; `should_stop`
/// is polled to allow an external timeout to abort. On a budget/stop cut-off the
/// best incumbent so far is returned with `proven_optimal == false`.
///
/// Returns `None` only when no feasible incumbent was ever found (neither seeded nor
/// discovered).
pub(crate) fn solve_branch_and_bound(
    instance: &PbInstance,
    objective: &PbObjective,
    seed_incumbent: Option<(Vec<bool>, i128)>,
    node_budget: u64,
    should_stop: &dyn Fn() -> bool,
) -> Option<BnbResult> {
    let num_vars = instance.num_vars;
    let n = usize::try_from(num_vars).ok()?;

    // Incumbent = best feasible assignment + value. Only ever accept an incumbent
    // that re-verifies feasible with a matching objective value; a bad seed is
    // discarded so it can never weaken the proof or be returned unchecked.
    let mut incumbent: Option<(Vec<bool>, i128)> = None;
    if let Some((assignment, value)) = seed_incumbent {
        if assignment.len() == n
            && verify_all_constraints(&instance.constraints, &assignment)
            && eval_objective(objective, &assignment) == value
        {
            incumbent = Some((assignment, value));
        }
    }

    // DFS over fixings. `completed` stays true only if the stack drains with no
    // budget/stop cut-off and no node skipped — the sole basis for proven_optimal.
    let mut stack: Vec<Node> = vec![Node {
        fixings: Vec::new(),
    }];
    let mut nodes_explored: u64 = 0;
    let mut completed = true;

    while let Some(node) = stack.pop() {
        // Budget / external-stop: leaving nodes unexplored forfeits the proof.
        if nodes_explored >= node_budget || should_stop() {
            completed = false;
            break;
        }
        nodes_explored += 1;

        // Augment the original constraints with one unit constraint per fixing:
        //   fix var v TRUE :  +1 x_v >= 1   (forces x_v = 1)
        //   fix var v FALSE: -1 x_v >= 0   (forces x_v = 0, since -x_v >= 0 <=> x_v <= 0)
        let mut node_constraints = augmented_constraints(&instance.constraints, &node.fixings);

        // The FAST safe LP gives BOTH a sound lower bound (for pruning) AND the LP
        // relaxation's primal optimum point (for LP-guided branching / integral
        // resolution). The bound is sound regardless of the point; the point is
        // purely advisory (see `safe_lp_bound_and_point`).
        //
        // `lb == None` means the LP declined to bound — it proves NOTHING, so we
        // must NOT prune; we branch to keep the subtree in the search.
        let (mut lb, mut frac) =
            safe_lp_bound_and_point(objective, &node_constraints, num_vars, should_stop);

        // BRANCH-AND-CUT: tighten this node's bound with valid cutting planes that
        // the LP optimum point violates, re-solving after each round. Every cut from
        // `separate_cuts` is ENTAILED by `node_constraints` (original constraints +
        // the path's unit fixings), so adding it keeps the LP a valid relaxation of
        // THIS subproblem — the bound stays a sound lower bound on the subproblem's
        // integer minimum (pruning stays sound), it only gets tighter. Cuts shrink
        // the integrality gap so fewer nodes are needed. The f64 point is converted
        // to rationals only to *choose* which cuts to separate; cut validity does not
        // depend on the point's precision. Keep the max (highest) sound bound seen.
        let mut cut_round = 0u32;
        while cut_round < BNB_NODE_CUT_ROUNDS && !should_stop() {
            // Stop cutting once the node is already prunable.
            if let (Some(b), Some((_, inc_value))) = (lb, incumbent.as_ref()) {
                if b >= *inc_value {
                    break;
                }
            }
            let Some(point) = frac.as_ref() else { break };
            let rational_point = frac_to_rational_point(point);
            let cuts = crate::optimize::cutting_planes::separate_cuts(
                &node_constraints,
                num_vars,
                &rational_point,
                should_stop,
            );
            if cuts.is_empty() {
                break;
            }
            node_constraints.extend(cuts);
            let (next_lb, next_frac) =
                safe_lp_bound_and_point(objective, &node_constraints, num_vars, should_stop);
            lb = match (lb, next_lb) {
                (Some(a), Some(b)) => Some(a.max(b)),
                (Some(a), None) => Some(a),
                (None, b) => b,
            };
            frac = next_frac;
            cut_round += 1;
        }

        if let (Some(lb), Some((_, inc_value))) = (lb, incumbent.as_ref()) {
            // Prune: every assignment in this subtree has objective >= lb >= incumbent,
            // so none is strictly better. Sound because lb is a valid lower bound on
            // the subproblem's integer minimum.
            if lb >= *inc_value {
                continue;
            }
        }

        // Try to improve the incumbent from the LP optimum point. The point is
        // ADVISORY (an approximate / possibly non-optimal LP primal from the fast
        // safe simplex), so we may only ever adopt the *rounded* assignment after an
        // independent feasibility re-check + exact objective eval — a wrong point
        // then cannot taint the incumbent (it just fails the re-check).
        //
        // SOUNDNESS: unlike an exact-rational LP optimum, an advisory integral point
        // does NOT prove this subtree is exhausted, so we must NOT unconditionally
        // skip branching here. We only `continue` (drop the subtree) when the sound
        // lower bound `lb` certifies it: after the incumbent improves, if
        // `lb >= incumbent` then no completion under this node beats the incumbent.
        // Otherwise we fall through and branch, keeping the subtree in the search.
        if let Some(point) = &frac {
            if let Some(rounded) = integral_assignment(point, n) {
                if verify_all_constraints(&instance.constraints, &rounded) {
                    let value = eval_objective(objective, &rounded);
                    let better = incumbent
                        .as_ref()
                        .map_or(true, |(_, inc_value)| value < *inc_value);
                    if better {
                        incumbent = Some((rounded, value));
                    }
                }
            }
        }

        // Re-check the prune test against the (possibly improved) incumbent: a strong
        // rounded incumbent may now let the sound bound close this subtree.
        if let (Some(lb), Some((_, inc_value))) = (lb, incumbent.as_ref()) {
            if lb >= *inc_value {
                continue;
            }
        }

        // Branch on the most-fractional unfixed variable (closest to 0.5). If no
        // fractional point or no branchable variable exists, fall back to the first
        // unfixed variable so the subtree is still split exhaustively over {0,1}.
        let Some(branch_var) = choose_branch_var(frac.as_deref(), &node.fixings, n) else {
            // Every variable is fixed yet the node was neither pruned nor resolved
            // integrally (e.g. LP declined on a fully-fixed leaf). Evaluate the
            // fully-determined assignment directly so the leaf is still accounted
            // for; this keeps the tree exhaustive.
            if let Some(assignment) = fully_fixed_assignment(&node.fixings, n) {
                if verify_all_constraints(&instance.constraints, &assignment) {
                    let value = eval_objective(objective, &assignment);
                    let better = incumbent
                        .as_ref()
                        .map_or(true, |(_, inc_value)| value < *inc_value);
                    if better {
                        incumbent = Some((assignment, value));
                    }
                }
            }
            continue;
        };

        // Push both children. Exhaustive over {0,1} for `branch_var`. Push the
        // true-child first so the false-child is explored first (DFS pops the top),
        // a mild heuristic; either order is sound.
        let mut true_fixings = node.fixings.clone();
        true_fixings.push((branch_var, true));
        let mut false_fixings = node.fixings;
        false_fixings.push((branch_var, false));
        stack.push(Node {
            fixings: true_fixings,
        });
        stack.push(Node {
            fixings: false_fixings,
        });
    }

    let (assignment, value) = incumbent?;
    Some(BnbResult {
        assignment,
        value,
        // ONLY true when the entire tree was explored. Any cut-off above set
        // `completed = false`, so a partial search cannot claim optimality.
        proven_optimal: completed,
    })
}

/// Converts an advisory f64 LP point in `[0,1]^n` to a rational `FractionalPoint`
/// for `separate_cuts`. Only used to *choose* which valid cuts to separate — cut
/// validity is structural and does not depend on this conversion's precision, so a
/// lossy/clamped value cannot make a cut unsound. Non-finite coords fall back to 0.
fn frac_to_rational_point(point: &[f64]) -> Vec<num_rational::BigRational> {
    use num_traits::Zero;
    point
        .iter()
        .map(|&v| {
            let clamped = v.clamp(0.0, 1.0);
            num_rational::BigRational::from_float(clamped)
                .unwrap_or_else(num_rational::BigRational::zero)
        })
        .collect()
}

/// Builds `constraints` plus one unit fixing constraint per `(var, value)`.
///
/// Fixing polarity (verified by `bnb_fixing_polarity`):
/// - `value == true`  => `+1 x_v >= 1`  forces `x_v = 1`.
/// - `value == false` => `-1 x_v >= 0`  forces `x_v = 0` (i.e. `x_v <= 0`).
fn augmented_constraints(
    constraints: &[PbConstraint],
    fixings: &[(u32, bool)],
) -> Vec<PbConstraint> {
    let mut out = Vec::with_capacity(constraints.len() + fixings.len());
    out.extend_from_slice(constraints);
    for &(var, value) in fixings {
        let (coeff, rhs) = if value { (1, 1) } else { (-1, 0) };
        out.push(PbConstraint {
            terms: vec![PbTerm {
                coeff,
                lits: vec![PbLit {
                    var,
                    negated: false,
                }],
            }],
            rel: PbRel::Ge,
            rhs,
        });
    }
    out
}

/// Rounds an LP point to a 0/1 assignment iff EVERY coordinate is within
/// [`INTEGRALITY_TOL`] of 0 or 1. Returns `None` if any coordinate is genuinely
/// fractional. (`point` has one entry per variable; index `v` = PB var `v + 1`.)
fn integral_assignment(point: &[f64], n: usize) -> Option<Vec<bool>> {
    if point.len() != n {
        return None;
    }
    let mut assignment = Vec::with_capacity(n);
    for &coord in point {
        if coord <= INTEGRALITY_TOL {
            assignment.push(false);
        } else if coord >= 1.0 - INTEGRALITY_TOL {
            assignment.push(true);
        } else {
            return None;
        }
    }
    Some(assignment)
}

/// Picks the unfixed variable whose LP value is closest to 0.5 (most fractional).
/// Falls back to the first unfixed variable when no fractional point is available.
/// Returns `None` iff all variables are fixed.
fn choose_branch_var(point: Option<&[f64]>, fixings: &[(u32, bool)], n: usize) -> Option<u32> {
    let fixed: std::collections::HashSet<u32> = fixings.iter().map(|&(v, _)| v).collect();

    if let Some(point) = point {
        if point.len() == n {
            let mut best: Option<(u32, f64)> = None;
            for v in 0..n {
                let var = (v as u32) + 1;
                if fixed.contains(&var) {
                    continue;
                }
                // Distance to 0.5: smaller = more fractional.
                let dist = (point[v] - 0.5).abs();
                match best {
                    Some((_, best_dist)) if dist >= best_dist => {}
                    _ => best = Some((var, dist)),
                }
            }
            if let Some((var, _)) = best {
                return Some(var);
            }
        }
    }

    // Fallback: first unfixed variable.
    for v in 0..n {
        let var = (v as u32) + 1;
        if !fixed.contains(&var) {
            return Some(var);
        }
    }
    None
}

/// Reconstructs the full assignment when every variable is fixed on the path.
/// Returns `None` if the fixings do not cover all `n` variables (a partial node,
/// which should not reach the all-fixed branch).
fn fully_fixed_assignment(fixings: &[(u32, bool)], n: usize) -> Option<Vec<bool>> {
    let mut assignment = vec![false; n];
    let mut set = vec![false; n];
    for &(var, value) in fixings {
        let idx = usize::try_from(var.checked_sub(1)?).ok()?;
        if idx >= n {
            return None;
        }
        assignment[idx] = value;
        set[idx] = true;
    }
    if set.iter().all(|&s| s) {
        Some(assignment)
    } else {
        None
    }
}

#[cfg(test)]
mod tests;
