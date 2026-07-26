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
mod tests {
    use super::*;
    use crate::types::{PbConstraint, PbLit, PbObjective, PbRel, PbTerm};

    fn lit(var: u32) -> PbLit {
        PbLit {
            var,
            negated: false,
        }
    }

    fn term(coeff: i128, var: u32) -> PbTerm {
        PbTerm {
            coeff,
            lits: vec![lit(var)],
        }
    }

    fn ge(terms: Vec<PbTerm>, rhs: i128) -> PbConstraint {
        PbConstraint {
            terms,
            rel: PbRel::Ge,
            rhs,
        }
    }

    fn instance(num_vars: u32, constraints: Vec<PbConstraint>) -> PbInstance {
        PbInstance {
            num_vars,
            num_constraints: constraints.len() as u32,
            constraints,
            objective: None,
        }
    }

    fn never_stop() -> bool {
        false
    }

    /// Tiny deterministic xorshift PRNG (no dev-deps).
    struct Rng(u64);
    impl Rng {
        fn next(&mut self) -> u64 {
            let mut x = self.0;
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            self.0 = x;
            x
        }
        fn range(&mut self, lo: i128, hi: i128) -> i128 {
            let span = (hi - lo + 1) as u64;
            lo + (self.next() % span) as i128
        }
    }

    /// Brute-force the true integer optimum over all 2^n feasible assignments,
    /// or `None` if no assignment satisfies the constraints (infeasible).
    fn brute_force_optimum(
        obj: &PbObjective,
        constraints: &[PbConstraint],
        n: u32,
    ) -> Option<(i128, Vec<bool>)> {
        let mut best: Option<(i128, Vec<bool>)> = None;
        for mask in 0u32..(1u32 << n) {
            let x: Vec<bool> = (0..n).map(|b| (mask >> b) & 1 == 1).collect();
            if verify_all_constraints(constraints, &x) {
                let v = eval_objective(obj, &x);
                let take = match &best {
                    Some((bv, _)) => v < *bv,
                    None => true,
                };
                if take {
                    best = Some((v, x));
                }
            }
        }
        best
    }

    /// Generates a random satisfiable linear PB instance with <= 14 vars, returning
    /// `(instance, objective, brute_force_optimum_value)`. Retries until feasible.
    fn random_feasible_instance(rng: &mut Rng) -> (PbInstance, PbObjective, i128) {
        loop {
            let n: u32 = rng.range(1, 14) as u32;

            // Random small-coeff objective (single literals only, linear).
            let mut obj_terms = Vec::new();
            for v in 1..=n {
                let coeff = rng.range(0, 5);
                if coeff != 0 {
                    obj_terms.push(term(coeff, v));
                }
            }
            if obj_terms.is_empty() {
                obj_terms.push(term(1, 1));
            }
            let obj = PbObjective { terms: obj_terms };

            // A few random cardinality / knapsack `>=` rows.
            let num_c = rng.range(0, 4);
            let mut constraints = Vec::new();
            for _ in 0..num_c {
                let mut terms = Vec::new();
                let mut total = 0i128;
                for v in 1..=n {
                    let coeff = rng.range(0, 4);
                    if coeff != 0 {
                        total += coeff;
                        terms.push(term(coeff, v));
                    }
                }
                if terms.is_empty() {
                    terms.push(term(1, 1));
                    total = 1;
                }
                // rhs in a range that keeps the row satisfiable when all vars true.
                let rhs = rng.range(1, total.max(1));
                constraints.push(ge(terms, rhs));
            }

            let inst = instance(n, constraints.clone());
            if let Some((opt, _)) = brute_force_optimum(&obj, &constraints, n) {
                return (inst, obj, opt);
            }
            // Infeasible (rare with all-nonneg coeffs and rhs<=sum, but guard anyway);
            // retry with a fresh draw.
        }
    }

    #[test]
    fn bnb_matches_bruteforce_optimum() {
        let mut rng = Rng(0xC0FF_EE12_3456_789A);
        let mut tested = 0usize;
        for _ in 0..200 {
            let (inst, obj, brute_opt) = random_feasible_instance(&mut rng);
            tested += 1;

            let result = solve_branch_and_bound(&inst, &obj, None, 1_000_000, &never_stop)
                .expect("feasible instance must yield an incumbent");

            assert!(
                result.proven_optimal,
                "large budget must prove optimality\nconstraints={:?}\nobj={:?}",
                inst.constraints, obj
            );
            assert_eq!(
                result.value, brute_opt,
                "B&B optimum {} != brute force {}\nconstraints={:?}\nobj={:?}",
                result.value, brute_opt, inst.constraints, obj
            );
            // Incumbent must be feasible with a matching objective value.
            assert!(
                verify_all_constraints(&inst.constraints, &result.assignment),
                "returned assignment must be feasible"
            );
            assert_eq!(
                eval_objective(&obj, &result.assignment),
                result.value,
                "assignment objective must match reported value"
            );
        }
        assert!(tested >= 200, "expected 200 instances, got {tested}");
    }

    #[test]
    fn bnb_small_budget_never_claims_wrong_optimum() {
        let mut rng = Rng(0x1357_9BDF_2468_ACE0);
        let mut tested = 0usize;
        let mut proven_count = 0usize;
        for _ in 0..400 {
            let (inst, obj, brute_opt) = random_feasible_instance(&mut rng);
            tested += 1;

            // Tiny node budget: search almost always cut off. The ONLY soundness
            // requirement is: IF it claims proven_optimal, the value is correct; and
            // any returned assignment is always feasible with a matching value.
            let budget = rng.range(1, 6) as u64;
            let Some(result) = solve_branch_and_bound(&inst, &obj, None, budget, &never_stop)
            else {
                continue; // no incumbent found within the tiny budget: nothing to check.
            };

            assert!(
                verify_all_constraints(&inst.constraints, &result.assignment),
                "any returned assignment must be feasible"
            );
            assert_eq!(
                eval_objective(&obj, &result.assignment),
                result.value,
                "assignment objective must match reported value"
            );
            if result.proven_optimal {
                proven_count += 1;
                assert_eq!(
                    result.value, brute_opt,
                    "CLAIMED optimum {} != brute force {} under tiny budget\nconstraints={:?}\nobj={:?}",
                    result.value, brute_opt, inst.constraints, obj
                );
            } else {
                // Not proven: still a valid upper bound (>= the true optimum).
                assert!(
                    result.value >= brute_opt,
                    "incumbent {} below true optimum {} (impossible if feasible)",
                    result.value,
                    brute_opt
                );
            }
        }
        assert!(tested >= 400, "expected 400 instances, got {tested}");
        // Sanity: at least some tiny-budget runs should still prove optimality on
        // trivial instances, exercising the proven==true branch under small budget.
        assert!(
            proven_count > 0,
            "expected some tiny-budget runs to prove optimality"
        );
    }

    #[test]
    fn bnb_fixing_polarity() {
        // min x1 + x2  s.t.  x1 + x2 >= 1.
        // True optimum: pick exactly one => value 1.
        let obj = PbObjective {
            terms: vec![term(1, 1), term(1, 2)],
        };
        let constraints = vec![ge(vec![term(1, 1), term(1, 2)], 1)];
        let inst = instance(2, constraints);

        // Unconstrained B&B: optimum is 1.
        let base = solve_branch_and_bound(&inst, &obj, None, 1_000_000, &never_stop).unwrap();
        assert!(base.proven_optimal);
        assert_eq!(base.value, 1);

        // Now verify the unit-fixing polarity through augmented_constraints directly:
        // forcing x1 TRUE must make x1=1 satisfy "+1 x1 >= 1", and x1=0 violate it.
        let force_true = augmented_constraints(&inst.constraints, &[(1, true)]);
        assert!(
            verify_all_constraints(&force_true, &[true, false]),
            "x1=true must satisfy a true-fixing"
        );
        assert!(
            !verify_all_constraints(&force_true, &[false, true]),
            "x1=false must violate a true-fixing"
        );

        // Forcing x1 FALSE must make x1=0 satisfy "-1 x1 >= 0", and x1=1 violate it.
        let force_false = augmented_constraints(&inst.constraints, &[(1, false)]);
        assert!(
            verify_all_constraints(&force_false, &[false, true]),
            "x1=false must satisfy a false-fixing"
        );
        assert!(
            !verify_all_constraints(&force_false, &[true, false]),
            "x1=true must violate a false-fixing"
        );

        // End-to-end through the LP: an instance where forcing a var changes the
        // optimum. min x1 + 2 x2  s.t.  x1 + x2 >= 1.
        //   free optimum: x1=1, x2=0 => 1.
        //   forcing x1=false: must take x2 => value 2.
        let obj2 = PbObjective {
            terms: vec![term(1, 1), term(2, 2)],
        };
        let c2 = vec![ge(vec![term(1, 1), term(1, 2)], 1)];
        // Free.
        let free = solve_branch_and_bound(
            &instance(2, c2.clone()),
            &obj2,
            None,
            1_000_000,
            &never_stop,
        )
        .unwrap();
        assert_eq!(free.value, 1);
        assert!(free.proven_optimal);
        // Forcing x1=false at the instance level: add -1 x1 >= 0 as a real constraint.
        let mut forced = c2.clone();
        forced.push(ge(vec![term(-1, 1)], 0)); // x1 <= 0
        let forced_inst = instance(2, forced);
        let forced_res =
            solve_branch_and_bound(&forced_inst, &obj2, None, 1_000_000, &never_stop).unwrap();
        assert!(forced_res.proven_optimal);
        assert_eq!(
            forced_res.value, 2,
            "forcing x1=false should force taking x2"
        );
        assert!(
            !forced_res.assignment[0],
            "x1 must be false under the forcing"
        );
    }

    #[test]
    fn bnb_seed_incumbent_respected() {
        // min x1 + x2 + x3  s.t.  x1 + x2 + x3 >= 2.  True optimum = 2.
        let obj = PbObjective {
            terms: vec![term(1, 1), term(1, 2), term(1, 3)],
        };
        let constraints = vec![ge(vec![term(1, 1), term(1, 2), term(1, 3)], 2)];
        let inst = instance(3, constraints);

        // A correct but non-optimal seed (all true => value 3).
        let seed = (vec![true, true, true], 3i128);
        let result =
            solve_branch_and_bound(&inst, &obj, Some(seed), 1_000_000, &never_stop).unwrap();
        assert!(result.proven_optimal);
        assert_eq!(
            result.value, 2,
            "seed must not prevent finding the true optimum"
        );
        assert!(verify_all_constraints(
            &inst.constraints,
            &result.assignment
        ));

        // An optimal seed: still yields the correct proven optimum (== seed value).
        let opt_seed = (vec![true, true, false], 2i128);
        let result2 =
            solve_branch_and_bound(&inst, &obj, Some(opt_seed), 1_000_000, &never_stop).unwrap();
        assert!(result2.proven_optimal);
        assert_eq!(result2.value, 2);
        assert!(verify_all_constraints(
            &inst.constraints,
            &result2.assignment
        ));

        // A BAD seed (infeasible / wrong value) must be discarded, not trusted: the
        // search still proves the true optimum.
        let bad_seed = (vec![false, false, false], 0i128); // infeasible, wrong value
        let result3 =
            solve_branch_and_bound(&inst, &obj, Some(bad_seed), 1_000_000, &never_stop).unwrap();
        assert!(result3.proven_optimal);
        assert_eq!(result3.value, 2);
        assert!(verify_all_constraints(
            &inst.constraints,
            &result3.assignment
        ));
    }

    #[test]
    fn bnb_infeasible_returns_none() {
        // x1 >= 1 AND -1 x1 >= 0 (x1 <= 0): contradictory => no incumbent.
        let obj = PbObjective {
            terms: vec![term(1, 1)],
        };
        let constraints = vec![ge(vec![term(1, 1)], 1), ge(vec![term(-1, 1)], 0)];
        let inst = instance(1, constraints);
        let result = solve_branch_and_bound(&inst, &obj, None, 1_000_000, &never_stop);
        assert!(
            result.is_none(),
            "infeasible instance must yield no incumbent"
        );
    }

    #[test]
    fn bnb_lp_gap_knapsack_like() {
        // A small LP-gap instance: min x1 + x2  s.t.  2 x1 + 2 x2 >= 3.
        // LP optimum = 3/2 -> ceil 2; integer optimum = 2 (both vars). Exercise B&B
        // end-to-end on an instance whose LP relaxation is fractional.
        let obj = PbObjective {
            terms: vec![term(1, 1), term(1, 2)],
        };
        let constraints = vec![ge(vec![term(2, 1), term(2, 2)], 3)];
        let inst = instance(2, constraints);
        let result = solve_branch_and_bound(&inst, &obj, None, 1_000_000, &never_stop).unwrap();
        assert!(result.proven_optimal);
        assert_eq!(result.value, 2);
    }

    #[test]
    fn bnb_proves_weighted_cover_optimum_with_bounded_nodes() {
        // Selecting at least three items with costs 1..=8 has the unique value
        // floor 1+2+3=6.  This distils the old corpus power probe into a fixed
        // branch-and-bound closure and verifies the returned witness exactly.
        let objective = PbObjective {
            terms: (1..=8).map(|var| term(i128::from(var), var)).collect(),
        };
        let constraint = ge((1..=8).map(|var| term(1, var)).collect(), 3);
        let inst = instance(8, vec![constraint]);
        let result = solve_branch_and_bound(&inst, &objective, None, 100_000, &never_stop)
            .expect("cover is feasible");

        assert!(result.proven_optimal);
        assert_eq!(result.value, 6);
        assert!(verify_all_constraints(
            &inst.constraints,
            &result.assignment
        ));
        assert_eq!(eval_objective(&objective, &result.assignment), 6);
    }
}
