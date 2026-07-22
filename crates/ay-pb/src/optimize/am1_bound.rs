// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! At-most-one (AM1) clique lower bound for the weighted core-guided optimizer.
//!
//! A class of pigeonhole/at-most-one bounds that the LP relaxation cannot see
//! (when the LP relaxation is `0`). It mirrors the technique UWrMaxSat uses
//! (`MsSolver::preprocess_soft_cls` + `impliedObservedLits`): greedy at-most-one
//! clique extraction over the soft-constraint selectors, with each clique
//! contributing a sound pigeonhole lower bound.
//!
//! # Applicability (important)
//! The mutual-exclusion edges are certified by *single-literal root
//! unit-propagation* over the converted PBO instance. This requires the soft
//! selectors to propagate against one another. On the targeted `wnqueen`/`wcsp`
//! PARTIAL-LIN families this does NOT happen: AY's WBO→PBO conversion relaxes each
//! soft with a big-`M` slack variable, which decouples the selector from
//! base-variable propagation (e.g. assuming a row's `sum x <= 1` selector free
//! forces no individual `x`, and the pigeonhole is a counting/Hall argument that
//! unit propagation never surfaces). On those instances this bound is `0`. It is
//! retained because it is fully sound and DOES fire on any instance whose soft
//! selectors carry propagation-visible at-most-one structure (e.g. directly
//! encoded exactly-one + selector relaxations — see the module tests); it is
//! gated OFF by default in [`crate::optimize::native_oll`] so it never adds probe
//! cost on the default path.
//!
//! # Model
//! The objective is `min sum_i w_i * s_i` over soft selector literals `s_i`
//! (paying `w_i` iff `s_i` is true). The "free" (no-cost) polarity of selector
//! `i` is `f_i = complement(s_i)`: setting `f_i` true means the soft is satisfied
//! for free. We build the *mutual-exclusion graph* over the free literals: an
//! edge `{i, j}` means `f_i` and `f_j` cannot both be true in any feasible
//! assignment. An edge is certified by root unit-propagation
//! ([`PbCdclSolver::implied_literals_at_root`]): assuming `f_i` forces `s_j`
//! true (so `f_j` is false), and/or vice versa.
//!
//! An *at-most-one clique* `C` over the free literals is a set in which at most
//! one `f_i` can be true (a clique in the mutual-exclusion graph guarantees this:
//! every pair is mutually exclusive, so no two can be simultaneously free). Hence
//! in any feasible assignment at least `|C| - 1` of the selectors in `C` are paid.
//!
//! # Lower-bound derivation (soundness)
//! Let `C` be an at-most-one clique with weights `{w_i : i in C}`. At most one
//! selector is free, so at least `|C| - 1` are paid; to minimize the paid weight
//! the single free selector is the most expensive one. Therefore
//! ```text
//!     sum_{i in C} w_i * s_i  >=  (sum_{i in C} w_i) - max_{i in C} w_i
//! ```
//! over every feasible assignment (this is the sum of the `|C|-1` smallest
//! weights, which is `>= (|C|-1) * min_w`, so it is at least as strong as the
//! `(|C|-1) * min_w` bound). We use the tighter `sum - max` form.
//!
//! A *forced-paid* selector (`f_i` alone conflicts at the root — the soft can
//! never be satisfied) contributes its full weight `w_i` unconditionally.
//!
//! To sum contributions across multiple cliques (and forced-paid selectors) we
//! require them to be **vertex-disjoint** (each selector used at most once). Then
//! `sum_i w_i * s_i >= sum_C contribution(C)`, because the cliques partition a
//! subset of the selectors, each contributes its lower bound independently, and
//! the remaining selectors contribute `>= 0`. This is a valid global lower bound
//! on the objective.
//!
//! The optimum gate ([`crate::optimize::native_oll`]'s `verify_native_optimum`)
//! re-evaluates the WITNESS against the ORIGINAL constraints (feasibility +
//! exact objective recompute) and checks the claimed value lies inside the
//! tracked `[lower_bound, upper_bound]` interval. Note the limit of that check:
//! the lower bound it compares against is the very floor derived here, so the
//! gate catches witness/value corruption but cannot detect an overshooting
//! lower bound by itself — the soundness of an OPTIMUM claim still rests on the
//! clique/pigeonhole derivation above being valid.

use crate::cdcl::{ImpliedLiteralsOutcome, PbCdclSolver};
use crate::types::{PbInstance, PbLit};

/// A soft selector with its weight (mirrors `native_oll::WeightedSoft`). The
/// `literal` true under a model means the soft is paid (costs `weight`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct Am1Soft {
    pub literal: PbLit,
    pub weight: i128,
}

/// Caps the work the AM1 bound is allowed to spend so it never starves the
/// core-guided descent that follows. Each cap is a hard upper bound on the
/// number of root-implication probes (one cheap unit-propagation each).
const MAX_SELECTORS: usize = 4_096;
/// Maximum number of probes total (each probe is one `implied_literals_at_root`).
const MAX_PROBES: usize = 4_096;

/// Computes a sound AM1 (at-most-one) clique lower bound on the objective
/// `sum_i w_i * softs[i].literal`, over the soft selectors, using root
/// unit-propagation to certify the mutual-exclusion edges.
///
/// `solver` must be a freshly built [`PbCdclSolver`] over the instance at the
/// root (decision level 0). The query is state-restoring, so the solver is left
/// exactly as it was found.
///
/// Returns `Some(bound)` with a valid lower bound `>= 0` on the objective, or
/// `None` when the technique does not apply (no selectors, no derivable
/// structure, interrupted, or budget exhausted before any contribution). A
/// returned bound is always a sound floor: `bound <= cost of any feasible
/// assignment`.
pub(crate) fn am1_clique_lower_bound<F>(
    solver: &mut PbCdclSolver,
    softs: &[Am1Soft],
    mut should_stop: F,
) -> Option<i128>
where
    F: FnMut() -> bool,
{
    if softs.is_empty() || softs.len() > MAX_SELECTORS {
        return None;
    }
    // Drop non-positive weights defensively (the caller normalizes to > 0, but a
    // zero-weight selector contributes nothing and would dilute cliques).
    let active: Vec<Am1Soft> = softs.iter().copied().filter(|s| s.weight > 0).collect();
    if active.is_empty() {
        return None;
    }

    // For each selector, the free literal `f_i` we probe and a lookup from the
    // selector's *paid* literal back to its index (so an implied paid literal in
    // one probe identifies the incompatible selector). We key on the (var, neg)
    // pair of the selector's `literal`.
    let free_lits: Vec<PbLit> = active.iter().map(|s| complement(s.literal)).collect();

    let mut paid_lit_to_index: std::collections::BTreeMap<PbLit, usize> =
        std::collections::BTreeMap::new();
    for (idx, soft) in active.iter().enumerate() {
        // If two distinct selectors share the same paid literal the caller's
        // normalization would have merged them; if not, keep the first (a later
        // duplicate simply will not gain edges via that key, which is safe).
        paid_lit_to_index.entry(soft.literal).or_insert(idx);
    }

    // Probe every selector's free literal once (capped at `MAX_PROBES`) and
    // record:
    //  - forced[i]: f_i alone conflicts -> selector i MUST be paid.
    //  - adjacency: edge i->j when assuming f_i implies s_j (so f_j is false).
    let n = active.len();
    let probe_limit = n.min(MAX_PROBES);
    let mut forced = vec![false; n];
    let mut adj: Vec<Vec<usize>> = vec![Vec::new(); n];
    let mut any_probe_ran = false;

    for i in 0..probe_limit {
        if should_stop() {
            break;
        }
        match solver.implied_literals_at_root(free_lits[i]) {
            ImpliedLiteralsOutcome::Conflict => {
                forced[i] = true;
                any_probe_ran = true;
            }
            ImpliedLiteralsOutcome::Implied(implied) => {
                any_probe_ran = true;
                for lit in implied {
                    if let Some(&j) = paid_lit_to_index.get(&lit) {
                        if j != i {
                            adj[i].push(j);
                        }
                    }
                }
            }
            ImpliedLiteralsOutcome::Unavailable => {
                // No information for this selector; skip it.
            }
        }
    }

    if !any_probe_ran {
        return None;
    }

    // Build the symmetric mutual-exclusion graph: an undirected edge {i, j} is
    // present iff EITHER direction certified incompatibility (f_i forces s_j, or
    // f_j forces s_i). A single direction is sufficient: it proves f_i and f_j
    // cannot both be true.
    let mut neighbors: Vec<std::collections::BTreeSet<usize>> =
        vec![std::collections::BTreeSet::new(); n];
    for i in 0..n {
        for &j in &adj[i] {
            // Both endpoints must be non-forced to participate in a clique (a
            // forced selector is accounted for separately and removed below).
            if !forced[i] && !forced[j] {
                neighbors[i].insert(j);
                neighbors[j].insert(i);
            }
        }
    }

    // Accumulate the bound with checked i128 arithmetic; clamp back to i128 at the
    // end (the objective fits i128 by precondition, so a valid floor does too).
    let mut bound: i128 = 0;

    // 1) Forced-paid selectors contribute their FULL weight.
    let mut used = vec![false; n];
    for i in 0..n {
        if forced[i] {
            bound = bound.checked_add(active[i].weight)?;
            used[i] = true;
        }
    }

    // 2) Greedy vertex-disjoint clique cover over the remaining vertices. Process
    //    seeds in descending weight so heavy selectors anchor cliques. Each clique
    //    contributes `sum(weights) - max(weight)`.
    let mut order: Vec<usize> = (0..n).filter(|&i| !used[i]).collect();
    order.sort_by(|&a, &b| active[b].weight.cmp(&active[a].weight).then(a.cmp(&b)));

    for &seed in &order {
        if used[seed] {
            continue;
        }
        // Grow a clique greedily from `seed`. A candidate `c` joins iff it is
        // adjacent to every current clique member (the at-most-one property is
        // pairwise, so a clique guarantees at most one free among all members).
        let mut clique = vec![seed];
        used[seed] = true;

        // Candidate set: neighbors of the seed, by descending weight.
        let mut candidates: Vec<usize> = neighbors[seed]
            .iter()
            .copied()
            .filter(|&c| !used[c])
            .collect();
        candidates.sort_by(|&a, &b| active[b].weight.cmp(&active[a].weight).then(a.cmp(&b)));

        for c in candidates {
            if used[c] {
                continue;
            }
            // Must be adjacent to ALL current members.
            if clique.iter().all(|&m| neighbors[c].contains(&m)) {
                clique.push(c);
                used[c] = true;
            }
        }

        if clique.len() >= 2 {
            // contribution = sum(weights) - max(weight): leave the single most
            // expensive selector free, pay the rest. Sound (see module docs).
            let mut sum: i128 = 0;
            let mut max_w: i128 = i128::MIN;
            for &m in &clique {
                sum = sum.checked_add(active[m].weight)?;
                max_w = max_w.max(active[m].weight);
            }
            let contribution = sum.checked_sub(max_w)?;
            debug_assert!(contribution >= 0, "AM1 clique contribution must be >= 0");
            bound = bound.checked_add(contribution)?;
        }
        // Singletons (clique.len() == 1) contribute nothing; the vertex is now
        // `used` so it cannot be double-counted by a later seed.
    }

    if bound <= 0 {
        return None;
    }
    i128::try_from(bound).ok()
}

/// Convenience wrapper: builds a fresh interruptible solver over `instance` and
/// computes the AM1 clique lower bound. Returns `None` if the bound does not
/// apply. The solver is discarded afterward (the bound is a standalone floor).
pub(crate) fn am1_clique_lower_bound_for_instance<F>(
    instance: &PbInstance,
    softs: &[Am1Soft],
    mut should_stop: F,
) -> Option<i128>
where
    F: FnMut() -> bool,
{
    if softs.is_empty() || should_stop() {
        return None;
    }
    let mut solver = PbCdclSolver::new_unpreprocessed_interruptible(instance, &mut should_stop);
    am1_clique_lower_bound(&mut solver, softs, should_stop)
}

fn complement(lit: PbLit) -> PbLit {
    PbLit {
        var: lit.var,
        negated: !lit.negated,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::eval::verify_all_constraints;
    use crate::parser::parse_opb;
    use crate::solver::eval_objective;
    use crate::types::{PbObjective, PbTerm};

    /// Brute-force exact minimum objective over all feasible 2^n assignments.
    fn brute_force_optimum(instance: &PbInstance, objective: &PbObjective) -> Option<i128> {
        let n = instance.num_vars as usize;
        assert!(n <= 22, "brute force only for tiny instances");
        let mut best: Option<i128> = None;
        for mask in 0u32..(1u32 << n) {
            let assignment: Vec<bool> = (0..n).map(|i| (mask >> i) & 1 == 1).collect();
            if !verify_all_constraints(&instance.constraints, &assignment) {
                continue;
            }
            let value = eval_objective(objective, &assignment);
            best = Some(best.map_or(value, |b| b.min(value)));
        }
        best
    }

    /// Extracts the soft selectors (relaxation vars) and weights from a converted
    /// PBO objective so the AM1 bound can be evaluated directly.
    fn softs_from_objective(objective: &PbObjective) -> Vec<Am1Soft> {
        objective
            .terms
            .iter()
            .filter_map(|t| {
                let [lit] = t.lits.as_slice() else {
                    return None;
                };
                (t.coeff > 0).then_some(Am1Soft {
                    literal: *lit,
                    weight: t.coeff,
                })
            })
            .collect()
    }

    #[test]
    fn am1_bound_is_zero_when_no_incompatibility() {
        // Two independent at-least-one constraints; the cheapest model pays 0 for
        // each selector (selectors can all be free). No AM1 structure.
        let input = "* #variable= 4 #constraint= 2\n\
            min: +1 x3 +1 x4 ;\n\
            +1 x1 +1 x2 +5 x3 >= 1 ;\n\
            +1 x1 +1 x2 >= 1 ;\n";
        let instance = parse_opb(input).expect("parse");
        let objective = instance.objective.clone().expect("obj");
        let softs = softs_from_objective(&objective);
        let bound = am1_clique_lower_bound_for_instance(&instance, &softs, || false);
        // No mutual exclusion among selectors -> no positive bound.
        assert!(bound.is_none() || bound == Some(0));
    }

    #[test]
    fn am1_bound_single_exactly_one_pigeonhole() {
        // Three booleans, exactly-one structure enforced by hard constraints, and
        // each "extra" selection costs. Encode an at-most-one group of THREE
        // selectors via reified constraints so assuming any free selector forces
        // the others paid. We test the bound never exceeds the true optimum.
        //
        // Hard: x1 + x2 + x3 = 1 (exactly one). Selectors s1,s2,s3 with
        // s_i = 0 meaning "x_i may be chosen". Use the relaxation form directly:
        //   x_i + M*s_i >= 1  (s_i free => x_i must be 1)
        // With exactly-one, at most one x_i is 1, so at most one s_i can be free.
        let input = "* #variable= 6 #constraint= 4\n\
            min: +1 x4 +1 x5 +1 x6 ;\n\
            +1 x1 +1 x2 +1 x3 = 1 ;\n\
            +1 x1 +1 x4 >= 1 ;\n\
            +1 x2 +1 x5 >= 1 ;\n\
            +1 x3 +1 x6 >= 1 ;\n";
        let instance = parse_opb(input).expect("parse");
        let objective = instance.objective.clone().expect("obj");
        let softs = softs_from_objective(&objective);
        let bound = am1_clique_lower_bound_for_instance(&instance, &softs, || false).unwrap_or(0);
        let bf = brute_force_optimum(&instance, &objective).expect("feasible");
        // SOUNDNESS: the bound must never exceed the true optimum.
        assert!(bound <= bf, "AM1 bound {bound} exceeds true optimum {bf}");
        // The exactly-one + relaxation structure forces >= 2 of the 3 selectors
        // paid (at most one x_i is 1, so at most one s_i free): bound should reach
        // the optimum here.
        assert_eq!(bf, 2, "expected optimum 2, got {bf}");
        assert_eq!(bound, 2, "AM1 bound should close this pigeonhole");
    }

    #[test]
    fn am1_bound_forced_paid_selector_full_weight() {
        // A selector whose free polarity is infeasible: x1 must be 1 (hard unit),
        // and s1 free forces x1 = 0 -> conflict. So s1 is forced paid (weight 7).
        let input = "* #variable= 2 #constraint= 2\n\
            min: +7 x2 ;\n\
            +1 x1 >= 1 ;\n\
            -1 x1 +1 x2 >= 0 ;\n";
        // Constraint 2: -x1 + x2 >= 0  i.e. x2 >= x1. With x1=1 forced, x2=1 forced.
        // Selector here is x2 (paid). Free polarity ~x2 forces x1<=0, conflict with
        // x1>=1. So forced-paid, contributing 7.
        let instance = parse_opb(input).expect("parse");
        let objective = instance.objective.clone().expect("obj");
        let softs = softs_from_objective(&objective);
        let bound = am1_clique_lower_bound_for_instance(&instance, &softs, || false).unwrap_or(0);
        let bf = brute_force_optimum(&instance, &objective).expect("feasible");
        assert!(bound <= bf, "bound {bound} exceeds optimum {bf}");
        assert_eq!(bf, 7);
        assert_eq!(
            bound, 7,
            "forced-paid selector should contribute full weight"
        );
    }

    #[test]
    fn am1_bound_never_exceeds_brute_force_random() {
        // Differential soundness: over random small weighted instances with
        // exactly-one + relaxation structure, the AM1 bound is ALWAYS <= the true
        // optimum. A bound that exceeds the optimum would be a false floor.
        let mut seed: u64 = 0xD1B5_4A32_D192_ED03;
        let mut next = || {
            seed = seed
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            seed >> 33
        };
        for _ in 0..200 {
            // n in 2..=4 groups, each an exactly-one over 2 base vars + a selector.
            let groups = 2 + (next() % 3) as u32; // 2..=4
            let mut constraints = Vec::new();
            let mut obj_terms = Vec::new();
            // Build `groups` independent exactly-one pairs sharing a global pool.
            // base vars: 2 per group; selector: 1 per group.
            let base_per = 2u32;
            let total_base = groups * base_per;
            // exactly-one over each group's base vars.
            for g in 0..groups {
                let start = g * base_per + 1;
                let lits: Vec<PbTerm> = (0..base_per)
                    .map(|k| PbTerm {
                        coeff: 1,
                        lits: vec![PbLit {
                            var: start + k,
                            negated: false,
                        }],
                    })
                    .collect();
                constraints.push(crate::types::PbConstraint {
                    terms: lits,
                    rel: crate::types::PbRel::Eq,
                    rhs: 1,
                });
            }
            let mut var = total_base + 1;
            // For each base var, a selector relaxation: base + M*sel >= 1.
            for b in 1..=total_base {
                let sel = var;
                var += 1;
                let w = 1 + (next() % 9) as i128; // 1..=9
                constraints.push(crate::types::PbConstraint {
                    terms: vec![
                        PbTerm {
                            coeff: 1,
                            lits: vec![PbLit {
                                var: b,
                                negated: false,
                            }],
                        },
                        PbTerm {
                            coeff: 1,
                            lits: vec![PbLit {
                                var: sel,
                                negated: false,
                            }],
                        },
                    ],
                    rel: crate::types::PbRel::Ge,
                    rhs: 1,
                });
                obj_terms.push(PbTerm {
                    coeff: w,
                    lits: vec![PbLit {
                        var: sel,
                        negated: false,
                    }],
                });
            }
            let num_vars = var - 1;
            if num_vars > 20 {
                continue;
            }
            let instance = PbInstance {
                num_vars,
                num_constraints: constraints.len() as u32,
                constraints,
                objective: Some(PbObjective {
                    terms: obj_terms.clone(),
                }),
            };
            let objective = instance.objective.clone().unwrap();
            let softs = softs_from_objective(&objective);
            let bound =
                am1_clique_lower_bound_for_instance(&instance, &softs, || false).unwrap_or(0);
            let bf = brute_force_optimum(&instance, &objective);
            if let Some(bf) = bf {
                assert!(
                    bound <= bf,
                    "AM1 bound {bound} exceeds brute-force optimum {bf}"
                );
                assert!(bound >= 0, "AM1 bound must be non-negative");
            }
        }
    }

    #[test]
    fn implied_literals_at_root_restores_solver_state() {
        // State-restoration gate: solving an instance, calling the probe, then
        // solving again must give the same result and leave the solver clean.
        let input = "* #variable= 6 #constraint= 4\n\
            min: +1 x4 +1 x5 +1 x6 ;\n\
            +1 x1 +1 x2 +1 x3 = 1 ;\n\
            +1 x1 +1 x4 >= 1 ;\n\
            +1 x2 +1 x5 >= 1 ;\n\
            +1 x3 +1 x6 >= 1 ;\n";
        let instance = parse_opb(input).expect("parse");
        let mut solver = PbCdclSolver::new_unpreprocessed_interruptible(&instance, &mut || false);
        let first = solver.solve_with_assumptions(&[]);
        // Probe a selector's free literal a few times; state must be restored each
        // time so the subsequent solve matches the first.
        for var in [4u32, 5, 6, 1, 2, 3] {
            let _ = solver.implied_literals_at_root(PbLit { var, negated: true });
            let _ = solver.implied_literals_at_root(PbLit {
                var,
                negated: false,
            });
        }
        let second = solver.solve_with_assumptions(&[]);
        match (first, second) {
            (
                crate::cdcl::PbCdclAssumptionResult::Satisfiable(_),
                crate::cdcl::PbCdclAssumptionResult::Satisfiable(_),
            ) => {}
            (a, b) => panic!("state not restored: first {a:?} second {b:?}"),
        }
    }
}
