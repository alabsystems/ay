// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::factor::{Factor, FactorConfig, FACTOR_SIZE_LIMIT};
use crate::occ_list::OccList;
use crate::symmetry::{self, BinarySwap};
use crate::{
    ProofOutput, SatFeatures, SolverVariant, VariantInput, VariantProfilePlan, VariantRouteProfile,
    VariantStartupPolicy,
};
use std::collections::BTreeMap;

const FACTOR_CANDIDATE_FILTER_ROUNDS: usize = 2;
const SYMMETRY_MAX_PAIRS: usize = 128;
const SYMMETRY_MAX_GROUP_SIZE: usize = 64;

#[derive(Debug)]
struct FactorCensus {
    consumed_candidates: usize,
    transaction_candidates: usize,
    accepted_by_shape: usize,
    rejected_by_lrat_preflight: usize,
    extension_vars_needed: usize,
    new_clauses: usize,
    delete_clauses: usize,
    ticks_consumed: u64,
    completed: bool,
}

#[derive(Debug)]
struct SymmetryCensus {
    refinement_rounds: usize,
    refined_groups: usize,
    largest_color_class: usize,
    skipped_large_groups: usize,
    checked_swaps: usize,
    verified_swaps: usize,
    hypothetical_sbp_clauses: usize,
}

fn clique_n2_k10_formula() -> Option<crate::DimacsFormula> {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join(
        "../../benchmarks/sat/satcomp2024-sample/\
         cb2e8b7fada420c5046f587ea754d052-clique_n2_k10.sanitized.cnf",
    );
    if !path.exists() {
        eprintln!("clique_n2_k10: benchmark missing, skipping");
        return None;
    }
    let content = std::fs::read_to_string(&path).expect("read clique_n2_k10");
    Some(crate::parse_dimacs(&content).expect("parse clique_n2_k10"))
}

fn official_main_lrat_solver(formula: &crate::DimacsFormula) -> Solver {
    let proof = ProofOutput::lrat_text(Vec::<u8>::new(), formula.num_clauses as u64);
    let mut solver = Solver::with_proof_output(formula.num_vars, proof);
    let features = SatFeatures::extract(formula.num_vars, &formula.clauses);
    let input = VariantInput::new(formula.num_vars, formula.num_clauses, true, true)
        .with_route_profile(VariantRouteProfile::OfficialSatCompMainLrat)
        .with_startup_policy(VariantStartupPolicy::DisableWarmupWalk);
    let plan = VariantProfilePlan::for_features(SolverVariant::Default, input, &features);
    plan.apply_to_solver(&mut solver);
    for clause in &formula.clauses {
        solver.add_clause(clause.clone());
    }
    solver
}

fn filtered_factor_occ(solver: &Solver) -> OccList {
    let mut occ = OccList::new(solver.num_vars);
    let lit_count = solver.num_vars * 2;
    let mut binary_counts = vec![0u32; lit_count];
    let mut large_counts = vec![0u32; lit_count];
    let mut next_large_counts = vec![0u32; lit_count];
    let mut candidates = Vec::new();

    for ci in solver.arena.active_indices() {
        if solver.arena.is_learned(ci) {
            continue;
        }
        let lits = solver.arena.literals(ci);
        match lits.len() {
            2 => {
                for &lit in lits {
                    binary_counts[lit.index()] += 1;
                }
                occ.add_clause(ci, lits);
            }
            3..=FACTOR_SIZE_LIMIT => {
                candidates.push(ci);
                for &lit in lits {
                    large_counts[lit.index()] += 1;
                }
            }
            _ => {}
        }
    }

    for _ in 0..FACTOR_CANDIDATE_FILTER_ROUNDS {
        let prev_len = candidates.len();
        next_large_counts.fill(0);
        candidates.retain(|&ci| {
            let lits = solver.arena.literals(ci);
            let keep = lits
                .iter()
                .all(|lit| binary_counts[lit.index()] + large_counts[lit.index()] >= 2);
            if keep {
                for &lit in lits {
                    next_large_counts[lit.index()] += 1;
                }
            }
            keep
        });
        std::mem::swap(&mut large_counts, &mut next_large_counts);
        if candidates.len() == prev_len {
            break;
        }
    }

    for ci in candidates {
        occ.add_clause(ci, solver.arena.literals(ci));
    }

    occ
}

fn factor_census(solver: &Solver) -> FactorCensus {
    let occ = filtered_factor_occ(solver);
    let mut factor = Factor::new(solver.num_vars);
    let result = factor.run(
        &solver.arena,
        &occ,
        &solver.vals,
        solver.var_lifecycle.as_slice(),
        &FactorConfig {
            next_var_id: solver.num_vars,
            effort_limit: u64::MAX,
            elim_bound: solver.inproc.bve.growth_bound() as i64,
        },
    );
    let transaction_candidates = result.applications.len() + result.self_subsuming.len();
    FactorCensus {
        consumed_candidates: result.consumed_candidates.len(),
        transaction_candidates,
        accepted_by_shape: result.factored_count,
        rejected_by_lrat_preflight: transaction_candidates,
        extension_vars_needed: result.extension_vars_needed,
        new_clauses: result.new_clauses.len(),
        delete_clauses: result.to_delete.len(),
        ticks_consumed: result.ticks_consumed,
        completed: result.completed,
    }
}

fn symmetry_census(clauses: &[Vec<Literal>]) -> SymmetryCensus {
    let refined = symmetry::refinement::iterative_color_refinement(clauses);
    let groups = refined.candidate_groups();
    let formula_counts = symmetry::build_formula_counts(clauses);
    let mut checked_swaps = 0usize;
    let mut verified_swaps = Vec::new();
    let mut largest_color_class = 0usize;
    let mut skipped_large_groups = 0usize;

    for variables in groups.values() {
        largest_color_class = largest_color_class.max(variables.len());
        if variables.len() < 2 {
            continue;
        }
        if variables.len() > SYMMETRY_MAX_GROUP_SIZE {
            skipped_large_groups += 1;
            continue;
        }
        for i in 0..variables.len() {
            for j in (i + 1)..variables.len() {
                if checked_swaps >= SYMMETRY_MAX_PAIRS {
                    break;
                }
                checked_swaps += 1;
                let pair = ordered_swap(variables[i], variables[j]);
                if swap_preserves_formula(&formula_counts, pair) {
                    verified_swaps.push(pair);
                }
            }
            if checked_swaps >= SYMMETRY_MAX_PAIRS {
                break;
            }
        }
    }

    let hypothetical_sbp_clauses = symmetry::orbits::extract_orbits(&verified_swaps)
        .iter()
        .map(|orbit| orbit.len().saturating_sub(1))
        .sum();

    SymmetryCensus {
        refinement_rounds: refined.rounds,
        refined_groups: groups.values().filter(|group| group.len() >= 2).count(),
        largest_color_class,
        skipped_large_groups,
        checked_swaps,
        verified_swaps: verified_swaps.len(),
        hypothetical_sbp_clauses,
    }
}

fn ordered_swap(a: Variable, b: Variable) -> BinarySwap {
    if a <= b {
        BinarySwap { lhs: a, rhs: b }
    } else {
        BinarySwap { lhs: b, rhs: a }
    }
}

fn swap_preserves_formula(formula_counts: &BTreeMap<Vec<u32>, u32>, pair: BinarySwap) -> bool {
    formula_counts.iter().all(|(clause, count)| {
        formula_counts
            .get(&swap_clause_key(clause, pair))
            .is_some_and(|swapped_count| swapped_count == count)
    })
}

fn swap_clause_key(clause: &[u32], pair: BinarySwap) -> Vec<u32> {
    let mut swapped = Vec::with_capacity(clause.len());
    for &raw in clause {
        let lit = Literal(raw);
        let mapped_var = if lit.variable() == pair.lhs {
            pair.rhs
        } else if lit.variable() == pair.rhs {
            pair.lhs
        } else {
            lit.variable()
        };
        let mapped_lit = if lit.is_positive() {
            Literal::positive(mapped_var)
        } else {
            Literal::negative(mapped_var)
        };
        swapped.push(mapped_lit.raw());
    }
    swapped.sort_unstable();
    swapped
}

/// Part of #7585/#8922: read-only dense-clique specialist census under the
/// exact official Main/default/regular/LRAT route shape. This test must not
/// enable or apply factor/symmetry; it only measures the rejected opportunity.
#[test]
fn test_official_main_lrat_clique_factor_symmetry_read_only_census() {
    let Some(formula) = clique_n2_k10_formula() else {
        return;
    };
    let solver = official_main_lrat_solver(&formula);

    assert!(
        !solver.is_bve_enabled(),
        "official Main/LRAT must still clamp BVE"
    );
    assert!(
        !solver.is_factor_enabled(),
        "official Main/LRAT must still clamp factor"
    );
    assert!(
        !solver.is_sbva_enabled(),
        "official Main/LRAT must still clamp SBVA"
    );
    assert!(
        !solver.is_sweep_enabled(),
        "official Main/LRAT must still clamp sweep"
    );
    assert!(
        !solver.is_symmetry_enabled(),
        "official Main/LRAT must still clamp symmetry"
    );
    assert!(
        solver.cold.lrat_enabled,
        "census must use an LRAT proof-enabled solver"
    );

    let factor = factor_census(&solver);
    let symmetry = symmetry_census(&formula.clauses);

    eprintln!(
        "clique_n2_k10 official-main-lrat factor/symmetry census: \
         vars={} clauses={} factor={factor:?} symmetry={symmetry:?}",
        formula.num_vars, formula.num_clauses,
    );

    assert_eq!(
        solver.factor_stats().factored_count,
        0,
        "read-only census must not mutate official factor stats"
    );
    assert_eq!(
        factor.consumed_candidates, formula.num_vars,
        "factor census should inspect all clique literals with occurrence count >= 2"
    );
    assert_eq!(
        factor.transaction_candidates, 93,
        "current read-only factor shape should expose the dense clique transaction surface"
    );
    assert_eq!(
        factor.accepted_by_shape, factor.transaction_candidates,
        "accepted factor shape count should match the measured transaction surface"
    );
    assert_eq!(
        factor.rejected_by_lrat_preflight, factor.transaction_candidates,
        "official LRAT census rejects every hypothetical factor transaction before mutation"
    );
    assert_eq!(
        factor.extension_vars_needed, 93,
        "one extension variable would be needed per hypothetical factor transaction"
    );
    assert_eq!(
        factor.new_clauses, 938,
        "read-only factor census should preserve the current hypothetical addition count"
    );
    assert_eq!(
        factor.delete_clauses, 2_815,
        "read-only factor census should preserve the current hypothetical deletion count"
    );
    assert_eq!(
        // #14-factor-cost: pin updated 217_764 → 321_914 when phase-2 of
        // find_next_factor started charging ticks honestly (it previously did
        // the same nested occ scan as phase 1 but charged zero).
        // #rank6: pin updated 321_914 → 217_764 when phase-2 was ELIMINATED —
        // find_next_factor now records (candidate, source, partner) triples
        // during the phase-1 counting scan and recovers the winner's matches
        // by filtering them, so the rescan's work (and its honest ticks) no
        // longer exist. Every other census pin (93 transactions, 938 adds,
        // 2_815 deletes) is unchanged: the merge is output-identical, only
        // cheaper. The value returning exactly to the pre-charging pin
        // confirms the removed ticks are exactly the former phase-2 scan.
        factor.ticks_consumed,
        217_764,
        "read-only factor census should preserve the current scan effort"
    );
    assert!(
        factor.completed,
        "read-only factor census should finish within an unbounded measurement budget"
    );
    assert_eq!(
        symmetry.refinement_rounds, 1,
        "clique symmetry refinement should currently stabilize in one round"
    );
    assert_eq!(
        symmetry.refined_groups, 1,
        "clique symmetry refinement should expose one non-trivial color class"
    );
    assert_eq!(
        symmetry.largest_color_class, formula.num_vars,
        "clique refinement should expose the dense 180-variable symmetry candidate class"
    );
    assert_eq!(
        symmetry.skipped_large_groups, 1,
        "current detector cap should skip the one oversized clique class"
    );
    assert_eq!(
        symmetry.checked_swaps, 0,
        "current symmetry cap must skip the oversized clique group before swap checks"
    );
    assert_eq!(
        symmetry.verified_swaps, 0,
        "no swaps can be verified while the oversized group is skipped"
    );
    assert_eq!(
        symmetry.hypothetical_sbp_clauses, 0,
        "no SBP clauses are available while the oversized group is skipped"
    );
}
