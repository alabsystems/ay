// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::bve::fast_eliminate::{QUICK_ELIM_BOUND, QUICK_ELIM_CLS_LIMIT, QUICK_ELIM_OCC_LIMIT};
use crate::{
    ProofOutput, SatFeatures, SolverVariant, VariantInput, VariantProfilePlan, VariantRouteProfile,
    VariantStartupPolicy,
};

#[derive(Debug, Default)]
struct FastelimCensus {
    candidates: usize,
    eliminable: usize,
    clauses_deleted: usize,
    resolvents_added: usize,
    strengthened: usize,
    satisfied_parents: usize,
    resolution_attempts: u64,
    max_resolvents_for_var: usize,
}

fn clique_n2_k10_formula() -> Option<crate::DimacsFormula> {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../benchmarks/sat/satcomp2024-sample/cb2e8b7fada420c5046f587ea754d052-clique_n2_k10.sanitized.cnf");
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

fn candidate_pass_census(
    solver: &mut Solver,
    bound: usize,
    occ_limit: usize,
    cls_limit: usize,
) -> FastelimCensus {
    solver.inproc.bve.set_growth_bound(bound);
    solver
        .inproc
        .bve
        .rebuild_with_vals(&solver.arena, &solver.vals);

    let mut vars = Vec::new();
    while let Some(var) =
        solver
            .inproc
            .bve
            .next_candidate(&solver.arena, &solver.vals, &solver.cold.freeze_counts)
    {
        let pos_occs = solver.inproc.bve.get_occs(Literal::positive(var));
        let neg_occs = solver.inproc.bve.get_occs(Literal::negative(var));
        if pos_occs.len() > occ_limit || neg_occs.len() > occ_limit {
            continue;
        }
        let has_oversized = pos_occs
            .iter()
            .chain(neg_occs.iter())
            .any(|&idx| solver.arena.len_of(idx) > cls_limit);
        if has_oversized {
            continue;
        }
        vars.push(var);
    }

    let mut census = FastelimCensus {
        candidates: vars.len(),
        ..FastelimCensus::default()
    };
    for var in vars {
        let stats_before = solver.inproc.bve.stats().clone();
        let result = solver.inproc.bve.try_eliminate_with_gate_with_marks(
            var,
            &solver.arena,
            None,
            false,
            &mut solver.lit_marks,
            &solver.vals,
            u64::MAX,
        );
        solver.inproc.bve.clear_removed_external(var.index());
        solver.inproc.bve.restore_stats(stats_before);

        census.resolution_attempts = census
            .resolution_attempts
            .saturating_add(result.resolution_attempts);
        if result.eliminated {
            census.eliminable += 1;
            census.clauses_deleted += result.to_delete.len();
            census.resolvents_added += result.resolvents.len();
            census.strengthened += result.strengthened.len();
            census.satisfied_parents += result.satisfied_parents.len();
            census.max_resolvents_for_var =
                census.max_resolvents_for_var.max(result.resolvents.len());
        }
    }

    census
}

/// Part of #8922: stats-only candidate census for the proof-safe question:
/// if official Main/LRAT allowed preprocessing BVE alone, would fastelim find
/// real bounded eliminations on clique_n2_k10 before enabling any other
/// destructive specialist?
#[test]
fn test_official_main_lrat_clique_fastelim_bve_only_census() {
    let Some(formula) = clique_n2_k10_formula() else {
        return;
    };
    let mut solver = official_main_lrat_solver(&formula);

    assert!(
        !solver.is_bve_enabled(),
        "official Main/LRAT must still clamp BVE"
    );
    assert!(
        !solver.is_factor_enabled(),
        "census route must not enable factor"
    );
    assert!(
        !solver.is_sbva_enabled(),
        "census route must not enable SBVA"
    );
    assert!(
        !solver.is_sweep_enabled(),
        "census route must not enable sweep"
    );
    assert!(
        solver.cold.lrat_enabled,
        "census must use an LRAT proof-enabled solver"
    );

    solver.inproc.bve.set_quick_elim_mode(true);
    let quick = candidate_pass_census(
        &mut solver,
        QUICK_ELIM_BOUND,
        QUICK_ELIM_OCC_LIMIT,
        QUICK_ELIM_CLS_LIMIT,
    );
    solver.inproc.bve.set_quick_elim_mode(false);
    let fast = candidate_pass_census(&mut solver, 16, 500, 100);

    eprintln!(
        "clique_n2_k10 official-main-lrat bve-only census: \
         vars={} clauses={} quick={quick:?} fastelim={fast:?}",
        formula.num_vars, formula.num_clauses,
    );

    assert_eq!(
        quick.candidates, 0,
        "tight quick-elim occurrence limits should reject all clique variables"
    );
    assert_eq!(
        quick.eliminable, 0,
        "tight quick-elim pass should not claim the clique opportunity"
    );
    assert_eq!(
        fast.candidates, formula.num_vars,
        "full fastelim should inspect every clique variable after LRAT clamps are bypassed for census"
    );
    assert_eq!(
        fast.resolution_attempts, 6_120,
        "census should document the full failed bounded-resolution surface"
    );
    assert_eq!(
        fast.resolvents_added, 0,
        "stats-only census must not report accepted resolvents without eliminations"
    );
    assert_eq!(
        fast.eliminable, 0,
        "BVE-only fastelim does not independently unlock clique_n2_k10 before other specialists"
    );
}
