// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `group_soundness::soundness_7904_preprocessing` to preserve test FQNs.

// ===========================================================================
// BVE (Bounded Variable Elimination) edge cases
//
// BVE resolves out a variable by replacing it with all resolvents of its
// positive and negative clauses. Bugs typically arise when:
// - Tautological resolvents are not filtered
// - Self-subsuming resolution creates incorrect clauses
// - Clause strengthening corrupts learned clauses
// - Model reconstruction after BVE is incorrect
// ===========================================================================

/// BVE on a variable that appears in both polarities with no tautological
/// resolvents. The result must remain SAT.
#[test]
fn bve_simple_elimination_sat() {
    // x0 appears in: (x0 v x1) and (-x0 v x2)
    // Resolvent: (x1 v x2) — still SAT
    let clauses = vec![vec![pos(0), pos(1)], vec![neg(0), pos(2)], vec![pos(3)]];
    solve_single_feature(4, &clauses, "bve-simple-sat", Some(true), |s| {
        s.set_bve_enabled(true);
    });
}

/// BVE elimination where all resolvents are tautological.
/// The variable can be eliminated without adding any clauses.
#[test]
fn bve_all_tautological_resolvents_sat() {
    // x0 in: (x0 v x1), (-x0 v -x1), (x2)
    // Resolvent of first two: (x1 v -x1) — tautology, discarded
    // Formula is SAT (x0=T, x1=T, x2=T)
    let clauses = vec![vec![pos(0), pos(1)], vec![neg(0), neg(1)], vec![pos(2)]];
    solve_single_feature(3, &clauses, "bve-taut-resolvent", Some(true), |s| {
        s.set_bve_enabled(true);
    });
}

/// BVE on a pure variable (appears in only one polarity).
/// Should be eliminable without adding any resolvents.
#[test]
fn bve_pure_variable_sat() {
    // x0 appears only positive: (x0 v x1), (x0 v x2)
    // Setting x0=T satisfies both. No negative occurrences.
    let clauses = vec![
        vec![pos(0), pos(1)],
        vec![pos(0), pos(2)],
        vec![neg(1), neg(2)],
    ];
    solve_single_feature(3, &clauses, "bve-pure-var", Some(true), |s| {
        s.set_bve_enabled(true);
    });
}

/// BVE where eliminating a variable makes the formula UNSAT.
/// The resolvent of the two clauses containing x0 produces the empty clause.
#[test]
fn bve_elimination_causes_unsat() {
    // (x0) and (-x0) — resolvent is the empty clause
    let clauses = vec![vec![pos(0)], vec![neg(0)]];
    solve_single_feature_with_drat(1, &clauses, "bve-elim-unsat", Some(false), |s| {
        s.set_bve_enabled(true);
    });
}

/// BVE with a variable that has many positive and negative occurrences.
/// Tests that the resolvent count limit (growth bound) is respected.
#[test]
fn bve_high_occurrence_count_sat() {
    let n = 10u32;
    let mut clauses = Vec::new();
    // x0 appears positive with x1..x5
    for i in 1..=5 {
        clauses.push(vec![pos(0), pos(i)]);
    }
    // x0 appears negative with x6..x10
    for i in 6..=n {
        clauses.push(vec![neg(0), pos(i)]);
    }
    // Force some variables to ensure SAT
    clauses.push(vec![pos(1)]);
    solve_single_feature(
        (n + 1) as usize,
        &clauses,
        "bve-high-occ",
        Some(true),
        |s| {
            s.set_bve_enabled(true);
        },
    );
}

/// BVE model reconstruction: after eliminating x0, the model for x0 must
/// be reconstructed to satisfy the original formula.
#[test]
fn bve_model_reconstruction_sat() {
    // (x0 v x1 v x2), (-x0 v x3), (-x1), (-x2)
    // With -x1, -x2 forced: x0 must be true. Then x3 is free.
    let clauses = vec![
        vec![pos(0), pos(1), pos(2)],
        vec![neg(0), pos(3)],
        vec![neg(1)],
        vec![neg(2)],
    ];
    let r = solve_single_feature(4, &clauses, "bve-model-recon", Some(true), |s| {
        s.set_bve_enabled(true);
    });
    if let SatResult::Sat(model) = &r {
        // x0 must be true since x1, x2 are forced false
        assert!(
            model.first().copied().unwrap_or(false),
            "BVE model reconstruction: x0 should be true"
        );
    }
}

/// BVE on a chain of implications. Eliminating middle variables must
/// preserve the implied relationship.
#[test]
fn bve_implication_chain_unsat() {
    // x0 => x1 => x2 => x3, plus x0 and -x3
    // UNSAT: x0=T forces x1=T, x2=T, x3=T, contradicting -x3
    let clauses = vec![
        vec![neg(0), pos(1)], // x0 => x1
        vec![neg(1), pos(2)], // x1 => x2
        vec![neg(2), pos(3)], // x2 => x3
        vec![pos(0)],         // x0
        vec![neg(3)],         // -x3
    ];
    solve_single_feature_with_drat(4, &clauses, "bve-impl-chain-unsat", Some(false), |s| {
        s.set_bve_enabled(true);
    });
}

// ===========================================================================
// Subsumption edge cases
//
// Forward subsumption removes clauses subsumed by existing clauses.
// Backward subsumption removes clauses subsumed by newly learned clauses.
// Bugs: removing the wrong clause, or self-subsumption corruption.
// ===========================================================================

/// Subsumption with exact subset relationship.
#[test]
fn subsume_exact_subset_sat() {
    // (x0) subsumes (x0 v x1) and (x0 v x2 v x3)
    let clauses = vec![
        vec![pos(0)],
        vec![pos(0), pos(1)],
        vec![pos(0), pos(2), pos(3)],
        vec![neg(1), pos(2)],
    ];
    solve_single_feature(4, &clauses, "subsume-subset-sat", Some(true), |s| {
        s.set_subsume_enabled(true);
    });
}

/// Self-subsuming resolution: (x0 v x1) and (-x0 v x1) implies (x1).
/// After strengthening, the formula must remain correct.
#[test]
fn subsume_self_subsuming_resolution_sat() {
    let clauses = vec![vec![pos(0), pos(1)], vec![neg(0), pos(1)], vec![pos(2)]];
    let r = solve_single_feature(3, &clauses, "subsume-ssr-sat", Some(true), |s| {
        s.set_subsume_enabled(true);
    });
    if let SatResult::Sat(model) = &r {
        // x1 must be true (implied by the two clauses)
        assert!(
            model.get(1).copied().unwrap_or(false),
            "Self-subsuming resolution should force x1=true"
        );
    }
}

/// Subsumption must not remove a clause that is NOT subsumed.
#[test]
fn subsume_near_miss_sat() {
    // (x0 v x1) does NOT subsume (x0 v -x1 v x2) — x1 vs -x1
    let clauses = vec![
        vec![pos(0), pos(1)],
        vec![pos(0), neg(1), pos(2)],
        vec![neg(0), neg(2)],
    ];
    solve_single_feature(3, &clauses, "subsume-near-miss", Some(true), |s| {
        s.set_subsume_enabled(true);
    });
}

/// Subsumption chain: unit clause subsumes binary subsumes ternary.
#[test]
fn subsume_chain_unsat() {
    // (x0), (-x0 v x1), (-x1) — UNSAT
    // (x0) subsumes (x0 v anything), but the chain matters for propagation
    let clauses = vec![vec![pos(0)], vec![neg(0), pos(1)], vec![neg(1)]];
    solve_single_feature_with_drat(2, &clauses, "subsume-chain-unsat", Some(false), |s| {
        s.set_subsume_enabled(true);
    });
}

// ===========================================================================
// Vivification edge cases
//
// Vivification strengthens clauses by attempting unit propagation on the
// negation of each literal. If a conflict is found, the clause can be
// shortened. Bugs: shortening a clause incorrectly, or losing literals.
// ===========================================================================

/// Vivification on a clause where one literal is implied by unit propagation.
#[test]
fn vivify_redundant_literal_sat() {
    // x0=T is forced. (x0 v x1 v x2) can be vivified since x0 is always true.
    let clauses = vec![
        vec![pos(0)],
        vec![pos(0), pos(1), pos(2)],
        vec![neg(1), pos(2)],
    ];
    solve_single_feature(3, &clauses, "vivify-redundant-lit", Some(true), |s| {
        s.set_vivify_enabled(true);
    });
}

/// Vivification must not shorten a clause below its actual implication.
#[test]
fn vivify_must_preserve_satisfiability_sat() {
    let n = 8u32;
    let mut clauses = Vec::new();
    // Create a satisfiable formula with long clauses
    for i in 0..(n - 1) {
        clauses.push(vec![pos(i), pos(i + 1)]);
        clauses.push(vec![neg(i), pos(i + 1)]);
    }
    clauses.push(vec![pos(n - 1)]);
    solve_single_feature(
        n as usize,
        &clauses,
        "vivify-preserve-sat",
        Some(true),
        |s| {
            s.set_vivify_enabled(true);
        },
    );
}

/// Vivification on UNSAT formula with DRAT proof.
#[test]
fn vivify_unsat_with_drat() {
    // PHP(3,2) — always UNSAT
    let clauses = vec![
        vec![pos(0), pos(1)], // pigeon 1 in hole 1 or 2
        vec![pos(2), pos(3)], // pigeon 2 in hole 1 or 2
        vec![pos(4), pos(5)], // pigeon 3 in hole 1 or 2
        vec![neg(0), neg(2)], // not both pigeons 1,2 in hole 1
        vec![neg(0), neg(4)], // not both pigeons 1,3 in hole 1
        vec![neg(2), neg(4)], // not both pigeons 2,3 in hole 1
        vec![neg(1), neg(3)], // not both pigeons 1,2 in hole 2
        vec![neg(1), neg(5)], // not both pigeons 1,3 in hole 2
        vec![neg(3), neg(5)], // not both pigeons 2,3 in hole 2
    ];
    solve_single_feature_with_drat(6, &clauses, "vivify-php32-drat", Some(false), |s| {
        s.set_vivify_enabled(true);
    });
}

// ===========================================================================
// BCE (Blocked Clause Elimination) edge cases
//
// A clause C is blocked on literal l if every resolvent of C with clauses
// containing -l is a tautology. BCE removes blocked clauses.
// Bug: removing a clause that is not actually blocked.
// ===========================================================================

/// BCE on a formula with a genuinely blocked clause.
#[test]
fn bce_blocked_clause_sat() {
    // (x0 v x1) is blocked on x0 if every clause with -x0 resolves
    // to a tautology. (-x0 v x1) resolves with (x0 v x1) to (x1 v x1) = (x1).
    // Not tautological, so (x0 v x1) is NOT blocked on x0.
    // But (x0 v x1 v x2) is blocked on x0 if (-x0 v -x1 v -x2) is the only
    // clause with -x0, since resolvent is (x1 v x2 v -x1 v -x2) = tautology.
    let clauses = vec![
        vec![pos(0), pos(1), pos(2)],
        vec![neg(0), neg(1), neg(2)],
        vec![pos(3)],
    ];
    solve_single_feature(4, &clauses, "bce-blocked-sat", Some(true), |s| {
        s.set_bce_enabled(true);
    });
}

/// BCE must not remove a non-blocked clause.
#[test]
fn bce_non_blocked_must_stay_unsat() {
    // Simple contradiction: (x0) and (-x0) — neither is blocked
    let clauses = vec![vec![pos(0)], vec![neg(0)]];
    solve_single_feature_with_drat(1, &clauses, "bce-non-blocked-unsat", Some(false), |s| {
        s.set_bce_enabled(true);
    });
}

// ===========================================================================
// Probe (failed literal probing) edge cases
//
// Probing tests assigning a literal and propagating. If a conflict occurs,
// the literal is a failed literal and the opposite is implied. Bugs:
// incorrect propagation during probing, or wrong literal implication.
// ===========================================================================

/// Probing discovers an implied unit.
#[test]
fn probe_failed_literal_sat() {
    // If x0=T leads to conflict, then x0=F is implied.
    // (-x0 v x1), (-x0 v -x1) — x0=T => x1=T and x1=F => conflict
    // But also need (x0 v x2) to keep formula SAT when x0=F
    let clauses = vec![
        vec![neg(0), pos(1)],
        vec![neg(0), neg(1)],
        vec![pos(0), pos(2)],
    ];
    let r = solve_single_feature(3, &clauses, "probe-failed-lit-sat", Some(true), |s| {
        s.set_probe_enabled(true);
    });
    if let SatResult::Sat(model) = &r {
        // x0 must be false (failed literal)
        assert!(
            !model.first().copied().unwrap_or(true),
            "probe should discover x0 is a failed literal"
        );
    }
}

/// Probing on UNSAT formula.
#[test]
fn probe_unsat_with_drat() {
    // Both x0=T and x0=F lead to conflict
    let clauses = vec![
        vec![neg(0), pos(1)],
        vec![neg(0), neg(1)],
        vec![pos(0), pos(2)],
        vec![pos(0), neg(2)],
    ];
    solve_single_feature_with_drat(3, &clauses, "probe-unsat-drat", Some(false), |s| {
        s.set_probe_enabled(true);
    });
}

// ===========================================================================
// Transitive reduction edge cases
//
// Transitive reduction removes redundant binary implications from the
// implication graph. Bug: removing a non-redundant implication.
// ===========================================================================

/// Transitive reduction on a chain: x0=>x1=>x2 with redundant x0=>x2.
#[test]
fn transred_removes_redundant_sat() {
    let clauses = vec![
        vec![neg(0), pos(1)], // x0 => x1
        vec![neg(1), pos(2)], // x1 => x2
        vec![neg(0), pos(2)], // x0 => x2 (redundant, transitive)
        vec![pos(3)],         // force SAT
    ];
    solve_single_feature(4, &clauses, "transred-redundant-sat", Some(true), |s| {
        s.set_transred_enabled(true);
    });
}

/// Transitive reduction must not break a non-redundant implication.
#[test]
fn transred_non_redundant_unsat() {
    // x0 => x1, x0 => -x1 with forced x0
    let clauses = vec![vec![neg(0), pos(1)], vec![neg(0), neg(1)], vec![pos(0)]];
    solve_single_feature_with_drat(2, &clauses, "transred-nonred-unsat", Some(false), |s| {
        s.set_transred_enabled(true);
    });
}
