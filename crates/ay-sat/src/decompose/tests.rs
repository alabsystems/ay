// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::clause_arena::ClauseArena;
use crate::literal::Variable;
use crate::test_util::lit;
use crate::watched::{WatchedLists, Watcher};

fn build_watches(clauses: &ClauseArena, num_vars: usize) -> WatchedLists {
    let mut watches = WatchedLists::new(num_vars);
    for idx in clauses.indices() {
        if clauses.is_empty_clause(idx) || clauses.len_of(idx) < 2 {
            continue;
        }
        let lit0 = clauses.literal(idx, 0);
        let lit1 = clauses.literal(idx, 1);
        let cref = crate::watched::ClauseRef(idx as u32);
        watches.add_watch(lit0, Watcher::binary(cref, lit1));
        watches.add_watch(lit1, Watcher::binary(cref, lit0));
    }
    watches
}

fn implication_reachability(clauses: &ClauseArena, num_vars: usize) -> Vec<Vec<bool>> {
    let num_lits = num_vars * 2;
    let mut reach = vec![vec![false; num_lits]; num_lits];

    for (i, row) in reach.iter_mut().enumerate() {
        row[i] = true;
    }

    for idx in clauses.indices() {
        if clauses.is_empty_clause(idx) || clauses.len_of(idx) != 2 {
            continue;
        }

        let a = clauses.literal(idx, 0);
        let b = clauses.literal(idx, 1);

        // Binary clause (a ∨ b) induces implications ¬a -> b and ¬b -> a.
        reach[a.negated().index()][b.index()] = true;
        reach[b.negated().index()][a.index()] = true;
    }

    // Floyd-Warshall transitive closure.
    for k in 0..num_lits {
        let row_k = reach[k].clone();
        for reach_row in reach.iter_mut().take(num_lits) {
            if !reach_row[k] {
                continue;
            }
            for (j, reachable_from_k) in row_k.iter().copied().enumerate() {
                if reachable_from_k {
                    reach_row[j] = true;
                }
            }
        }
    }

    reach
}

fn next_seed(seed: &mut u64) -> u64 {
    *seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1);
    *seed
}

#[test]
fn test_simple_equivalence() {
    // x0 → x1 and x1 → x0 (x0 ≡ x1)
    // C0: (¬x0 ∨ x1) means x0 → x1
    // C1: (¬x1 ∨ x0) means x1 → x0
    let mut clauses = ClauseArena::new();
    clauses.add(&[lit(0, false), lit(1, true)], false); // ¬x0 ∨ x1
    clauses.add(&[lit(1, false), lit(0, true)], false); // ¬x1 ∨ x0

    let watches = build_watches(&clauses, 2);
    let vals = vec![0i8; 4]; // 2 vars, all unassigned
    let frozen = vec![0u32; 2];

    let mut decompose = Decompose::new(2);
    let var_states = vec![crate::solver::lifecycle::VarState::Active; 2];
    let result = decompose.run(&watches, 2, &vals, &frozen, &var_states, true);

    assert!(!result.unsat, "Should not be UNSAT");
    assert!(
        result.substituted > 0,
        "Should find equivalence: got {} substitutions",
        result.substituted
    );

    // x0 and x1 should map to the same representative (x0, the smaller variable).
    let repr0_pos = result.reprs[lit(0, true).index()];
    let repr1_pos = result.reprs[lit(1, true).index()];
    assert_eq!(
        repr0_pos,
        lit(0, true),
        "x0 should be its own representative"
    );
    assert_eq!(repr1_pos, lit(0, true), "x1 should map to x0");

    // Negation consistency.
    let repr1_neg = result.reprs[lit(1, false).index()];
    assert_eq!(repr1_neg, lit(0, false), "¬x1 should map to ¬x0");
}

#[test]
fn test_conflicting_scc() {
    // x0 → x1 → ¬x0 → ¬x1 → x0, so {x0,x1,¬x0,¬x1} are all in one SCC → UNSAT
    let mut clauses = ClauseArena::new();
    clauses.add(&[lit(0, false), lit(1, true)], false); // x0 → x1
    clauses.add(&[lit(1, false), lit(0, false)], false); // x1 → ¬x0
    clauses.add(&[lit(0, true), lit(1, false)], false); // ¬x0 → ¬x1
    clauses.add(&[lit(1, true), lit(0, true)], false); // ¬x1 → x0

    let watches = build_watches(&clauses, 2);
    let vals = vec![0i8; 4]; // 2 vars, all unassigned
    let frozen = vec![0u32; 2];

    let mut decompose = Decompose::new(2);
    let var_states = vec![crate::solver::lifecycle::VarState::Active; 2];
    let result = decompose.run(&watches, 2, &vals, &frozen, &var_states, true);

    assert!(result.unsat, "Should detect UNSAT from conflicting SCC");
}

#[test]
fn test_no_equivalence() {
    // x0 → x1 but NOT x1 → x0 (not equivalent)
    // C0: (¬x0 ∨ x1)
    let mut clauses = ClauseArena::new();
    clauses.add(&[lit(0, false), lit(1, true)], false);

    let watches = build_watches(&clauses, 2);
    let vals = vec![0i8; 4]; // 2 vars, all unassigned
    let frozen = vec![0u32; 2];

    let mut decompose = Decompose::new(2);
    let var_states = vec![crate::solver::lifecycle::VarState::Active; 2];
    let result = decompose.run(&watches, 2, &vals, &frozen, &var_states, true);

    assert!(!result.unsat);
    assert_eq!(result.substituted, 0, "Should find no equivalences");
}

#[test]
fn test_transitive_chain_equivalence() {
    // x0 ≡ x1, x1 ≡ x2 → all three equivalent
    let mut clauses = ClauseArena::new();
    clauses.add(&[lit(0, false), lit(1, true)], false);
    clauses.add(&[lit(1, false), lit(0, true)], false);
    clauses.add(&[lit(1, false), lit(2, true)], false);
    clauses.add(&[lit(2, false), lit(1, true)], false);

    let watches = build_watches(&clauses, 3);
    let vals = vec![0i8; 6]; // 3 vars, all unassigned
    let frozen = vec![0u32; 3];

    let mut decompose = Decompose::new(3);
    let var_states = vec![crate::solver::lifecycle::VarState::Active; 3];
    let result = decompose.run(&watches, 3, &vals, &frozen, &var_states, true);

    assert!(!result.unsat);
    // All should map to x0 (smallest variable).
    let repr0 = result.reprs[lit(0, true).index()];
    let repr1 = result.reprs[lit(1, true).index()];
    let repr2 = result.reprs[lit(2, true).index()];
    assert_eq!(repr0, lit(0, true));
    assert_eq!(repr1, lit(0, true), "x1 should map to x0");
    assert_eq!(repr2, lit(0, true), "x2 should map to x0");
}

#[test]
fn test_frozen_variable_stays_representative() {
    // x0 ≡ x1, but x1 is frozen → x1 should be the representative
    let mut clauses = ClauseArena::new();
    clauses.add(&[lit(0, false), lit(1, true)], false);
    clauses.add(&[lit(1, false), lit(0, true)], false);

    let watches = build_watches(&clauses, 2);
    let vals = vec![0i8; 4]; // 2 vars, all unassigned
    let frozen = vec![0u32, 1]; // x1 is frozen

    let mut decompose = Decompose::new(2);
    let var_states = vec![crate::solver::lifecycle::VarState::Active; 2];
    let result = decompose.run(&watches, 2, &vals, &frozen, &var_states, true);

    assert!(!result.unsat);
    // x1 is frozen, so it should be the representative.
    let repr0 = result.reprs[lit(0, true).index()];
    let repr1 = result.reprs[lit(1, true).index()];
    assert_eq!(
        repr1,
        lit(1, true),
        "frozen x1 should be its own representative"
    );
    assert_eq!(repr0, lit(1, true), "x0 should map to frozen x1");
}

#[test]
fn test_two_frozen_variables_in_scc_remain_self_represented() {
    // x0 ≡ x1 ≡ x2 and x1/x2 are frozen.
    let mut clauses = ClauseArena::new();
    clauses.add(&[lit(0, false), lit(1, true)], false);
    clauses.add(&[lit(1, false), lit(0, true)], false);
    clauses.add(&[lit(1, false), lit(2, true)], false);
    clauses.add(&[lit(2, false), lit(1, true)], false);

    let watches = build_watches(&clauses, 3);
    let vals = vec![0i8; 6]; // 3 vars, all unassigned
    let frozen = vec![0u32, 1u32, 1u32];

    let mut decompose = Decompose::new(3);
    let var_states = vec![crate::solver::lifecycle::VarState::Active; 3];
    let result = decompose.run(&watches, 3, &vals, &frozen, &var_states, true);

    assert!(!result.unsat);
    assert_eq!(
        result.reprs[lit(1, true).index()],
        lit(1, true),
        "frozen x1 must remain self-represented"
    );
    assert_eq!(
        result.reprs[lit(1, false).index()],
        lit(1, false),
        "frozen ¬x1 must remain self-represented"
    );
    assert_eq!(
        result.reprs[lit(2, true).index()],
        lit(2, true),
        "frozen x2 must remain self-represented"
    );
    assert_eq!(
        result.reprs[lit(2, false).index()],
        lit(2, false),
        "frozen ¬x2 must remain self-represented"
    );
}

#[test]
fn test_clause_rewriting() {
    // x0 ≡ x1 (via SCC). Clause C: (x1 ∨ x2) → should become (x0 ∨ x2)
    let mut clauses = ClauseArena::new();
    clauses.add(&[lit(0, false), lit(1, true)], false); // C0: equivalence
    clauses.add(&[lit(1, false), lit(0, true)], false); // C1: equivalence
    clauses.add(&[lit(1, true), lit(2, true)], false); // C2: x1 ∨ x2

    let watches = build_watches(&clauses, 3);
    let vals = vec![0i8; 6]; // 3 vars, all unassigned
    let frozen = vec![0u32; 3];

    let mut decompose = Decompose::new(3);
    let var_states = vec![crate::solver::lifecycle::VarState::Active; 3];
    let scc_result = decompose.run(&watches, 3, &vals, &frozen, &var_states, true);

    assert!(!scc_result.unsat);
    assert!(scc_result.substituted > 0);

    let vals = vec![0i8; 6]; // all unassigned
    let rewrite_result = rewrite_clauses(&clauses, &scc_result.reprs, &vals);

    // C2 should have been rewritten. Check that x1 was replaced by x0.
    // (C0 and C1 become tautologies: ¬x0∨x0 → deleted)
    assert!(
        rewrite_result.removed >= 2,
        "Equivalence clauses should be removed as tautologies, got {} removed",
        rewrite_result.removed
    );
}

#[test]
fn test_rewrite_removes_duplicates() {
    // If substitution produces (x0 ∨ x0 ∨ x2), it should become (x0 ∨ x2)
    let mut clauses = ClauseArena::new();
    // Equivalence: x0 ≡ x1
    clauses.add(&[lit(0, false), lit(1, true)], false);
    clauses.add(&[lit(1, false), lit(0, true)], false);
    // Clause with both x0 and x1 → after substitution both become x0 → duplicate removal
    clauses.add(&[lit(0, true), lit(1, true), lit(2, true)], false);

    let watches = build_watches(&clauses, 3);
    let vals = vec![0i8; 6]; // 3 vars, all unassigned
    let frozen = vec![0u32; 3];

    let mut decompose = Decompose::new(3);
    let var_states = vec![crate::solver::lifecycle::VarState::Active; 3];
    let scc_result = decompose.run(&watches, 3, &vals, &frozen, &var_states, true);

    let vals = vec![0i8; 6];
    let rewrite_result = rewrite_clauses(&clauses, &scc_result.reprs, &vals);

    // The ternary clause should have been shortened (x0∨x0∨x2 → x0∨x2).
    assert!(
        rewrite_result.shortened > 0 || rewrite_result.new_binary,
        "Should detect duplicate after substitution"
    );
}

#[test]
fn test_tarjan_matches_naive_scc_on_random_binary_formulas() {
    const NUM_VARS: usize = 3;
    const NUM_LITS: usize = NUM_VARS * 2;

    let vals = vec![0i8; NUM_LITS]; // all unassigned
    let frozen = vec![0u32; NUM_VARS];
    let mut seed = 0x9E3779B97F4A7C15u64;

    for case_idx in 0..64usize {
        let mut clauses = ClauseArena::new();

        // Dense randomized binary clause set to stress SCC traversal order.
        for _ in 0..18 {
            let a = (next_seed(&mut seed) % NUM_LITS as u64) as u32;
            let b = (next_seed(&mut seed) % NUM_LITS as u64) as u32;
            if a == b {
                continue;
            }
            clauses.add(&[Literal(a), Literal(b)], false);
        }

        // Ensure shared-child/cross-edge shape appears in every case.
        clauses.add(&[lit(0, false), lit(2, true)], false); // x0 -> x2
        clauses.add(&[lit(1, false), lit(2, true)], false); // x1 -> x2
        clauses.add(&[lit(2, false), lit(0, true)], false); // x2 -> x0

        let reach = implication_reachability(&clauses, NUM_VARS);
        let watches = build_watches(&clauses, NUM_VARS);

        let mut expected_unsat = false;
        for var in 0..NUM_VARS {
            let pos = Literal::positive(Variable(var as u32)).index();
            let neg = Literal::negative(Variable(var as u32)).index();
            if reach[pos][neg] && reach[neg][pos] {
                expected_unsat = true;
                break;
            }
        }

        let mut decompose = Decompose::new(NUM_VARS);
        let var_states = vec![crate::solver::lifecycle::VarState::Active; NUM_VARS];
        let result = decompose.run(&watches, NUM_VARS, &vals, &frozen, &var_states, true);

        assert_eq!(
            result.unsat, expected_unsat,
            "case {case_idx}: UNSAT mismatch between Tarjan and reachability oracle"
        );

        if result.unsat {
            continue;
        }

        for (i, reach_i) in reach.iter().enumerate().take(NUM_LITS) {
            for (j, _) in reach_i.iter().enumerate().take(NUM_LITS) {
                let same_scc = reach[i][j] && reach[j][i];
                let same_repr = result.reprs[i] == result.reprs[j];
                assert_eq!(
                    same_repr, same_scc,
                    "case {case_idx}: repr mismatch for literals {i} and {j}"
                );
            }
        }
    }
}

/// Regression test for #4349: proof_log carries valid clause_idx for LRAT lookup.
#[test]
fn test_rewrite_proof_log_carries_clause_idx() {
    let mut clauses = ClauseArena::new();
    let c0 = clauses.add(&[lit(0, false), lit(1, true)], false); // x0≡x1 equiv
    let c1 = clauses.add(&[lit(1, false), lit(0, true)], false); // x0≡x1 equiv
    let c2 = clauses.add(&[lit(1, true), lit(2, true)], false); // x1 ∨ x2

    let watches = build_watches(&clauses, 3);
    let vals = vec![0i8; 6]; // 3 vars, all unassigned
    let frozen = vec![0u32; 3];
    let mut decompose = Decompose::new(3);
    let var_states = vec![crate::solver::lifecycle::VarState::Active; 3];
    let scc = decompose.run(&watches, 3, &vals, &frozen, &var_states, true);
    assert!(!scc.unsat);
    assert!(scc.substituted > 0);

    let vals = vec![0i8; 6];
    let rw = rewrite_clauses(&clauses, &scc.reprs, &vals);

    assert!(!rw.actions.is_empty(), "actions should record mutations");

    // Helper: extract clause_idx from any mutation variant.
    let idx_of = |m: &ClauseMutation| match m {
        ClauseMutation::Deleted { clause_idx, .. }
        | ClauseMutation::Replaced { clause_idx, .. }
        | ClauseMutation::Unit { clause_idx, .. } => *clause_idx,
    };

    // Every clause_idx must be in range.
    let max_idx = c2 + 1;
    for m in &rw.actions {
        assert!(idx_of(m) < max_idx, "clause_idx {} out of range", idx_of(m));
    }

    // 2 Deleted (tautological equiv clauses) + 1 Replaced (rewritten clause).
    let n_del = rw
        .actions
        .iter()
        .filter(|m| matches!(m, ClauseMutation::Deleted { .. }))
        .count();
    let n_rep = rw
        .actions
        .iter()
        .filter(|m| matches!(m, ClauseMutation::Replaced { .. }))
        .count();
    assert_eq!(n_del, 2, "two equiv clauses should be deleted");
    assert_eq!(n_rep, 1, "one clause should be replaced");

    // Replaced mutation references c2, rewritten to 2 lits (x0,x2).
    let rep = rw
        .actions
        .iter()
        .find(|m| matches!(m, ClauseMutation::Replaced { .. }))
        .expect("invariant: one replaced mutation");
    let ClauseMutation::Replaced {
        clause_idx, new, ..
    } = rep
    else {
        unreachable!("find() guaranteed Replaced variant");
    };
    assert_eq!(*clause_idx, c2, "replaced should reference c2");
    assert_eq!(new.len(), 2, "replaced clause should have 2 lits");

    // Deleted mutations reference c0 and c1. Reuse idx_of helper.
    let del_idxs: Vec<usize> = rw
        .actions
        .iter()
        .filter(|m| matches!(m, ClauseMutation::Deleted { .. }))
        .map(idx_of)
        .collect();
    assert!(
        del_idxs.contains(&c0) && del_idxs.contains(&c1),
        "deleted should reference c0={c0} and c1={c1}, got {del_idxs:?}"
    );
}
