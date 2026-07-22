// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for SAT sweeping (kitten-based equivalence detection).

use super::*;
use crate::test_util::lit;

#[test]
fn kitten_sweep_backbone_detects_forced_literal() {
    // (x0 ∨ x1 ∨ x2) ∧ (x0 ∨ x1 ∨ ¬x2) ∧ (x0 ∨ ¬x1 ∨ x2) ∧ (x0 ∨ ¬x1 ∨ ¬x2)
    // → x0 is a backbone literal (forced true in all satisfying assignments).
    // Backbone probing with incremental kitten should detect this.
    let mut clauses = ClauseArena::new();
    clauses.add(&[lit(0, true), lit(1, true), lit(2, true)], false);
    clauses.add(&[lit(0, true), lit(1, true), lit(2, false)], false);
    clauses.add(&[lit(0, true), lit(1, false), lit(2, true)], false);
    clauses.add(&[lit(0, true), lit(1, false), lit(2, false)], false);

    let vals = vec![0i8; 6]; // all unassigned
    let frozen: Vec<u32> = vec![0; 3];
    let mut sweeper = Sweeper::new(3);
    let outcome = sweeper.sweep_with_kitten(&clauses, &vals, &frozen, u64::MAX);
    assert!(!outcome.unsat);
    // x0 (positive) should be detected as backbone.
    assert!(
        outcome.new_units.iter().any(|u| u.0 == 0), // lit index 0 = x0 positive
        "Backbone probing should detect x0 as forced literal, got: {:?}",
        outcome.new_units
    );
}

#[test]
fn kitten_sweep_detects_unsat_neighborhood() {
    // Unsatisfiable clause set: (x) ∧ (¬x)
    let mut clauses = ClauseArena::new();
    clauses.add(&[lit(0, true)], false);
    clauses.add(&[lit(0, false)], false);

    let vals = vec![0i8; 2];
    let frozen: Vec<u32> = vec![0; 1];
    let mut sweeper = Sweeper::new(1);
    let outcome = sweeper.sweep_with_kitten(&clauses, &vals, &frozen, u64::MAX);
    assert!(outcome.unsat);
}

#[test]
fn kitten_sweep_equivalence_from_ternary() {
    // x0 ↔ x1 implied by ternary clauses (not binary):
    // (x0 ∨ ¬x1 ∨ x2) ∧ (x0 ∨ ¬x1 ∨ ¬x2) → (x0 ∨ ¬x1) by resolution
    // (¬x0 ∨ x1 ∨ x2) ∧ (¬x0 ∨ x1 ∨ ¬x2) → (¬x0 ∨ x1) by resolution
    // So x0 ↔ x1, but this requires resolving through x2 which SCC can't do.
    let mut clauses = ClauseArena::new();
    clauses.add(&[lit(0, true), lit(1, false), lit(2, true)], false);
    clauses.add(&[lit(0, true), lit(1, false), lit(2, false)], false);
    clauses.add(&[lit(0, false), lit(1, true), lit(2, true)], false);
    clauses.add(&[lit(0, false), lit(1, true), lit(2, false)], false);

    let vals = vec![0i8; 6];
    let frozen: Vec<u32> = vec![0; 3];
    let mut sweeper = Sweeper::new(3);
    let outcome = sweeper.sweep_with_kitten(&clauses, &vals, &frozen, u64::MAX);
    assert!(!outcome.unsat);

    // Should find x0 ≡ x1.
    let stats = sweeper.stats();
    assert!(
        stats.kitten_equivalences > 0 || !outcome.lit_map.is_empty(),
        "Expected kitten to find ternary-implied equivalence x0 ≡ x1"
    );
}

#[test]
fn kitten_sweep_rejects_asymmetric_implication_as_equivalence() {
    // This formula forbids only (¬x0 ∧ x1): it encodes x1 -> x0, not x0 ↔ x1.
    // A buggy incremental kitten can turn the two opposite probes into a
    // false equivalence by leaking state from the UNSAT branch into the SAT
    // branch. Sweep must not report any equivalence here.
    let mut clauses = ClauseArena::new();
    clauses.add(&[lit(0, true), lit(2, true)], false);
    clauses.add(&[lit(1, false), lit(2, true)], false);
    clauses.add(&[lit(0, true), lit(1, false), lit(2, false)], false);
    clauses.add(&[lit(0, false), lit(1, true), lit(2, false)], false);

    let vals = vec![0i8; 6];
    let frozen: Vec<u32> = vec![0; 3];
    let mut sweeper = Sweeper::new(3);
    let outcome = sweeper.sweep_with_kitten(&clauses, &vals, &frozen, u64::MAX);

    assert!(!outcome.unsat, "formula should remain SAT");
    assert_eq!(
        sweeper.stats().kitten_equivalences,
        0,
        "sweep must not report x0 and x1 equivalent when only x1 -> x0 holds"
    );
    assert!(
        outcome.lit_map.is_empty(),
        "no sweep substitution should be produced for asymmetric implication"
    );
}

#[test]
fn kitten_lit_map_preserves_negation_invariant_for_equivalence_chain() {
    let mut sweeper = Sweeper::new(3);
    let lit_map = sweeper.build_lit_map_from_equivalences(&[(0, 2), (2, 4)], &[], 6);

    assert_eq!(lit_map.len(), 6);
    for i in (0..lit_map.len()).step_by(2) {
        let pos = lit_map[i].index();
        let neg = lit_map[i + 1].index();
        assert_eq!(
            pos ^ 1,
            neg,
            "negation invariant broken after equivalence chaining for var {}: {:?}",
            i / 2,
            lit_map
        );
    }
}

#[test]
#[cfg(debug_assertions)]
fn debug_verify_rejects_false_positive() {
    // XOR encodes x0 <-> !x1, so x0 <-> x1 is false and must be rejected.
    let mut clauses = ClauseArena::new();
    clauses.add(&[lit(0, true), lit(1, true)], false);
    clauses.add(&[lit(0, false), lit(1, false)], false);

    let vals = vec![0i8; 4];
    let sweeper = Sweeper::new(2);
    assert!(
        !sweeper.debug_verify_equivalence_claim(0, 2, &clauses, &vals),
        "debug_verify must reject bogus x0 <-> x1 claim"
    );
}

#[test]
#[cfg(debug_assertions)]
fn debug_verify_accepts_true_equivalence() {
    // XOR makes x0 <-> !x1 true, so x0 <-> !x1 (lit 0 <-> lit 3) should pass.
    let mut clauses = ClauseArena::new();
    clauses.add(&[lit(0, true), lit(1, true)], false);
    clauses.add(&[lit(0, false), lit(1, false)], false);

    let vals = vec![0i8; 4];
    let sweeper = Sweeper::new(2);
    assert!(
        sweeper.debug_verify_equivalence_claim(0, 3, &clauses, &vals),
        "debug_verify must accept true x0 <-> !x1 claim"
    );
}

#[test]
fn kitten_sweep_detects_negated_equivalence() {
    // XOR encodes x0 <-> !x1. Sweep must probe signed candidates in the
    // same partition, otherwise it will never try the mixed-polarity pair.
    let mut clauses = ClauseArena::new();
    clauses.add(&[lit(0, true), lit(1, true)], false);
    clauses.add(&[lit(0, false), lit(1, false)], false);

    let vals = vec![0i8; 4];
    let frozen: Vec<u32> = vec![0; 2];
    let mut sweeper = Sweeper::new(2);
    let outcome = sweeper.sweep_with_kitten(&clauses, &vals, &frozen, u64::MAX);

    assert!(!outcome.unsat, "formula should remain SAT");
    assert!(
        !outcome.lit_map.is_empty(),
        "sweep should detect x0 <-> !x1 and build a substitution map"
    );
    assert_eq!(
        outcome.lit_map[0].index(),
        outcome.lit_map[3].index(),
        "x0 and !x1 should share a representative after sweeping"
    );
    assert_eq!(
        outcome.lit_map[1].index(),
        outcome.lit_map[2].index(),
        "!x0 and x1 should share a representative after sweeping"
    );
    assert_ne!(
        outcome.lit_map[0].index(),
        outcome.lit_map[2].index(),
        "the negated equivalence should preserve opposite-polarity representatives"
    );
}

// ── Regression tests for kitten probe correctness (#8530, #8538) ───

/// Regression test for #8538: stress test with many COI variables.
///
/// Builds a formula with several equivalence classes and verifies that
/// sweep correctly identifies all of them without producing false
/// equivalences. This exercises the incremental kitten path with many
/// variables, which is where QF_ABV stress benchmarks triggered false
/// equivalence claims.
#[test]
fn kitten_sweep_stress_no_false_equivalences_8538() {
    let mut clauses = ClauseArena::new();

    // Class 1: x0 <-> x1 via ternary clauses (through x6).
    clauses.add(&[lit(0, true), lit(1, false), lit(6, true)], false);
    clauses.add(&[lit(0, true), lit(1, false), lit(6, false)], false);
    clauses.add(&[lit(0, false), lit(1, true), lit(6, true)], false);
    clauses.add(&[lit(0, false), lit(1, true), lit(6, false)], false);

    // Class 2: x2 <-> x3 via ternary clauses (through x7).
    clauses.add(&[lit(2, true), lit(3, false), lit(7, true)], false);
    clauses.add(&[lit(2, true), lit(3, false), lit(7, false)], false);
    clauses.add(&[lit(2, false), lit(3, true), lit(7, true)], false);
    clauses.add(&[lit(2, false), lit(3, true), lit(7, false)], false);

    // x4 and x5 are independent — connected to the rest loosely.
    clauses.add(&[lit(4, true), lit(5, true), lit(0, true)], false);
    clauses.add(&[lit(4, false), lit(5, false), lit(2, true)], false);
    clauses.add(&[lit(4, true), lit(5, false), lit(6, true)], false);

    let num_vars = 8;
    let vals = vec![0i8; num_vars * 2];
    let frozen: Vec<u32> = vec![0; num_vars];
    let mut sweeper = Sweeper::new(num_vars);
    let outcome = sweeper.sweep_with_kitten(&clauses, &vals, &frozen, u64::MAX);

    assert!(!outcome.unsat, "formula should be SAT");

    // Check that any reported equivalences are actually correct.
    // The lit_map must satisfy: if lit_map[a] == lit_map[b], then a <-> b
    // must hold in the formula. We verify by checking that no cross-class
    // equivalences are reported (x0/x1 should not map to x2/x3).
    if !outcome.lit_map.is_empty() {
        let map = &outcome.lit_map;
        // x0 and x2 should NOT be equivalent (different classes).
        let x0_rep = map[0].index();
        let x2_rep = map[4].index();
        assert_ne!(
            x0_rep, x2_rep,
            "x0 and x2 should NOT be equivalent (different classes)"
        );
        // x1 and x3 should NOT be equivalent (different classes).
        let x1_rep = map[2].index();
        let x3_rep = map[6].index();
        assert_ne!(
            x1_rep, x3_rep,
            "x1 and x3 should NOT be equivalent (different classes)"
        );
    }
}

/// Regression test: verify that tight ticks budget does not cause
/// sweep to report false equivalences. With a tight budget, some
/// probes will hit the ticks limit and return Unknown. The sweep
/// must treat Unknown as "not equivalent" (conservative), not as
/// evidence of equivalence.
#[test]
fn kitten_sweep_tight_budget_no_false_equivalences() {
    let mut clauses = ClauseArena::new();

    // x0 -> x1 (but NOT x1 -> x0, so NOT equivalent).
    clauses.add(&[lit(0, false), lit(1, true)], false);
    // x1 is unconstrained otherwise.
    clauses.add(&[lit(1, true), lit(2, true)], false);
    clauses.add(&[lit(1, false), lit(2, false)], false);

    let num_vars = 3;
    let vals = vec![0i8; num_vars * 2];
    let frozen: Vec<u32> = vec![0; num_vars];
    let mut sweeper = Sweeper::new(num_vars);

    // Use very tight budget — may cause some probes to time out.
    let outcome = sweeper.sweep_with_kitten(&clauses, &vals, &frozen, 100);

    assert!(!outcome.unsat, "formula should be SAT");
    // x0 and x1 must NOT be reported equivalent (only one direction holds).
    let stats = sweeper.stats();
    if stats.kitten_equivalences > 0 {
        // If any equivalences were found, verify they don't include x0 <-> x1.
        if !outcome.lit_map.is_empty() {
            let x0_rep = outcome.lit_map[0].index();
            let x1_rep = outcome.lit_map[2].index();
            assert_ne!(
                x0_rep, x1_rep,
                "x0 and x1 must not be equivalent (only x0 -> x1 holds)"
            );
        }
    }
}

#[test]
fn kitten_partition_refinement_splits_sat_countermodel_class() {
    // Start with a polluted candidate class [x0, x1, x2], where x0 is
    // independent but x1 <-> x2 is real. A SAT countermodel for x0 vs x1
    // should split the class by model value and leave [x1, x2] to be proved.
    let mut clauses = ClauseArena::new();
    clauses.add(&[lit(1, false), lit(2, true)], false);
    clauses.add(&[lit(1, true), lit(2, false)], false);

    let vals = vec![0i8; 6];
    let mut sweeper = Sweeper::new(3);
    for idx in clauses.indices() {
        let ext_lits: Vec<u32> = clauses.literals(idx).iter().map(|lit| lit.0).collect();
        sweeper
            .kitten
            .add_clause_with_id(idx as u32, &ext_lits, u32::MAX);
    }
    sweeper.kitten.seal_original();
    assert_eq!(sweeper.randomized_kitten_solve(), 10);

    let mut equivalences = Vec::new();
    sweeper.probe_partition_classes(&clauses, &vals, &[0, 2, 4], &mut equivalences);

    assert_eq!(
        sweeper.stats().kitten_partition_refinements,
        1,
        "expected one SAT-countermodel partition split"
    );
    assert!(
        equivalences
            .iter()
            .any(|&(a, b)| (a, b) == (2, 4) || (a, b) == (4, 2)),
        "refinement should preserve and prove x1 <-> x2, got {equivalences:?}"
    );
}

// ── Random simulation tests (#6868) ────────────────────────────────

#[test]
fn simulation_finds_candidates_with_unit_propagation() {
    // Binary clauses force x0 ↔ x1 via unit propagation:
    //   (x0 ∨ ¬x1) — if x1=T then x0 must be T
    //   (¬x0 ∨ x1) — if x0=T then x1 must be T
    // Plus unrelated variables x2, x3 with different behavior:
    //   (x2 ∨ x3)    — weak coupling
    //   (¬x2 ∨ ¬x3)  — weak coupling
    //
    // Simulation: random x0 assignment propagates to force x1 to same value.
    // x2/x3 have anti-correlated signatures (complement).
    let mut clauses = ClauseArena::new();
    clauses.add(&[lit(0, true), lit(1, false)], false);
    clauses.add(&[lit(0, false), lit(1, true)], false);
    clauses.add(&[lit(2, true), lit(3, true)], false);
    clauses.add(&[lit(2, false), lit(3, false)], false);

    let vals = vec![0i8; 8];
    let frozen: Vec<u32> = vec![0; 4];
    let sweeper = Sweeper::new(4);
    let classes = sweeper.find_candidates_by_simulation(&clauses, &vals, &frozen);

    // x0 and x1 should be in the same equivalence class.
    let x0_class = classes.iter().find(|c| c.iter().any(|&l| l >> 1 == 0));
    let x1_in_class = x0_class
        .map(|c| c.iter().any(|&l| l >> 1 == 1))
        .unwrap_or(false);
    assert!(
        x1_in_class,
        "Simulation should group x0 and x1 as equivalence candidates, got: {classes:?}"
    );
}

#[test]
fn simulation_finds_negated_equivalence_via_propagation() {
    // XOR via binary clauses: (x0 ∨ x1) ∧ (¬x0 ∨ ¬x1)
    // Forces x0 ↔ ¬x1.
    //
    // If x0=T randomly: clause 2 has (F ∨ ¬x1), so ¬x1 must be T → x1=F.
    // If x0=F randomly: clause 1 has (F ∨ x1), so x1 must be T.
    // Result: x0 always opposite to x1. Signatures are complements.
    // Complement folding should group them.
    let mut clauses = ClauseArena::new();
    clauses.add(&[lit(0, true), lit(1, true)], false);
    clauses.add(&[lit(0, false), lit(1, false)], false);

    let vals = vec![0i8; 4];
    let frozen: Vec<u32> = vec![0; 2];
    let sweeper = Sweeper::new(2);
    let classes = sweeper.find_candidates_by_simulation(&clauses, &vals, &frozen);

    // x0 and x1 should be in the same class (via complement signature folding).
    assert!(
        !classes.is_empty(),
        "Simulation should find x0 ↔ ¬x1 candidates"
    );
    let has_both = classes.iter().any(|c| {
        let vars: Vec<u32> = c.iter().map(|&l| l >> 1).collect();
        vars.contains(&0) && vars.contains(&1)
    });
    assert!(
        has_both,
        "Simulation should group x0 and x1 in same class, got: {classes:?}"
    );
}

#[test]
fn simulation_skips_assigned_and_frozen_variables() {
    let mut clauses = ClauseArena::new();
    clauses.add(&[lit(0, true), lit(1, false), lit(2, true)], false);
    clauses.add(&[lit(0, true), lit(1, false), lit(2, false)], false);
    clauses.add(&[lit(0, false), lit(1, true), lit(2, true)], false);
    clauses.add(&[lit(0, false), lit(1, true), lit(2, false)], false);

    // x0 is assigned (positive).
    let mut vals = vec![0i8; 6];
    vals[0] = 1; // x0 positive is true
    vals[1] = -1; // x0 negative is false

    // x1 is frozen.
    let frozen: Vec<u32> = vec![0, 1, 0];

    let sweeper = Sweeper::new(3);
    let classes = sweeper.find_candidates_by_simulation(&clauses, &vals, &frozen);

    // Neither x0 nor x1 should appear in any class.
    for class in &classes {
        for &signed_lit in class {
            let var = signed_lit >> 1;
            assert_ne!(
                var, 0,
                "Assigned variable x0 should not appear in simulation candidates"
            );
            assert_ne!(
                var, 1,
                "Frozen variable x1 should not appear in simulation candidates"
            );
        }
    }
}

#[test]
fn simulation_returns_empty_on_no_clauses() {
    let clauses = ClauseArena::new();
    let vals: Vec<i8> = vec![0; 4];
    let frozen: Vec<u32> = vec![0; 2];
    let sweeper = Sweeper::new(2);
    let classes = sweeper.find_candidates_by_simulation(&clauses, &vals, &frozen);
    assert!(classes.is_empty(), "No clauses → no candidates");
}

#[test]
fn simulation_candidates_verified_by_kitten_on_ternary() {
    // Full integration: simulation finds candidates on ternary-only formula,
    // then kitten verifies them in sweep_with_kitten.
    // x0 ↔ x1 via ternary clauses:
    let mut clauses = ClauseArena::new();
    clauses.add(&[lit(0, true), lit(1, false), lit(2, true)], false);
    clauses.add(&[lit(0, true), lit(1, false), lit(2, false)], false);
    clauses.add(&[lit(0, false), lit(1, true), lit(2, true)], false);
    clauses.add(&[lit(0, false), lit(1, true), lit(2, false)], false);

    let vals = vec![0i8; 6];
    let frozen: Vec<u32> = vec![0; 3];
    let mut sweeper = Sweeper::new(3);
    let outcome = sweeper.sweep_with_kitten(&clauses, &vals, &frozen, u64::MAX);
    assert!(!outcome.unsat);

    // Either COI or simulation should find the equivalence.
    let stats = sweeper.stats();
    assert!(
        stats.kitten_equivalences > 0 || !outcome.lit_map.is_empty(),
        "Expected sweep to find ternary-implied equivalence x0 ≡ x1 \
         (kitten_equivs={}, sim_rounds={}, sim_candidates={})",
        stats.kitten_equivalences,
        stats.simulation_rounds,
        stats.simulation_candidates,
    );
}
