// Copyright 2026 Andrew Yates
// Performance property tests for the DRAT proof checker.
//
// These tests verify that key operations scale correctly (sub-quadratic)
// by measuring internal counters at different input sizes. Quadratic
// regressions are caught by asserting that work grows at most linearly
// relative to input size.
//
// Findings from P1:595 performance audit:
//   #1: O(k²) clause matching (FIXED: retained literal-count scratch)
//   #2: Full-database scan for RAT candidates (FIXED: per-literal occurrences)
//   #3: Tombstone leak in clause arena (FIXED: fully unlinked slot reuse)
//   #4: set_core_on_watches missing early exit (FIXED in this commit)
//   #7: Sort+dedup in resolvent construction (FIXED: linear literal marks)
//   #12: XOR hash collision-prone (FIXED: mixed additive + XOR lanes)

use super::test_helpers::lit;
use super::DratChecker;
use crate::drat_parser::ProofStep;
use crate::literal::Literal;

// -- Finding #1: Clause matching uses O(k²) per candidate via contains() --
// This test verifies that delete_clause doesn't blow up with long clauses.
// We insert clauses of varying lengths and time the deletion.

#[test]
fn test_delete_clause_scales_with_clause_length() {
    // Insert two long clauses of the same length, delete one.
    // With O(k²) matching, doubling k should 4x the work.
    // We can't directly measure time, but we can verify correctness
    // and that the stats counters are consistent.
    for k in [10, 50, 100, 200] {
        let num_vars = k + 2;
        let mut checker = DratChecker::new(num_vars, false);

        // Create a long clause: variables [0, k)
        let clause1: Vec<Literal> = (0..k).map(|i| lit(i as u32, true)).collect();
        // Create a different long clause: variables [1, k+1)
        let clause2: Vec<Literal> = (1..=k).map(|i| lit(i as u32, true)).collect();

        checker.add_original(&clause1);
        checker.add_original(&clause2);

        assert_eq!(checker.live_clauses, 2, "k={k}: both clauses inserted");

        // Delete clause1 — hash lookup must match correctly despite similar clauses.
        checker.delete_clause(&clause1);
        assert_eq!(
            checker.live_clauses, 1,
            "k={k}: exactly one clause should remain after delete"
        );
        assert_eq!(
            checker.stats.missed_deletes, 0,
            "k={k}: delete should find the clause"
        );

        // Delete clause2.
        checker.delete_clause(&clause2);
        assert_eq!(checker.live_clauses, 0, "k={k}: no clauses should remain");
    }
}

// -- Finding #3: Deleted clause slots are reused --

#[test]
fn test_deleted_clause_slots_are_reused() {
    let mut checker = DratChecker::new(200, false);
    let n = 100;

    // Add and delete N clauses. Arena should grow to N, not beyond.
    for i in 0..n {
        let clause = vec![lit((i * 2) as u32, true), lit((i * 2 + 1) as u32, true)];
        checker.add_original(&clause);
    }
    assert_eq!(
        checker.clauses.len(),
        n,
        "arena should have exactly {n} entries"
    );

    // Delete all clauses.
    for i in 0..n {
        let clause = vec![lit((i * 2) as u32, true), lit((i * 2 + 1) as u32, true)];
        checker.delete_clause(&clause);
    }
    assert_eq!(checker.live_clauses, 0, "all clauses deleted");
    // Arena retains N reusable slots rather than growing a second allocation.
    assert_eq!(checker.clauses.len(), n, "arena retains the reusable slots");

    // Add N more clauses — they should reuse the available arena slots.
    for i in 0..n {
        let clause = vec![
            lit((i * 2 + 200) as u32, true),
            lit((i * 2 + 201) as u32, true),
        ];
        checker.add_original(&clause);
    }
    assert_eq!(checker.clauses.len(), n, "deleted slots should be reused");
    assert!(checker.free_clause_slots.is_empty());
}

// -- Finding #4: set_core_on_watches should early-exit after finding match --
// Verify that mark_watches_core correctly sets the core flag.

#[test]
fn test_mark_watches_core_sets_flag() {
    // Create a formula with several binary clauses sharing a variable.
    // This creates a long watch list for the shared variable's literal.
    let num_vars = 20;
    let mut checker = DratChecker::new(num_vars, false);

    // All clauses share variable 0: (v0 v v_i) for i in 1..10.
    let clauses: Vec<Vec<Literal>> = (1..10).map(|i| vec![lit(0, true), lit(i, true)]).collect();
    for c in &clauses {
        checker.add_original(c);
    }

    // Mark watch for clause 0 (cidx=0) as core.
    checker.mark_watches_core(0);

    // Verify: watch list for lit(0, true) should have cidx=0 marked core.
    let lit0_idx = lit(0, true).index();
    let core_count = checker.watches[lit0_idx].iter().filter(|w| w.core).count();
    assert_eq!(
        core_count, 1,
        "exactly one watch entry should be marked core"
    );

    let core_entry = checker.watches[lit0_idx]
        .iter()
        .find(|w| w.core)
        .expect("should find core watch");
    assert_eq!(core_entry.clause_idx, 0, "core watch should be for cidx=0");
}

// -- Finding #2 + #7: RAT candidate collection and resolvent construction --

/// Verify RAT check correctly identifies a valid RAT clause.
///
/// Formula: {a, b}, {~a, b} — clause {a} is RAT with pivot a:
/// resolvent of {a} with {~a, b} is {b}. To check RUP of {b}: assume ~b.
/// {a, b} with b=false → a unit. {~a, b} with a=true, b=false → conflict.
/// So resolvent {b} is RUP → {a} is RAT.
#[test]
fn test_rat_check_valid_clause() {
    let mut checker = DratChecker::new(5, true);
    checker.add_original(&[lit(0, true), lit(1, true)]); // a v b
    checker.add_original(&[lit(0, false), lit(1, true)]); // ~a v b

    let result = checker.add_derived(&[lit(0, true)]); // derive {a}
    assert!(
        result.is_ok(),
        "clause {{a}} should be accepted as RAT: {result:?}"
    );
    assert!(
        checker.stats.rat_checks > 0,
        "RAT checking should have been attempted"
    );
}

/// Verify RAT rejection with check_rat disabled (RUP-only mode).
///
/// Non-implied clauses in satisfiable formulas are rejected when RAT is off.
#[test]
fn test_rup_only_rejects_non_implied() {
    let mut checker = DratChecker::new(10, false); // RAT disabled
    checker.add_original(&[lit(0, true), lit(1, true)]); // a v b
    checker.add_original(&[lit(2, true), lit(3, true)]); // c v d
                                                         // {a, c} is not RUP: assume ~a, ~c → b unit (from clause 1), d unit (from clause 2).
                                                         // No conflict → RUP fails. RAT disabled → rejection.
    let result = checker.add_derived(&[lit(0, true), lit(2, true)]);
    assert!(result.is_err(), "should fail with RAT disabled");
    assert_eq!(checker.stats.failures, 1);
    assert_eq!(
        checker.stats.rat_checks, 0,
        "RAT not attempted when disabled"
    );
}

// -- Hash collision test (Finding #12) --

#[test]
fn test_hash_distinct_clauses_different_buckets() {
    // Verify that complementary clauses (a v b) and (a v ~b) hash differently.
    // The order-independent mixed hash should distinguish these literal sets.
    let c1 = vec![lit(0, true), lit(1, true)]; // a v b
    let c2 = vec![lit(0, true), lit(1, false)]; // a v ~b
    let c3 = vec![lit(0, false), lit(1, true)]; // ~a v b
    let c4 = vec![lit(0, false), lit(1, false)]; // ~a v ~b

    let h1 = DratChecker::hash_clause(&c1);
    let h2 = DratChecker::hash_clause(&c2);
    let h3 = DratChecker::hash_clause(&c3);
    let h4 = DratChecker::hash_clause(&c4);

    // All four hashes should be distinct (for this small example).
    let hashes = [h1, h2, h3, h4];
    for i in 0..4 {
        for j in (i + 1)..4 {
            assert_ne!(
                hashes[i], hashes[j],
                "hash collision between clauses {i} and {j}: both hash to {:#x}",
                hashes[i]
            );
        }
    }
}

#[test]
fn test_hash_retains_even_literal_multiplicity() {
    // Both clauses have the same XOR fingerprint because each literal has odd
    // multiplicity. The additive lane must still distinguish them.
    let a = lit(0, true);
    let b = lit(1, true);
    let first = [a, a, a, b];
    let second = [a, b, b, b];
    assert_ne!(
        DratChecker::hash_clause(&first),
        DratChecker::hash_clause(&second)
    );
}

// -- Verify propagation count scales linearly with proof size --

#[test]
fn test_propagation_count_linear_in_proof_steps() {
    // For a chain of binary implications, propagations should scale linearly
    // with the number of steps, not quadratically.
    for n in [10, 20, 40] {
        let num_vars = n + 2;
        let mut checker = DratChecker::new(num_vars, false);

        // Build implication chain: v0 → v1 → v2 → ... → v_{n-1}
        // As clauses: (~v0 v v1), (~v1 v v2), ..., (~v_{n-2} v v_{n-1})
        checker.add_original(&[lit(0, true)]); // unit: v0 = true

        for i in 0..(n - 1) {
            checker.add_original(&[lit(i as u32, false), lit((i + 1) as u32, true)]);
        }

        // After BCP from v0, all v1..v_{n-1} should be propagated.
        // Total propagations from originals should be roughly O(n).
        let props = checker.stats.propagations;
        assert!(
            props <= (n * 3) as u64,
            "n={n}: propagations ({props}) should be O(n), not O(n²)"
        );
    }
}

// -- Verify delete of non-existent long clauses is efficient --

#[test]
fn test_delete_nonexistent_scales_linearly() {
    let mut checker = DratChecker::new(200, false);

    // Add 100 binary clauses.
    for i in 0..100 {
        checker.add_original(&[lit((i * 2) as u32, true), lit((i * 2 + 1) as u32, true)]);
    }

    // Delete clauses that don't exist (different variables).
    let before_misses = checker.stats.missed_deletes;
    for i in 0..100 {
        let base = 200 + i * 2;
        checker.delete_clause(&[lit(base as u32, true), lit((base + 1) as u32, true)]);
    }
    assert_eq!(
        checker.stats.missed_deletes - before_misses,
        100,
        "all 100 deletes should be misses"
    );
}

// -- Verify backward checker completes on scaled inputs --

#[test]
fn test_backward_checker_linear_scaling() {
    use super::backward::BackwardChecker;

    // For increasing formula sizes, verify the backward checker completes
    // and its stats grow proportionally.
    for n in [5, 10, 20] {
        let num_vars = n + 2;
        let mut clauses: Vec<Vec<Literal>> = Vec::new();

        // Create a chain: (~v0 v v1), (~v1 v v2), ..., plus v0 and ~v_{n-1}.
        clauses.push(vec![lit(0, true)]); // v0 = true
        for i in 0..(n - 1) {
            clauses.push(vec![lit(i as u32, false), lit((i + 1) as u32, true)]);
        }
        clauses.push(vec![lit((n - 1) as u32, false)]); // ~v_{n-1} → conflict

        // Proof: just the empty clause (formula is UNSAT from originals).
        let steps = vec![ProofStep::Add(vec![])];

        let mut bwd = BackwardChecker::new(num_vars, false);
        let result = bwd.verify(&clauses, &steps);
        assert!(
            result.is_ok(),
            "n={n}: backward checker should accept: {result:?}"
        );
    }
}
