// Copyright 2026 Andrew Yates
// Coverage gap tests and binary DRAT end-to-end tests for the forward DRAT
// checker.

use super::*;
use crate::checker::test_helpers::lit;
use std::path::PathBuf;

// ─── Hash table rehash coverage ────────────────────────────────────

#[test]
fn test_maybe_rehash_triggers_on_large_formula() {
    // Initial hash capacity is 1024. Adding >1024 clauses triggers rehash.
    let num_clauses = 1100;
    let mut checker = DratChecker::new(num_clauses * 2, false);
    assert_eq!(checker.hash_buckets.len(), INITIAL_HASH_CAPACITY);

    // Add enough 2-literal clauses to exceed the initial capacity.
    for i in 0..num_clauses {
        let a = i as u32 * 2;
        let b = a + 1;
        checker.add_original(&[lit(a, true), lit(b, true)]);
    }

    // After inserting >1024 clauses, hash table should have doubled.
    assert!(
        checker.hash_buckets.len() > INITIAL_HASH_CAPACITY,
        "hash table should have rehashed: got {} buckets for {} live clauses",
        checker.hash_buckets.len(),
        checker.live_clauses
    );

    // Deletion should still find clauses after rehash.
    checker.delete_clause(&[lit(0, true), lit(1, true)]);
    assert_eq!(checker.stats.missed_deletes, 0);
}

// ─── Coverage gap tests ─────────────────────────────────────────────

/// RAT failure path: a RAT check fails because a resolvent is not RUP.
///
/// Formula: (a v b), (~a v ~b). Adding (a) is NOT RUP and NOT RAT:
/// - RAT with pivot a: clauses with ~a = {(~a v ~b)}.
///   Resolvent of (a) with (~a v ~b) = (~b). NOT RUP -> RAT fails.
#[test]
fn test_rat_failure_resolvent_not_rup() {
    let mut checker = DratChecker::new(3, true); // RAT enabled
    checker.add_original(&[lit(0, true), lit(1, true)]); // a v b
    checker.add_original(&[lit(0, false), lit(1, false)]); // ~a v ~b
    let result = checker.add_derived(&[lit(0, true)]); // (a) — not RUP, not RAT
    assert!(result.is_err(), "RAT check should fail: {result:?}");
}

/// Pivot fallback: a clause that is RAT only on its second literal.
///
/// Without pivot fallback (drat-trim.c:662-683), this clause is rejected.
#[test]
fn test_rat_pivot_fallback_succeeds_on_second_literal() {
    let mut checker = DratChecker::new(3, true); // RAT enabled
    checker.add_original(&[lit(0, false), lit(1, true)]); // ~a v b
    checker.add_original(&[lit(0, true), lit(1, false)]); // a v ~b

    // (a v c): NOT RUP, NOT RAT with pivot a, but IS RAT with pivot c.
    let result = checker.add_derived(&[lit(0, true), lit(2, true)]);
    assert!(
        result.is_ok(),
        "Pivot fallback RAT should succeed on second literal: {result:?}"
    );
    assert!(
        checker.stats.rat_checks > 0,
        "RAT check should have been triggered"
    );
}

/// ACTIVE filtering in RAT: check_rat_with_pivot skips non-ACTIVE clauses.
///
/// With active_filter, RAT succeeds (non-ACTIVE skipped).
/// Without active_filter, RAT fails (non-ACTIVE resolvent fails RUP).
#[test]
fn test_rat_active_filtering_skips_non_active_clause() {
    let mut checker = DratChecker::new(4, true);
    checker.add_original(&[lit(0, true), lit(1, true)]); // C0: a v b (cidx=0)
    checker.add_original(&[lit(0, false), lit(1, true)]); // C1: ~a v b (cidx=1)
    checker.add_original(&[lit(0, false), lit(3, true)]); // C2: ~a v d (cidx=2)

    let clause = &[lit(0, true), lit(2, true)]; // (a v c)

    // Without ACTIVE filter: RAT with pivot a should FAIL (C2 resolvent not RUP).
    let result_no_filter = checker.check_rat_with_pivot(clause, lit(0, true), None);
    assert!(
        !result_no_filter,
        "RAT without active filter should fail (non-RUP resolvent with C2)"
    );

    // With ACTIVE filter: C0=active, C1=active, C2=NOT active.
    let active = vec![true, true, false];
    let result_filtered = checker.check_rat_with_pivot(clause, lit(0, true), Some(&active));
    assert!(
        result_filtered,
        "RAT with active filter should succeed (C2 skipped)"
    );
}

/// check_rat_with_pivot_deps returns resolution candidate indices and RUP
/// proof chain dependencies (#5215).
#[test]
fn test_rat_with_pivot_deps_returns_candidates_and_rup_deps() {
    let mut checker = DratChecker::new(4, true);
    checker.add_original(&[lit(0, true), lit(1, true)]); // C0: a v b (cidx=0)
    checker.add_original(&[lit(0, false), lit(1, true)]); // C1: ~a v b (cidx=1)
    checker.add_original(&[lit(0, false), lit(3, true)]); // C2: ~a v d (cidx=2)

    let clause = &[lit(0, true), lit(2, true)]; // (a v c)
    let active = vec![true, true, false]; // C0 active, C1 active, C2 not

    let result = checker.check_rat_with_pivot_deps(clause, lit(0, true), Some(&active));

    assert!(result.success, "RAT should succeed with active filter");
    assert!(
        result.candidate_indices.contains(&1),
        "C1 (idx=1) should be a resolution candidate: {:?}",
        result.candidate_indices
    );
    assert!(
        !result.candidate_indices.contains(&2),
        "C2 (idx=2) should be filtered out: {:?}",
        result.candidate_indices
    );
    assert!(
        !result.rup_deps.is_empty(),
        "RUP deps should be non-empty (resolvent (c v b) depends on C0 and/or C1)"
    );
}

// ─── drat-trim cross-validation tests ────────────────────────────────
//
// Cross-validate ay-drat-check (forward and backward) against the
// drat-trim reference examples. These are the same CNF+DRAT pairs
// that drat-trim verifies as VERIFIED.

/// Helper: load a CNF+DRAT file pair from reference/drat-trim/examples/
/// and verify with both forward and backward checkers.
fn drat_trim_examples_dir() -> Option<PathBuf> {
    let dir = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../reference/drat-trim/examples");
    if dir.is_dir() {
        Some(dir)
    } else {
        eprintln!(
            "SKIP: optional drat-trim examples not found at {}",
            dir.display()
        );
        None
    }
}

fn verify_drat_trim_drat_example(name: &str) {
    use crate::cnf_parser::parse_cnf;
    use crate::drat_parser::parse_drat;

    let Some(base) = drat_trim_examples_dir() else {
        return;
    };
    let cnf_path = base.join(format!("{name}.cnf"));
    let drat_path = base.join(format!("{name}.drat"));

    let cnf_data = std::fs::read(&cnf_path).unwrap();
    let drat_data = std::fs::read(&drat_path).unwrap();

    let cnf = parse_cnf(&cnf_data[..]).unwrap();
    let steps = parse_drat(&drat_data[..]).unwrap();

    // Forward checker
    let mut fwd = DratChecker::new(cnf.num_vars, true);
    let fwd_result = fwd.verify(&cnf.clauses, &steps);
    assert!(
        fwd_result.is_ok(),
        "drat-trim example {name}: forward checker failed: {fwd_result:?}"
    );

    // Backward checker
    let mut bwd = backward::BackwardChecker::new(cnf.num_vars, true);
    let bwd_result = bwd.verify(&cnf.clauses, &steps);
    assert!(
        bwd_result.is_ok(),
        "drat-trim example {name}: backward checker failed: {bwd_result:?}"
    );
}

#[test]
fn test_drat_trim_example_4_vars_drat() {
    verify_drat_trim_drat_example("example-4-vars");
}

#[test]
fn test_drat_trim_example_5_vars_drat() {
    verify_drat_trim_drat_example("example-5-vars");
}

#[test]
fn test_drat_trim_example_schur_drat() {
    verify_drat_trim_drat_example("example-Schur");
}

#[test]
fn test_drat_trim_uuf_30_1_drat() {
    verify_drat_trim_drat_example("uuf-30-1");
}

#[test]
fn test_drat_trim_uuf_50_2_drat() {
    verify_drat_trim_drat_example("uuf-50-2");
}

#[test]
fn test_drat_trim_uuf_50_3_drat() {
    verify_drat_trim_drat_example("uuf-50-3");
}

#[test]
fn test_drat_trim_uuf_100_1_drat() {
    verify_drat_trim_drat_example("uuf-100-1");
}

#[test]
fn test_drat_trim_uuf_100_2_drat() {
    verify_drat_trim_drat_example("uuf-100-2");
}

#[test]
fn test_drat_trim_uuf_100_3_drat() {
    verify_drat_trim_drat_example("uuf-100-3");
}

#[test]
fn test_drat_trim_uuf_100_4_drat() {
    verify_drat_trim_drat_example("uuf-100-4");
}

#[test]
fn test_drat_trim_uuf_100_5_drat() {
    verify_drat_trim_drat_example("uuf-100-5");
}

/// DRUP (RUP-only) example: Schur formula with RUP-only proof.
/// Tests that the checker works in RUP-only mode (no RAT needed).
#[test]
fn test_drat_trim_example_schur_drup() {
    use crate::cnf_parser::parse_cnf;
    use crate::drat_parser::parse_drat;

    let Some(base) = drat_trim_examples_dir() else {
        return;
    };
    let cnf_data = std::fs::read(base.join("example-Schur.cnf")).unwrap();
    let drup_data = std::fs::read(base.join("example-Schur.drup")).unwrap();

    let cnf = parse_cnf(&cnf_data[..]).unwrap();
    let steps = parse_drat(&drup_data[..]).unwrap();

    // RUP-only mode (no RAT)
    let mut fwd = DratChecker::new(cnf.num_vars, false);
    let fwd_result = fwd.verify(&cnf.clauses, &steps);
    assert!(
        fwd_result.is_ok(),
        "DRUP example-Schur: forward (RUP-only) failed: {fwd_result:?}"
    );

    let mut bwd = backward::BackwardChecker::new(cnf.num_vars, false);
    let bwd_result = bwd.verify(&cnf.clauses, &steps);
    assert!(
        bwd_result.is_ok(),
        "DRUP example-Schur: backward (RUP-only) failed: {bwd_result:?}"
    );
}

/// Binary DRAT end-to-end: encode a valid proof in binary format,
/// parse it, and verify through both forward and backward checkers.
#[test]
fn test_binary_drat_end_to_end_forward_and_backward() {
    use crate::cnf_parser::parse_cnf;
    use crate::drat_parser::parse_drat;

    let cnf_text = "\
p cnf 2 4
1 2 0
-1 2 0
1 -2 0
-1 -2 0
";
    // Binary DRAT proof: add(2), add(-2), add(empty)
    // DIMACS lit 2 -> encoded 4, DIMACS lit -2 -> encoded 5
    let proof_data: Vec<u8> = vec![
        0x61, 0x04, 0x00, // add (b)
        0x61, 0x05, 0x00, // add (~b)
        0x61, 0x00, // add ()
    ];

    let cnf = parse_cnf(cnf_text.as_bytes()).unwrap();
    let steps = parse_drat(&proof_data).unwrap();
    assert_eq!(steps.len(), 3, "expected 3 proof steps");

    // Forward checker
    let mut fwd = DratChecker::new(cnf.num_vars, false);
    let fwd_result = fwd.verify(&cnf.clauses, &steps);
    assert!(
        fwd_result.is_ok(),
        "forward must accept binary proof: {fwd_result:?}"
    );

    // Backward checker
    let mut bwd = backward::BackwardChecker::new(cnf.num_vars, false);
    let bwd_result = bwd.verify(&cnf.clauses, &steps);
    assert!(
        bwd_result.is_ok(),
        "backward must accept binary proof: {bwd_result:?}"
    );
}
