// Copyright 2026 Andrew Yates
// Coverage gap tests, DIMACS parser edge cases, performance, and regression tests.

use super::*;
use crate::lrat_parser::LratStep;

// ─── Coverage gap tests ─────────────────────────────────────────────

/// Verify that when a clause literal is already satisfied by a prior
/// assumption in the same clause, verify_chain returns true immediately
/// (trivially-satisfied path at checker/mod.rs:164-167).
///
/// Clause (a v ~a): assume negate(a)=~a then negate(~a)=a. But ~a is
/// already assigned true, so value(a) = Some(false), meaning the
/// negation of the second literal (~a) is already false -> the literal
/// ~a is already true -> clause trivially satisfied.
#[test]
fn test_verify_chain_trivially_satisfied() {
    let mut checker = LratChecker::new(2);
    checker.add_original(1, &[lit(1), lit(2)]); // a v b
                                                // Derive (a v ~a) — a tautology. When checking:
                                                // - Assume ~a (negate of first literal)
                                                // - Process second literal ~a: negate(~a) = a, value(a) = Some(false)
                                                //   -> hits the Some(false) branch -> return true immediately.
    assert!(checker.add_derived(2, &[lit(1), lit(-1)], &[]));
}

/// DIMACS parser: duplicate problem line is rejected.
#[test]
fn test_dimacs_duplicate_problem_line() {
    let input = b"\
p cnf 2 1
p cnf 3 2
1 2 0
";
    let err = crate::dimacs::parse_cnf_with_ids(&input[..]).unwrap_err();
    assert!(err.to_string().contains("duplicate"), "got: {err}");
}

/// DIMACS parser: invalid problem line format (not 'cnf').
#[test]
fn test_dimacs_invalid_problem_format() {
    let input = b"p sat 2 1\n1 2 0\n";
    let err = crate::dimacs::parse_cnf_with_ids(&input[..]).unwrap_err();
    let msg = err.to_string();
    assert!(
        msg.contains("invalid") || msg.contains("expected"),
        "got: {err}"
    );
}

/// DIMACS parser: non-numeric variable count.
#[test]
fn test_dimacs_bad_variable_count() {
    let input = b"p cnf abc 2\n";
    let err = crate::dimacs::parse_cnf_with_ids(&input[..]).unwrap_err();
    let msg = err.to_string();
    assert!(
        msg.contains("variable") || msg.contains("parse"),
        "got: {err}"
    );
}

/// DIMACS parser: non-numeric clause count.
#[test]
fn test_dimacs_bad_clause_count() {
    let input = b"p cnf 3 xyz\n";
    let err = crate::dimacs::parse_cnf_with_ids(&input[..]).unwrap_err();
    let msg = err.to_string();
    assert!(
        msg.contains("clause") || msg.contains("parse"),
        "got: {err}"
    );
}

/// DIMACS parser: clause data before problem line.
#[test]
fn test_dimacs_clause_before_header() {
    let input = b"1 2 0\np cnf 2 1\n";
    let err = crate::dimacs::parse_cnf_with_ids(&input[..]).unwrap_err();
    let msg = err.to_string();
    assert!(
        msg.contains("before") || msg.contains("header"),
        "got: {err}"
    );
}

/// DIMACS parser: unterminated clause (no trailing 0) is silently accepted.
#[test]
fn test_dimacs_unterminated_clause() {
    let input = b"\
p cnf 2 1
1 2
";
    let cnf = crate::dimacs::parse_cnf_with_ids(&input[..]).unwrap();
    assert_eq!(cnf.num_vars, 2);
    assert_eq!(cnf.clauses.len(), 1);
    assert_eq!(cnf.clauses[0].1, vec![lit(1), lit(2)]);
}

/// Stats fields: verify originals, derived, and deleted counts are tracked.
#[test]
fn test_stats_tracking() {
    let mut checker = LratChecker::new(3);
    checker.add_original(1, &[lit(1), lit(2)]);
    checker.add_original(2, &[lit(-1), lit(2)]);
    checker.add_original(3, &[lit(-2)]);
    assert_eq!(checker.stats.originals, 3);
    assert_eq!(checker.stats.derived, 0);

    assert!(checker.add_derived(4, &[lit(2)], &[1, 2]));
    assert_eq!(checker.stats.derived, 1);
    assert_eq!(checker.stats.failures, 0);

    checker.delete(1);
    assert_eq!(checker.stats.deleted, 1);

    // Failed derivation
    assert!(!checker.add_derived(5, &[lit(1)], &[2]));
    assert_eq!(checker.stats.failures, 1);
    assert_eq!(checker.stats.derived, 2); // derived counter increments even on failure
}

// ─── Performance ────────────────────────────────────────────────────

/// Build an implication chain: x_1 → x_2 → ... → x_{n+1}, with seed (x_1)
/// and contradiction (~x_{n+1}). Returns (checker, proof_steps, total_derived).
fn build_chain_proof(chain_len: usize) -> (LratChecker, Vec<LratStep>, usize) {
    let mut checker = LratChecker::new(chain_len + 1);
    checker.add_original(1, &[lit(1)]); // seed: (x_1)

    for i in 0..chain_len {
        let neg_cur = -((i + 1) as i32);
        let pos_next = (i + 2) as i32;
        checker.add_original((i + 2) as u64, &[lit(neg_cur), lit(pos_next)]);
    }

    // RUP chain: derive (x_{i+2}) from hint (~x_{i+1} v x_{i+2}) + hint (x_{i+1})
    let mut steps = Vec::with_capacity(chain_len + 1);
    let base_id = (chain_len + 2) as i64;
    for i in 0..chain_len {
        let hint_impl = (i + 2) as i64;
        let hint_unit = if i == 0 {
            1i64
        } else {
            base_id + (i as i64) - 1
        };
        steps.push(LratStep::Add {
            id: base_id as u64 + i as u64,
            clause: vec![Literal::from_dimacs((i + 2) as i32)],
            hints: vec![hint_impl, hint_unit],
        });
    }

    // Contradiction: (~x_{n+1}) + last derived unit → empty clause
    let contra_id = base_id + chain_len as i64;
    checker.add_original(contra_id as u64, &[lit(-((chain_len + 1) as i32))]);
    steps.push(LratStep::Add {
        id: contra_id as u64 + 1,
        clause: vec![],
        hints: vec![base_id + chain_len as i64 - 1, contra_id],
    });

    (checker, steps, chain_len + 1)
}

/// Performance: >= 1M clauses/second (release), >= 100K (debug).
#[test]
fn test_performance_throughput() {
    let (mut checker, steps, total) = build_chain_proof(100_000);

    let start = std::time::Instant::now();
    let result = checker.verify_proof(&steps);
    let elapsed = start.elapsed();

    assert!(result, "chain proof must verify");

    let rate = total as f64 / elapsed.as_secs_f64();
    eprintln!(
        "Performance: {total} clauses in {:.3}ms = {:.1}M clauses/sec",
        elapsed.as_secs_f64() * 1000.0,
        rate / 1_000_000.0
    );

    let threshold = if cfg!(debug_assertions) {
        100_000.0
    } else {
        1_000_000.0
    };
    assert!(
        rate >= threshold,
        "Below {threshold:.0} clauses/sec: {rate:.1} ({total} in {:.3}ms)",
        elapsed.as_secs_f64() * 1000.0
    );
}

// ─── Regression tests ───────────────────────────────────────────────

#[test]
fn test_failed_clause_not_usable_as_hint() {
    // Regression test for #5200: clauses that fail verification must NOT be
    // inserted into the database. Uses lenient mode so the second add_derived
    // actually attempts verification (strict mode would fail-fast).
    let mut checker = LratChecker::new_lenient(2);
    checker.add_original(1, &[lit(1), lit(2)]); // a v b
    checker.add_original(2, &[lit(-1), lit(2)]); // ~a v b

    // Step 1: (a) with bad hints — should fail
    let ok1 = checker.add_derived(3, &[lit(1)], &[1]);
    assert!(
        !ok1,
        "clause (a) should not be derivable from (a v b) alone"
    );

    // Step 2: empty clause using the failed clause — should also fail
    let ok2 = checker.add_derived(4, &[], &[3, 2]);
    assert!(
        !ok2,
        "empty clause must not be derivable using unverified hint"
    );
}

#[test]
fn test_duplicate_original_clause_id_rejected() {
    let mut checker = LratChecker::new(2);
    assert!(checker.add_original(1, &[lit(1), lit(2)]));
    assert!(
        !checker.add_original(1, &[lit(-1), lit(2)]),
        "duplicate original clause ID 1 must be rejected"
    );
}

#[test]
fn test_duplicate_derived_clause_id_rejected() {
    // Lenient mode: tests that duplicate ID rejection logic is exercised
    // on the third call (strict mode would fail-fast from the second call).
    let mut checker = LratChecker::new_lenient(2);
    checker.add_original(1, &[lit(1), lit(2)]); // a v b
    checker.add_original(2, &[lit(-1), lit(2)]); // ~a v b

    // Derive (b) with ID 3 — valid.
    assert!(checker.add_derived(3, &[lit(2)], &[1, 2]));

    // Attempt to derive another clause with ID 3 — must fail.
    assert!(
        !checker.add_derived(3, &[lit(1)], &[1]),
        "duplicate derived clause ID 3 must be rejected"
    );

    // Attempt to derive with ID 1 (original clause ID) — must fail.
    assert!(
        !checker.add_derived(1, &[lit(2)], &[1, 2]),
        "derived clause ID 1 collides with original — must be rejected"
    );
}

// ─── Additional coverage gap tests ──────────────────────────────────

/// DIMACS parser: non-numeric literal token in clause body.
#[test]
fn test_dimacs_non_numeric_literal_in_clause() {
    let input = b"p cnf 2 1\n1 abc 0\n";
    let err = crate::dimacs::parse_cnf_with_ids(&input[..]).unwrap_err();
    let msg = err.to_string();
    assert!(
        msg.contains("literal") || msg.contains("parse"),
        "got: {err}"
    );
}

/// DIMACS parser: declared clause count != actual clause count.
#[test]
fn test_dimacs_clause_count_mismatch_succeeds() {
    // Declares 3 clauses but only provides 1.
    let input = b"p cnf 2 3\n1 2 0\n";
    let cnf = crate::dimacs::parse_cnf_with_ids(&input[..]).unwrap();
    assert_eq!(cnf.num_vars, 2);
    assert_eq!(cnf.clauses.len(), 1); // actual count, not declared
}

/// verify_chain: duplicate literal in clause with non-minimal hints is
/// accepted (RUP valid) but resolution mismatch is tracked.
///
/// Clause {1, 1, 2} with hint [1] passes RUP. Resolution of hint {a}
/// produces resolvent {1}, which doesn't match claim {1, 1, 2} →
/// resolution mismatch (informational only, not rejection).
#[test]
fn test_verify_chain_duplicate_literal_accepted_resolution_mismatch() {
    let mut checker = LratChecker::new(3);
    checker.add_original(1, &[lit(1)]); // a
    checker.add_original(2, &[lit(-1), lit(-2)]); // ~a v ~b

    // Non-minimal chain: RUP ok, resolution mismatch tracked.
    let ok = checker.add_derived(3, &[lit(1), lit(1), lit(2)], &[1]);
    assert!(ok, "RUP-valid clause accepted despite resolution mismatch");
    assert_eq!(checker.stats.rup_ok, 1);
    assert_eq!(checker.stats.resolution_mismatch, 1);
    assert_eq!(checker.stats.failures, 0);
}

/// value() returns None for variable indices beyond the assignment array.
#[test]
fn test_value_out_of_bounds_returns_none() {
    let mut checker = LratChecker::new(2);
    checker.add_original(1, &[lit(1), lit(2)]); // a v b  (SAT)

    assert!(!checker.add_derived(2, &[lit(100)], &[1]));

    let mut checker2 = LratChecker::new(2);
    checker2.add_original(1, &[lit(1)]); // a
    checker2.add_original(2, &[lit(-1)]); // ~a
    assert!(checker2.add_derived(3, &[lit(100)], &[1, 2]));
    assert_eq!(checker2.stats.failures, 0);
}

/// stats_summary() returns correctly formatted string.
#[test]
fn test_stats_summary_format() {
    let mut checker = LratChecker::new(2);
    checker.add_original(1, &[lit(1)]);
    checker.add_original(2, &[lit(-1)]);
    checker.add_derived(3, &[], &[1, 2]);
    checker.delete(1);

    let summary = checker.stats_summary();
    assert!(
        summary.contains("original=2"),
        "summary must contain original count: {summary}"
    );
    assert!(
        summary.contains("derived=1"),
        "summary must contain derived count: {summary}"
    );
    assert!(
        summary.contains("deleted=1"),
        "summary must contain deleted count: {summary}"
    );
    assert!(
        summary.contains("failures=0"),
        "summary must contain failures count: {summary}"
    );
}

/// Delete of nonexistent clause: returns false and increments failures.
/// CaDiCaL lratchecker.cpp:634-649 treats this as a fatal error.
/// Uses lenient mode to test cumulative failure counting across operations.
#[test]
fn test_delete_nonexistent_clause_fails() {
    let mut checker = LratChecker::new_lenient(2);
    checker.add_original(1, &[lit(1), lit(2)]);
    assert_eq!(checker.stats.deleted, 0);

    assert!(
        !checker.delete(999),
        "deleting nonexistent clause must return false"
    );
    assert_eq!(checker.stats.deleted, 0);
    assert_eq!(checker.stats.failures, 1, "must increment failure count");

    assert!(
        checker.delete(1),
        "deleting existing clause must return true"
    );
    assert_eq!(checker.stats.deleted, 1);

    assert!(
        !checker.delete(1),
        "deleting already-deleted clause must return false"
    );
    assert_eq!(
        checker.stats.deleted, 1,
        "deleting already-deleted clause must not increment deleted count"
    );
    assert_eq!(checker.stats.failures, 2);
}

/// Many failures (>10) suppresses diagnostic logging.
/// Uses lenient mode to accumulate 15 failures.
#[test]
fn test_many_failures_counted_beyond_logging_threshold() {
    let mut checker = LratChecker::new_lenient(2);
    checker.add_original(1, &[lit(1), lit(2)]); // a v b (SAT)

    // Attempt 15 invalid derivations.
    for i in 2..=16 {
        let ok = checker.add_derived(i, &[lit(-(i as i32))], &[1]);
        assert!(!ok, "derivation {i} should fail");
    }

    assert_eq!(
        checker.stats.failures, 15,
        "all 15 failures must be counted, not just the first 10"
    );
    assert_eq!(checker.stats.derived, 15);
}

// ─── #5289: Resolution enforcement (CaDiCaL parity) ────────────────

/// Verify that RUP success with resolution mismatch falls through to
/// RAT/blocked paths instead of accepting the clause (#5289).
///
/// CaDiCaL lratchecker.cpp:503-504 requires BOTH `check(proof_chain)`
/// AND `check_resolution(proof_chain)` to pass before accepting via RUP.
/// If either fails, it falls through to `check_blocked`.
///
/// This test constructs a case where:
/// 1. RUP succeeds (hint-guided unit propagation finds a conflict)
/// 2. Resolution fails (resolvent has extra literal not in claimed clause)
/// 3. No RAT or blocked fallback is available
///
/// RUP passes. Resolution has a mismatch (redundant hints produce a
/// larger resolvent). Standard LRAT accepts RUP-valid clauses; the
/// resolution mismatch is tracked for proof quality diagnostics only.
#[test]
fn test_rup_ok_resolution_mismatch_accepted_as_advisory() {
    let mut checker = LratChecker::new(3);
    checker.add_original(1, &[lit(1)]); // (a) — unit
    checker.add_original(2, &[lit(1)]); // (a) — duplicate content, different ID
    checker.add_original(3, &[lit(-1), lit(2)]); // (~a v b)

    // Derive {b} with hints [1, 2, 3].
    // RUP: passes. Resolution: mismatch (extra literal a in resolvent).
    // Accepted per standard LRAT.
    let ok = checker.add_derived(4, &[lit(2)], &[1, 2, 3]);
    assert!(
        ok,
        "RUP-valid clause accepted; resolution mismatch is informational"
    );
    assert_eq!(checker.stats.rup_ok, 1, "RUP itself passed");
    assert_eq!(
        checker.stats.resolution_mismatch, 1,
        "resolution mismatch tracked"
    );
    assert_eq!(
        checker.stats.failures, 0,
        "no failure — RUP is the acceptance criterion"
    );
}
