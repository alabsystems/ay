// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The verification-consumer `slices/range` base obligations (both genuinely SAT; z3 solves
//! each in ~0.01s).
//!
//! Before the extensionality expression-split, ay bailed
//! `Unknown(ExpressionSplit)` on these at ~6-7s:
//! `create_expression_split_atoms` returned `None` for the Array-sorted
//! disequalities left over in the base (`seq_array(s1) ≠ seq_array(s2)`,
//! `seq_array(s) ≠ store(a,i,v)` over `(Array Int Int)`), because the split
//! machinery only knew how to branch Int/Real disequalities.
//!
//! The fix (in `create_expression_split_atoms`) skolemizes a fresh difference
//! index `k` and reduces the array disequality `A ≠ B` to the element-sorted
//! `select(A,k) ≠ select(B,k)` — the standard array extensionality axiom —
//! which the existing Int split then handles. That removes the bail.
//!
//! IGNORED — the base does NOT yet flip to SAT. Once the extensionality split
//! feeds the array solver a `select(A,k) ≠ select(B,k)` witness, the solve
//! reaches the deeper `ArraySolver::explain_distinct_if_provable` /
//! `equality_reason_paths_from` store-chain eq-path wall (the #7956-class
//! O(selects²×aliases²) reason-set BFS over the dense seq-equality graph) and
//! times out (>90s vs z3's 0.01s). That is the separate, multi-week array
//! decision-procedure (weak-equivalence / near-linear read-over-write) rewrite,
//! not an expression-split issue. These tests are kept as permanent, ready
//! targets: DELETE the `#[ignore]` (keeping `expect_sat`) once that wall lands
//! and slices/range flips.
//!
//! SHARPENED PIN (2026-07-21, #7956 F1 session — reproduce with `AY_F1_DIAG=1`):
//! the wall is CONVERGENCE-bound, not wall-clock-bound — a 20-MINUTE budget
//! still times out, so no constant-factor speedup of the eq-path walk can flip
//! these tests. The decisive repro is the QUANTIFIER-FREE core (strip the 3
//! `forall` assertions): ay reaches a Sat fixpoint in ~3s, then the candidate
//! model is DISCARDED at `complete_unconstrained_constants_for_output` because
//! the merged EUF model carries `function_table_conflicts={"select"}` — two
//! same-array select rows (`select(A, (+ (seq_offset a_current_view) 1))`
//! hard-pinned 0 and `select(A, (+ (seq_offset final_a_view) 1))` hard-pinned
//! 1) whose index terms receive EQUAL final LIA values — and the public funnel
//! fail-closes to `unknown (:reason-unknown incomplete)` via "No model
//! available" (#8373). The theory never refutes the inconsistent branch
//! because the index equality `(+ off_f 1) = (+ off_c 1)` (entailed by the
//! asserted `(= (seq_offset final_a_view) (seq_offset a_current_view))`) is
//! UNPROVABLE inside the arrays solver: `parse_affine_int_expr` returns `None`
//! on UF leaves (`seq_offset x` is an opaque App), and the #6820 removal
//! delegated eq-substituted affine reasoning to LIA, which never feeds this
//! congruence back as an arrays-visible index equality. On the FULL (quantified)
//! fixture the same doomed ground solve is additionally re-run by the
//! quantifier pipeline's certification probes (`instance_closure_ground_unsat`
//! → `isolated_ground_solve_is_unsat`, no inner budget) with read-congruence
//! pairs disabled (#read-congruence-quantified-scope), burning the entire
//! timeout. Fix classes that CAN flip these tests: (a) index-congruence
//! completeness — prove `f(a)+c = f(b)+c` from asserted `f(a)=f(b)` with a
//! SAT-visible explanation so the select conflict fires and SAT backtracks the
//! inconsistent array merge; (b) the full weak-equivalence rewrite. The
//! window-scoped store-chain walk memos landed in this session
//! (eq_paths_cache::store_through / alias_diseq_pairs) cut the profiled
//! witness-check subtree ~10x but cannot change the verdict alone.

use crate::common::{run_executor_smt_with_timeout, SolverOutcome};
use ntest::timeout;

fn expect_sat(input: &str, label: &str) {
    let result = run_executor_smt_with_timeout(input, 30).expect("execution should succeed");
    assert_eq!(result, SolverOutcome::Sat, "{label}: expected SAT");
}

#[test]
#[ignore = "#7956 wall is convergence-bound (20min still times out): select function_table_conflicts discard every candidate model — see module doc SHARPENED PIN"]
#[timeout(120_000)]
fn slices_range_base_000_is_sat() {
    expect_sat(
        include_str!("../fixtures/slr_expression_split/slices_range_base_000_sat.smt2"),
        "slices/range base-000 (Array-sorted diseq extensionality split)",
    );
}

#[test]
#[ignore = "#7956 wall is convergence-bound (20min still times out): select function_table_conflicts discard every candidate model — see module doc SHARPENED PIN"]
#[timeout(120_000)]
fn slices_range_base_001_is_sat() {
    expect_sat(
        include_str!("../fixtures/slr_expression_split/slices_range_base_001_sat.smt2"),
        "slices/range base-001 (Array-sorted diseq extensionality split)",
    );
}
