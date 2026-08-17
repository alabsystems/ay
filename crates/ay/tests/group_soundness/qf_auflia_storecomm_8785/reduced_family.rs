// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Reduced store-commutativity soundness regressions.

use super::*;

/// Reduced generated family member for #8785.
///
/// This is smaller than the checked-in 30/40-store fixtures but keeps the same
/// shape: two reordered store towers over the same base, one deep repeated
/// write on the left, and one fresh witness index on the right. The formula is
/// SAT because the Skolem witness can pick index 12, where the right tower
/// stores `e12` and the left tower still reads the unconstrained base array.
///
/// This broadens coverage beyond exact benchmark files while still rejecting
/// only false `unsat`.
#[test]
#[timeout(60_000)]
fn auflia_storecomm_reduced_shared_prefix_family_member_is_not_unsat() {
    let input = reduced_shared_prefix_storecomm_input();
    let (stdout, stderr) = run_ay_on_input(&input);
    let result = first_line(&stdout);
    let panicked = stderr.contains("panicked at")
        || stderr.contains("BUG:")
        || stderr.contains("out-of-bounds");
    assert!(
        !panicked,
        "Soundness regression: AY panicked on reduced #8785 family member. \
         stdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert_ne!(
        result, "unsat",
        "Soundness regression (#8785): AY reported 'unsat' on a reduced \
         shared-prefix invalid-commutativity SAT instance. The expected answer \
         is 'sat' or 'unknown'; 'unsat' is a soundness bug. \
         stdout:\n{stdout}\nstderr:\n{stderr}"
    );
}

/// Parfit's 12-index direct-disequality sibling for #8785.
///
/// This uses the same reduced 12-index store towers as the shared-prefix
/// witness canary above, but reaches the false-UNSAT family through a direct
/// top-level array disequality instead of an explicit Skolem select witness.
/// That keeps coverage on the direct-disequality branch without requiring the
/// larger checked-in `00030_007` benchmark.
#[test]
#[timeout(60_000)]
fn auflia_storecomm_reduced_shared_prefix_direct_disequality_is_not_unsat() {
    let input = reduced_shared_prefix_direct_disequality_storecomm_input();
    let (stdout, stderr) = run_ay_on_input(&input);
    let result = first_line(&stdout);
    let panicked = stderr.contains("panicked at")
        || stderr.contains("BUG:")
        || stderr.contains("out-of-bounds");
    assert!(
        !panicked,
        "Soundness regression: AY panicked on Parfit's reduced 12-index \
         direct-disequality #8785 family member. stdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert_ne!(
        result, "unsat",
        "Soundness regression (#8785): AY reported 'unsat' on Parfit's \
         reduced 12-index direct-disequality invalid-commutativity SAT \
         instance. The expected answer is 'sat' or 'unknown'; 'unsat' is a \
         soundness bug. stdout:\n{stdout}\nstderr:\n{stderr}"
    );
}

/// Smaller concrete nested-store family member for #8785.
///
/// This instance keeps the repeated left-side write and the fresh right-side
/// witness index, but trims the tower down to six concrete stores. It catches
/// the same false-`unsat` class through an internal shared-prefix collapse:
/// the Skolem witness can pick index 40, where only the right tower writes.
#[test]
#[timeout(60_000)]
fn auflia_storecomm_reduced_concrete_prefix_family_member_is_not_unsat() {
    let input = reduced_concrete_prefix_storecomm_input();
    let (stdout, stderr) = run_ay_on_input(&input);
    let result = first_line(&stdout);
    let panicked = stderr.contains("panicked at")
        || stderr.contains("BUG:")
        || stderr.contains("out-of-bounds");
    assert!(
        !panicked,
        "Soundness regression: AY panicked on reduced concrete #8785 family member. \
         stdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert_ne!(
        result, "unsat",
        "Soundness regression (#8785): AY reported 'unsat' on a reduced \
         concrete-prefix invalid-commutativity SAT instance. The expected answer \
         is 'sat' or 'unknown'; 'unsat' is a soundness bug. \
        stdout:\n{stdout}\nstderr:\n{stderr}"
    );
}

/// Smaller sparse-RHS/root-faithful family member for #8785.
///
/// `rhs` is constrained by two same-target store equalities over the same root
/// array `a`, but both writes can be faithful write-backs, so `rhs` can still
/// equal `a`. `lhs` then adds one fresh write at `k`, and the extensional
/// witness is forced to that fresh index rather than either write-back index.
///
/// This keeps the live `ROW2` / disjunctive store-target flavor while trimming
/// the reproducer to one named shared target and one sparse extra RHS branch.
#[test]
#[timeout(60_000)]
fn auflia_storecomm_reduced_sparse_rhs_root_faithful_family_member_is_not_unsat() {
    let input = reduced_sparse_rhs_root_faithful_storecomm_input();
    let (stdout, stderr) = run_ay_on_input(&input);
    let result = first_line(&stdout);
    let panicked = stderr.contains("panicked at")
        || stderr.contains("BUG:")
        || stderr.contains("out-of-bounds");
    assert!(
        !panicked,
        "Soundness regression: AY panicked on reduced sparse-RHS/root-faithful #8785 family member. \
         stdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert_ne!(
        result, "unsat",
        "Soundness regression (#8785): AY reported 'unsat' on a reduced \
         sparse-RHS/root-faithful invalid-commutativity SAT instance. The \
         expected answer is 'sat' or 'unknown'; 'unsat' is a soundness bug. \
         stdout:\n{stdout}\nstderr:\n{stderr}"
    );
}

/// Smaller symbolic-witness family member for #8785 (`t1_pp_nf_ai_00030_002`).
///
/// This keeps the still-live `pp_nf_ai` shape: all indices are symbolic and
/// pairwise distinct, the left tower repeats `i1`, and the right tower is a
/// permutation that introduces one fresh RHS-only index `i7` before replaying
/// the shared root write. The formula is SAT because the Skolem witness can
/// pick `i7`, where only the right tower writes.
#[test]
#[timeout(60_000)]
fn auflia_storecomm_reduced_symbolic_witness_family_member_is_not_unsat() {
    let input = reduced_symbolic_witness_storecomm_input();
    let (stdout, stderr) = run_ay_on_input(&input);
    let result = first_line(&stdout);
    let panicked = stderr.contains("panicked at")
        || stderr.contains("BUG:")
        || stderr.contains("out-of-bounds");
    assert!(
        !panicked,
        "Soundness regression: AY panicked on reduced symbolic-witness #8785 family member. \
         stdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert_ne!(
        result, "unsat",
        "Soundness regression (#8785): AY reported 'unsat' on a reduced \
         symbolic-witness invalid-commutativity SAT instance. The expected \
         answer is 'sat' or 'unknown'; 'unsat' is a soundness bug. \
         stdout:\n{stdout}\nstderr:\n{stderr}"
    );
}
