// Copyright 2026 Andrew Yates
// Tests for the checker's dense variable envelope: refusing variables beyond
// `MAX_DENSE_VARS` on the library API, and allocating the dense arrays
// fallibly.

use super::*;
use crate::checker::test_helpers::lit;
use crate::drat_parser::ProofStep;

// -- Dense-envelope refusal on the library API --
//
// The frontends refuse variables beyond `MAX_DENSE_VARS` before parsing, but
// the public checker API accepts any `Literal`. One literal of variable
// `Variable::MAX_ID` used to make `ensure_capacity` resize the watch arrays to
// 2^32 entries (~200GB) and abort the process. The checker now refuses such
// clauses and fails every conclusion closed.

type TestResult = Result<(), Box<dyn std::error::Error>>;

/// Literal of the first variable index outside the dense envelope.
fn first_out_of_envelope_lit(positive: bool) -> Result<Literal, Box<dyn std::error::Error>> {
    let dimacs = i32::try_from(MAX_DENSE_VARS)?
        .checked_add(1)
        .ok_or("dimacs overflow")?;
    let signed = if positive {
        dimacs
    } else {
        dimacs.checked_neg().ok_or("dimacs negation")?
    };
    let lit = Literal::try_from_dimacs(signed)?;
    if lit.variable().index() != MAX_DENSE_VARS {
        return Err(format!("expected variable index {MAX_DENSE_VARS}, got {lit}").into());
    }
    Ok(lit)
}

#[test]
fn test_out_of_envelope_originals_fail_conclusion_closed() -> TestResult {
    // (x) and (~x) are contradictory; previously this concluded UNSAT after
    // allocating the dense arrays for x. The clauses cannot be stored now, so
    // the conclusion must fail closed instead of resting on a partial formula.
    let x = first_out_of_envelope_lit(true)?;
    let not_x = first_out_of_envelope_lit(false)?;
    let mut checker = DratChecker::new(2, false);
    checker.add_original(&[x]);
    checker.add_original(&[not_x]);
    if checker.num_vars != 2 {
        return Err(format!("dense arrays grew to {} variables", checker.num_vars).into());
    }
    let conclusion = checker.conclude_unsat();
    if conclusion != ConcludeResult::Failed(ConcludeFailure::VariableOutOfRange) {
        return Err(format!("expected VariableOutOfRange, got {conclusion:?}").into());
    }
    Ok(())
}

#[test]
fn test_max_variable_literal_is_refused_without_allocation() -> TestResult {
    // Variable::MAX_ID: the ~200GB worst case.
    let big = Literal::try_from_dimacs(i32::MAX)?;
    let mut checker = DratChecker::new(2, false);
    checker.add_original(&[lit(0, true), lit(1, true)]);
    let derived = checker.add_derived(&[big, lit(0, true)]);
    let expected = DratCheckError::VariableOutOfRange {
        variable: big.variable().index(),
        maximum: MAX_DENSE_VARS,
        step: 1,
    };
    if derived != Err(expected) {
        return Err(format!("unexpected add_derived result {derived:?}").into());
    }
    if checker.stats.failures != 1 {
        return Err(format!("expected one failure, got {}", checker.stats.failures).into());
    }
    // A deletion mentioning the variable cannot match a stored clause.
    checker.delete_clause(&[big, lit(0, true)]);
    if checker.stats.missed_deletes != 1 || checker.live_clauses != 1 {
        return Err(format!(
            "deletion changed the database: missed {} live {}",
            checker.stats.missed_deletes, checker.live_clauses
        )
        .into());
    }
    if checker.num_vars != 2 {
        return Err(format!("dense arrays grew to {} variables", checker.num_vars).into());
    }
    Ok(())
}

#[test]
fn test_out_of_envelope_bulk_verifiers_fail_closed() -> TestResult {
    let x = first_out_of_envelope_lit(true)?;
    let not_x = first_out_of_envelope_lit(false)?;
    let clauses = vec![vec![x], vec![not_x]];
    let conclusion_err = DratCheckError::ConclusionFailed(ConcludeFailure::VariableOutOfRange);

    let forward = DratChecker::new(2, false).verify(&clauses, &[]);
    if forward != Err(conclusion_err.clone()) {
        return Err(format!("forward verify: {forward:?}").into());
    }
    let backward = backward::BackwardChecker::new(2, false).verify(&clauses, &[]);
    if backward != Err(conclusion_err) {
        return Err(format!("backward verify: {backward:?}").into());
    }

    // A PR step whose witness leaves the envelope is refused, not checked.
    let a = lit(0, true);
    let steps = vec![ProofStep::AddPr {
        clause: vec![a],
        witness: vec![a, x],
    }];
    let sr = SrChecker::new(2, false).verify(&[vec![a, lit(1, true)]], &steps);
    let Err(DratCheckError::StepFailed { step: 1, source }) = sr else {
        return Err(format!("sr verify: {sr:?}").into());
    };
    if !matches!(*source, DratCheckError::VariableOutOfRange { variable, .. } if variable == MAX_DENSE_VARS)
    {
        return Err(format!("sr step source: {source:?}").into());
    }
    Ok(())
}

#[test]
fn test_new_allocates_every_dense_array() -> TestResult {
    let checker = DratChecker::new(3, false);
    let lengths = [
        checker.assigns.len(),
        checker.reasons.len(),
        checker.conflict_marked.len(),
        checker.watches.len(),
        checker.occ_lists.len(),
        checker.marks.len(),
    ];
    if checker.num_vars != 3 || lengths != [3, 3, 3, 6, 6, 6] {
        return Err(format!("num_vars {} array lengths {lengths:?}", checker.num_vars).into());
    }
    if checker.dense_refusal.is_some() {
        return Err("an allocatable universe must not fail closed".into());
    }
    Ok(())
}

#[test]
fn test_unallocatable_universe_fails_closed_without_panicking() -> TestResult {
    // `vec![None; usize::MAX]` used to panic with a capacity overflow (and
    // `2 * usize::MAX` literal slots cannot even be counted). The checker now
    // starts with an empty universe and fails every conclusion closed.
    let mut checker = DratChecker::new(usize::MAX, false);
    if checker.num_vars != 0 || !checker.assigns.is_empty() || !checker.watches.is_empty() {
        return Err(format!("expected an empty universe, got {}", checker.num_vars).into());
    }
    checker.add_original(&[lit(0, true)]);
    checker.add_original(&[lit(0, false)]);
    let conclusion = checker.conclude_unsat();
    if conclusion != ConcludeResult::Failed(ConcludeFailure::VariableOutOfRange) {
        return Err(format!("expected VariableOutOfRange, got {conclusion:?}").into());
    }
    let clauses = vec![vec![lit(0, true)], vec![lit(0, false)]];
    let forward = DratChecker::new(usize::MAX, false).verify(&clauses, &[]);
    if forward.is_ok() {
        return Err("forward verify accepted an unallocated universe".into());
    }
    let backward = backward::BackwardChecker::new(usize::MAX, false).verify(&clauses, &[]);
    if backward.is_ok() {
        return Err("backward verify accepted an unallocated universe".into());
    }
    Ok(())
}

/// Growth inside the envelope keeps every dense array in step and keeps the
/// existing contents; it is now reserved fallibly before any array is filled.
#[test]
fn test_ensure_capacity_grows_every_array_in_step() -> TestResult {
    let mut checker = DratChecker::new(3, false);
    checker.assign(lit(1, true));
    if checker.ensure_capacity(9).is_err() {
        return Err("growth inside the envelope was refused".into());
    }
    let lengths = [
        checker.assigns.len(),
        checker.reasons.len(),
        checker.conflict_marked.len(),
        checker.watches.len(),
        checker.occ_lists.len(),
        checker.marks.len(),
    ];
    if checker.num_vars != 10 || lengths != [10, 10, 10, 20, 20, 20] {
        return Err(format!("num_vars {} array lengths {lengths:?}", checker.num_vars).into());
    }
    if checker.assigns.get(1) != Some(&Some(true)) || checker.assigns.get(9) != Some(&None) {
        return Err("growth disturbed or mis-filled the assignment array".into());
    }
    Ok(())
}

/// The fallible growth helpers: an unsatisfiable reservation is an error that
/// leaves the vector untouched (it used to be an aborting `resize`), and
/// filling never shrinks.
#[test]
fn test_fallible_growth_helpers() -> TestResult {
    let mut v: Vec<u64> = vec![7];
    if try_reserve_to(&mut v, usize::MAX).is_ok() || v != [7] {
        return Err(format!("impossible reservation succeeded or changed {v:?}").into());
    }
    try_reserve_to(&mut v, 3)?;
    fill_to(&mut v, 3, 0);
    fill_to(&mut v, 1, 9);
    if v != [7, 0, 0] {
        return Err(format!("expected [7, 0, 0], got {v:?}").into());
    }
    if try_filled(0u64, usize::MAX).is_some() {
        return Err("an impossible table allocation succeeded".into());
    }
    Ok(())
}

// -- Allocator refusal inside the envelope --
//
// `ensure_capacity` reserves all six dense arrays before filling any. The
// test-only `reservations_before_refusal` budget makes the k-th reservation
// ask for `usize::MAX` elements, which the real `try_reserve` refuses: the
// same error path an allocator refusal takes.

/// Every dense array length, in a fixed order.
fn dense_lengths(checker: &DratChecker) -> [usize; 6] {
    [
        checker.assigns.len(),
        checker.reasons.len(),
        checker.conflict_marked.len(),
        checker.watches.len(),
        checker.occ_lists.len(),
        checker.marks.len(),
    ]
}

/// A refusal at any of the six reservations leaves the universe and every
/// array length unchanged (so the arrays stay in step), reports an
/// allocation failure rather than an out-of-envelope variable, and the
/// checker can still grow once the allocator cooperates.
#[test]
fn test_allocation_refusal_leaves_dense_arrays_in_step() -> TestResult {
    for granted in 0..6 {
        let mut checker = DratChecker::new(3, false);
        checker.assign(lit(1, true));
        checker.reservations_before_refusal = Some(granted);
        let refused = checker.ensure_capacity(9);
        if refused != Err(DenseRefusal::AllocationFailed) {
            return Err(format!("refusal after {granted} reservations: {refused:?}").into());
        }
        let lengths = dense_lengths(&checker);
        if checker.num_vars != 3 || lengths != [3, 3, 3, 6, 6, 6] {
            return Err(format!(
                "refusal after {granted}: num_vars {} lengths {lengths:?}",
                checker.num_vars
            )
            .into());
        }
        checker.reservations_before_refusal = None;
        checker
            .ensure_capacity(9)
            .map_err(|r| format!("growth after the refusal: {r:?}"))?;
        let lengths = dense_lengths(&checker);
        if checker.num_vars != 10 || lengths != [10, 10, 10, 20, 20, 20] {
            return Err(format!("regrowth lengths {lengths:?}").into());
        }
        if checker.assigns.get(1) != Some(&Some(true)) {
            return Err("the refusal disturbed the assignment array".into());
        }
    }
    Ok(())
}

/// A derived clause whose growth is refused is a failed step naming an
/// allocation failure (not `VariableOutOfRange` for an in-range variable),
/// and the conclusion fails closed.
#[test]
fn test_allocation_refusal_in_add_derived_fails_closed() -> TestResult {
    let mut checker = DratChecker::new(2, false);
    checker.add_original(&[lit(0, true), lit(1, true)]);
    checker.reservations_before_refusal = Some(1);
    let derived = checker.add_derived(&[lit(0, true), lit(5, true)]);
    let expected = DratCheckError::DenseAllocationFailed {
        variable: 5,
        step: 1,
    };
    if derived != Err(expected) {
        return Err(format!("unexpected add_derived result {derived:?}").into());
    }
    if checker.stats.failures != 1 || checker.num_vars != 2 {
        return Err(format!(
            "failures {} num_vars {}",
            checker.stats.failures, checker.num_vars
        )
        .into());
    }
    let conclusion = checker.conclude_unsat();
    if conclusion != ConcludeResult::Failed(ConcludeFailure::StepFailures) {
        return Err(format!("expected StepFailures, got {conclusion:?}").into());
    }
    Ok(())
}

/// An original clause that cannot be stored because growth was refused
/// fails every later conclusion closed, even once the formula is
/// contradictory, with an allocation-failure reason.
#[test]
fn test_allocation_refusal_in_add_original_fails_conclusion_closed() -> TestResult {
    let mut checker = DratChecker::new(2, false);
    checker.reservations_before_refusal = Some(0);
    checker.add_original(&[lit(4, true), lit(0, true)]);
    checker.reservations_before_refusal = None;
    checker.add_original(&[lit(0, true)]);
    checker.add_original(&[lit(0, false)]);
    let conclusion = checker.conclude_unsat();
    if conclusion != ConcludeResult::Failed(ConcludeFailure::DenseAllocationFailed) {
        return Err(format!("expected DenseAllocationFailed, got {conclusion:?}").into());
    }
    Ok(())
}

/// The bulk forward verifier surfaces a refused extension variable as the
/// failed step's allocation-failure source.
#[test]
fn test_allocation_refusal_in_bulk_verify_fails_step() -> TestResult {
    let mut checker = DratChecker::new(2, false);
    checker.reservations_before_refusal = Some(2);
    let clauses = vec![vec![lit(0, true), lit(1, true)]];
    let steps = vec![ProofStep::Add(vec![lit(0, true), lit(7, false)])];
    let result = checker.verify(&clauses, &steps);
    let Err(DratCheckError::StepFailed { step: 1, source }) = result else {
        return Err(format!("forward verify: {result:?}").into());
    };
    if *source
        != (DratCheckError::DenseAllocationFailed {
            variable: 7,
            step: 1,
        })
    {
        return Err(format!("step source: {source:?}").into());
    }
    Ok(())
}

/// Each refusal kind maps to its own step error and conclusion failure.
#[test]
fn test_dense_refusal_diagnostics() {
    assert_eq!(
        DenseRefusal::OutOfEnvelope.step_error(MAX_DENSE_VARS, 3),
        DratCheckError::VariableOutOfRange {
            variable: MAX_DENSE_VARS,
            maximum: MAX_DENSE_VARS,
            step: 3,
        }
    );
    assert_eq!(
        DenseRefusal::AllocationFailed.step_error(9, 3),
        DratCheckError::DenseAllocationFailed {
            variable: 9,
            step: 3
        }
    );
    assert_eq!(
        DenseRefusal::OutOfEnvelope.conclude_failure(),
        ConcludeFailure::VariableOutOfRange
    );
    assert_eq!(
        DenseRefusal::AllocationFailed.conclude_failure(),
        ConcludeFailure::DenseAllocationFailed
    );
}
