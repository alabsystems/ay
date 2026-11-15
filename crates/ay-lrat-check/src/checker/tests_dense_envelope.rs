// Copyright 2026 Andrew Yates
// Tests for the checker's dense variable envelope on the library API: a
// literal beyond `MAX_DENSE_VARS` is refused or ignored instead of sizing the
// dense arrays to its index. The frontends refuse such literals while
// parsing; these cover direct `LratChecker` callers.

use super::*;

/// A derived or trusted clause mentioning a variable beyond the dense
/// envelope is refused instead of sizing the arrays to 2^31 entries.
#[test]
fn test_out_of_envelope_extension_variable_refused() -> Result<(), Box<dyn std::error::Error>> {
    let big = Literal::try_from_dimacs(i32::MAX)?;
    let mut checker = LratChecker::new_lenient(2);
    if !checker.add_original(1, &[lit(1)]) || !checker.add_original(2, &[lit(-1)]) {
        return Err("originals rejected".into());
    }
    if checker.add_derived(3, &[big], &[1, 2]) || checker.add_trusted(4, &[big]) {
        return Err("an out-of-envelope clause was admitted".into());
    }
    if checker.assigns.len() > 2 || checker.stats.failures != 2 {
        return Err(format!(
            "assigns grew to {}, failures {}",
            checker.assigns.len(),
            checker.stats.failures
        )
        .into());
    }
    Ok(())
}

/// A superset deletion may name a literal far beyond every stored literal;
/// it cannot match anything, so it neither grows `marks` nor blocks deletion.
#[test]
fn test_delete_verified_out_of_range_extra_literal() -> Result<(), Box<dyn std::error::Error>> {
    let big = Literal::try_from_dimacs(i32::MAX)?;
    let mut checker = LratChecker::new(2);
    if !checker.add_original(1, &[lit(1), lit(2)]) {
        return Err("original rejected".into());
    }
    let marks_before = checker.marks.len();
    if !checker.delete_verified(1, &[lit(2), big, lit(1)]) {
        return Err("superset deletion with an out-of-range literal failed".into());
    }
    if checker.marks.len() != marks_before {
        return Err(format!("marks grew {marks_before} -> {}", checker.marks.len()).into());
    }
    Ok(())
}

/// The dense arrays are allocated through `try_filled`: two slots per
/// variable for the literal-indexed arrays, and an allocator refusal is an
/// error the constructor turns into a failed checker (it used to be an
/// aborting `vec![..; n]`).
#[test]
fn test_dense_arrays_allocated_fallibly() -> Result<(), Box<dyn std::error::Error>> {
    let checker = LratChecker::new(3);
    let lengths = [
        checker.assigns.len(),
        checker.marks.len(),
        checker.checked_lits.len(),
        checker.occ_lists.len(),
    ];
    if lengths != [3, 6, 6, 6] || checker.failed {
        return Err(format!("array lengths {lengths:?}, failed {}", checker.failed).into());
    }
    if try_filled(0u64, usize::MAX).is_ok() {
        return Err("an impossible allocation succeeded".into());
    }
    if try_filled(Vec::<u64>::new(), 2)? != vec![Vec::<u64>::new(); 2] {
        return Err("try_filled did not fill".into());
    }
    Ok(())
}

/// An allocator refusal of the dense arrays (here a real `try_reserve`
/// failure from an impossible size) yields a refused checker: empty
/// universe, already failed with one recorded failure, and no operation or
/// conclusion succeeds. It used to abort the process.
#[test]
fn test_dense_allocation_refusal_yields_failed_checker() -> Result<(), Box<dyn std::error::Error>> {
    let allocation = DenseArrays::try_alloc(usize::MAX, usize::MAX);
    if allocation.is_ok() {
        return Err("an impossible dense allocation succeeded".into());
    }
    for strict in [true, false] {
        let mut checker = LratChecker::from_allocation(3, allocation_refusal()?, strict);
        if !checker.failed || checker.stats.failures != 1 || checker.num_vars != 0 {
            return Err(format!(
                "strict {strict}: failed {} failures {} num_vars {}",
                checker.failed, checker.stats.failures, checker.num_vars
            )
            .into());
        }
        let lengths = [
            checker.assigns.len(),
            checker.marks.len(),
            checker.checked_lits.len(),
            checker.occ_lists.len(),
        ];
        if lengths != [0; 4] {
            return Err(format!("refused checker kept arrays {lengths:?}").into());
        }
        let a = Literal::try_from_dimacs(1)?;
        if checker.add_original(1, &[a]) || checker.add_original(2, &[a.negated()]) {
            return Err(format!("strict {strict}: refused checker accepted a clause").into());
        }
        if checker.add_derived(3, &[], &[1, 2]) {
            return Err(format!("strict {strict}: refused checker derived a clause").into());
        }
        let conclusion = checker.conclude_unsat();
        if matches!(conclusion, ConcludeResult::Verified) {
            return Err(format!("strict {strict}: refused checker verified UNSAT").into());
        }
    }
    Ok(())
}

/// A real allocator-refusal error, from a reservation no allocator can meet.
fn allocation_refusal() -> Result<Result<DenseArrays, TryReserveError>, Box<dyn std::error::Error>>
{
    match Vec::<u8>::new().try_reserve(usize::MAX) {
        Ok(()) => Err("an impossible reservation succeeded".into()),
        Err(error) => Ok(Err(error)),
    }
}
