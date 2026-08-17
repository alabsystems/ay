// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `branching` to preserve item DefPaths.

/// Binary split branching for `indomain_split` / `indomain_reverse_split`.
///
/// Recursively narrows the domain using range constraints (`<=`, `>`) instead
/// of per-value equality assertions. Each split prunes half the domain.
/// Uses the incremental solver with push/pop for backtracking.
///
/// Propagates `SearchOutcome::Unknown` when ay returns UNKNOWN for any branch
/// and no solution is found (soundness fix for #327).
fn split_branch(
    solver: &mut IncrementalSolver,
    plan: &[SearchPlanEntry],
    depth: usize,
    lo: i64,
    hi: i64,
    reverse: bool,
) -> Result<SearchOutcome, SolverError> {
    if lo > hi {
        return Ok(SearchOutcome::NotFound);
    }

    let entry = &plan[depth];

    if lo == hi {
        let assertion = format!("(assert (= {} {}))\n", entry.smt_var, smt_int(lo));

        let status = solver.check_sat_incremental(&assertion)?;

        let outcome = match status {
            CheckSatResult::Sat => match backtrack_search(solver, plan, depth + 1)? {
                SearchOutcome::Found => {
                    return Ok(SearchOutcome::Found);
                }
                other => other,
            },
            CheckSatResult::Unsat => SearchOutcome::NotFound,
            CheckSatResult::Unknown => SearchOutcome::Unknown,
        };
        solver.pop()?;
        return Ok(outcome);
    }

    let mid = lo + (hi - lo) / 2;

    // Branch order: indomain_split tries <= mid first, reverse_split tries > mid first.
    let branches: [(i64, i64, String); 2] = if !reverse {
        [
            (
                lo,
                mid,
                format!("(assert (<= {} {}))\n", entry.smt_var, smt_int(mid)),
            ),
            (
                mid + 1,
                hi,
                format!("(assert (> {} {}))\n", entry.smt_var, smt_int(mid)),
            ),
        ]
    } else {
        [
            (
                mid + 1,
                hi,
                format!("(assert (> {} {}))\n", entry.smt_var, smt_int(mid)),
            ),
            (
                lo,
                mid,
                format!("(assert (<= {} {}))\n", entry.smt_var, smt_int(mid)),
            ),
        ]
    };

    let mut found_unknown = false;

    for (branch_lo, branch_hi, ref assertion) in &branches {
        let status = solver.check_sat_incremental(assertion)?;

        match status {
            CheckSatResult::Sat => {
                match split_branch(solver, plan, depth, *branch_lo, *branch_hi, reverse)? {
                    SearchOutcome::Found => return Ok(SearchOutcome::Found),
                    SearchOutcome::Unknown => {
                        found_unknown = true;
                        solver.pop()?;
                    }
                    SearchOutcome::NotFound => {
                        solver.pop()?;
                    }
                }
            }
            CheckSatResult::Unsat => {
                solver.pop()?;
            }
            CheckSatResult::Unknown => {
                found_unknown = true;
                solver.pop()?;
            }
        }
    }

    if found_unknown {
        Ok(SearchOutcome::Unknown)
    } else {
        Ok(SearchOutcome::NotFound)
    }
}
