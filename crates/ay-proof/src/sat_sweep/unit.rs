// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The sweep's cheapest proof: a candidate lemma that follows by unit
//! propagation alone is recorded as one RUP step, without a solver call.

use ay_sat::Literal;

/// Unit propagation alone over `clauses` (over `vars` variables): the clauses
/// that propagated, in
/// order, ending with the one every literal of which is false; `None` when
/// propagation reaches no conflict within a few passes.
pub(super) fn unit_refutation(clauses: &[Vec<Literal>], vars: usize) -> Option<Vec<usize>> {
    unit_refutation_counted(clauses, vars).0
}

/// [`unit_refutation`], and the literals it read (`work.rs`).
pub(super) fn unit_refutation_counted(
    clauses: &[Vec<Literal>],
    vars: usize,
) -> (Option<Vec<usize>>, u64) {
    const MAX_PASSES: usize = 64;
    let mut read = 0_u64;
    let mut value: Vec<Option<bool>> = vec![None; vars];
    let mut settled = vec![false; clauses.len()];
    let mut used = Vec::new();
    for _ in 0..MAX_PASSES {
        let mut changed = false;
        for (index, clause) in clauses.iter().enumerate() {
            if settled[index] {
                continue;
            }
            let mut open: Option<Literal> = None;
            let mut open_count = 0_usize;
            let mut satisfied = false;
            for literal in clause {
                read += 1;
                match value[literal.variable().index()] {
                    Some(assigned) if assigned == literal.is_positive() => {
                        satisfied = true;
                        break;
                    }
                    Some(_) => {}
                    None => {
                        open_count += 1;
                        open = Some(*literal);
                    }
                }
            }
            if satisfied {
                settled[index] = true;
                continue;
            }
            match (open_count, open) {
                (0, _) => {
                    used.push(index);
                    return (Some(used), read);
                }
                (1, Some(unit)) => {
                    value[unit.variable().index()] = Some(unit.is_positive());
                    settled[index] = true;
                    used.push(index);
                    changed = true;
                }
                _ => {}
            }
        }
        if !changed {
            return (None, read);
        }
    }
    (None, read)
}
