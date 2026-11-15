// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Unit resolution over the exact clauses subsequently loaded into SAT.
//!
//! Only a completed, consistent closure licenses omitting pairs whose Boolean
//! outputs have the same forced polarity. These are logical
//! consequences of the input CNF, never guesses from a candidate assignment.
//! Residual pairs fit the old full-group pair envelope and shared work bound.
//! All small-group behavior is unchanged.

use ay_core::{Sort, TermStore, TseitinResult};

use super::{Application, MAX_GROUP_APPLICATIONS};
use crate::executor::theories::fp::bitblast::backend::{Encoder, Predicate};

#[path = "forced_outputs/residual.rs"]
mod residual;

// A local bookkeeping allowance, shared across this entire plan. It bounds
// new CNF/argument scans and allocation, not recursive encoder construction:
// the existing owning encoder and its stop checks still govern that work.
const MAX_FORCING_WORK: usize = MAX_GROUP_APPLICATIONS * MAX_GROUP_APPLICATIONS;

struct Work(usize);

impl Work {
    fn debit(&mut self, amount: usize) -> bool {
        match self.0.checked_sub(amount) {
            Some(remaining) => {
                self.0 = remaining;
                true
            }
            None => {
                self.0 = 0;
                false
            }
        }
    }
}

enum Closure {
    Uncomputed,
    Unavailable,
    Complete(Vec<i8>),
}

pub(super) struct ForcedOutputs {
    work: Work,
    closure: Closure,
}

impl ForcedOutputs {
    pub(super) fn new() -> Self {
        Self {
            work: Work(MAX_FORCING_WORK),
            closure: Closure::Uncomputed,
        }
    }

    pub(super) fn residual_pairs<E: Encoder>(
        &mut self,
        terms: &TermStore,
        fp: &mut E,
        tseitin: &TseitinResult,
        group: &[Application],
        check: &mut dyn FnMut() -> Result<(), E::Error>,
    ) -> Result<Option<Vec<(usize, usize)>>, E::Error> {
        check()?;
        if matches!(self.closure, Closure::Uncomputed) {
            self.closure = Closure::Unavailable;
            if let Some(values) = unit_closure(tseitin, &mut self.work, check)? {
                self.closure = Closure::Complete(values);
            }
        }
        let Closure::Complete(values) = &self.closure else {
            return Ok(None);
        };
        if group.is_empty() || !self.work.debit(group.len()) {
            return Ok(None);
        }
        let mut counts = [0usize; 3];
        for (term, args) in group {
            check()?;
            // Reserve BOTH the borrowed argument census and the subsequent
            // materialization admissions before traversing or encoding them.
            let Some(cost) = args.len().checked_mul(2) else {
                return Ok(None);
            };
            if !self.work.debit(cost) || terms.sort(*term) != &Sort::Bool {
                return Ok(None);
            }
            let Some(variable) = tseitin.var_for_term(*term) else {
                return Ok(None);
            };
            if variable == 0 || tseitin.term_for_var(variable) != Some(*term) {
                return Ok(None);
            }
            let Some(&value) = values.get(variable as usize) else {
                return Ok(None);
            };
            // Even unforced outputs need the exact term/variable roundtrip.
            counts[match value {
                -1 => 0,
                0 => 1,
                1 => 2,
                _ => return Ok(None),
            }] += 1;
            for &arg in args {
                check()?;
                if !matches!(terms.sort(arg), Sort::FloatingPoint(..) | Sort::BitVec(_)) {
                    return Ok(None);
                }
            }
        }
        let Some(pairs) = residual::pairs(tseitin, values, group, counts, &mut self.work, check)?
        else {
            return Ok(None);
        };
        // Eliding pair clauses must not elide the argument values needed by
        // model reconstruction. Checked self-equality traverses and caches
        // both FP decompositions and supported BV expressions; its resulting
        // (tautological) literal does not need to be asserted.
        for (_, args) in group {
            for &arg in args {
                check()?;
                let predicate = match terms.sort(arg) {
                    Sort::FloatingPoint(..) => Predicate::StructuralEq(arg, arg),
                    Sort::BitVec(_) => Predicate::BvEq(arg, arg),
                    _ => return Ok(None),
                };
                if fp.predicate(predicate)?.is_none() {
                    return Ok(None);
                }
            }
        }
        check()?;
        fp.checkpoint()?;
        Ok(Some(pairs))
    }
}

fn unit_closure<E>(
    tseitin: &TseitinResult,
    work: &mut Work,
    check: &mut dyn FnMut() -> Result<(), E>,
) -> Result<Option<Vec<i8>>, E> {
    check()?;
    let Some(slots) = (tseitin.num_vars as usize).checked_add(1) else {
        return Ok(None);
    };
    if tseitin.num_vars > i32::MAX as u32
        || !work.debit(slots)
        || !work.debit(tseitin.clauses.len())
    {
        return Ok(None);
    }
    // Validate every literal before allocation or inference. In particular,
    // root is NOT an activation literal: the real prepare path sets it to 0.
    for clause in &tseitin.clauses {
        check()?;
        if clause.is_empty() || !work.debit(clause.0.len()) {
            return Ok(None);
        }
        for &lit in &clause.0 {
            check()?;
            if lit
                .checked_abs()
                .is_none_or(|v| v == 0 || v as u32 > tseitin.num_vars)
            {
                return Ok(None);
            }
        }
    }
    check()?;
    let mut values = vec![0; slots];
    // Seed units together after validation, avoiding an extra fixed-point
    // pass when an assertion's activation unit follows all its definitions.
    for clause in &tseitin.clauses {
        check()?;
        if !work.debit(1) {
            return Ok(None);
        }
        if let [lit] = clause.0.as_slice() {
            let slot = &mut values[lit.unsigned_abs() as usize];
            let sign = if *lit > 0 { 1 } else { -1 };
            if *slot != 0 && *slot != sign {
                return Ok(None);
            }
            *slot = sign;
        }
    }
    loop {
        check()?;
        if !work.debit(1) {
            return Ok(None);
        }
        let mut changed = false;
        for clause in &tseitin.clauses {
            check()?;
            let mut candidate = 0;
            let mut multiple = false;
            let mut satisfied = false;
            for &lit in &clause.0 {
                check()?;
                if !work.debit(1) {
                    return Ok(None);
                }
                let value = values[lit.unsigned_abs() as usize];
                if value == if lit > 0 { 1 } else { -1 } {
                    satisfied = true;
                    break;
                }
                if value == 0 {
                    if candidate == 0 {
                        candidate = lit;
                    } else if candidate != lit {
                        multiple = true;
                    }
                }
            }
            if satisfied {
                continue;
            }
            if candidate == 0 {
                return Ok(None);
            }
            // Duplicated same-polarity literals are one unit; p OR NOT p
            // has two different candidates and can never manufacture one.
            if !multiple {
                values[candidate.unsigned_abs() as usize] = if candidate > 0 { 1 } else { -1 };
                changed = true;
            }
        }
        if !changed {
            check()?;
            return Ok(Some(values));
        }
    }
}

#[cfg(test)]
#[path = "forced_outputs/tests.rs"]
mod tests;
