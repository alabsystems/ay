// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Complete small-remainder cases over source-entailed interval bounds.
//!
//! Each branch starts from the same original state. An actual conflict in
//! EVERY integer value of an entailed interval refutes the original state.
//! An inconclusive branch or any resource refusal proves nothing. All cases
//! share the parent checker's original meter and interval work allocation.

use num_traits::ToPrimitive;

use super::*;

const MAX_CASE_ATOMS: usize = 8;
const MAX_CASE_VALUES: usize = 16;
// Additional transient copy, inside the existing per-lemma allocation envelope.
const MAX_CASE_COPY_BYTES: usize = 16 * 1024 * 1024;

impl QueryChecker<'_> {
    pub(super) fn small_remainder_cases_refute(
        &mut self,
        clauses: &[Vec<ClauseLiteral>],
        source: &IntervalState,
        entry_work: u64,
    ) -> Result<bool, BvLiaUnsatAuthenticationError> {
        self.meter.check_entry()?;
        let candidates = self.small_remainder_case_atoms(source, entry_work)?;
        for (atom, (lower, count)) in candidates {
            let mut all_refuted = true;
            for digit in 0..count {
                self.meter.charge(1)?;
                let Some(mut branch) = self.copy_interval_case_state(source, entry_work)? else {
                    return Ok(false);
                };
                let Some(value) = i64::try_from(digit)
                    .ok()
                    .and_then(|digit| lower.checked_add(digit))
                else {
                    return Ok(false);
                };
                self.meter.charge(2)?;
                let value = BigInt::from(value);
                let Some(previous) = branch.bounds.get(&atom) else {
                    return Ok(false);
                };
                let singleton = Interval {
                    lower: Some(value.clone()),
                    upper: Some(value),
                };
                let Some(limbs) = branch
                    .bound_limbs
                    .checked_sub(previous.limbs())
                    .and_then(|remaining| remaining.checked_add(singleton.limbs()))
                else {
                    return Ok(false);
                };
                if limbs > MAX_BOUND_LIMBS {
                    return Ok(false);
                }
                branch.bound_limbs = limbs;
                branch.bounds.insert(atom, singleton);
                match self.propagate_interval_clauses(clauses, &mut branch, entry_work)? {
                    AssumeOutcome::Conflict => {}
                    AssumeOutcome::Decline => return Ok(false),
                    AssumeOutcome::Stable | AssumeOutcome::Changed => {
                        all_refuted = false;
                        break;
                    }
                }
            }
            if all_refuted {
                self.meter.check_entry()?;
                return Ok(self.meter.work.saturating_sub(entry_work) <= MAX_INTERVAL_WORK);
            }
        }
        Ok(false)
    }

    /// Keep at most eight source atoms in deterministic term order. The full
    /// interval, including BOTH endpoints, must fit the small-case envelope.
    fn small_remainder_case_atoms(
        &mut self,
        state: &IntervalState,
        entry_work: u64,
    ) -> Result<BTreeMap<LinearAtom, (i64, usize)>, BvLiaUnsatAuthenticationError> {
        let mut candidates = BTreeMap::new();
        for (&atom, interval) in &state.bounds {
            self.meter.charge(1)?;
            if self.meter.work.saturating_sub(entry_work) > MAX_INTERVAL_WORK {
                return Ok(BTreeMap::new());
            }
            let LinearAtom::Int(term) = atom else {
                continue;
            };
            let TermData::App(Symbol::Named(name), args) = self.terms.get(term) else {
                continue;
            };
            if name != "mod" || args.len() != 2 {
                continue;
            }
            let TermData::Const(Constant::Int(divisor)) = self.terms.get(args[1]) else {
                continue;
            };
            let Some(divisor @ 1..=16) = divisor.to_i64() else {
                continue;
            };
            let Some(lower) = interval.lower.as_ref().and_then(ToPrimitive::to_i64) else {
                continue;
            };
            let Some(upper) = interval.upper.as_ref().and_then(ToPrimitive::to_i64) else {
                continue;
            };
            if lower < 0 || upper >= divisor || upper <= lower {
                continue;
            }
            let Ok(count @ 2..=MAX_CASE_VALUES) = usize::try_from(upper - lower + 1) else {
                continue;
            };
            candidates.insert(atom, (lower, count));
            if candidates.len() > MAX_CASE_ATOMS {
                let _ = candidates.pop_last();
            }
        }
        Ok(candidates)
    }

    /// Precharge the complete clone before any reserve or BigInt copy. The
    /// additional byte cap is conservative for hash-table slack and payloads.
    fn copy_interval_case_state(
        &mut self,
        source: &IntervalState,
        entry_work: u64,
    ) -> Result<Option<IntervalState>, BvLiaUnsatAuthenticationError> {
        let Some(bytes) = source
            .bounds
            .len()
            .checked_mul(512)
            .and_then(|n| n.checked_add(source.booleans.len().checked_mul(128)?))
            .and_then(|n| n.checked_add(usize::try_from(source.bound_limbs).ok()?.checked_mul(8)?))
        else {
            return Ok(None);
        };
        if bytes > MAX_CASE_COPY_BYTES {
            return Ok(None);
        }
        let work = u64::try_from(source.bounds.len())
            .ok()
            .and_then(|n| n.checked_add(u64::try_from(source.booleans.len()).ok()?))
            .and_then(|n| n.checked_add(source.bound_limbs));
        let Some(work) = work else {
            return Ok(None);
        };
        self.meter.charge(work.max(1))?;
        if self.meter.work.saturating_sub(entry_work) > MAX_INTERVAL_WORK {
            return Ok(None);
        }
        let mut copy = IntervalState::default();
        copy.bounds.try_reserve(source.bounds.len()).map_err(|_| {
            BvLiaUnsatAuthenticationError::ResourceLimit {
                resource: "interval case-bound allocation",
            }
        })?;
        copy.booleans
            .try_reserve(source.booleans.len())
            .map_err(|_| BvLiaUnsatAuthenticationError::ResourceLimit {
                resource: "interval case-Boolean allocation",
            })?;
        for (&atom, interval) in &source.bounds {
            self.meter.charge(1)?;
            if self.meter.work.saturating_sub(entry_work) > MAX_INTERVAL_WORK {
                return Ok(None);
            }
            copy.bounds.insert(atom, interval.clone());
        }
        for (&term, &value) in &source.booleans {
            self.meter.charge(1)?;
            if self.meter.work.saturating_sub(entry_work) > MAX_INTERVAL_WORK {
                return Ok(None);
            }
            copy.booleans.insert(term, value);
        }
        copy.bound_limbs = source.bound_limbs;
        Ok(Some(copy))
    }
}

#[cfg(test)]
#[path = "cases_tests.rs"]
mod tests;

#[cfg(test)]
#[path = "cases_adversarial_tests.rs"]
mod adversarial_tests;
