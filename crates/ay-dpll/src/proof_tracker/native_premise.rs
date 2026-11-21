// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Move an independently checked, source-owned unit into the existing ledger.

use super::*;

#[cfg(test)]
mod tests;
use ay_core::kani_compat::hash_table_cost as table;

impl ProofTracker {
    /// Only the native source-offer producer calls this, after its full
    /// original-scope check and before appending any working assertion. Proof
    /// storage is moved; no input/working assertion becomes a free Assume.
    pub(crate) fn append_native_premise(
        &mut self,
        mut fragment: Proof,
        checked: &ay_proof::AuthenticatedPremiseClauses,
        target: TermId,
        progress: &mut dyn FnMut(usize, usize) -> bool,
    ) -> Option<ProofId> {
        if !self.enabled || !progress(0, 0) || !fragment.named_steps.is_empty() {
            return None;
        }
        let count = fragment.steps.len();
        let last = ProofId(u32::try_from(count.checked_sub(1)?).ok()?);
        if checked.clause(last)? != [target] {
            return None;
        }
        let offset = u32::try_from(self.proof.steps.len()).ok()?;
        let result = ProofId(offset.checked_add(last.0)?);
        for (index, step) in fragment.steps.iter().enumerate() {
            if !progress(1, 0) {
                return None;
            }
            let (clause, premises, args): (&[TermId], &[ProofId], &[TermId]) = match step {
                ProofStep::Assume(term) => (std::slice::from_ref(term), &[], &[]),
                ProofStep::Step {
                    clause,
                    premises,
                    args,
                    ..
                } => (clause, premises, args),
                ProofStep::TheoryLemma { clause, .. } => (clause, &[], &[]),
                ProofStep::Resolution {
                    clause,
                    clause1,
                    clause2,
                    ..
                } => {
                    if clause1.0 as usize >= index || clause2.0 as usize >= index {
                        return None;
                    }
                    (clause, &[], &[])
                }
                _ => return None,
            };
            if !progress(
                clause
                    .len()
                    .checked_add(premises.len())?
                    .checked_add(args.len())?,
                0,
            ) || checked.clause(ProofId(u32::try_from(index).ok()?))? != clause
                || premises.iter().any(|id| id.0 as usize >= index)
            {
                return None;
            }
        }
        // Rebase only local, already-validated proof references. Every edge
        // was priced before this mutation and no foreign/anchor scope exists.
        for step in &mut fragment.steps {
            match step {
                ProofStep::Step { premises, .. } => {
                    for id in premises {
                        id.0 = offset.checked_add(id.0)?;
                    }
                }
                ProofStep::Resolution {
                    clause1, clause2, ..
                } => {
                    clause1.0 = offset.checked_add(clause1.0)?;
                    clause2.0 = offset.checked_add(clause2.0)?;
                }
                _ => {}
            }
        }
        let new_len = self.proof.steps.len().checked_add(count)?;
        if new_len > self.proof.steps.capacity() {
            let capacity = self.proof.steps.capacity().checked_mul(2)?.max(new_len);
            if !progress(
                self.proof.steps.len().checked_add(capacity)?,
                capacity
                    .checked_mul(std::mem::size_of::<ProofStep>())?
                    .checked_mul(2)?,
            ) {
                return None;
            }
            self.proof
                .steps
                .try_reserve_exact(capacity.checked_sub(self.proof.steps.len())?)
                .ok()?;
        }
        let reserve = table::reserve_one::<(TermId, ProofId)>(
            self.assumption_map.allocation_size(),
            self.assumption_map.len(),
            self.assumption_map.capacity(),
        )?;
        if !progress(reserve.work, reserve.storage_bytes) {
            return None;
        }
        self.assumption_map.try_reserve(1).ok()?;
        if !progress(
            table::fixed_lookup::<(TermId, ProofId)>(
                self.assumption_map.allocation_size(),
                self.assumption_map.len(),
            )?,
            0,
        ) || !progress(count, 0)
        {
            return None;
        }
        self.proof.steps.extend(fragment.steps);
        self.assumption_map.insert(target, result);
        // A final refusal can leave valid proof data, but no offered working
        // assertion escapes. The original owner stays sticky across retries.
        progress(0, 0).then_some(result)
    }
}
