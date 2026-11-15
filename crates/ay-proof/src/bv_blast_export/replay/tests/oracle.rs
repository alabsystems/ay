// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::*;

// Frozen pre-cancellation replay. Phase extraction is mechanical; old
// collection, set equality, resolution and work/error ordering remain here.

mod clauses;
mod graph;
mod resolution;

fn check_var(proof: &BvBlastProof, var: u32) -> Result<(), BvBlastValidateError> {
    if var < proof.vars.len() as u32 {
        Ok(())
    } else {
        Err(BvBlastValidateError::UndefinedVar(var))
    }
}

fn is_input_role(role: &VarRole) -> bool {
    matches!(
        role,
        VarRole::InputA { .. } | VarRole::InputB { .. } | VarRole::InputLeaf { .. }
    )
}

struct ReplayBudget<'a> {
    limits: &'a BvBlastValidateLimits,
    work: u64,
}

impl ReplayBudget<'_> {
    fn deadline(&self) -> Result<(), BvBlastValidateError> {
        if self
            .limits
            .deadline
            .is_some_and(|deadline| Instant::now() >= deadline)
        {
            Err(BvBlastValidateError::DeadlineExceeded)
        } else {
            Ok(())
        }
    }

    fn count(
        &self,
        resource: &'static str,
        actual: usize,
        limit: usize,
    ) -> Result<(), BvBlastValidateError> {
        if actual <= limit {
            Ok(())
        } else {
            Err(BvBlastValidateError::ResourceLimit {
                resource,
                limit: u64::try_from(limit).unwrap_or(u64::MAX),
                actual: u64::try_from(actual).unwrap_or(u64::MAX),
            })
        }
    }

    fn add_work(&mut self, units: usize) -> Result<(), BvBlastValidateError> {
        let units = u64::try_from(units).unwrap_or(u64::MAX);
        self.work = self.work.saturating_add(units);
        if self.work > self.limits.max_work {
            return Err(BvBlastValidateError::ResourceLimit {
                resource: "validation work",
                limit: self.limits.max_work,
                actual: self.work,
            });
        }
        self.deadline()
    }
}

pub(super) fn validate(
    proof: &BvBlastProof,
    limits: &BvBlastValidateLimits,
) -> Result<(), BvBlastValidateError> {
    let mut budget = ReplayBudget { limits, work: 0 };
    budget.deadline()?;
    if proof.format_version != FORMAT_VERSION {
        return Err(BvBlastValidateError::UnsupportedFormatVersion {
            got: proof.format_version,
            expected: FORMAT_VERSION,
        });
    }
    let equality_width = proof.obligation.width;
    if equality_width == 0 || equality_width > MAX_WIDTH {
        return Err(BvBlastValidateError::MalformedBitEqLayout {
            reason: format!("equality width {equality_width} is outside 1..={MAX_WIDTH}"),
        });
    }
    budget.count("variables", proof.vars.len(), limits.max_vars)?;
    budget.count("bit lemmas", proof.bit_lemmas.len(), limits.max_bit_lemmas)?;
    budget.count("clauses", proof.clauses.len(), limits.max_clauses)?;
    budget.count(
        "resolution steps",
        proof.refutation.steps.len(),
        limits.max_resolution_steps,
    )?;
    // Every certificate id is a u32. Refuse impossible/truncating id spaces
    // even for callers of the compatibility `validate()` entry point.
    budget.count("variables", proof.vars.len(), u32::MAX as usize)?;
    budget.count("clauses", proof.clauses.len(), u32::MAX as usize)?;

    let defined_by = graph::definitions(proof, &mut budget)?;
    let equality = graph::equality(proof, &defined_by, &mut budget)?;
    graph::disequality(proof, &equality, &mut budget)?;
    clauses::validate(proof, &mut budget)?;
    resolution::validate(proof, &mut budget)?;
    budget.deadline()
}

fn resolve(a: &[Lit], b: &[Lit], pivot: u32) -> Option<Vec<Lit>> {
    let a_has_pos = a.contains(&Lit::pos(pivot));
    let a_has_neg = a.contains(&Lit::neg(pivot));
    let b_has_pos = b.contains(&Lit::pos(pivot));
    let b_has_neg = b.contains(&Lit::neg(pivot));

    // Exactly one polarity of the pivot in each, opposite across the two clauses.
    let valid = (a_has_pos && b_has_neg && !a_has_neg && !b_has_pos)
        || (a_has_neg && b_has_pos && !a_has_pos && !b_has_neg);
    if !valid {
        return None;
    }

    let mut out: Vec<Lit> = Vec::new();
    let mut seen: BTreeSet<Lit> = BTreeSet::new();
    for &l in a.iter().chain(b.iter()) {
        if l.var == pivot {
            continue;
        }
        // Tautology check: pivot-free complementary literals make a useless resolvent.
        if seen.contains(&l.negated()) {
            return None;
        }
        if seen.insert(l) {
            out.push(l);
        }
    }
    Some(out)
}

/// Order-insensitive, duplicate-insensitive clause equality.
fn clause_set_eq(a: &[Lit], b: &[Lit]) -> bool {
    let sa: BTreeSet<Lit> = a.iter().copied().collect();
    let sb: BTreeSet<Lit> = b.iter().copied().collect();
    sa == sb
}
