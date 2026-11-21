// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Input ownership for the common EUF planner/emitter. An owned input is a
//! disposable candidate, never the caller's retained authority-bearing proof.

use super::*;
use ay_core::ProofStep;

pub(super) enum ProofInput<'a> {
    Borrowed(&'a Proof),
    Owned(Proof),
}

impl ProofInput<'_> {
    pub(super) fn proof(&self) -> &Proof {
        match self {
            Self::Borrowed(proof) => proof,
            Self::Owned(proof) => proof,
        }
    }

    pub(super) fn is_owned(&self) -> bool {
        matches!(self, Self::Owned(_))
    }

    pub(super) fn unchanged(self) -> Option<Proof> {
        match self {
            Self::Borrowed(_) => None,
            Self::Owned(proof) => Some(proof),
        }
    }
}

enum Steps<'a> {
    Borrowed(std::slice::Iter<'a, ProofStep>),
    Owned(std::vec::IntoIter<ProofStep>),
}

pub(super) enum InputStep<'a> {
    Borrowed(&'a ProofStep),
    Owned(ProofStep),
}

impl InputStep<'_> {
    pub(super) fn into_owned(self) -> ProofStep {
        match self {
            Self::Borrowed(step) => step.clone(),
            Self::Owned(step) => step,
        }
    }
}

impl<'a> Iterator for Steps<'a> {
    type Item = InputStep<'a>;
    fn next(&mut self) -> Option<Self::Item> {
        match self {
            Self::Borrowed(steps) => steps.next().map(InputStep::Borrowed),
            Self::Owned(steps) => steps.next().map(InputStep::Owned),
        }
    }
}

enum AssumeSource<'a> {
    Borrowed(&'a [ProofStep]),
    Owned(Vec<bool>),
}

impl AssumeSource<'_> {
    fn permits(&self, index: usize) -> bool {
        match self {
            Self::Borrowed(steps) => matches!(steps.get(index), Some(ProofStep::Assume(_))),
            Self::Owned(mask) => mask.get(index).copied().unwrap_or(false),
        }
    }
}

pub(super) struct Assembly<'a> {
    pub(super) proof: Proof,
    steps: Steps<'a>,
    assumes: AssumeSource<'a>,
    borrowed_names: Option<&'a HashMap<String, ProofId>>,
}

impl<'a> ProofInput<'a> {
    /// The caller has prepaid the entire new steps backing and fresh emission
    /// payload. Only owned mode needs a new original-Assume mask. Capture it
    /// before taking any rows, and retain the entire owned Proof container.
    pub(super) fn assembly(
        self,
        steps_bound: usize,
        budget: &mut SurgeryPlanningBudget,
    ) -> Option<Assembly<'a>> {
        match self {
            Self::Borrowed(input) => {
                let mut proof = Proof::new();
                proof.steps.try_reserve_exact(steps_bound).ok()?;
                Some(Assembly {
                    proof,
                    steps: Steps::Borrowed(input.steps.iter()),
                    assumes: AssumeSource::Borrowed(&input.steps),
                    borrowed_names: Some(&input.named_steps),
                })
            }
            Self::Owned(mut proof) => {
                let n = proof.steps.len();
                if !budget.admit_owned(
                    n.checked_add(proof.named_steps.allocation_size())?,
                    n.checked_mul(2)?,
                ) {
                    return None;
                }
                let mut mask = Vec::new();
                mask.try_reserve_exact(n).ok()?;
                for step in &proof.steps {
                    if !budget.spend_work(1) {
                        return None;
                    }
                    mask.push(matches!(step, ProofStep::Assume(_)));
                }
                let mut output = Vec::new();
                output.try_reserve_exact(steps_bound).ok()?;
                if !budget.poll_stop() {
                    return None;
                }
                let input = std::mem::replace(&mut proof.steps, output);
                Some(Assembly {
                    proof,
                    steps: Steps::Owned(input.into_iter()),
                    assumes: AssumeSource::Owned(mask),
                    borrowed_names: None,
                })
            }
        }
    }
}

impl<'a> Assembly<'a> {
    pub(super) fn next(&mut self) -> Option<InputStep<'a>> {
        self.steps.next()
    }

    /// The owned named map and its String keys are retained, never cloned or
    /// rehashed. Both inputs sanitize names against the ORIGINAL Assume rows.
    pub(super) fn finish(
        mut self,
        remap: &[ProofId],
        budget: &mut SurgeryPlanningBudget,
    ) -> Option<Proof> {
        let count = self
            .borrowed_names
            .map_or(self.proof.named_steps.len(), HashMap::len);
        if !budget.spend_work(count.saturating_add(1)) {
            return None;
        }
        if let Some(names) = self.borrowed_names {
            self.proof.named_steps = names.clone();
        }
        self.proof.named_steps.retain(|_, id| {
            let old = id.0 as usize;
            if !self.assumes.permits(old) {
                return false;
            }
            let Some(new) = remap.get(old) else {
                return false;
            };
            *id = *new;
            true
        });
        budget.poll_stop().then_some(self.proof)
    }
}
