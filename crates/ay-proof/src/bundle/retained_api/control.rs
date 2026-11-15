// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::diagnostics::{RetainedReadErrorClass, RetainedReadTerminal};
use super::{BundleReCheck, Instant, ProofCheckError, TermId};
use std::mem::size_of;

pub(super) struct Control<'a> {
    deadline: Instant,
    progress: &'a mut dyn FnMut(usize, usize) -> bool,
    stopped: Option<Stop>,
}

#[derive(Clone, Copy)]
enum Stop {
    Resource,
    Deadline,
}

impl Stop {
    fn error(self) -> ProofCheckError {
        match self {
            Self::Resource => ProofCheckError::ResourceLimit,
            Self::Deadline => ProofCheckError::Cancelled,
        }
    }
}

impl Control<'_> {
    pub(super) fn charge(&mut self, work: usize, bytes: usize) -> Result<(), ProofCheckError> {
        if let Some(stop) = self.stopped {
            return Err(stop.error());
        }
        if Instant::now() >= self.deadline {
            self.stopped = Some(Stop::Deadline);
            return Err(ProofCheckError::Cancelled);
        }
        // Poison BEFORE user code: an inner caught panic cannot revive control.
        self.stopped = Some(Stop::Resource);
        if !(self.progress)(work, bytes) {
            return Err(ProofCheckError::ResourceLimit);
        }
        if Instant::now() >= self.deadline {
            self.stopped = Some(Stop::Deadline);
            return Err(ProofCheckError::Cancelled);
        }
        self.stopped = None;
        Ok(())
    }

    pub(super) fn copied_text(&mut self, text: &str) -> Result<String, ProofCheckError> {
        self.charge(text.len(), text.len())?;
        let mut owned = String::new();
        owned
            .try_reserve_exact(text.len())
            .map_err(|_| ProofCheckError::ResourceLimit)?;
        self.charge(0, owned.capacity().saturating_sub(text.len()))?;
        owned.push_str(text);
        Ok(owned)
    }

    pub(super) fn malformed(&mut self, reason: &str) -> Result<ProofCheckError, ProofCheckError> {
        Ok(ProofCheckError::MalformedProofBundle {
            reason: self.copied_text(reason)?,
        })
    }

    pub(super) fn ordered_unique(
        &mut self,
        terms: &[TermId],
    ) -> Result<Vec<TermId>, ProofCheckError> {
        let bytes = terms
            .len()
            .checked_mul(size_of::<TermId>())
            .ok_or(ProofCheckError::ResourceLimit)?;
        self.charge(terms.len(), bytes)?;
        let mut unique = Vec::new();
        unique
            .try_reserve_exact(terms.len())
            .map_err(|_| ProofCheckError::ResourceLimit)?;
        let actual = unique
            .capacity()
            .checked_mul(size_of::<TermId>())
            .ok_or(ProofCheckError::ResourceLimit)?;
        self.charge(0, actual.saturating_sub(bytes))?;
        for &term in terms {
            self.charge(1, 0)?;
            let mut repeated = false;
            for &prior in &unique {
                self.charge(1, 0)?;
                if prior == term {
                    repeated = true;
                    break;
                }
            }
            if !repeated {
                unique.push(term);
            }
        }
        Ok(unique)
    }

    pub(super) fn exact_inventory(
        &mut self,
        checked: &BundleReCheck,
        inventory: &[TermId],
    ) -> Result<(), ProofCheckError> {
        self.charge(1, 0)?;
        if !checked.quality.is_complete() || checked.assume_terms.is_empty() {
            return Err(
                self.malformed("retained exact proof requires complete nonempty assumptions")?
            );
        }
        let mut next = 0usize;
        for (index, term) in checked.assume_terms.iter().enumerate() {
            self.charge(1, 0)?;
            let mut repeated = false;
            for prior in &checked.assume_terms[..index] {
                self.charge(1, 0)?;
                if prior == term {
                    repeated = true;
                    break;
                }
            }
            if !repeated {
                self.charge(1, 0)?;
                if inventory.get(next) != Some(term) {
                    return Err(self.malformed("retained exact first-use inventory mismatch")?);
                }
                next += 1; // At most one increment per existing slice element.
            }
        }
        self.charge(1, 0)?;
        if next != inventory.len() {
            return Err(self.malformed("retained exact inventory has unused or reordered entries")?);
        }
        Ok(())
    }
}

pub(super) fn run<T>(
    deadline: Instant,
    progress: &mut dyn FnMut(usize, usize) -> bool,
    operation: impl FnOnce(&mut Control<'_>) -> Result<T, ProofCheckError>,
) -> Result<T, ProofCheckError> {
    run_observed(deadline, progress, &mut None, operation)
}

// The diagnostic sibling uses the SAME control and existing final observation.
// No new callback, clock sample, debit, error precedence or retry is introduced.
pub(super) fn run_observed<T>(
    deadline: Instant,
    progress: &mut dyn FnMut(usize, usize) -> bool,
    terminal: &mut Option<RetainedReadTerminal>,
    operation: impl FnOnce(&mut Control<'_>) -> Result<T, ProofCheckError>,
) -> Result<T, ProofCheckError> {
    let mut control = Control {
        deadline,
        progress,
        stopped: None,
    };
    if let Err(error) = control.charge(0, 0) {
        // Even an entry refusal must drop the moved pending capture first.
        drop(operation);
        let _ = control.charge(0, 0);
        return Err(error);
    }
    let result = operation(&mut control);
    let already_refused = control.stopped.is_some();
    // Operation-local owners have dropped on both success and semantic failure.
    match control.charge(0, 0) {
        Ok(()) => {
            *terminal = Some(RetainedReadTerminal::Healthy);
            result
        }
        Err(error) => {
            let kind = RetainedReadErrorClass::of(&error);
            *terminal = Some(if already_refused {
                RetainedReadTerminal::AlreadyRefused(kind)
            } else {
                RetainedReadTerminal::NewlyRefused(kind)
            });
            drop(result);
            let _ = control.charge(0, 0);
            Err(error)
        }
    }
}
