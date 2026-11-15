// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! One-use accounting reservations tied to an immutable proof and term store.
//! Neither census eligibility nor prepayment authenticates a source or proof.

use ay_core::time::Instant;

use super::*;
use crate::bv_blast_solver::retained::work::WorkAllowance;

#[cfg(test)]
mod tests;

mod replay_pricing;
use crate::bv_blast_solver::retained::pricing::ReplayPrice;

#[derive(Clone, Copy)]
struct Entry<'a> {
    position: usize,
    step: &'a ProofStep,
    charge: ExpensiveBvAggregateCharge,
    taken: bool,
    replay_price: Option<ReplayPrice>,
}

impl Entry<'_> {
    fn ordinary_clause(&self) -> Option<&[TermId]> {
        match self.step {
            ProofStep::TheoryLemma {
                kind: TheoryLemmaKind::BvBitBlast | TheoryLemmaKind::BvBitBlastGate { .. },
                clause,
                ..
            } => Some(clause),
            _ => None,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, thiserror::Error)]
pub(crate) enum BvCreditError {
    #[error("BV credit operation already refused or cancelled")]
    Refused,
    #[error("BV credit deadline expired")]
    Deadline,
    #[error("BV census position or charge cannot be represented")]
    Overflow,
    #[error("step {0} has no prepaid expensive-BV entry")]
    UnknownStep(ProofId),
    #[error("step {0} is not an ordinary expensive-BV entry")]
    NonOrdinary(ProofId),
    #[error("ordinary BV credit for step {0} was already consumed")]
    AlreadyTaken(ProofId),
    #[error("ordinary BV credit for step {0} was not consumed")]
    Unconsumed(ProofId),
}

/// A fixed-size census, not yet paid. All expensive families occupy entries.
/// Every entry borrows its step from the census's one proof.
pub(crate) struct ExpensiveBvCreditPlan<'a> {
    terms: &'a TermStore,
    entries: [Option<Entry<'a>>; MAX_EXPENSIVE_BV_LEMMAS_PER_PROOF],
    aggregate: ExpensiveBvAggregateCharge,
}

impl<'a> ExpensiveBvCreditPlan<'a> {
    pub(super) fn new(terms: &'a TermStore) -> Self {
        Self {
            terms,
            entries: [None; MAX_EXPENSIVE_BV_LEMMAS_PER_PROOF],
            aggregate: ExpensiveBvAggregateCharge::default(),
        }
    }

    pub(super) fn record(
        &mut self,
        slot: usize,
        position: usize,
        step: &'a ProofStep,
        work: usize,
        bytes: usize,
    ) {
        // The shared census checks the cap before recording a slot.
        self.entries[slot] = Some(Entry {
            position,
            step,
            charge: ExpensiveBvAggregateCharge { work, bytes },
            taken: false,
            replay_price: None,
        });
    }

    pub(super) fn set_aggregate(&mut self, aggregate: ExpensiveBvAggregateCharge) {
        self.aggregate = aggregate;
    }

    pub(crate) fn aggregate_charge(&self) -> ExpensiveBvAggregateCharge {
        self.aggregate
    }

    /// Consume the plan after exactly one existing aggregate debit succeeds.
    /// The callback is the caller's cumulative budget, never a fresh grant.
    /// Classification's existing outer precharge remains the caller's duty.
    pub(crate) fn prepay(
        self,
        deadline: Instant,
        progress: Progress<'_>,
    ) -> Result<PrepaidBvCredits<'a>, BvCreditError> {
        let mut control = Control {
            deadline,
            refused: false,
        };
        control.check()?;
        for entry in self.entries.iter().flatten() {
            u32::try_from(entry.position).map_err(|_| BvCreditError::Overflow)?;
            u64::try_from(entry.charge.work).map_err(|_| BvCreditError::Overflow)?;
        }
        control.debit(self.aggregate.work, self.aggregate.bytes, progress)?;
        control.debit(0, 0, progress)?;
        Ok(PrepaidBvCredits {
            plan: self,
            control,
        })
    }
}

struct Control {
    deadline: Instant,
    refused: bool,
}

impl Control {
    fn check(&mut self) -> Result<(), BvCreditError> {
        if self.refused {
            return Err(BvCreditError::Refused);
        }
        if Instant::now() >= self.deadline {
            self.refused = true;
            return Err(BvCreditError::Deadline);
        }
        Ok(())
    }

    fn debit(
        &mut self,
        work: usize,
        bytes: usize,
        progress: Progress<'_>,
    ) -> Result<(), BvCreditError> {
        self.check()?;
        // A callback panic caught by a caller leaves this owner poisoned.
        self.refused = true;
        let accepted = progress(work, bytes);
        if Instant::now() >= self.deadline {
            return Err(BvCreditError::Deadline);
        }
        if !accepted {
            return Err(BvCreditError::Refused);
        }
        self.refused = false;
        Ok(())
    }
}

/// Non-Clone credits, preserving all paid entries and the original deadline.
/// Nonordinary entries contribute to payment but cannot issue an allowance.
pub(crate) struct PrepaidBvCredits<'a> {
    plan: ExpensiveBvCreditPlan<'a>,
    control: Control,
}

impl<'a> PrepaidBvCredits<'a> {
    #[cfg(test)]
    pub(crate) fn terms(&self) -> &'a TermStore {
        self.plan.terms
    }
    pub(crate) fn deadline(&self) -> Instant {
        self.control.deadline
    }

    /// The complete ordinary inventory, unchanged by consumption.
    pub(crate) fn ordinary_ids(&self) -> impl Iterator<Item = ProofId> + '_ {
        self.plan.entries.iter().flatten().filter_map(|entry| {
            entry
                .ordinary_clause()
                .map(|_| ProofId(entry.position as u32))
        })
    }

    pub(crate) fn ordinary_count(&self) -> usize {
        self.ordinary_ids().count()
    }

    pub(crate) fn source_step(&self, id: ProofId) -> Option<&'a ProofStep> {
        self.plan
            .entries
            .iter()
            .flatten()
            .find(|entry| entry.position == id.0 as usize && entry.ordinary_clause().is_some())
            .map(|entry| entry.step)
    }

    /// Issue at most once. Any refusal, including a bad ID, poisons the set.
    pub(crate) fn take(
        &mut self,
        id: ProofId,
        progress: Progress<'_>,
    ) -> Result<OrdinaryBvCredit<'a>, BvCreditError> {
        self.control.debit(0, 0, progress)?;
        // Keep the whole owner poisoned until issuance and its final poll finish.
        self.control.refused = true;
        let entry = self
            .plan
            .entries
            .iter_mut()
            .flatten()
            .find(|entry| entry.position == id.0 as usize)
            .ok_or(BvCreditError::UnknownStep(id))?;
        let clause = match entry.step {
            ProofStep::TheoryLemma {
                kind: TheoryLemmaKind::BvBitBlast | TheoryLemmaKind::BvBitBlastGate { .. },
                clause,
                ..
            } => clause.as_slice(),
            _ => return Err(BvCreditError::NonOrdinary(id)),
        };
        if entry.taken {
            return Err(BvCreditError::AlreadyTaken(id));
        }
        entry.taken = true;
        // The aggregate holds native source U AND expression work. The
        // consumed inner allowance gets only expression work: no native
        // reserve floats into RUP/codec credit, and neither piece is refunded.
        let expression_work = match entry.replay_price {
            Some(price) => price.expression_work().ok_or(BvCreditError::Overflow)?,
            None => entry.charge.work,
        };
        let work = u64::try_from(expression_work).map_err(|_| BvCreditError::Overflow)?;
        let step = entry.step;
        let replay_price = entry.replay_price;
        #[cfg(test)]
        let charge = entry.charge;
        self.control.refused = false;
        self.control.debit(0, 0, progress)?;
        Ok(OrdinaryBvCredit {
            #[cfg(test)]
            id,
            step,
            clause,
            terms: self.plan.terms,
            #[cfg(test)]
            charge,
            allowance: WorkAllowance::new(work, self.control.deadline),
            replay_price,
        })
    }

    /// Completion checks accounting consumption, NOT successful proof checking.
    /// The enclosing session still owns its final external cancellation poll.
    pub(crate) fn finish(mut self) -> Result<(), BvCreditError> {
        self.control.check()?;
        for entry in self.plan.entries.iter().flatten() {
            if entry.ordinary_clause().is_some() && !entry.taken {
                return Err(BvCreditError::Unconsumed(ProofId(entry.position as u32)));
            }
        }
        self.control.check()
    }
}

/// An accounting grant bound to one exact source; not checked-proof authority.
/// Its id and charge are observed only by tests: the session already holds
/// the id it asked for, and the charge reaches it as the work allowance.
pub(crate) struct OrdinaryBvCredit<'a> {
    #[cfg(test)]
    id: ProofId,
    step: &'a ProofStep,
    clause: &'a [TermId],
    terms: &'a TermStore,
    #[cfg(test)]
    charge: ExpensiveBvAggregateCharge,
    allowance: WorkAllowance,
    replay_price: Option<ReplayPrice>,
}

impl<'a> OrdinaryBvCredit<'a> {
    #[cfg(test)]
    pub(crate) fn id(&self) -> ProofId {
        self.id
    }
    pub(crate) fn step(&self) -> &'a ProofStep {
        self.step
    }
    pub(crate) fn clause(&self) -> &'a [TermId] {
        self.clause
    }
    pub(crate) fn terms(&self) -> &'a TermStore {
        self.terms
    }
    #[cfg(test)]
    pub(crate) fn charge(&self) -> ExpensiveBvAggregateCharge {
        self.charge
    }
    pub(crate) fn replay_price(&self) -> Option<ReplayPrice> {
        self.replay_price
    }
    pub(crate) fn into_allowance(self) -> WorkAllowance {
        self.allowance
    }
}
