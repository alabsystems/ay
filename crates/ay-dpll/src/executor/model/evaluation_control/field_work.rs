// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Exclusive borrowing of the existing field algorithm ceiling, not a grant.
use super::*;

pub(super) struct FieldWorkState {
    left: usize,
    borrowed: bool,
}
impl Default for FieldWorkState {
    fn default() -> Self {
        Self {
            left: 4_000_000,
            borrowed: false,
        }
    }
}
pub(in crate::executor) struct FieldWorkLoan {
    attempt: EvaluationAttempt,
    granted: usize,
    left: usize,
}
impl EvaluationAttempt {
    pub(in crate::executor) fn borrow_field_work(
        &self,
        available: Option<u64>,
    ) -> Result<FieldWorkLoan, UnknownOrigin> {
        let mut data = lock(&self.data);
        if let Some(origin) = data.origin {
            return Err(origin);
        }
        if data.field_work.borrowed {
            drop(data);
            return Err(self.record_stop(UnknownOrigin::IncompleteSolverLane));
        }
        let original = available.map_or(usize::MAX, |left| {
            usize::try_from(left).unwrap_or(usize::MAX)
        });
        let left = data.field_work.left.min(original);
        if left == 0 {
            drop(data);
            return Err(self.record_stop(UnknownOrigin::DeterministicResourceBudget));
        }
        data.field_work.borrowed = true;
        Ok(FieldWorkLoan {
            attempt: self.clone(),
            granted: left,
            left,
        })
    }
}
impl FieldWorkLoan {
    pub(in crate::executor) fn budget(&mut self) -> &mut usize {
        &mut self.left
    }
}
impl Drop for FieldWorkLoan {
    fn drop(&mut self) {
        let spent = self.granted.saturating_sub(self.left);
        let mut data = lock(&self.attempt.data);
        data.field_work.left = data.field_work.left.saturating_sub(spent);
        data.field_work.borrowed = false;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn field_loan_spends_only_consumed_original_balance_across_clones() {
        let attempt = EvaluationAttempt::default();
        {
            let mut loan = attempt.borrow_field_work(Some(7)).unwrap();
            assert_eq!(*loan.budget(), 7);
            *loan.budget() -= 3;
        }
        let mut next = attempt.clone().borrow_field_work(None).unwrap();
        assert_eq!(*next.budget(), 4_000_000 - 3);
        *next.budget() = 0;
        drop(next);
        assert!(matches!(
            attempt.borrow_field_work(None),
            Err(UnknownOrigin::DeterministicResourceBudget)
        ));
        assert!(EvaluationAttempt::default()
            .borrow_field_work(Some(1))
            .is_ok());
    }

    #[test]
    fn reentry_and_unwind_cannot_refresh_or_revive_field_work() {
        let attempt = EvaluationAttempt::default();
        let shared = attempt.clone();
        let _ = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let mut loan = attempt.borrow_field_work(Some(10)).unwrap();
            *loan.budget() -= 4;
            panic!("actual caller unwind");
        }));
        let mut loan = shared.borrow_field_work(None).unwrap();
        assert_eq!(*loan.budget(), 4_000_000 - 4);
        assert!(matches!(
            attempt.borrow_field_work(Some(9)),
            Err(UnknownOrigin::IncompleteSolverLane)
        ));
        drop(loan);
        assert!(matches!(
            shared.borrow_field_work(None),
            Err(UnknownOrigin::IncompleteSolverLane)
        ));
    }
}
