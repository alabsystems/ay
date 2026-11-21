// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Sequence constants use the same live nominal carrier as constructors and
//! declarations. Borrowed sort work is admitted before contextual lowering.

use std::{mem::size_of, sync::Arc};

use super::declaration_budget::Meter;
use super::sort_inspection::{admit_lowering, admit_shape};
use crate::api::{
    NativeDeclarationBudget as Budget, NativeDeclarationError as Error,
    NativeDeclarationLimits as Limits, NativeDeclarationRefusal as Refusal, Solver, SolverError,
    Sort, Term,
};

impl Solver {
    /// Construct an empty sequence in the current live element carrier.
    /// A datatype definition must already be declared. Native uninterpreted
    /// sorts retain their existing construction semantics.
    pub fn try_seq_empty(&mut self, element_sort: Sort) -> Result<Term, SolverError> {
        let mut budget = Budget::new(Limits::new(64 * 1024 * 1024, 64 * 1024 * 1024, 128));
        self.try_seq_empty_with_progress(&element_sort, &mut budget, &mut |_, _| true)
            .map_err(|error| match error {
                Error::Declaration(error) => error,
                Error::Refused(refusal) => SolverError::InvalidArgument {
                    operation: "seq.empty",
                    message: refusal.to_string(),
                },
            })
    }

    /// Admit all physical input and live-sort copies through the caller's
    /// cumulative owner. No handle is published on refusal or cancellation;
    /// reservations or an inert interned entry can remain if the terminal poll
    /// stops after commit. An assertion pop cannot renew this borrowed budget.
    pub fn try_seq_empty_with_progress(
        &mut self,
        element_sort: &Sort,
        budget: &mut Budget,
        progress: &mut dyn FnMut(usize, usize) -> bool,
    ) -> Result<Term, Error> {
        let mut meter = Meter {
            budget,
            progress,
            interrupt: Arc::clone(&self.interrupt),
            deadline: self.executor.current_solve_deadline(),
        };
        meter.pay(0, 0, 0)?;
        admit_shape(element_sort, &mut meter, 1)?;
        admit_lowering(self, element_sort, &mut meter, 1)?;
        meter.pay(8, size_of::<ay_core::TermData>().saturating_add(128), 0)?;
        // An admission fence precedes contextual lowering. Controlled interning
        // continues polling this SAME owner through collisions and reservation;
        // no caller code can mutate the solver through this exclusive borrow.
        meter.pay(0, 0, 0)?;
        let element_sort = self.lower_live_sort(element_sort);
        let sort = Sort::seq(element_sort);
        let input = ay_core::TermData::App(ay_core::term::Symbol::named("seq.empty"), vec![]);
        let mut precise_error = None;
        let result = self.terms_mut().try_intern_with_progress(
            &input,
            &sort,
            &mut |work, bytes| match meter.pay(work, bytes, 0) {
                Ok(()) => true,
                Err(error) => {
                    precise_error = Some(error);
                    false
                }
            },
        );
        let result = match result {
            Ok(term) => term,
            Err(error) => {
                if let Some(error) = precise_error {
                    return Err(error);
                }
                return meter.fail(match error {
                    ay_core::term::ControlledTermInternError::ResourceLimit => Refusal::Allocation,
                    _ => Refusal::UnsupportedSource {
                        shape: "empty sequence controlled construction refused its live sort",
                    },
                });
            }
        };
        Ok(self.wrap_term(result))
    }
}
