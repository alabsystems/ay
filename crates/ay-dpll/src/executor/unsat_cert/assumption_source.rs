// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact assumption binding and external literal-false source authority.

use super::*;
use ay_frontend::command::{Constant as FrontendConstant, Term as FrontendTerm};
use ay_frontend::Command;

fn command_has_literal_false_assumption(
    command: &Command,
    assumption_ids: &[TermId],
    false_term: TermId,
) -> bool {
    let Command::CheckSatAssuming(assumptions) = command else {
        return false;
    };
    assumptions.len() == assumption_ids.len()
        && assumptions.iter().zip(assumption_ids).any(|(term, &id)| {
            id == false_term
                && matches!(
                    crate::executor::proof_surface_syntax::strip_frontend_annotations(term),
                    FrontendTerm::Const(FrontendConstant::False)
                )
        })
}

impl Executor {
    /// Bind the exact caller-supplied assumptions before entering a solve.
    ///
    /// Rebinding is accepted only when it is byte-for-byte identical. This lets
    /// narrow wrapper layers be idempotent without permitting an internal retry
    /// to change the authority of an already-started public query.
    pub(crate) fn bind_unsat_query_assumptions(&mut self, assumptions: &[TermId]) {
        let pending = self.pending_nested_array_bool_bv_unsat.take();
        // Binding is a pre-solve authority mutation. Even an idempotent or
        // rejected late bind must retire a previously minted certificate.
        // Pending finite-array evidence is narrower: a truly idempotent bind
        // may preserve it, but only after its whole term snapshot and exact
        // ordered roots are rechecked below.
        self.last_unsat_certificate = None;
        let Some(assumption_entries) = UnsatQueryEpoch::capture_entries(self, assumptions) else {
            self.unsat_query_epoch = None;
            return;
        };
        let Some(epoch) = self.unsat_query_epoch.as_ref() else {
            return;
        };
        if !epoch.is_current(self) {
            self.unsat_query_epoch = None;
            return;
        }
        let idempotent = matches!(
            (&epoch.assumptions, &epoch.assumption_entries),
            (Some(bound), Some(bound_entries))
                if bound == assumptions && bound_entries == &assumption_entries
        );
        let retire = match (&epoch.assumptions, &epoch.assumption_entries) {
            (Some(bound), Some(_)) if bound != assumptions => {
                // Preserve the first binding. Certification will reject the
                // wrapper's later, mismatching assumption slice.
                false
            }
            (Some(_), Some(bound_entries)) => bound_entries != &assumption_entries,
            (None, None) => false,
            _ => true,
        };
        if retire {
            self.unsat_query_epoch = None;
            return;
        }
        if let Some(epoch) = self.unsat_query_epoch.as_mut() {
            if epoch.assumptions.is_none() {
                epoch.assumptions = Some(assumptions.to_vec());
                epoch.assumption_entries = Some(assumption_entries);
            }
        }
        if idempotent
            && pending.as_ref().is_some_and(|candidate| {
                self.pending_nested_array_bool_bv_unsat_is_current(candidate, assumptions)
            })
        {
            self.pending_nested_array_bool_bv_unsat = pending;
        }
    }

    /// Bind exact assumption handles submitted at the public native API boundary.
    pub(crate) fn bind_native_query_assumptions(&mut self, assumptions: &[TermId]) {
        self.bind_unsat_query_assumptions(assumptions);
        if assumptions.contains(&self.ctx.terms.false_term()) {
            self.bind_unsat_query_literal_false_assumption_source(assumptions);
        }
    }

    /// Bind assumptions originating in the current parsed text command.
    pub(in crate::executor) fn bind_authored_unsat_query_assumptions(
        &mut self,
        assumptions: &[TermId],
        command: &Command,
    ) {
        self.bind_unsat_query_assumptions(assumptions);
        let false_term = self.ctx.terms.false_term();
        if command_has_literal_false_assumption(command, assumptions, false_term) {
            self.bind_unsat_query_literal_false_assumption_source(assumptions);
        }
    }

    fn bind_unsat_query_literal_false_assumption_source(&mut self, assumptions: &[TermId]) {
        let false_term = self.ctx.terms.false_term();
        let state = self.unsat_query_epoch.as_ref().map(|epoch| {
            let current = epoch.is_current(self)
                && epoch.assumptions.as_deref() == Some(assumptions)
                && assumptions.contains(&false_term);
            (current, current && epoch.literal_false_assumption_source)
        });
        if matches!(state, Some((true, true))) {
            return;
        }
        self.last_unsat_certificate = None;
        self.pending_nested_array_bool_bv_unsat = None;
        if !matches!(state, Some((true, false))) {
            self.unsat_query_epoch = None;
            return;
        }
        if let Some(epoch) = self.unsat_query_epoch.as_mut() {
            epoch.literal_false_assumption_source = true;
        }
    }

    /// Whether the current query has exact parsed/native literal-false authority.
    pub(in crate::executor) fn unsat_query_has_literal_false_assumption_source(&self) -> bool {
        let false_term = self.ctx.terms.false_term();
        self.unsat_query_epoch.as_ref().is_some_and(|epoch| {
            epoch.is_current(self)
                && epoch.literal_false_assumption_source
                && epoch
                    .assumptions
                    .as_deref()
                    .is_some_and(|assumptions| assumptions.contains(&false_term))
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn literal_false_source_is_position_aligned_and_query_scoped() {
        let mut executor = Executor::new();
        let false_term = executor.ctx.terms.false_term();
        let proposition = executor
            .ctx
            .terms
            .mk_var("assumption-source-p", CoreSort::Bool);

        executor.begin_public_solve(false);
        executor.bind_authored_unsat_query_assumptions(
            &[false_term, proposition],
            &Command::CheckSatAssuming(vec![
                FrontendTerm::Annotated(
                    Box::new(FrontendTerm::Const(FrontendConstant::False)),
                    Vec::new(),
                ),
                FrontendTerm::Symbol("assumption-source-p".to_string()),
            ]),
        );
        assert!(executor.unsat_query_has_literal_false_assumption_source());

        executor.begin_public_solve(false);
        executor.bind_authored_unsat_query_assumptions(
            &[false_term],
            &Command::CheckSatAssuming(vec![FrontendTerm::App(
                "not".to_string(),
                vec![FrontendTerm::Const(FrontendConstant::True)],
            )]),
        );
        assert!(!executor.unsat_query_has_literal_false_assumption_source());

        executor.begin_public_solve(false);
        executor.bind_authored_unsat_query_assumptions(
            &[proposition, false_term],
            &Command::CheckSatAssuming(vec![
                FrontendTerm::Const(FrontendConstant::False),
                FrontendTerm::Symbol("assumption-source-p".to_string()),
            ]),
        );
        assert!(!executor.unsat_query_has_literal_false_assumption_source());
    }
}
