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

/// Whether the current query's `check-sat-assuming` literals are known as
/// the caller wrote them, each respelled only by `normalize_premise_surface`
/// (with and without its `!` annotations).
///
/// Only a parsed text command supplies them
/// ([`Executor::bind_authored_unsat_query_assumptions`]). The elaborated
/// assumption terms are NOT a substitute: elaboration rewrites
/// `(not (distinct a b))` to `(= a b)`, drops a `let`, folds `(and p true)`
/// to `p`, and an external checker matches an `assume` against the literal it
/// parsed, not against AY's elaboration.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) enum AuthoredAssumptionSurfaces {
    /// No parsed command supplied them (a plain `check-sat`, or a native API
    /// query whose assumptions are term handles with no surface syntax).
    Unbound,
    /// The normalized surfaces of the literals of the one parsed command that
    /// bound this query's assumptions.
    Bound(Vec<String>),
    /// Two parsed commands bound the same assumption handles with different
    /// text; which one the query answers is not known, so neither is used.
    Conflicting,
}

impl Executor {
    /// Exact external query assumptions, excluding named-core redirects and
    /// minimizer probes that may overwrite the operational last_assumptions.
    pub(crate) fn native_proof_query_assumptions(&self) -> Option<&[TermId]> {
        self.last_proof()?;
        self.unsat_query_epoch.as_ref()?.assumptions.as_deref()
    }

    /// The assumptions the CALLER supplied to the current public query:
    /// `Some(&[])` for a plain `check-sat`, the `check-sat-assuming` literals
    /// otherwise, `None` when no current query epoch records them.
    ///
    /// Not `last_assumptions`: that also carries the solver's own assumption
    /// literals (named-core tracking solves a plain `check-sat` under
    /// `:produce-unsat-cores` as an assumption query over the named
    /// assertions), and those are not premises the problem states.
    pub(in crate::executor) fn unsat_query_caller_assumptions(&self) -> Option<&[TermId]> {
        let epoch = self.unsat_query_epoch.as_ref()?;
        Some(epoch.assumptions.as_deref().unwrap_or(&[]))
    }

    /// Bind the exact caller-supplied assumptions before entering a solve.
    ///
    /// Rebinding is accepted only when it is byte-for-byte identical. This lets
    /// narrow wrapper layers be idempotent without permitting an internal retry
    /// to change the authority of an already-started public query.
    pub(crate) fn bind_unsat_query_assumptions(&mut self, assumptions: &[TermId]) {
        let pending = self.pending_nested_array_bool_bv_unsat.take();
        let pending_bv_lia = self.pending_bounded_bv_lia_unsat.take();
        self.clear_strict_native_bundle_states();
        // Binding is a pre-solve authority mutation. Even an idempotent or
        // rejected late bind must retire a previously minted certificate.
        // Pending finite-array evidence is narrower: a truly idempotent bind
        // may preserve it, but only after its whole term snapshot and exact
        // ordered roots are rechecked below.
        self.last_unsat_certificate = None;
        let Some(assumption_entries) = UnsatQueryEpoch::capture_entries(self, assumptions) else {
            if ay_core::misc_cli_flags().debug_cert {
                eprintln!("CERT/epoch cleared: bind_unsat_query_assumptions decline");
            }
            self.unsat_query_epoch = None;
            return;
        };
        let Some(epoch) = self.unsat_query_epoch.as_ref() else {
            return;
        };
        if !epoch.is_current(self) {
            if ay_core::misc_cli_flags().debug_cert {
                eprintln!(
                    "CERT/epoch cleared: bind stale (not current) exec={:p}",
                    std::ptr::from_ref(self)
                );
            }
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
            if ay_core::misc_cli_flags().debug_cert {
                eprintln!(
                    "CERT/epoch cleared: bind retire (assumption change) exec={:p}",
                    std::ptr::from_ref(self)
                );
            }
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
        if idempotent
            && pending_bv_lia.as_ref().is_some_and(|candidate| {
                self.pending_bounded_bv_lia_unsat_is_current(candidate, assumptions)
            })
        {
            self.pending_bounded_bv_lia_unsat = pending_bv_lia;
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
        self.bind_unsat_query_authored_assumption_surfaces(assumptions, command);
    }

    /// Record the caller's `check-sat-assuming` literals as written, for the
    /// premise comparison of `authored_premise_surfaces`. Recorded only on the
    /// current epoch whose bound assumptions are exactly `assumptions`, and
    /// only when the command supplied one literal per assumption handle.
    fn bind_unsat_query_authored_assumption_surfaces(
        &mut self,
        assumptions: &[TermId],
        command: &Command,
    ) {
        let Command::CheckSatAssuming(literals) = command else {
            return;
        };
        let bound = self.unsat_query_epoch.as_ref().is_some_and(|epoch| {
            epoch.is_current(self) && epoch.assumptions.as_deref() == Some(assumptions)
        });
        if !bound || literals.len() != assumptions.len() {
            return;
        }
        let mut surfaces = Vec::with_capacity(literals.len() * 2);
        for literal in literals {
            surfaces.push(crate::executor::normalize_premise_surface(
                &crate::executor::proof_surface_syntax::format_authored_frontend_term(literal),
            ));
            surfaces.push(crate::executor::normalize_premise_surface(
                &crate::executor::proof_surface_syntax::format_frontend_term(literal),
            ));
        }
        let Some(epoch) = self.unsat_query_epoch.as_mut() else {
            return;
        };
        epoch.authored_assumption_surfaces = match &epoch.authored_assumption_surfaces {
            AuthoredAssumptionSurfaces::Unbound => AuthoredAssumptionSurfaces::Bound(surfaces),
            AuthoredAssumptionSurfaces::Bound(existing) if *existing == surfaces => {
                AuthoredAssumptionSurfaces::Bound(surfaces)
            }
            AuthoredAssumptionSurfaces::Bound(_) | AuthoredAssumptionSurfaces::Conflicting => {
                AuthoredAssumptionSurfaces::Conflicting
            }
        };
    }

    /// The normalized surfaces of the caller's `check-sat-assuming` literals
    /// as written, when the current query's assumptions came from exactly one
    /// parsed command; `None` otherwise (no current epoch, a native API
    /// query, or two conflicting parsed bindings).
    pub(in crate::executor) fn unsat_query_authored_assumption_surfaces(
        &self,
    ) -> Option<&[String]> {
        let epoch = self.unsat_query_epoch.as_ref()?;
        match &epoch.authored_assumption_surfaces {
            AuthoredAssumptionSurfaces::Bound(surfaces) => Some(surfaces),
            AuthoredAssumptionSurfaces::Unbound | AuthoredAssumptionSurfaces::Conflicting => None,
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
        self.pending_bounded_bv_lia_unsat = None;
        self.clear_strict_native_bundle_states();
        if !matches!(state, Some((true, false))) {
            if ay_core::misc_cli_flags().debug_cert {
                eprintln!(
                    "CERT/epoch cleared: literal-false-source retire exec={:p}",
                    std::ptr::from_ref(self)
                );
            }
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

    /// The premise reference holds the caller's literal AS WRITTEN, never its
    /// elaborated term, and a query whose assumptions have no surface syntax
    /// has no complete reference at all.
    #[test]
    fn assumption_surfaces_are_the_literals_as_written_and_query_scoped() {
        let mut executor = Executor::new();
        let a = executor.ctx.terms.mk_var("surface-a", CoreSort::Bool);
        let b = executor.ctx.terms.mk_var("surface-b", CoreSort::Bool);
        // The elaborated handle of `(not (distinct surface-a surface-b))`.
        let elaborated = executor.ctx.terms.mk_eq(a, b);
        let written = FrontendTerm::App(
            "not".to_string(),
            vec![FrontendTerm::App(
                "distinct".to_string(),
                vec![
                    FrontendTerm::Symbol("surface-a".to_string()),
                    FrontendTerm::Symbol("surface-b".to_string()),
                ],
            )],
        );

        executor.begin_public_solve(false);
        executor.bind_authored_unsat_query_assumptions(
            &[elaborated],
            &Command::CheckSatAssuming(vec![written.clone()]),
        );
        let surfaces = executor
            .authored_premise_surfaces()
            .expect("a parsed literal is a complete reference");
        assert!(surfaces.contains("(not (distinct surface-a surface-b))"));
        assert!(
            !surfaces.contains(&crate::executor::normalize_premise_surface(
                &ay_proof::format_term_alethe(&executor.ctx.terms, elaborated)
            )),
            "the elaborated form must not stand in for the literal as written"
        );

        // A second parsed binding of the same handles with other text leaves
        // the query's literals unknown.
        executor.bind_authored_unsat_query_assumptions(
            &[elaborated],
            &Command::CheckSatAssuming(vec![FrontendTerm::App(
                "=".to_string(),
                vec![
                    FrontendTerm::Symbol("surface-a".to_string()),
                    FrontendTerm::Symbol("surface-b".to_string()),
                ],
            )]),
        );
        assert!(executor.authored_premise_surfaces().is_none());

        // A new query forgets the previous query's literals, and native
        // handles carry no surface syntax.
        executor.begin_public_solve(false);
        executor.bind_native_query_assumptions(&[elaborated]);
        assert!(executor
            .unsat_query_authored_assumption_surfaces()
            .is_none());
        assert!(executor.authored_premise_surfaces().is_none());

        // A plain query has no literals to know.
        executor.begin_public_solve(false);
        executor.bind_unsat_query_assumptions(&[]);
        assert!(executor.authored_premise_surfaces().is_some());
    }
}
