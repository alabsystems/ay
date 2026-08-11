// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! SMT-LIB2 parsing bridge.

use ay_frontend::{
    Command, FiniteSetOp, FiniteSetTermMetadata, FiniteSetTypingMode, PublicAssertionMetadata,
    PublicSort, PublicSymbolSignature, PublicTermMetadata,
};

use crate::api::types::{SolverError, Term};
use crate::api::Solver;

/// Public-sort metadata for one parsed term occurrence.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParsedPublicTermMetadata {
    /// Lowered engine term for this occurrence.
    pub engine_term: Term,
    /// Public sort before finite-set lowering.
    pub public_sort: PublicSort,
    /// Finite-set operator at this occurrence.
    pub finite_set_op: Option<FiniteSetOp>,
    /// Public binder sorts for a quantifier or lambda.
    pub public_bound_sorts: Vec<PublicSort>,
    /// Source arguments in order.
    pub arguments: Vec<Self>,
}

/// Public finite-set metadata aligned with one parsed formula.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParsedPublicFormulaMetadata {
    /// Aggregate finite-set decision obligations.
    pub finite_sets: FiniteSetTermMetadata,
    /// Occurrence tree when public collection typing is relevant.
    pub root: Option<ParsedPublicTermMetadata>,
}

/// One parsed hard assertion, soft constraint, or objective.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParsedSmtlib2Formula {
    /// Engine term installed by the elaborator.
    pub term: Term,
    /// Public type/provenance metadata for this occurrence.
    pub metadata: ParsedPublicFormulaMetadata,
}

/// Complete delta produced by one Z3-5-strict SMT-LIB parse.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParsedSmtlib2Batch {
    /// Hard assertions introduced by this call.
    pub assertions: Vec<ParsedSmtlib2Formula>,
    /// Soft constraints introduced by this call.
    pub soft_constraints: Vec<ParsedSmtlib2Formula>,
    /// Optimization objectives introduced by this call.
    pub objectives: Vec<ParsedSmtlib2Formula>,
    /// Public signatures visible after this call.
    pub symbol_signatures: Vec<PublicSymbolSignature>,
}

fn wrap_public_term(metadata: PublicTermMetadata) -> ParsedPublicTermMetadata {
    ParsedPublicTermMetadata {
        engine_term: Term(metadata.engine_term),
        public_sort: metadata.public_sort,
        finite_set_op: metadata.finite_set_op,
        public_bound_sorts: metadata.public_bound_sorts,
        arguments: metadata
            .arguments
            .into_iter()
            .map(wrap_public_term)
            .collect(),
    }
}

fn wrap_formula(term: ay_core::TermId, metadata: PublicAssertionMetadata) -> ParsedSmtlib2Formula {
    ParsedSmtlib2Formula {
        term: Term(term),
        metadata: ParsedPublicFormulaMetadata {
            finite_sets: metadata.finite_sets,
            root: metadata.root.map(wrap_public_term),
        },
    }
}

impl Solver {
    /// Parse an SMT-LIB2 string, executing declarations and assertions.
    ///
    /// Processes declarations, definitions, assertions, and options. Skips
    /// `check-sat`, `get-model`, and other query commands. `push`, `pop`,
    /// `reset`, and `reset-assertions` are rejected before execution because
    /// this assertion-returning bridge cannot represent destructive stack edits
    /// atomically; use the dedicated scope/reset API for those operations.
    ///
    /// Returns the assertions added during parsing as `Vec<Term>`.
    ///
    /// # Errors
    ///
    /// Returns `SolverError::ParseError` if parsing fails, or other errors
    /// if command execution fails.
    pub fn parse_smtlib2(&mut self, input: &str) -> Result<Vec<Term>, SolverError> {
        Ok(self
            .parse_smtlib2_with_public_metadata(input, FiniteSetTypingMode::LegacyCompatible)?
            .assertions
            .into_iter()
            .map(|formula| formula.term)
            .collect())
    }

    /// Parse with Z3 5.0.0's strict public collection typing and return every
    /// formula delta plus occurrence-level public metadata.
    ///
    /// This is the adapter entry point for AY's Z3-compatible C API. In
    /// particular, it distinguishes `FiniteSet` from its internal Array
    /// lowering for hard assertions, soft constraints, objectives, binders,
    /// and declared symbol signatures.
    ///
    /// # Errors
    ///
    /// Returns an error for syntax/semantic failures, unsupported destructive
    /// state commands, or an internal metadata-alignment violation.
    pub fn parse_smtlib2_z3_5(&mut self, input: &str) -> Result<ParsedSmtlib2Batch, SolverError> {
        self.parse_smtlib2_with_public_metadata(input, FiniteSetTypingMode::Z3_5Strict)
    }

    fn parse_smtlib2_with_public_metadata(
        &mut self,
        input: &str,
        typing_mode: FiniteSetTypingMode,
    ) -> Result<ParsedSmtlib2Batch, SolverError> {
        let commands = ay_frontend::parse(input).map_err(|e| SolverError::InvalidArgument {
            operation: "parse_smtlib2",
            message: format!("{e}"),
        })?;

        // This API returns the assertions introduced by THIS call. Destructive
        // scope controls can make the final assertion stack shorter than its
        // entry length (the old `assertions[before..after]` implementation then
        // panicked), and a retained `push` cannot be paired by a later call once
        // destructive controls are rejected. Refuse the complete state-control
        // family before executing any command. Callers that need an interactive
        // scope protocol should use `try_push`/`try_pop`/`try_reset_assertions`
        // directly instead of the assertion-returning parse bridge.
        if commands.iter().any(|command| {
            matches!(
                command,
                Command::Push(_) | Command::Pop(_) | Command::Reset | Command::ResetAssertions
            )
        }) {
            return Err(SolverError::InvalidArgument {
                operation: "parse_smtlib2",
                message: "push/pop/reset commands are not supported by the assertion-returning parse bridge"
                    .to_string(),
            });
        }

        let before_assertions = self.executor.context().assertions.len();
        let before_softs = self.executor.context().soft_constraints().len();
        let before_objectives = self.executor.context().objectives().len();
        let previous_mode = self.executor.context().finite_set_typing_mode();
        self.executor
            .context_mut()
            .set_finite_set_typing_mode(typing_mode);

        let execution = (|| {
            for cmd in &commands {
                match cmd {
                    // Skip query commands — only process declarations and formulas.
                    Command::CheckSat
                    | Command::CheckSatAssuming(_)
                    | Command::GetModel
                    | Command::GetValue(_)
                    | Command::Eval(_)
                    | Command::GetConsequences(_, _)
                    | Command::GetUnsatCore
                    | Command::GetUnsatCoreWithFarkas
                    | Command::GetUnsatAssumptions
                    | Command::GetProof
                    | Command::GetAssertions
                    | Command::GetAssignment
                    | Command::GetInfo(_)
                    | Command::GetOption(_)
                    | Command::Labels
                    | Command::GetObjectives
                    | Command::GetObjectiveCertificates
                    | Command::GetAbduct(_, _)
                    | Command::Echo(_)
                    | Command::Display(..)
                    | Command::Exit => continue,
                    _ => {
                        self.executor.execute(cmd)?;
                    }
                }
            }
            Ok::<(), SolverError>(())
        })();
        self.executor
            .context_mut()
            .set_finite_set_typing_mode(previous_mode);
        execution?;

        let context = self.executor.context();
        let after_assertions = context.assertions.len();
        let after_softs = context.soft_constraints().len();
        let after_objectives = context.objectives().len();
        if context.assertion_finite_set_metadata().len() != after_assertions
            || context.soft_finite_set_metadata().len() != after_softs
            || context.objective_finite_set_metadata().len() != after_objectives
        {
            return Err(SolverError::InvalidArgument {
                operation: "parse_smtlib2",
                message: "public formula metadata is not aligned with the semantic stacks"
                    .to_string(),
            });
        }
        let assertion_terms = &context.assertions[before_assertions..after_assertions];
        let assertion_metadata =
            &context.assertion_finite_set_metadata()[before_assertions..after_assertions];
        let soft_terms = &context.soft_constraints()[before_softs..after_softs];
        let soft_metadata = &context.soft_finite_set_metadata()[before_softs..after_softs];
        let objective_terms = &context.objectives()[before_objectives..after_objectives];
        let objective_metadata =
            &context.objective_finite_set_metadata()[before_objectives..after_objectives];

        let assertions = assertion_terms
            .iter()
            .copied()
            .zip(assertion_metadata.iter().cloned())
            .map(|(term, metadata)| wrap_formula(term, metadata))
            .collect();
        let soft_constraints = soft_terms
            .iter()
            .zip(soft_metadata.iter().cloned())
            .map(|(soft, metadata)| wrap_formula(soft.term, metadata))
            .collect();
        let objectives = objective_terms
            .iter()
            .zip(objective_metadata.iter().cloned())
            .map(|(objective, metadata)| wrap_formula(objective.term, metadata))
            .collect();
        Ok(ParsedSmtlib2Batch {
            assertions,
            soft_constraints,
            objectives,
            symbol_signatures: context.public_symbol_signatures(),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::api::Logic;

    #[test]
    fn destructive_controls_are_rejected_before_any_execution() {
        for control in ["(pop 1)", "(reset)", "(reset-assertions)", "(push 1)"] {
            let mut solver = Solver::try_new(Logic::All).expect("solver");
            let initial = solver
                .parse_smtlib2("(declare-const a Bool) (assert a)")
                .expect("initial parse");
            assert_eq!(initial.len(), 1);

            let script = format!("(assert false) {control}");
            let err = solver
                .parse_smtlib2(&script)
                .expect_err("state control must be rejected");
            assert!(format!("{err}").contains("push/pop/reset"));

            // Preflight rejection is atomic: the assertion before the control
            // was not installed, and the previously asserted `a` remains live.
            assert_eq!(solver.assertions().len(), 1);
        }
    }

    #[test]
    fn non_boolean_assertion_is_a_semantic_error() {
        let mut solver = Solver::try_new(Logic::All).expect("solver");
        let error = solver
            .parse_smtlib2("(assert 1)")
            .expect_err("SMT-LIB assert requires Bool");
        assert!(format!("{error}").contains("Bool"));
        assert!(solver.assertions().is_empty());
    }
}
