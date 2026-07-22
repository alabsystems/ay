// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! SMT-LIB2 parsing bridge.

use ay_frontend::Command;

use crate::api::types::{SolverError, Term};
use crate::api::Solver;

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

        let before = self.executor.context().assertions.len();

        for cmd in &commands {
            match cmd {
                // Skip query commands — only process declarations and assertions
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
                | Command::GetObjectives
                | Command::GetObjectiveCertificates
                | Command::GetAbduct(_, _)
                | Command::Echo(_)
                | Command::Exit => continue,
                _ => {
                    self.executor.execute(cmd)?;
                }
            }
        }

        let after = self.executor.context().assertions.len();
        let new_assertions: Vec<Term> = self.executor.context().assertions[before..after]
            .iter()
            .map(|tid| Term(*tid))
            .collect();

        Ok(new_assertions)
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
