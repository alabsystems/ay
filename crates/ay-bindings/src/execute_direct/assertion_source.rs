// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates

use std::fmt::{self, Write};

use ay_dpll::api::Term;

use super::context::ExecutionContext;
use super::ExecuteError;
use crate::constraint::Constraint;
use crate::{AYProgram, Expr};

/// Scan the complete program so a late proof request also retains the source
/// of earlier assertions. Programs that never export proofs keep native-only
/// execution, including native definitions and binders without parser identities.
pub(super) fn program_requests_proofs(program: &AYProgram) -> bool {
    let enabled = |name: &str, value: &str| {
        name.trim_start_matches(':') == "produce-proofs" && value == "true"
    };
    program.options().iter().any(|(name, value)| enabled(name, value))
        || program.commands().iter().any(|command| {
            matches!(command, Constraint::SetOption { name, value } if enabled(name, value))
        })
}

struct AssertionSource(String);

impl Write for AssertionSource {
    fn write_str(&mut self, value: &str) -> fmt::Result {
        if value.len() > (8 * 1024 * 1024_usize).saturating_sub(self.0.len()) {
            return Err(fmt::Error);
        }
        self.0.push_str(value);
        Ok(())
    }
}

pub(super) fn assert_with_source(
    ctx: &mut ExecutionContext,
    term: Term,
    expr: &Expr,
) -> Result<(), ExecuteError> {
    if !ctx.retain_assertion_sources {
        return ctx
            .solver
            .try_assert_term(term)
            .map_err(|error| ExecuteError::ConstraintExecution(error.to_string()));
    }
    let mut source = AssertionSource(String::new());
    write!(source, "(assert {expr})").map_err(|_| {
        ExecuteError::ConstraintExecution("assertion source exceeds 8 MiB".to_string())
    })?;
    ctx.solver
        .try_assert_term_with_source(term, &source.0)
        .map_err(|error| ExecuteError::ConstraintExecution(error.to_string()))
}
