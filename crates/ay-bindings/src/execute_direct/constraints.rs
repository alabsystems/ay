// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates

use super::context::ExecutionContext;
use super::translate::{bridge_datatype, translate_expr};
use super::translate_bridge;
use super::ExecuteError;
use crate::constraint::Constraint;

/// Execute a single constraint.
pub(super) fn execute_constraint(
    ctx: &mut ExecutionContext,
    constraint: &Constraint,
) -> Result<(), ExecuteError> {
    match constraint {
        Constraint::SetLogic(_) => {
            // Already handled in parse_logic
            Ok(())
        }

        Constraint::SetOption { name, value } => {
            // Forward options to the solver (#5505)
            ctx.solver.set_option(name, value);
            Ok(())
        }

        Constraint::DeclareConst { name, sort } => translate_bridge::declare_const(ctx, name, sort),

        Constraint::DeclareFun {
            name,
            arg_sorts,
            return_sort,
        } => translate_bridge::declare_fun(ctx, name, arg_sorts, return_sort),

        Constraint::DefineFun {
            name,
            params,
            return_sort,
            body,
        } => translate_bridge::define_fun(ctx, name, params, return_sort, body),

        Constraint::Assert { expr, label: _ } => {
            let term = translate_expr(ctx, expr)?;
            ctx.solver
                .try_assert_term(term)
                .map_err(|e| ExecuteError::ConstraintExecution(e.to_string()))?;
            Ok(())
        }

        Constraint::Push => {
            ctx.solver
                .try_push()
                .map_err(|e| ExecuteError::ConstraintExecution(e.to_string()))?;
            Ok(())
        }

        Constraint::Pop(n) => {
            for _ in 0..*n {
                ctx.solver
                    .try_pop()
                    .map_err(|e| ExecuteError::ConstraintExecution(e.to_string()))?;
            }
            Ok(())
        }

        Constraint::CheckSat => {
            // Defer to main execute() for result handling
            Ok(())
        }

        // CheckSatAssuming: translate assumptions and store for execute() (#5456).
        Constraint::CheckSatAssuming(exprs) => {
            ctx.check_sat_assumptions.clear();
            for expr in exprs {
                let term = translate_expr(ctx, expr)?;
                ctx.check_sat_assumptions.push(term);
            }
            Ok(())
        }

        // GetValue: collect terms for evaluation after check-sat (#1977)
        Constraint::GetValue(exprs) => {
            for expr in exprs {
                let term = translate_expr(ctx, expr)?;
                // Store the expression string for output formatting
                ctx.get_value_terms.push((format!("{expr}"), term));
            }
            Ok(())
        }

        Constraint::GetModel | Constraint::GetUnsatCore => {
            // Output commands, skip
            Ok(())
        }

        Constraint::Exit => {
            // No-op
            Ok(())
        }

        // SoftAssert should be filtered by needs_fallback().
        // If it slips through, return an execution error instead of panicking.
        Constraint::SoftAssert { .. } => Err(ExecuteError::ConstraintExecution(
            "soft-assert requires fallback execution".to_string(),
        )),

        Constraint::DeclareVar { name, sort } => translate_bridge::declare_var(ctx, name, sort),

        Constraint::DeclareDatatype(dt) => {
            let core_dt = bridge_datatype(dt)?;
            ctx.solver
                .try_declare_datatype(&core_dt)
                .map_err(|e| ExecuteError::ConstraintExecution(e.to_string()))?;
            ctx.declared_datatypes.insert(dt.name.clone(), core_dt);
            Ok(())
        }

        // CHC commands should be filtered by needs_fallback().
        // If they slip through, return an execution error instead of panicking.
        Constraint::DeclareRel { .. } | Constraint::Rule { .. } | Constraint::Query(_) => {
            Err(ExecuteError::ConstraintExecution(
                "CHC commands require fallback execution".to_string(),
            ))
        }

        // OMT commands are routed to the OMT executor bridge (#6702).
        // They should never reach this function — execute_typed() detects
        // objective-bearing programs before entering the Solver path.
        Constraint::Maximize(_) | Constraint::Minimize(_) | Constraint::GetObjectives => {
            Err(ExecuteError::ConstraintExecution(
                "OMT commands should be routed through the OMT executor bridge".to_string(),
            ))
        }
    }
}
