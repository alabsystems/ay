// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates

//! Incremental multi-check-sat execution for `execute_direct` (#8154).

use ay_dpll::api::{ConsumerAcceptanceError, SolveResult};

use super::constraints::execute_constraint;
use super::context::{catch_execute_stage, ExecutionContext};
use super::extract::{extract_get_values_from_terms_typed, extract_model_typed};
use super::fallback::needs_fallback;
use super::logic::parse_logic;
use super::translate::translate_expr;
use super::types::{
    CheckSatOutcome, ExecuteCounterexample, ExecuteDegradation, ExecuteDegradationKind,
    ExecuteError, ExecuteTypedResult, ExecuteValueMap,
};
use super::ModelValue;
use crate::constraint::Constraint;
use crate::program::AYProgram;

pub(super) fn execute_incremental_impl(
    program: &AYProgram,
) -> Result<Vec<CheckSatOutcome>, ExecuteError> {
    if needs_fallback(program).is_some() {
        return Err(ExecuteError::Internal(
            "incremental execution does not support fallback programs".to_string(),
        ));
    }
    let logic = parse_logic(program)?;
    let mut ctx = ExecutionContext::new(logic)?;
    for (name, value) in program.options() {
        let option = Constraint::set_option(name.clone(), value.clone());
        execute_constraint_safe(&mut ctx, &option)?;
    }
    let mut outcomes = Vec::new();
    let mut pending_outcome: Option<CheckSatOutcome> = None;
    let mut check_sat_index: usize = 0;

    for constraint in program.commands() {
        match constraint {
            Constraint::CheckSat => {
                flush_pending_outcome(&mut outcomes, &mut pending_outcome);
                pending_outcome = Some(run_check_sat(&mut ctx, check_sat_index)?);
                check_sat_index += 1;
            }
            Constraint::CheckSatAssuming(_) => {
                flush_pending_outcome(&mut outcomes, &mut pending_outcome);
                execute_constraint_safe(&mut ctx, constraint)?;
                pending_outcome = Some(run_check_sat(&mut ctx, check_sat_index)?);
                ctx.check_sat_assumptions.clear();
                check_sat_index += 1;
            }
            Constraint::GetValue(exprs) => {
                append_get_values(&mut ctx, &mut pending_outcome, exprs)?;
            }
            Constraint::GetModel | Constraint::GetUnsatCore | Constraint::Exit => {}
            _ => {
                flush_pending_outcome(&mut outcomes, &mut pending_outcome);
                execute_constraint_safe(&mut ctx, constraint)?;
            }
        }
    }
    flush_pending_outcome(&mut outcomes, &mut pending_outcome);
    Ok(outcomes)
}

fn flush_pending_outcome(
    outcomes: &mut Vec<CheckSatOutcome>,
    pending_outcome: &mut Option<CheckSatOutcome>,
) {
    if let Some(outcome) = pending_outcome.take() {
        outcomes.push(outcome);
    }
}

fn execute_constraint_safe(
    ctx: &mut ExecutionContext,
    constraint: &Constraint,
) -> Result<(), ExecuteError> {
    catch_execute_stage(
        || execute_constraint(ctx, constraint),
        |reason| {
            Err(ExecuteError::ConstraintExecution(format!(
                "constraint translation panic: {reason}"
            )))
        },
    )
}

fn append_get_values(
    ctx: &mut ExecutionContext,
    pending_outcome: &mut Option<CheckSatOutcome>,
    exprs: &[crate::Expr],
) -> Result<(), ExecuteError> {
    let Some(outcome) = pending_outcome.as_mut() else {
        return Err(ExecuteError::ConstraintExecution(
            "get-value in incremental execution requires a preceding check-sat".to_string(),
        ));
    };
    let ExecuteTypedResult::Counterexample(counterexample) = &mut outcome.result else {
        return Err(ExecuteError::ConstraintExecution(
            "get-value in incremental execution requires the preceding check-sat to be SAT"
                .to_string(),
        ));
    };

    let translated_terms: Vec<(String, ay_dpll::api::Term)> = catch_execute_stage(
        || {
            let mut translated = Vec::with_capacity(exprs.len());
            for expr in exprs {
                let term = translate_expr(ctx, expr)?;
                translated.push((expr.to_string(), term));
            }
            Ok(translated)
        },
        |reason| {
            Err(ExecuteError::ConstraintExecution(format!(
                "constraint translation panic: {reason}"
            )))
        },
    )?;

    let values_result: Result<ExecuteValueMap<ModelValue>, String> = catch_execute_stage(
        || {
            extract_get_values_from_terms_typed(ctx, &translated_terms)
                .map_err(|e| format!("get-value extraction failed: {e}"))
        },
        |reason| Err(format!("get-value extraction panic: {reason}")),
    );

    match values_result {
        Ok(values) => {
            counterexample.values.extend(values);
            Ok(())
        }
        Err(reason) => {
            outcome.result = ExecuteTypedResult::Unknown(reason.clone());
            outcome.degradation = Some(ExecuteDegradation {
                kind: if reason.starts_with("get-value extraction panic:") {
                    ExecuteDegradationKind::GetValueExtractionPanic
                } else {
                    ExecuteDegradationKind::GetValueExtractionFailure
                },
                message: reason,
            });
            Ok(())
        }
    }
}

fn run_check_sat(
    ctx: &mut ExecutionContext,
    check_sat_index: usize,
) -> Result<CheckSatOutcome, ExecuteError> {
    let check_result = if ctx.check_sat_assumptions.is_empty() {
        catch_execute_stage(
            || Ok(ctx.solver.check_sat_with_details()),
            |reason| {
                Err(ExecuteDegradation {
                    kind: ExecuteDegradationKind::SolverPanic,
                    message: format!("solver panic: {reason}"),
                })
            },
        )
    } else {
        catch_execute_stage(
            || {
                Ok(ctx
                    .solver
                    .check_sat_assuming_with_details(&ctx.check_sat_assumptions)
                    .solve)
            },
            |reason| {
                Err(ExecuteDegradation {
                    kind: ExecuteDegradationKind::SolverPanic,
                    message: format!("solver panic: {reason}"),
                })
            },
        )
    };

    let solve_details = match check_result {
        Ok(d) => d,
        Err(degradation) => {
            return Ok(CheckSatOutcome {
                result: ExecuteTypedResult::Unknown(degradation.message.clone()),
                degradation: Some(degradation),
                solve_details: None,
                unsat_proof: None,
                check_sat_index,
                unsat_core: None,
            })
        }
    };

    match solve_details.result.accept_for_consumer() {
        Ok(SolveResult::Unsat(_)) => {
            let unsat_proof = ctx.solver.export_last_unsat_artifact();
            let unsat_core = ctx.solver.try_get_unsat_core().ok();
            Ok(CheckSatOutcome {
                result: ExecuteTypedResult::Verified,
                degradation: None,
                solve_details: Some(solve_details),
                unsat_proof,
                check_sat_index,
                unsat_core,
            })
        }
        Ok(SolveResult::Sat) => {
            let model_result: Result<ExecuteValueMap<ModelValue>, String> = catch_execute_stage(
                || extract_model_typed(ctx).map_err(|e| format!("model extraction failed: {e}")),
                |reason| Err(format!("model extraction panic: {reason}")),
            );
            match model_result {
                Ok(model) => Ok(CheckSatOutcome {
                    result: ExecuteTypedResult::Counterexample(ExecuteCounterexample::new(
                        model,
                        ExecuteValueMap::default(),
                    )),
                    degradation: None,
                    solve_details: Some(solve_details),
                    unsat_proof: None,
                    check_sat_index,
                    unsat_core: None,
                }),
                Err(reason) => Ok(CheckSatOutcome {
                    result: ExecuteTypedResult::Unknown(reason.clone()),
                    degradation: Some(ExecuteDegradation {
                        kind: if reason.starts_with("model extraction panic:") {
                            ExecuteDegradationKind::ModelExtractionPanic
                        } else {
                            ExecuteDegradationKind::ModelExtractionFailure
                        },
                        message: reason,
                    }),
                    solve_details: Some(solve_details),
                    unsat_proof: None,
                    check_sat_index,
                    unsat_core: None,
                }),
            }
        }
        Ok(SolveResult::Unknown) | Ok(_) => {
            let reason = solve_details
                .unknown_reason
                .map(|r| r.to_string())
                .unwrap_or_else(|| "incomplete".to_string());
            Ok(CheckSatOutcome {
                result: ExecuteTypedResult::Unknown(reason.clone()),
                degradation: Some(ExecuteDegradation {
                    kind: ExecuteDegradationKind::SolverUnknown,
                    message: reason,
                }),
                solve_details: Some(solve_details),
                unsat_proof: None,
                check_sat_index,
                unsat_core: None,
            })
        }
        Err(error) => {
            let message = error.to_string();
            let kind = match error {
                ConsumerAcceptanceError::SatModelNotValidated => {
                    ExecuteDegradationKind::UnvalidatedSatBoundary
                }
                _ => ExecuteDegradationKind::UnvalidatedSatBoundary,
            };
            Ok(CheckSatOutcome {
                result: ExecuteTypedResult::Unknown(message.clone()),
                degradation: Some(ExecuteDegradation { kind, message }),
                solve_details: Some(solve_details),
                unsat_proof: None,
                check_sat_index,
                unsat_core: None,
            })
        }
    }
}
