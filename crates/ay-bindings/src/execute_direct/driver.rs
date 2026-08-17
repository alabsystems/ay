// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates

use ay_dpll::api::{ConsumerAcceptanceError, SolveResult};

use super::constraints::execute_constraint;
use super::context::{catch_execute_stage, ExecutionContext};
use super::extract::{extract_get_values_typed, extract_model_typed, render_model_values};
use super::fallback::{contains_objectives, needs_fallback};
use super::logic::parse_logic;
use super::omt;
use super::types::{
    DirectSolveEnvelope, ExecuteCounterexample, ExecuteDegradation, ExecuteDegradationKind,
    ExecuteDetails, ExecuteError, ExecuteResult, ExecuteTypedDetails, ExecuteTypedResult,
    ExecuteValueMap,
};
use super::ModelValue;
use crate::program::AYProgram;

pub(super) fn execute_typed_with_details_impl(
    program: &AYProgram,
) -> Result<ExecuteTypedDetails, ExecuteError> {
    // Check for fallback conditions
    if let Some(fallback) = needs_fallback(program) {
        return Ok(ExecuteTypedDetails {
            result: ExecuteTypedResult::NeedsFallback(fallback.message.clone()),
            fallback: Some(fallback),
            degradation: None,
            solve_details: None,
            assumption_solve_details: None,
            unsat_proof: None,
        });
    }

    // Route OMT-bearing programs through the executor bridge (#6702).
    // The Solver API does not expose objective registration, so these
    // programs are lowered to SMT-LIB and run through ay_dpll::Executor.
    if contains_objectives(program) {
        let result = omt::execute_omt(program)?;
        return Ok(ExecuteTypedDetails {
            result,
            fallback: None,
            degradation: None,
            solve_details: None,
            assumption_solve_details: None,
            unsat_proof: None,
        });
    }

    // Parse logic
    let logic = parse_logic(program)?;

    // Create execution context
    let mut ctx = ExecutionContext::new(logic)?;

    // `AYProgram::set_option` stores program-level metadata rather than a
    // `Constraint::SetOption` command. The text executor has always emitted
    // that metadata before commands, but execute_direct silently ignored it,
    // making ProgramBuilder::option/with_models/with_unsat_cores no-ops on the
    // primary in-process path. Apply it at the identical point here; explicit
    // SetOption commands below retain their source order and may override it.
    // Execute constraints with panic handling (#6329).
    // ay-classified panics degrade to Unknown; non-ay panics propagate.
    let constraint_result: Result<(), Result<ExecuteTypedResult, ExecuteError>> =
        catch_execute_stage(
            || {
                for (name, value) in program.options() {
                    ctx.solver.set_option(name, value);
                }
                for constraint in program.commands() {
                    execute_constraint(&mut ctx, constraint).map_err(Err)?;
                }
                Ok(())
            },
            |reason| {
                Err(Ok(ExecuteTypedResult::Unknown(format!(
                    "constraint translation panic: {reason}"
                ))))
            },
        );
    match constraint_result {
        Ok(()) => {}
        Err(Ok(typed_result)) => {
            return Ok(ExecuteTypedDetails {
                result: typed_result.clone(),
                fallback: None,
                degradation: Some(ExecuteDegradation {
                    kind: ExecuteDegradationKind::ConstraintTranslationPanic,
                    message: extract_unknown_message(&typed_result),
                }),
                solve_details: None,
                assumption_solve_details: None,
                unsat_proof: None,
            });
        }
        Err(Err(e)) => return Err(e),
    }

    // Interpret result with panic handling (#1044, #6329).
    // ay-classified panics degrade to Unknown; non-ay panics propagate.
    let check_result: Result<DirectSolveEnvelope, ExecuteDegradation> =
        if ctx.check_sat_assumptions.is_empty() {
            catch_execute_stage(
                || {
                    let report = ctx.solver.check_sat_with_details();
                    Ok(DirectSolveEnvelope::Solve(report))
                },
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
                    let report = ctx
                        .solver
                        .check_sat_assuming_with_details(&ctx.check_sat_assumptions);
                    Ok(DirectSolveEnvelope::Assumptions(report))
                },
                |reason| {
                    Err(ExecuteDegradation {
                        kind: ExecuteDegradationKind::SolverPanic,
                        message: format!("solver panic: {reason}"),
                    })
                },
            )
        };

    let solve_envelope = match check_result {
        Ok(report) => report,
        Err(degradation) => {
            return Ok(ExecuteTypedDetails {
                result: ExecuteTypedResult::Unknown(degradation.message.clone()),
                fallback: None,
                degradation: Some(degradation),
                solve_details: None,
                assumption_solve_details: None,
                unsat_proof: None,
            });
        }
    };

    match solve_envelope.verified_result().accept_for_consumer() {
        Ok(SolveResult::Unsat(_)) => {
            let unsat_proof = ctx.solver.export_last_unsat_artifact();
            Ok(ExecuteTypedDetails {
                result: ExecuteTypedResult::Verified,
                fallback: None,
                degradation: None,
                solve_details: solve_envelope.solve_details().cloned(),
                assumption_solve_details: solve_envelope.assumption_solve_details().cloned(),
                unsat_proof,
            })
        }
        Ok(SolveResult::Sat) => {
            // Extract model, catching ay panics during extraction
            let model_result: Result<ExecuteValueMap<ModelValue>, String> = catch_execute_stage(
                || extract_model_typed(&ctx).map_err(|e| format!("model extraction failed: {e}")),
                |reason| Err(format!("model extraction panic: {reason}")),
            );
            match model_result {
                Ok(model) => {
                    // Evaluate get-value terms (#1977), catching ay panics
                    let values_result: Result<ExecuteValueMap<ModelValue>, String> =
                        catch_execute_stage(
                            || {
                                extract_get_values_typed(&ctx)
                                    .map_err(|e| format!("get-value extraction failed: {e}"))
                            },
                            |reason| Err(format!("get-value extraction panic: {reason}")),
                        );
                    match values_result {
                        Ok(values) => Ok(ExecuteTypedDetails {
                            result: ExecuteTypedResult::Counterexample(ExecuteCounterexample::new(
                                model, values,
                            )),
                            fallback: None,
                            degradation: None,
                            solve_details: solve_envelope.solve_details().cloned(),
                            assumption_solve_details: solve_envelope
                                .assumption_solve_details()
                                .cloned(),
                            unsat_proof: None,
                        }),
                        Err(reason) => Ok(ExecuteTypedDetails {
                            result: ExecuteTypedResult::Unknown(reason.clone()),
                            fallback: None,
                            degradation: Some(ExecuteDegradation {
                                kind: if reason.starts_with("get-value extraction panic:") {
                                    ExecuteDegradationKind::GetValueExtractionPanic
                                } else {
                                    ExecuteDegradationKind::GetValueExtractionFailure
                                },
                                message: reason,
                            }),
                            solve_details: solve_envelope.solve_details().cloned(),
                            assumption_solve_details: solve_envelope
                                .assumption_solve_details()
                                .cloned(),
                            unsat_proof: None,
                        }),
                    }
                }
                Err(reason) => Ok(ExecuteTypedDetails {
                    result: ExecuteTypedResult::Unknown(reason.clone()),
                    fallback: None,
                    degradation: Some(ExecuteDegradation {
                        kind: if reason.starts_with("model extraction panic:") {
                            ExecuteDegradationKind::ModelExtractionPanic
                        } else {
                            ExecuteDegradationKind::ModelExtractionFailure
                        },
                        message: reason,
                    }),
                    solve_details: solve_envelope.solve_details().cloned(),
                    assumption_solve_details: solve_envelope.assumption_solve_details().cloned(),
                    unsat_proof: None,
                }),
            }
        }
        Ok(SolveResult::Unknown) | Ok(_) => {
            let reason = solve_envelope
                .unknown_reason()
                .map(|r| r.to_string())
                .unwrap_or_else(|| "incomplete".to_string());
            Ok(ExecuteTypedDetails {
                result: ExecuteTypedResult::Unknown(reason.clone()),
                fallback: None,
                degradation: Some(ExecuteDegradation {
                    kind: ExecuteDegradationKind::SolverUnknown,
                    message: reason,
                }),
                solve_details: solve_envelope.solve_details().cloned(),
                assumption_solve_details: solve_envelope.assumption_solve_details().cloned(),
                unsat_proof: None,
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
            Ok(ExecuteTypedDetails {
                result: ExecuteTypedResult::Unknown(message.clone()),
                fallback: None,
                degradation: Some(ExecuteDegradation { kind, message }),
                solve_details: solve_envelope.solve_details().cloned(),
                assumption_solve_details: solve_envelope.assumption_solve_details().cloned(),
                unsat_proof: None,
            })
        }
    }
}

fn extract_unknown_message(result: &ExecuteTypedResult) -> String {
    match result {
        ExecuteTypedResult::Unknown(reason) | ExecuteTypedResult::NeedsFallback(reason) => {
            reason.clone()
        }
        ExecuteTypedResult::Verified => "verified".to_string(),
        ExecuteTypedResult::Counterexample(_) => "counterexample".to_string(),
    }
}

pub(super) fn render_execute_result(result: ExecuteTypedResult) -> ExecuteResult {
    match result {
        ExecuteTypedResult::Verified => ExecuteResult::Verified,
        ExecuteTypedResult::Counterexample(ExecuteCounterexample { model, values }) => {
            ExecuteResult::Counterexample {
                model: render_model_values(model),
                values: render_model_values(values),
            }
        }
        ExecuteTypedResult::NeedsFallback(reason) => ExecuteResult::NeedsFallback(reason),
        ExecuteTypedResult::Unknown(reason) => ExecuteResult::Unknown(reason),
    }
}

pub(super) fn into_untyped_details(details: ExecuteTypedDetails) -> ExecuteDetails {
    ExecuteDetails {
        result: render_execute_result(details.result),
        fallback: details.fallback,
        degradation: details.degradation,
        solve_details: details.solve_details,
        assumption_solve_details: details.assumption_solve_details,
        unsat_proof: details.unsat_proof,
    }
}
