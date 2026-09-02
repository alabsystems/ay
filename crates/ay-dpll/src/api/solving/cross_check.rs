// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Script-first cross-check replay helpers for logic-mode and seed perturbation.

use ay_frontend::command::Term as ParsedTerm;
use ay_frontend::sexp::SExpr;
use ay_frontend::{parse, Command};

use crate::api::types::{
    CrossCheckDisagreement, CrossCheckReport, CrossCheckRun, CrossCheckVariant, SolveResult,
    SolverError, VerificationSummary,
};
use crate::Executor;

use crate::api::Solver;

const CROSS_CHECK_OPERATION: &str = "cross_check_smtlib2";
const BASELINE_LABEL: &str = "baseline";

#[derive(Debug, Clone)]
enum SolveCommand {
    CheckSat,
    CheckSatAssuming(Vec<ParsedTerm>),
}

#[derive(Debug, Clone)]
struct CrossCheckScript {
    setup_commands: Vec<Command>,
    solve_command: SolveCommand,
}

impl CrossCheckScript {
    fn parse(input: &str) -> Result<Self, SolverError> {
        let commands = parse(input).map_err(|err| SolverError::InvalidArgument {
            operation: CROSS_CHECK_OPERATION,
            message: format!("{err}"),
        })?;

        let mut setup_commands = Vec::new();
        let mut solve_command = None;

        for command in commands {
            match command {
                Command::CheckSat => {
                    if solve_command.is_some() {
                        return Err(multi_solve_error());
                    }
                    solve_command = Some(SolveCommand::CheckSat);
                }
                Command::CheckSatAssuming(terms) => {
                    if solve_command.is_some() {
                        return Err(multi_solve_error());
                    }
                    solve_command = Some(SolveCommand::CheckSatAssuming(terms));
                }
                command if is_follow_up_query(&command) => {
                    return Err(SolverError::InvalidArgument {
                        operation: CROSS_CHECK_OPERATION,
                        message: format!(
                            "Packet 1 only supports single-query scripts; unsupported follow-up command {}",
                            command_name(&command)
                        ),
                    });
                }
                // `setup_commands` are replayed before the one solve command.
                // Accepting a command after that solve would silently move it
                // before the query and cross-check a different problem. Keep
                // the single-query packet exact by requiring the solve to be
                // terminal (follow-up queries retain their dedicated rejection
                // above).
                _ if solve_command.is_some() => {
                    return Err(post_solve_command_error());
                }
                command => setup_commands.push(command),
            }
        }

        let solve_command = solve_command.ok_or_else(|| SolverError::InvalidArgument {
            operation: CROSS_CHECK_OPERATION,
            message: "expected exactly one check-sat or check-sat-assuming command".to_string(),
        })?;

        Ok(Self {
            setup_commands,
            solve_command,
        })
    }

    fn setup_for_variant(&self, variant: Option<&CrossCheckVariant>) -> Vec<Command> {
        let Some(variant) = variant else {
            return self.setup_commands.clone();
        };

        let live_epoch_start = self
            .setup_commands
            .iter()
            .rposition(|command| matches!(command, Command::Reset))
            .map_or(0, |index| index + 1);
        let mut commands = self.setup_commands[..live_epoch_start].to_vec();
        let mut live_logic_seen = false;
        let mut live_seed_seen = false;

        for command in &self.setup_commands[live_epoch_start..] {
            match command {
                Command::SetLogic(_) if variant.logic.is_some() => {
                    commands.push(Command::SetLogic(
                        variant.logic.unwrap().as_str().to_string(),
                    ));
                    live_logic_seen = true;
                }
                Command::SetOption(keyword, _) if is_random_seed_option(keyword) => {
                    if let Some(seed) = variant.random_seed {
                        commands.push(Command::SetOption(
                            RANDOM_SEED_OPTION.to_string(),
                            SExpr::Numeral(seed.to_string()),
                        ));
                    } else {
                        commands.push(command.clone());
                    }
                    live_seed_seen = true;
                }
                Command::SetLogic(_) => {
                    live_logic_seen = true;
                    commands.push(command.clone());
                }
                _ => commands.push(command.clone()),
            }
        }

        let mut injected = Vec::with_capacity(2);
        if let Some(logic) = variant.logic.filter(|_| !live_logic_seen) {
            injected.push(Command::SetLogic(logic.as_str().to_string()));
        }
        if let Some(seed) = variant.random_seed.filter(|_| !live_seed_seen) {
            injected.push(Command::SetOption(
                RANDOM_SEED_OPTION.to_string(),
                SExpr::Numeral(seed.to_string()),
            ));
        }
        if !injected.is_empty() {
            commands.splice(live_epoch_start..live_epoch_start, injected);
        }

        commands
    }
}

impl Solver {
    /// Replay one SMT-LIB script under multiple logic/seed variants and report
    /// trusted SAT/UNSAT contradictions.
    ///
    /// Packet 1 accepts exactly one solve command (`check-sat` or
    /// `check-sat-assuming`) and rejects scripts with follow-up query commands.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError::InvalidArgument`] for unsupported script shapes
    /// and propagates elaboration/executor failures from replayed runs.
    pub fn cross_check_smtlib2(
        input: &str,
        variants: &[CrossCheckVariant],
    ) -> Result<CrossCheckReport, SolverError> {
        super::check::reject_bv_cnf_export_operation(CROSS_CHECK_OPERATION)?;
        let script = CrossCheckScript::parse(input)?;

        let baseline = run_cross_check(&script, None)?;
        let mut variant_runs = Vec::with_capacity(variants.len());
        for variant in variants {
            variant_runs.push(run_cross_check(&script, Some(variant))?);
        }

        let disagreement = find_disagreement(&baseline, &variant_runs);
        Ok(CrossCheckReport {
            baseline,
            variants: variant_runs,
            disagreement,
        })
    }
}

const RANDOM_SEED_OPTION: &str = ":random-seed";

fn run_cross_check(
    script: &CrossCheckScript,
    variant: Option<&CrossCheckVariant>,
) -> Result<CrossCheckRun, SolverError> {
    let mut executor = Executor::new();
    for command in script.setup_for_variant(variant) {
        executor.execute(&command).map_err(SolverError::from)?;
    }

    let solve_command = match &script.solve_command {
        SolveCommand::CheckSat => Command::CheckSat,
        SolveCommand::CheckSatAssuming(terms) => Command::CheckSatAssuming(terms.clone()),
    };

    // Cross-check replay is a public authored decision, not a disposable
    // executor probe. Route it through the same closed command boundary as the
    // CLI so `begin_public_solve`, exact authored-root binding, strict UNSAT
    // certification, and one-shot SAT/UNSAT capability consumption are all
    // mandatory. Calling `Context::process_command` followed by raw
    // `Executor::check_sat*` used to bypass that boundary and let an
    // uncertified UNSAT participate in a reported disagreement.
    executor
        .execute_authored(&solve_command)
        .map_err(SolverError::from)?;
    let result = executor
        .last_result()
        .cloned()
        .unwrap_or(SolveResult::Unknown);

    let verification = build_verification_summary(&executor, &result);
    let unknown_reason = if result.is_unknown() {
        Some(
            executor
                .unknown_reason()
                .map_or_else(|| "unknown".to_string(), |reason| reason.to_string()),
        )
    } else {
        None
    };
    Ok(CrossCheckRun {
        label: variant
            .map(|variant| variant.label.clone())
            .unwrap_or_else(|| BASELINE_LABEL.to_string()),
        result,
        verification,
        unknown_reason,
    })
}

#[allow(clippy::redundant_closure_for_method_calls)] // ValidationStats path not pub(crate)
fn build_verification_summary(executor: &Executor, result: &SolveResult) -> VerificationSummary {
    let (independent, delegated, incomplete) = executor
        .last_validation_stats
        .as_ref()
        .map(|stats| stats.verification_evidence_counts())
        .unwrap_or((0, 0, 0));
    let statistics = executor.statistics();

    VerificationSummary {
        sat_model_validated: executor.was_model_validated(),
        unsat_proof_available: result.is_unsat() && executor.last_proof().is_some(),
        unsat_proof_decline: result
            .is_unsat()
            .then(|| executor.last_proof_decline())
            .flatten(),
        // `run_cross_check` has already crossed `execute_authored`, whose text
        // boundary consumes the exact one-shot certificate and records its
        // sealed class. A bare surviving UNSAT proves admission, but does not
        // distinguish strict proof checking from the exact semantic theorem.
        unsat_proof_strictly_verified: result.is_unsat()
            && executor.last_command_unsat_was_strictly_verified(),
        unsat_independently_verified: result.is_unsat()
            && executor.last_command_unsat_was_independently_verified(),
        unsat_exact_semantically_verified: result.is_unsat()
            && executor.last_command_unsat_was_exact_semantically_verified(),
        unsat_proof_checker_failures: statistics.get_int("proof_checker_failures").unwrap_or(0),
        sat_independent_checks: independent,
        sat_delegated_checks: delegated,
        sat_incomplete_checks: incomplete,
    }
}

fn find_disagreement(
    baseline: &CrossCheckRun,
    variants: &[CrossCheckRun],
) -> Option<CrossCheckDisagreement> {
    let mut runs = Vec::with_capacity(variants.len() + 1);
    runs.push(baseline);
    runs.extend(variants.iter());

    for (idx, lhs) in runs.iter().enumerate() {
        for rhs in runs.iter().skip(idx + 1) {
            let Some(lhs_result) = accepted_definite_result(lhs) else {
                continue;
            };
            let Some(rhs_result) = accepted_definite_result(rhs) else {
                continue;
            };
            if lhs_result != rhs_result {
                return Some(CrossCheckDisagreement {
                    lhs_label: lhs.label.clone(),
                    rhs_label: rhs.label.clone(),
                    lhs: lhs_result,
                    rhs: rhs_result,
                });
            }
        }
    }

    None
}

fn accepted_definite_result(run: &CrossCheckRun) -> Option<SolveResult> {
    // Diagnostic reconstruction of an ALREADY-decided run for cross-run
    // comparison — NOT a fresh public SAT emission, so it does not (and cannot)
    // carry an `emit_sat_verdict` `SatCertificate`. Replicate
    // `VerifiedSolveResult::accept_for_consumer` inline: a `Sat` is definite
    // only if its model was validated, and an `Unsat` only if the authored
    // command boundary recorded one of the complete exact-query certification
    // classes. Keep the classes distinct in the public metadata.
    match &run.result {
        SolveResult::Sat if run.verification.sat_model_validated => Some(SolveResult::Sat),
        SolveResult::Unsat(_)
            if run.verification.unsat_proof_strictly_verified
                || run.verification.unsat_independently_verified
                || run.verification.unsat_exact_semantically_verified =>
        {
            Some(run.result.clone())
        }
        _ => None,
    }
}

fn is_random_seed_option(keyword: &str) -> bool {
    keyword == RANDOM_SEED_OPTION
}

fn is_follow_up_query(command: &Command) -> bool {
    matches!(
        command,
        Command::GetModel
            | Command::GetObjectives
            | Command::GetObjectiveCertificates
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
            | Command::Exit
            | Command::Echo(_)
            | Command::Display(..)
            | Command::Simplify(_)
            | Command::GetAbduct(_, _)
    )
}

fn command_name(command: &Command) -> &'static str {
    match command {
        Command::GetModel => "get-model",
        Command::GetObjectives => "get-objectives",
        Command::GetObjectiveCertificates => "get-objective-certificates",
        Command::GetValue(_) => "get-value",
        Command::Eval(_) => "eval",
        Command::GetConsequences(_, _) => "get-consequences",
        Command::GetUnsatCore => "get-unsat-core",
        Command::GetUnsatCoreWithFarkas => "get-unsat-core :farkas",
        Command::GetUnsatAssumptions => "get-unsat-assumptions",
        Command::GetProof => "get-proof",
        Command::GetAssertions => "get-assertions",
        Command::GetAssignment => "get-assignment",
        Command::GetInfo(_) => "get-info",
        Command::GetOption(_) => "get-option",
        Command::Labels => "labels",
        Command::Exit => "exit",
        Command::Echo(_) => "echo",
        Command::Display(..) => "display",
        Command::Simplify(_) => "simplify",
        Command::GetAbduct(_, _) => "get-abduct",
        _ => "unsupported-query",
    }
}

fn multi_solve_error() -> SolverError {
    SolverError::InvalidArgument {
        operation: CROSS_CHECK_OPERATION,
        message: "expected exactly one check-sat or check-sat-assuming command".to_string(),
    }
}

fn post_solve_command_error() -> SolverError {
    SolverError::InvalidArgument {
        operation: CROSS_CHECK_OPERATION,
        message: "commands after check-sat or check-sat-assuming are unsupported".to_string(),
    }
}

#[cfg(test)]
#[path = "cross_check_tests.rs"]
mod tests;
