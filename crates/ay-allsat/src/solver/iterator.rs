// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ay_sat::{Literal, SatResult, Variable};
use tracing::warn;

use crate::outcome::{AllSatInputError, AllSatOutcome, AllSatStats};

use super::{AllSatConfig, AllSatSolver, Solution, SolverBackend};

enum BackendStep {
    Model(Vec<bool>),
    Exhausted,
    Unknown,
}

fn classify_backend_result(result: ay_sat::SolverSatResult) -> BackendStep {
    match result.into_inner() {
        SatResult::Sat(model) => BackendStep::Model(model),
        SatResult::Unsat(_) => BackendStep::Exhausted,
        SatResult::Unknown => BackendStep::Unknown,
        _ => BackendStep::Unknown,
    }
}

/// Create a blocking clause that excludes the given solution.
///
/// When projection is configured, the blocking clause only references projected
/// variables, producing minimal cubes that efficiently block duplicate projected
/// assignments without over-constraining non-projected variables.
///
/// `all_vars` provides the default set of variables to block over when no
/// projection is configured. This differs by backend: internal uses 1..=max_var
/// (1-indexed), external uses 0..num_vars (0-indexed).
fn make_blocking_clause(
    config: &AllSatConfig,
    solution: &Solution,
    all_vars: &[u32],
) -> Result<Vec<Literal>, AllSatInputError> {
    let vars: &[u32] = if let Some(ref proj) = config.projection {
        proj
    } else {
        all_vars
    };

    // Blocking clause: at least one variable must differ.
    // If var=true in solution, add negated literal; if false, add positive literal.
    vars.iter()
        .map(|&v| {
            let var = Variable::new(v);
            let value = solution
                .get(v)
                .ok_or(AllSatInputError::BackendModelMissingVariable(v))?;
            Ok(if value {
                Literal::negative(var)
            } else {
                Literal::positive(var)
            })
        })
        .collect()
}

/// Iterator over all solutions.
pub struct AllSatIterator<'a> {
    pub(super) solver: &'a mut AllSatSolver,
    config: AllSatConfig,
    /// Default variable set for blocking clauses (precomputed from backend).
    all_vars: Vec<u32>,
    /// Blocking clauses accumulated during this iteration (internal backend only).
    blocking_clauses: Vec<Vec<Literal>>,
    solutions_returned: usize,
    exhausted: bool,
    /// Termination reason, once `next` has returned `None`.
    termination: Option<AllSatOutcome>,
    /// User-model length captured before the external enumeration scope.
    external_model_len: Option<usize>,
    /// Whether this iterator owns an active external SAT scope.
    external_scope_active: bool,
    /// Per-run counters returned by callback and reporting APIs.
    pub(super) run_stats: AllSatStats,
}

impl AllSatIterator<'_> {
    /// Returns the outcome of this iteration.
    ///
    /// Returns [`AllSatOutcome::InProgress`] until the iterator reaches a
    /// terminal result. Dropping it early records
    /// [`AllSatOutcome::IteratorDropped`] in the solver's statistics.
    pub fn outcome(&self) -> AllSatOutcome {
        self.termination.unwrap_or(AllSatOutcome::InProgress)
    }
}

impl<'a> AllSatIterator<'a> {
    pub(super) fn new(solver: &'a mut AllSatSolver, config: AllSatConfig) -> Self {
        let validation = solver
            .validate_config(&config)
            .and_then(|()| solver.default_vars());
        let all_vars = match validation {
            Ok(vars) => vars,
            Err(error) => {
                solver.set_last_outcome(AllSatOutcome::InvalidInput, Some(error));
                let run_stats = AllSatStats {
                    outcome: AllSatOutcome::InvalidInput,
                    input_error: Some(error),
                    ..Default::default()
                };
                return Self {
                    solver,
                    config,
                    all_vars: Vec::new(),
                    blocking_clauses: Vec::new(),
                    solutions_returned: 0,
                    exhausted: true,
                    termination: Some(AllSatOutcome::InvalidInput),
                    external_model_len: None,
                    external_scope_active: false,
                    run_stats,
                };
            }
        };
        let external_model_len = match &solver.backend {
            SolverBackend::Internal { .. } => None,
            SolverBackend::External(sat_solver) => Some(sat_solver.user_num_vars()),
        };
        let external_scope_active = if let SolverBackend::External(sat_solver) = &mut solver.backend
        {
            sat_solver.push();
            true
        } else {
            false
        };
        solver.set_last_outcome(AllSatOutcome::InProgress, None);
        Self {
            solver,
            config,
            all_vars,
            blocking_clauses: Vec::new(),
            solutions_returned: 0,
            exhausted: false,
            termination: None,
            external_model_len,
            external_scope_active,
            run_stats: AllSatStats::default(),
        }
    }

    pub(super) fn finish(&mut self, mut outcome: AllSatOutcome) {
        if self.external_scope_active {
            if let SolverBackend::External(sat_solver) = &mut self.solver.backend {
                let popped = sat_solver.pop();
                if !popped {
                    let error = AllSatInputError::BackendScopePopFailed;
                    self.run_stats.input_error = Some(error);
                    self.solver.stats.input_error = Some(error);
                    self.solver.invalid_input.get_or_insert(error);
                    outcome = AllSatOutcome::InvalidInput;
                }
            }
            self.external_scope_active = false;
        }
        self.exhausted = true;
        self.termination = Some(outcome);
        self.run_stats.outcome = outcome;
        self.solver.stats.outcome = outcome;
    }

    fn finish_input_error(&mut self, error: AllSatInputError) {
        self.run_stats.input_error = Some(error);
        self.solver.stats.input_error = Some(error);
        self.solver.invalid_input.get_or_insert(error);
        self.finish(AllSatOutcome::InvalidInput);
    }

    fn solve_backend(&mut self) -> Result<BackendStep, AllSatInputError> {
        self.run_stats.sat_calls = self.run_stats.sat_calls.saturating_add(1);
        self.solver.stats.sat_calls = self.solver.stats.sat_calls.saturating_add(1);
        let result = match &mut self.solver.backend {
            SolverBackend::Internal { clauses, max_var } => {
                let mut sat_solver =
                    AllSatSolver::build_solver_internal(clauses, *max_var, &self.blocking_clauses)?;
                sat_solver.solve()
            }
            SolverBackend::External(sat_solver) => sat_solver.solve(),
        };
        Ok(classify_backend_result(result))
    }
}

impl Iterator for AllSatIterator<'_> {
    type Item = Solution;

    fn next(&mut self) -> Option<Self::Item> {
        if self.exhausted {
            return None;
        }

        if let Some(max) = self.config.max_solutions {
            if self.solutions_returned >= max {
                // Probe once without yielding or blocking the model. If no
                // additional model exists, exactly `max` solutions is still an
                // exhaustive enumeration rather than a truncation.
                match self.solve_backend() {
                    Ok(BackendStep::Exhausted) => self.finish(AllSatOutcome::Exhaustive),
                    Ok(BackendStep::Unknown) => self.finish(AllSatOutcome::SolverUnknown),
                    Ok(BackendStep::Model(_)) => {
                        self.run_stats.allsat_cap_hits =
                            self.run_stats.allsat_cap_hits.saturating_add(1);
                        self.solver.stats.allsat_cap_hits =
                            self.solver.stats.allsat_cap_hits.saturating_add(1);
                        self.finish(AllSatOutcome::Capped);
                        warn!(
                            event = "allsat_iter_cap_hit",
                            cap = max,
                            solutions_returned = self.solutions_returned,
                            "AllSAT iterator found another model beyond max_solutions; \
                             enumeration is incomplete"
                        );
                    }
                    Err(error) => self.finish_input_error(error),
                }
                return None;
            }
        }

        let step = match self.solve_backend() {
            Ok(step) => step,
            Err(error) => {
                self.finish_input_error(error);
                return None;
            }
        };
        let model = match step {
            BackendStep::Model(model) => model,
            BackendStep::Exhausted => {
                self.finish(AllSatOutcome::Exhaustive);
                return None;
            }
            BackendStep::Unknown => {
                self.finish(AllSatOutcome::SolverUnknown);
                return None;
            }
        };
        let solution = match AllSatSolver::solution_from_model(model, self.external_model_len) {
            Ok(solution) => solution,
            Err(error) => {
                self.finish_input_error(error);
                return None;
            }
        };

        // Create blocking clause using minimal projected cube
        let blocking = match make_blocking_clause(&self.config, &solution, &self.all_vars) {
            Ok(blocking) => blocking,
            Err(error) => {
                self.finish_input_error(error);
                return None;
            }
        };

        let Some(next_solutions_returned) = self.solutions_returned.checked_add(1) else {
            self.finish(AllSatOutcome::CountOverflow);
            return None;
        };
        if u64::try_from(next_solutions_returned).is_err() {
            self.finish(AllSatOutcome::CountOverflow);
            return None;
        }

        match &mut self.solver.backend {
            SolverBackend::Internal { .. } => {
                self.blocking_clauses.push(blocking);
            }
            SolverBackend::External(sat_solver) => {
                sat_solver.add_clause(blocking);
            }
        }

        self.solver.stats.blocking_clauses = self.solver.stats.blocking_clauses.saturating_add(1);
        self.solver.stats.solutions_found = self.solver.stats.solutions_found.saturating_add(1);
        self.run_stats.blocking_clauses = self.run_stats.blocking_clauses.saturating_add(1);
        self.run_stats.solutions_found = self.run_stats.solutions_found.saturating_add(1);
        self.solutions_returned = next_solutions_returned;

        Some(solution)
    }
}

impl Drop for AllSatIterator<'_> {
    fn drop(&mut self) {
        if self.termination.is_none() {
            self.finish(AllSatOutcome::IteratorDropped);
        }
    }
}
