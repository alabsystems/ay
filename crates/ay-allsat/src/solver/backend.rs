// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Backend-specific helpers for model conversion and internal solver rebuilds.

use ay_sat::{Literal, Solver as SatSolver};

use super::{AllSatInputError, AllSatSolver, Solution, SolutionIndexing, SolverBackend};

impl AllSatSolver {
    /// Return the default set of variables for blocking clauses.
    ///
    /// Internal backend: 1-indexed (1..=max_var).
    /// External backend: 0-indexed (0..num_vars).
    pub(super) fn default_vars(&self) -> Result<Vec<u32>, AllSatInputError> {
        match &self.backend {
            SolverBackend::Internal { max_var, .. } => Ok((1..=*max_var).collect()),
            SolverBackend::External(solver) => {
                let count = u32::try_from(solver.user_num_vars()).map_err(|_| {
                    AllSatInputError::BackendVariableCountOutOfRange(solver.user_num_vars())
                })?;
                Ok((0..count).collect())
            }
        }
    }

    pub(super) fn solution_from_model(
        mut model: Vec<bool>,
        external_model_len: Option<usize>,
    ) -> Result<Solution, AllSatInputError> {
        if let Some(expected_len) = external_model_len {
            if model.len() < expected_len {
                let missing = model.len();
                return Err(AllSatInputError::BackendModelMissingVariable(
                    u32::try_from(missing).unwrap_or(u32::MAX),
                ));
            }
            // `push()` allocates an internal selector. It must never leak into
            // a public 0-based user assignment even if a backend model includes
            // internal variables.
            model.truncate(expected_len);
            Ok(Solution::new(model, SolutionIndexing::ZeroBased))
        } else {
            Ok(Solution::new(model, SolutionIndexing::OneBased))
        }
    }

    /// Build a fresh SAT solver with the current clauses plus blocking clauses.
    ///
    /// Only valid for the internal backend.
    pub(super) fn build_solver_internal(
        clauses: &[Vec<Literal>],
        max_var: u32,
        blocking_clauses: &[Vec<Literal>],
    ) -> Result<SatSolver, AllSatInputError> {
        let num_vars = usize::try_from(max_var)
            .ok()
            .and_then(|max| max.checked_add(1))
            .ok_or(AllSatInputError::BackendVariableCountOutOfRange(
                max_var as usize,
            ))?;
        let mut solver = SatSolver::new(num_vars);

        for clause in clauses {
            solver.add_clause(clause.clone());
        }
        for clause in blocking_clauses {
            solver.add_clause(clause.clone());
        }
        Ok(solver)
    }
}
