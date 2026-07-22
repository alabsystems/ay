// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! ALL-SAT Solver Implementation
//!
//! This module implements solution enumeration using iterative SAT solving
//! with blocking clauses. Supports two backends:
//!
//! - **Internal**: Clauses accumulated in memory; a fresh SAT solver is built
//!   for each enumeration call (backwards-compatible default).
//! - **External**: An existing `ay_sat::Solver` is passed in; blocking clauses
//!   are added incrementally, preserving learned clauses between iterations.

use ay_sat::{Literal, SignedClause, Solver as SatSolver, Variable};
use tracing::warn;

/// Default safety limit for model enumeration (#8625).
///
/// The `enumerate()` and `iter()` convenience methods apply this cap to
/// prevent accidental OOM on problems with exponentially many models. Use
/// `enumerate_with_config()` or `iter_with_config()` with an explicit
/// `max_solutions` to override.
const DEFAULT_MAX_SOLUTIONS: usize = 1_000_000;

/// A satisfying assignment.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct Solution {
    /// Assignment: index is variable number, value is true/false.
    /// Index 0 is unused (variables are 1-indexed).
    pub assignment: Vec<bool>,
}

impl Solution {
    /// Get the value of a variable in this solution.
    pub fn get(&self, var: u32) -> Option<bool> {
        self.assignment.get(var as usize).copied()
    }

    /// Check if a variable is true in this solution.
    pub fn is_true(&self, var: u32) -> bool {
        self.get(var).unwrap_or(false)
    }

    /// Check if a literal is satisfied by this solution.
    pub fn satisfies(&self, lit: i32) -> bool {
        let var = lit.unsigned_abs() as usize;
        let polarity = lit > 0;
        self.assignment.get(var).copied().unwrap_or(false) == polarity
    }

    /// Convert to a vector of literals representing this assignment.
    /// Returns positive literal if var=true, negative if var=false.
    pub fn to_literals(&self, vars: &[u32]) -> Vec<i32> {
        vars.iter()
            .map(|&v| {
                if self.is_true(v) {
                    v as i32
                } else {
                    -(v as i32)
                }
            })
            .collect()
    }
}

/// Configuration for ALL-SAT enumeration.
#[derive(Debug, Clone, Default)]
pub struct AllSatConfig {
    /// Maximum number of solutions to enumerate (None = unlimited).
    pub max_solutions: Option<usize>,

    /// Variables to project onto (None = all variables).
    /// When set, blocking clauses only reference these variables,
    /// effectively finding all distinct assignments to projected vars.
    pub projection: Option<Vec<u32>>,
}

/// Whether an AllSAT enumeration was exhaustive or truncated.
///
/// This is important for consumers that rely on complete enumeration (e.g.,
/// interpolant computation). A truncated enumeration produces a weaker result
/// that may still be sound but is not exact.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
#[derive(Default)]
pub enum AllSatOutcome {
    /// All solutions were enumerated; the result is exact.
    #[default]
    Exhaustive,
    /// Enumeration was truncated because the `max_solutions` cap was reached.
    /// The `solutions_found` field of [`AllSatStats`] indicates how many were
    /// enumerated before the cap was hit.
    Capped,
}

/// Statistics for ALL-SAT solving.
#[derive(Debug, Clone, Default)]
#[non_exhaustive]
pub struct AllSatStats {
    /// Number of SAT solver calls.
    pub sat_calls: u64,
    /// Number of solutions found.
    pub solutions_found: u64,
    /// Number of blocking clauses added.
    pub blocking_clauses: u64,
    /// Number of times the solution cap (`max_solutions`) was reached,
    /// meaning enumeration was truncated rather than exhaustive.
    pub allsat_cap_hits: u64,
    /// Whether the most recent enumeration was exhaustive or capped.
    pub outcome: AllSatOutcome,
}

/// Backend for the ALL-SAT solver.
///
/// Internal mode stores clauses and rebuilds a fresh solver per iteration.
/// External mode wraps a caller-provided solver and adds blocking clauses
/// incrementally, preserving learned clauses.
///
/// Indexing convention: the internal backend uses 1-indexed variables
/// (matching the `SignedClause` convention where variable 0 is unused).
/// The external backend uses 0-indexed variables (matching ay-sat's
/// native `Variable::new(idx)` convention).
enum SolverBackend {
    /// Clauses accumulated internally; fresh solver built per call.
    /// Variables are 1-indexed: variable indices go from 1 to max_var.
    Internal {
        clauses: Vec<Vec<Literal>>,
        max_var: u32,
    },
    /// External solver; blocking clauses added incrementally.
    /// Variables are 0-indexed: variable indices go from 0 to num_vars-1.
    External(Box<SatSolver>),
}

/// ALL-SAT Solver
///
/// Enumerates all satisfying assignments to a Boolean formula.
///
/// Two construction modes:
/// - [`AllSatSolver::new()`]: Internal mode — accumulate clauses, rebuild solver
///   each iteration. Simple and correct.
/// - [`AllSatSolver::from_solver()`]: External mode — wrap an existing SAT solver,
///   add blocking clauses incrementally. Preserves learned clauses between
///   iterations for better performance on large formulas.
pub struct AllSatSolver {
    backend: SolverBackend,
    stats: AllSatStats,
}

impl AllSatSolver {
    /// Create a new ALL-SAT solver (internal backend).
    ///
    /// Clauses are accumulated via [`add_clause`](Self::add_clause) and a fresh
    /// SAT solver is constructed for each enumeration call.
    pub fn new() -> Self {
        Self {
            backend: SolverBackend::Internal {
                clauses: Vec::new(),
                max_var: 0,
            },
            stats: AllSatStats::default(),
        }
    }

    /// Create an ALL-SAT solver wrapping an existing SAT solver (external backend).
    ///
    /// The solver should already have clauses loaded. Blocking clauses are added
    /// incrementally to the same solver instance, preserving learned clauses
    /// between iterations. This is more efficient for large formulas and useful
    /// when the caller wants to share learned clauses with other solving tasks.
    pub fn from_solver(solver: SatSolver) -> Self {
        Self {
            backend: SolverBackend::External(Box::new(solver)),
            stats: AllSatStats::default(),
        }
    }

    /// Add a clause to the formula.
    ///
    /// Literals use signed integer encoding: positive = positive literal,
    /// negative = negated literal. E.g., `vec![1, -2]` means x1 OR NOT x2.
    pub fn add_clause(&mut self, clause: SignedClause) {
        let lits: Vec<Literal> = clause.iter().map(|&l| Literal::from(l)).collect();
        match &mut self.backend {
            SolverBackend::Internal {
                ref mut clauses,
                ref mut max_var,
            } => {
                for &lit in &clause {
                    let var = lit.unsigned_abs();
                    *max_var = (*max_var).max(var);
                }
                clauses.push(lits);
            }
            SolverBackend::External(solver) => {
                solver.add_clause(lits);
            }
        }
    }

    /// Get the number of variables.
    ///
    /// For the internal backend this is the maximum variable index seen.
    /// For the external backend this is the solver's user variable count.
    pub fn num_vars(&self) -> u32 {
        match &self.backend {
            SolverBackend::Internal { max_var, .. } => *max_var,
            SolverBackend::External(solver) => solver.user_num_vars() as u32,
        }
    }

    /// Get solver statistics.
    pub fn stats(&self) -> &AllSatStats {
        &self.stats
    }

    /// Create an iterator over all solutions.
    ///
    /// Applies `DEFAULT_MAX_SOLUTIONS` as a safety cap to prevent OOM on
    /// problems with exponentially many models. Use [`iter_with_config`](Self::iter_with_config)
    /// with an explicit `max_solutions` to override (#8625).
    pub fn iter(&mut self) -> AllSatIterator<'_> {
        let config = AllSatConfig {
            max_solutions: Some(DEFAULT_MAX_SOLUTIONS),
            ..Default::default()
        };
        self.iter_with_config(config)
    }

    /// Create an iterator with custom configuration.
    pub fn iter_with_config(&mut self, config: AllSatConfig) -> AllSatIterator<'_> {
        AllSatIterator::new(self, config)
    }

    /// Enumerate all solutions (convenience method).
    ///
    /// Applies `DEFAULT_MAX_SOLUTIONS` as a safety cap. Use
    /// [`enumerate_with_config`](Self::enumerate_with_config) to override (#8625).
    pub fn enumerate(&mut self) -> Vec<Solution> {
        self.iter().collect()
    }

    /// Enumerate solutions with custom configuration (convenience method).
    pub fn enumerate_with_config(&mut self, config: AllSatConfig) -> Vec<Solution> {
        self.iter_with_config(config).collect()
    }

    /// Enumerate solutions via callback without collecting them.
    ///
    /// The callback receives each solution as it is found. Return `true` to
    /// continue enumeration, `false` to stop early. Returns statistics for
    /// the enumeration run.
    ///
    /// This is useful for large state spaces where collecting all solutions
    /// into a `Vec` would be prohibitively expensive.
    pub fn enumerate_with_callback<F>(
        &mut self,
        config: AllSatConfig,
        mut callback: F,
    ) -> AllSatStats
    where
        F: FnMut(&Solution) -> bool,
    {
        let mut local_stats = AllSatStats::default();
        let mut blocking_clauses: Vec<Vec<Literal>> = Vec::new();
        let mut solutions_found: usize = 0;
        let all_vars = self.default_vars();

        loop {
            // Check solution limit
            if let Some(max) = config.max_solutions {
                if solutions_found >= max {
                    local_stats.allsat_cap_hits += 1;
                    local_stats.outcome = AllSatOutcome::Capped;
                    warn!(
                        event = "allsat_cap_hit",
                        cap = max,
                        solutions_found,
                        "AllSAT enumeration truncated at max_solutions cap; \
                         result may be weaker than exact"
                    );
                    break;
                }
            }

            // Solve
            local_stats.sat_calls += 1;
            let model = match &mut self.backend {
                SolverBackend::Internal { clauses, max_var } => {
                    let mut solver = SatSolver::new((*max_var + 1) as usize);
                    for clause in clauses.iter() {
                        solver.add_clause(clause.clone());
                    }
                    for clause in &blocking_clauses {
                        solver.add_clause(clause.clone());
                    }
                    solver.solve().into_model()
                }
                SolverBackend::External(solver) => solver.solve().into_model(),
            };

            let Some(model) = model else {
                break;
            };

            let solution = Solution { assignment: model };

            // Build blocking clause using minimal projected cube
            let blocking = make_blocking_clause(&config, &solution, &all_vars);
            local_stats.blocking_clauses += 1;
            local_stats.solutions_found += 1;
            solutions_found += 1;

            // Add blocking clause to appropriate backend
            match &mut self.backend {
                SolverBackend::Internal { .. } => {
                    blocking_clauses.push(blocking);
                }
                SolverBackend::External(solver) => {
                    solver.add_clause(blocking);
                }
            }

            // Invoke callback; stop if it returns false
            if !callback(&solution) {
                break;
            }
        }

        // Accumulate into persistent stats
        self.stats.sat_calls += local_stats.sat_calls;
        self.stats.solutions_found += local_stats.solutions_found;
        self.stats.blocking_clauses += local_stats.blocking_clauses;
        self.stats.allsat_cap_hits += local_stats.allsat_cap_hits;
        self.stats.outcome = local_stats.outcome;

        local_stats
    }

    /// Count the number of solutions without storing them.
    pub fn count(&mut self) -> u64 {
        self.count_with_config(AllSatConfig::default())
    }

    /// Count with custom configuration.
    pub fn count_with_config(&mut self, config: AllSatConfig) -> u64 {
        let mut count = 0u64;
        self.enumerate_with_callback(config, |_| {
            count += 1;
            true
        });
        count
    }

    /// Check if the formula is satisfiable.
    pub fn is_sat(&mut self) -> bool {
        let config = AllSatConfig {
            max_solutions: Some(1),
            ..Default::default()
        };
        self.count_with_config(config) > 0
    }

    /// Check if the formula has exactly one solution.
    pub fn has_unique_solution(&mut self) -> bool {
        let config = AllSatConfig {
            max_solutions: Some(2),
            ..Default::default()
        };
        self.count_with_config(config) == 1
    }

    /// Return the default set of variables for blocking clauses.
    ///
    /// Internal backend: 1-indexed (1..=max_var).
    /// External backend: 0-indexed (0..num_vars).
    fn default_vars(&self) -> Vec<u32> {
        match &self.backend {
            SolverBackend::Internal { max_var, .. } => (1..=*max_var).collect(),
            SolverBackend::External(solver) => (0..solver.user_num_vars() as u32).collect(),
        }
    }

    /// Build a fresh SAT solver with the current clauses plus blocking clauses.
    ///
    /// Only valid for the internal backend.
    fn build_solver_internal(
        clauses: &[Vec<Literal>],
        max_var: u32,
        blocking_clauses: &[Vec<Literal>],
    ) -> SatSolver {
        let mut solver = SatSolver::new((max_var + 1) as usize);

        for clause in clauses {
            solver.add_clause(clause.clone());
        }

        for clause in blocking_clauses {
            solver.add_clause(clause.clone());
        }

        solver
    }
}

impl Default for AllSatSolver {
    fn default() -> Self {
        Self::new()
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
) -> Vec<Literal> {
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
            if solution.is_true(v) {
                Literal::negative(var)
            } else {
                Literal::positive(var)
            }
        })
        .collect()
}

/// Iterator over all solutions.
pub struct AllSatIterator<'a> {
    solver: &'a mut AllSatSolver,
    config: AllSatConfig,
    /// Default variable set for blocking clauses (precomputed from backend).
    all_vars: Vec<u32>,
    /// Blocking clauses accumulated during this iteration (internal backend only).
    blocking_clauses: Vec<Vec<Literal>>,
    solutions_returned: usize,
    exhausted: bool,
    /// Whether the iteration cap was hit (vs. natural exhaustion).
    capped: bool,
}

impl AllSatIterator<'_> {
    /// Returns the outcome of this iteration: whether all solutions were
    /// enumerated ([`AllSatOutcome::Exhaustive`]) or the `max_solutions` cap
    /// was reached ([`AllSatOutcome::Capped`]).
    ///
    /// This is only meaningful after the iterator has been fully consumed
    /// (i.e., `next()` returned `None`). While still iterating, it reflects
    /// the state so far.
    pub fn outcome(&self) -> AllSatOutcome {
        if self.capped {
            AllSatOutcome::Capped
        } else {
            AllSatOutcome::Exhaustive
        }
    }
}

impl<'a> AllSatIterator<'a> {
    fn new(solver: &'a mut AllSatSolver, config: AllSatConfig) -> Self {
        let all_vars = solver.default_vars();
        Self {
            solver,
            config,
            all_vars,
            blocking_clauses: Vec::new(),
            solutions_returned: 0,
            exhausted: false,
            capped: false,
        }
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
                if !self.capped {
                    self.capped = true;
                    self.solver.stats.allsat_cap_hits += 1;
                    self.solver.stats.outcome = AllSatOutcome::Capped;
                    warn!(
                        event = "allsat_iter_cap_hit",
                        cap = max,
                        solutions_returned = self.solutions_returned,
                        "AllSAT iterator reached max_solutions cap; \
                         enumeration is incomplete and result may be weaker"
                    );
                }
                return None;
            }
        }

        // Solve using the appropriate backend
        self.solver.stats.sat_calls += 1;

        let model = match &mut self.solver.backend {
            SolverBackend::Internal { clauses, max_var } => {
                let mut sat_solver =
                    AllSatSolver::build_solver_internal(clauses, *max_var, &self.blocking_clauses);
                sat_solver.solve().into_model()
            }
            SolverBackend::External(sat_solver) => sat_solver.solve().into_model(),
        };

        let model = model?;
        let solution = Solution { assignment: model };

        // Create blocking clause using minimal projected cube
        let blocking = make_blocking_clause(&self.config, &solution, &self.all_vars);

        match &mut self.solver.backend {
            SolverBackend::Internal { .. } => {
                self.blocking_clauses.push(blocking);
            }
            SolverBackend::External(sat_solver) => {
                sat_solver.add_clause(blocking);
            }
        }

        self.solver.stats.blocking_clauses += 1;
        self.solver.stats.solutions_found += 1;
        self.solutions_returned += 1;

        Some(solution)
    }
}

#[cfg(test)]
#[path = "solver_tests.rs"]
mod tests;
