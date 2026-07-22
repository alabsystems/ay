// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Cube-and-conquer parallel SAT solver.
//!
//! Implements the divide-and-conquer technique for hard combinatorial SAT
//! instances (Heule et al., "Cube and Conquer: Guiding CDCL SAT Solvers by
//! Lookaheads", 2012).
//!
//! ## Algorithm
//!
//! 1. **Cubing phase**: Run lookahead on the formula, branching on
//!    high-quality variables to generate 2^d cubes (partial assignments)
//!    that partition the search space.
//! 2. **Conquer phase**: Solve formula AND cube for each cube using CDCL,
//!    dispatched across worker threads. This is embarrassingly parallel.
//! 3. **Result**: If any cube is SAT, the whole formula is SAT. If all
//!    cubes are UNSAT, the formula is logically UNSAT, but this implementation
//!    returns `UNKNOWN` until it can emit an aggregate UNSAT proof.
//!
//! ## When to use
//!
//! Cube-and-conquer is orthogonal to portfolio solving. It excels on hard
//! combinatorial/crafted instances (Schur numbers, pigeonhole, Ramsey)
//! where CDCL alone struggles. Portfolio solves the SAME formula with
//! different heuristics; cube-and-conquer solves DIFFERENT subproblems.

use crate::dimacs::DimacsFormula;
use crate::literal::Literal;
use crate::solver::{AssumeResult, SatResult, Solver};

use parking_lot::Mutex;
use std::collections::VecDeque;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;
use std::thread;

/// Parallel cube-and-conquer SAT solver.
///
/// Generates cubes via lookahead, then solves each cube in parallel
/// using CDCL with assumptions.
pub struct CubeAndConquerSolver {
    /// Number of worker threads for the conquer phase.
    num_threads: usize,
    /// Lookahead depth for cube generation. Produces up to 2^depth cubes.
    depth: usize,
}

impl CubeAndConquerSolver {
    /// Create a new cube-and-conquer solver.
    ///
    /// `num_threads`: number of parallel CDCL workers for the conquer phase.
    /// `depth`: lookahead depth (typically 10-20). Produces up to 2^depth cubes.
    pub fn new(num_threads: usize, depth: usize) -> Self {
        Self {
            num_threads: num_threads.max(1),
            depth,
        }
    }

    /// Solve a DIMACS formula using cube-and-conquer.
    ///
    /// Phase 1 (cube): generates cubes via lookahead on a temporary solver.
    /// Phase 2 (conquer): dispatches cubes to worker threads that solve
    /// formula AND cube using assumption-based CDCL.
    ///
    /// SAT is direct evidence because the returned model is over the original
    /// variables and can be checked against the original clauses. UNSAT is
    /// fail-closed: per-cube UNSAT results are not enough for SAT-COMP Main
    /// unless an aggregate proof is emitted, so this method intentionally
    /// returns `SatResult::Unknown` for all UNSAT CnC paths, including
    /// non-proof CLI runs, until CnC has an explicit proof-ready mode.
    pub fn solve(&self, formula: &DimacsFormula) -> SatResult {
        // Phase 1: Generate cubes using lookahead.
        let cubes = {
            let mut cubing_solver = Solver::new(formula.num_vars);
            for clause in &formula.clauses {
                cubing_solver.add_clause(clause.clone());
            }
            cubing_solver.generate_cubes(self.depth)
        };

        eprintln!(
            "c cube-and-conquer: {} cubes generated (depth {}), {} threads",
            cubes.len(),
            self.depth,
            self.num_threads,
        );

        // No cubes: UNSAT detected during cubing phase.
        if cubes.is_empty() {
            return Self::unknown_unverified_unsat("cubing");
        }

        // Single empty cube: formula is unsplit, solve normally.
        if cubes.len() == 1 && cubes[0].is_empty() {
            let mut solver = Solver::new(formula.num_vars);
            for clause in &formula.clauses {
                solver.add_clause(clause.clone());
            }
            return match solver.solve().into_inner() {
                SatResult::Unsat(_) => Self::unknown_unverified_unsat("unsplit cdcl"),
                other => other,
            };
        }

        // Phase 2: Conquer -- dispatch cubes to worker threads.
        let terminate = Arc::new(AtomicBool::new(false));
        let sat_result: Arc<Mutex<Option<Vec<bool>>>> = Arc::new(Mutex::new(None));
        let cube_queue: Arc<Mutex<VecDeque<Vec<Literal>>>> =
            Arc::new(Mutex::new(VecDeque::from(cubes)));

        // Track how many cubes returned UNSAT vs Unknown.
        let unsat_count = Arc::new(std::sync::atomic::AtomicUsize::new(0));
        let total_cubes = cube_queue.lock().len();

        thread::scope(|scope| {
            let handles: Vec<_> = (0..self.num_threads)
                .map(|_| {
                    let formula_clauses = &formula.clauses;
                    let num_vars = formula.num_vars;
                    let terminate = Arc::clone(&terminate);
                    let sat_result = Arc::clone(&sat_result);
                    let cube_queue = Arc::clone(&cube_queue);
                    let unsat_count = Arc::clone(&unsat_count);

                    scope.spawn(move || {
                        loop {
                            // Check termination before dequeuing.
                            if terminate.load(Ordering::Relaxed) {
                                break;
                            }

                            // Dequeue next cube.
                            let cube = {
                                let mut queue = cube_queue.lock();
                                queue.pop_front()
                            };

                            let cube = match cube {
                                Some(c) => c,
                                None => break, // No more cubes.
                            };

                            // Create a fresh solver for this cube.
                            let mut solver = Solver::new(num_vars);
                            for clause in formula_clauses {
                                solver.add_clause(clause.clone());
                            }

                            // Solve formula under cube assumptions.
                            let result = solver
                                .solve_with_assumptions_interruptible(&cube, || {
                                    terminate.load(Ordering::Relaxed)
                                })
                                .into_inner();

                            match result {
                                AssumeResult::Sat(model) => {
                                    // SAT: store result and signal termination.
                                    let mut guard = sat_result.lock();
                                    if guard.is_none() {
                                        *guard = Some(model);
                                        terminate.store(true, Ordering::Relaxed);
                                    }
                                    break;
                                }
                                AssumeResult::Unsat(..) => {
                                    unsat_count.fetch_add(1, Ordering::Relaxed);
                                }
                                AssumeResult::Unknown => {
                                    // Cube interrupted (timeout). Continue to next cube.
                                }
                            }
                        }
                    })
                })
                .collect();

            // Wait for all workers to finish.
            for handle in handles {
                let _ = handle.join();
            }
        });

        // Check results.
        let guard = sat_result.lock();
        if let Some(model) = guard.as_ref() {
            return SatResult::Sat(model.clone());
        }
        drop(guard);

        // If all cubes returned UNSAT, formula is UNSAT.
        if unsat_count.load(Ordering::Relaxed) == total_cubes {
            return Self::unknown_unverified_unsat("conquer");
        }

        // Some cubes were interrupted or returned Unknown.
        SatResult::Unknown
    }

    fn unknown_unverified_unsat(stage: &str) -> SatResult {
        eprintln!(
            "c cube-and-conquer: {stage} found UNSAT without an aggregate proof; returning UNKNOWN"
        );
        SatResult::Unknown
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::literal::{Literal, Variable};

    /// Helper: build a DimacsFormula from raw clause data.
    fn make_formula(num_vars: usize, clauses: Vec<Vec<Literal>>) -> DimacsFormula {
        DimacsFormula {
            num_vars,
            num_clauses: clauses.len(),
            clauses,
        }
    }

    fn add_formula_to_solver(formula: &DimacsFormula) -> Solver {
        let mut solver = Solver::new(formula.num_vars);
        for clause in &formula.clauses {
            solver.add_clause(clause.clone());
        }
        solver
    }

    fn all_three_var_assignments_blocked_formula() -> DimacsFormula {
        let v0 = Variable::new(0);
        let v1 = Variable::new(1);
        let v2 = Variable::new(2);
        let vars = [v0, v1, v2];
        let mut clauses = Vec::new();

        for mask in 0..8 {
            let mut clause = Vec::new();
            for (idx, &var) in vars.iter().enumerate() {
                if (mask & (1 << idx)) == 0 {
                    clause.push(Literal::positive(var));
                } else {
                    clause.push(Literal::negative(var));
                }
            }
            clauses.push(clause);
        }

        make_formula(3, clauses)
    }

    #[test]
    fn test_cube_and_conquer_trivial_sat() {
        // x0 AND x1 -- satisfiable
        let v0 = Variable::new(0);
        let v1 = Variable::new(1);
        let formula = make_formula(
            2,
            vec![vec![Literal::positive(v0)], vec![Literal::positive(v1)]],
        );
        let solver = CubeAndConquerSolver::new(2, 1);
        let result = solver.solve(&formula);
        assert!(
            matches!(result, SatResult::Sat(ref model) if model[0] && model[1]),
            "expected SAT with x0=true, x1=true, got {result:?}"
        );
    }

    #[test]
    fn test_cube_and_conquer_unsat_is_fail_closed_unknown() {
        // x0 AND NOT x0 -- unsatisfiable
        let v0 = Variable::new(0);
        let formula = make_formula(
            1,
            vec![vec![Literal::positive(v0)], vec![Literal::negative(v0)]],
        );
        let solver = CubeAndConquerSolver::new(2, 1);
        let result = solver.solve(&formula);
        assert!(
            matches!(result, SatResult::Unknown),
            "proof-incomplete cube-and-conquer must fail closed, got {result:?}"
        );
    }

    #[test]
    fn test_cube_and_conquer_all_conquered_cubes_unsat_requires_aggregate_proof() {
        // Blocks all 2^3 complete assignments with width-3 clauses. Depth 1
        // produces a non-trivial cube split, while each conquered cube is UNSAT.
        let formula = all_three_var_assignments_blocked_formula();

        let cubes = add_formula_to_solver(&formula).generate_cubes(1);
        assert!(
            cubes.len() > 1,
            "test fixture must exercise the conquer aggregation path, got {cubes:?}"
        );

        for cube in &cubes {
            let mut worker = add_formula_to_solver(&formula);
            let result = worker.solve_with_assumptions(cube).into_inner();
            assert!(
                matches!(result, AssumeResult::Unsat(..)),
                "each conquered cube must be locally UNSAT, cube={cube:?}, result={result:?}"
            );
        }

        let solver = CubeAndConquerSolver::new(2, 1);
        let result = solver.solve(&formula);
        assert!(
            matches!(result, SatResult::Unknown),
            "all-cube UNSAT still lacks aggregate proof and must fail closed, got {result:?}"
        );
    }

    #[test]
    fn test_cube_and_conquer_depth_zero_sat() {
        // Depth 0 produces a single empty cube -- solved normally.
        let v0 = Variable::new(0);
        let formula = make_formula(1, vec![vec![Literal::positive(v0)]]);
        let solver = CubeAndConquerSolver::new(1, 0);
        let result = solver.solve(&formula);
        assert!(
            matches!(result, SatResult::Sat(_)),
            "expected SAT, got {result:?}"
        );
    }

    #[test]
    fn test_cube_and_conquer_depth_zero_unsat_is_fail_closed_unknown() {
        let v0 = Variable::new(0);
        let formula = make_formula(
            1,
            vec![vec![Literal::positive(v0)], vec![Literal::negative(v0)]],
        );
        let solver = CubeAndConquerSolver::new(1, 0);
        let result = solver.solve(&formula);
        assert!(
            matches!(result, SatResult::Unknown),
            "unsplit unverified UNSAT must fail closed, got {result:?}"
        );
    }

    #[test]
    fn test_cube_and_conquer_multi_thread() {
        // 4 variables, several clauses, depth 2 -> up to 4 cubes, 4 threads
        let v0 = Variable::new(0);
        let v1 = Variable::new(1);
        let v2 = Variable::new(2);
        let v3 = Variable::new(3);
        let formula = make_formula(
            4,
            vec![
                vec![Literal::positive(v0), Literal::positive(v1)],
                vec![Literal::negative(v1), Literal::positive(v2)],
                vec![Literal::negative(v2), Literal::positive(v3)],
                vec![Literal::positive(v0), Literal::negative(v3)],
            ],
        );
        let solver = CubeAndConquerSolver::new(4, 2);
        let result = solver.solve(&formula);
        assert!(
            matches!(result, SatResult::Sat(_)),
            "expected SAT, got {result:?}"
        );
    }
}
