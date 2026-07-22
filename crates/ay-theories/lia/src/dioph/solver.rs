// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::DetHashMap as HashMap;
use num_bigint::BigInt;
use num_traits::Zero;

use super::equation::IntEquation;

/// Result of solving a system of Diophantine equations
#[derive(Debug)]
pub(crate) enum DiophResult {
    /// System is infeasible - no integer solutions exist.
    /// Contains the indices of original input equations that form the
    /// infeasibility proof.  When empty, the caller should fall back to
    /// using all equations (backwards-compatible).
    Infeasible { sources: Vec<usize> },
    /// System has solutions, with some variables uniquely determined
    /// Maps variable index -> value
    Solved(HashMap<usize, BigInt>),
    /// System is underdetermined - some free variables remain
    Partial { determined: HashMap<usize, BigInt> },
}

/// Diophantine equation system solver
pub(crate) struct DiophSolver {
    /// The equations in the system
    pub(super) equations: Vec<IntEquation>,
    /// Variables that have been eliminated (var -> (coeffs, constant))
    /// Meaning: var = constant + Σ(coeff * other_var)
    pub(super) substitutions: HashMap<usize, (HashMap<usize, BigInt>, BigInt)>,
    /// Next available fresh variable index
    pub(super) next_fresh_var: usize,
    /// The original-variable boundary. Indices `< first_fresh_id` are caller
    /// (original) variables; indices `>= first_fresh_id` are fresh variables
    /// introduced during coefficient reduction. Fresh variables are internal to
    /// elimination and must NOT leak into the `Solved`/`Partial` result maps.
    first_fresh_id: usize,
    /// Maximum consecutive rounds where the global minimum coefficient
    /// stays flat before the solver breaks out of the elimination loop.
    pub(super) max_stall_rounds: usize,
    /// Debug flag
    pub(super) debug: bool,
}

impl DiophSolver {
    /// Create a new solver.
    ///
    /// `first_fresh_id` must be greater than any variable index that will appear
    /// in equations added to this solver. Fresh variables introduced during
    /// coefficient reduction are allocated starting from this value.
    pub(crate) fn new(first_fresh_id: usize) -> Self {
        Self {
            equations: Vec::new(),
            substitutions: HashMap::default(),
            next_fresh_var: first_fresh_id,
            first_fresh_id,
            max_stall_rounds: 64,
            debug: ay_core::debug_channel_active(ay_core::DebugChannel::Dioph),
        }
    }

    /// Add an equation to the system.
    ///
    /// All variable indices in the equation must be less than `first_fresh_id`.
    pub(crate) fn add_equation(&mut self, eq: IntEquation) {
        assert!(
            eq.coeffs.keys().all(|&v| v < self.next_fresh_var),
            "BUG: equation contains variable index >= first_fresh_id ({}); \
             this will collide with fresh variables",
            self.next_fresh_var,
        );
        self.equations.push(eq);
    }

    /// Add an equation from coefficients and constant (no provenance tracking).
    #[cfg(test)]
    pub(crate) fn add_equation_from(
        &mut self,
        coeffs: impl IntoIterator<Item = (usize, BigInt)>,
        constant: BigInt,
    ) {
        let coeffs_map: HashMap<usize, BigInt> = coeffs.into_iter().collect();
        self.add_equation(IntEquation::new(coeffs_map, constant));
    }

    /// Add an equation from coefficients and constant, with provenance tracking.
    /// `source_idx` is the index of this equation in the caller's equality list.
    pub(crate) fn add_equation_with_source(
        &mut self,
        coeffs: impl IntoIterator<Item = (usize, BigInt)>,
        constant: BigInt,
        source_idx: usize,
    ) {
        let coeffs_map: HashMap<usize, BigInt> = coeffs.into_iter().collect();
        let eq = IntEquation::with_source(coeffs_map, constant, source_idx);
        self.add_equation(eq);
    }

    /// Return original-variable indices that are safely dependent on other original variables.
    ///
    /// A variable is considered "safe dependent" if we have derived a substitution for it
    /// that references only original variables (no fresh variables introduced during
    /// coefficient reduction). Such variables are typically poor branching choices in
    /// the outer LIA solver because their integrality is implied by the referenced vars.
    pub(crate) fn safe_original_dependents(&self, num_original_vars: usize) -> Vec<usize> {
        let mut vars: Vec<usize> = self
            .substitutions
            .iter()
            .filter_map(|(&var, (coeffs, _))| {
                let is_original = var < num_original_vars;
                let depends_only_on_original = coeffs.keys().all(|&v| v < num_original_vars);
                (is_original && depends_only_on_original).then_some(var)
            })
            .collect();
        vars.sort_unstable();
        vars
    }

    #[cfg(test)]
    pub(super) fn next_fresh_var_for_tests(&self) -> usize {
        self.next_fresh_var
    }

    /// Override the stall counter threshold for testing.
    #[cfg(test)]
    pub(super) fn set_max_stall_rounds(&mut self, rounds: usize) {
        self.max_stall_rounds = rounds;
    }

    /// Return an Infeasible result carrying the sources of the given equation.
    pub(super) fn infeasible_from(eq: &IntEquation) -> DiophResult {
        DiophResult::Infeasible {
            sources: eq.sources.clone(),
        }
    }

    /// Solve single-variable equations (c*x = d) after elimination.
    ///
    /// Returns `Err(DiophResult::Infeasible)` if any single-var equation
    /// is not divisible (no integer solution).  Otherwise returns determined
    /// variable values and stores them in self.substitutions.
    fn solve_single_var_equations(&mut self) -> Result<HashMap<usize, BigInt>, DiophResult> {
        let mut determined: HashMap<usize, BigInt> = HashMap::default();
        let mut idx = 0;
        while idx < self.equations.len() {
            let eq = &self.equations[idx];
            if eq.coeffs.len() == 1 {
                let (&var, coeff) = eq.coeffs.iter().next().unwrap();
                let constant = &eq.constant;

                if !(constant % coeff).is_zero() {
                    if self.debug {
                        safe_eprintln!(
                            "[DIOPH] Infeasible single-var eq: {}*x = {} (not divisible)",
                            coeff,
                            constant
                        );
                    }
                    return Err(Self::infeasible_from(eq));
                }

                let value = constant / coeff;
                if self.debug {
                    safe_eprintln!("[DIOPH] Solved single-var eq: var {} = {}", var, value);
                }
                determined.insert(var, value);
                self.equations.remove(idx);
            } else {
                idx += 1;
            }
        }

        for (&var, value) in &determined {
            self.substitutions
                .insert(var, (HashMap::default(), value.clone()));
        }

        Ok(determined)
    }

    /// Back-substitute determined values through substitution definitions.
    fn back_substitute(&self, determined: &mut HashMap<usize, BigInt>) {
        let mut progress = true;
        while progress {
            progress = false;
            for (&var, (coeffs, constant)) in &self.substitutions {
                if determined.contains_key(&var) {
                    continue;
                }
                if coeffs.is_empty() || coeffs.keys().all(|v| determined.contains_key(v)) {
                    let mut value = constant.clone();
                    for (&other_var, coeff) in coeffs {
                        if let Some(other_val) = determined.get(&other_var) {
                            value += coeff * other_val;
                        }
                    }
                    determined.insert(var, value);
                    progress = true;
                }
            }
        }
    }

    /// Solve the system using variable elimination.
    pub(crate) fn solve(&mut self) -> DiophResult {
        if self.debug {
            safe_eprintln!("[DIOPH] Starting with {} equations", self.equations.len());
        }

        for eq in &self.equations {
            if eq.gcd_infeasible() {
                if self.debug {
                    safe_eprintln!("[DIOPH] GCD infeasibility detected");
                }
                return Self::infeasible_from(eq);
            }
        }

        for eq in &mut self.equations {
            eq.normalize();
        }

        if let Some(result) = self.elimination_loop() {
            return result;
        }

        let mut determined = match self.solve_single_var_equations() {
            Ok(d) => d,
            Err(infeasible) => return infeasible,
        };

        self.back_substitute(&mut determined);

        if self.debug {
            safe_eprintln!(
                "[DIOPH] Solved: {} determined variables, {} remaining equations",
                determined.len(),
                self.equations.len()
            );
        }

        // The Solved/Partial result must expose ONLY original-variable
        // assignments. solve_single_var_equations and back_substitute also record
        // values for fresh variables (indices >= first_fresh_id) introduced during
        // coefficient reduction, but those are internal to elimination and have no
        // caller-visible term. Leaking them tripped a debug_assert in dioph_bridge
        // ("Solved value has out-of-range var index") -- e.g. on a 2x2 system with
        // no unit coefficients like 2x+3y=13, 4x+5y=23 -- crashing debug builds;
        // in release the bridge's range guard silently dropped them. Decide
        // Solved-vs-Partial on the FULL determined set (preserving the "every
        // substituted variable is determined" invariant), THEN strip fresh
        // variables from the returned map so the result contract holds.
        let solved_fully =
            self.equations.is_empty() && determined.len() == self.substitutions.len();
        determined.retain(|&var, _| var < self.first_fresh_id);
        if solved_fully {
            DiophResult::Solved(determined)
        } else {
            DiophResult::Partial { determined }
        }
    }
}
