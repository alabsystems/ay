// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Model minimization and projection helpers.
//!
//! `try_minimize_model()` greedily simplifies BV variable assignments using an
//! expanded candidate list (0, 1, all-ones, nearest power of 2) with a budget
//! cap of 1000 incremental checks. `project_model()` filters the current model
//! to a set of interesting variable names. `infer_relevant_vars()` heuristically
//! identifies user-declared "input" variables.

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};

use ay_core::Sort;
use num_bigint::BigInt;
use num_traits::One;

use crate::api::types::{ModelValue, SolveResult, SolverError, Term};
use crate::api::Solver;

/// Maximum number of incremental satisfiability checks during model
/// minimization. Prevents excessive runtime on models with many variables.
const MINIMIZATION_BUDGET: usize = 1000;

/// Check whether `assertion` is satisfiable in the current state without
/// permanently modifying the assertion stack.
fn check_sat_with_assertion(solver: &mut Solver, assertion: Term) -> Result<bool, SolverError> {
    solver.try_push()?;
    let result = (|| -> Result<bool, SolverError> {
        solver.try_assert_term(assertion)?;
        Ok(solver.check_sat() == SolveResult::Sat)
    })();
    let pop_result = solver.try_pop();

    match (result, pop_result) {
        (Ok(is_sat), Ok(())) => Ok(is_sat),
        (_, Err(err)) => Err(err),
        (Err(err), Ok(())) => Err(err),
    }
}

/// Permanently assert `term == value` (a BV equality) in the current scope.
fn pin_bv_value(
    solver: &mut Solver,
    term: Term,
    value: &BigInt,
    width: u32,
) -> Result<(), SolverError> {
    let value_term = solver.try_bv_const_bigint(value, width)?;
    let equality = solver.try_eq(term, value_term)?;
    solver.try_assert_term(equality)
}

/// Permanently assert `term == value` (an Int equality) in the current scope.
fn pin_int_value(solver: &mut Solver, term: Term, value: &BigInt) -> Result<(), SolverError> {
    let value_term = solver.int_const_bigint(value);
    let equality = solver.try_eq(term, value_term)?;
    solver.try_assert_term(equality)
}

/// Generate BV minimization candidates for a given width and current value.
///
/// Candidate order (first feasible wins):
/// 1. 0x0
/// 2. 0x1
/// 3. 0xFF...F (all-ones / unsigned -1)
/// 4. Nearest power of 2 to the original value
fn bv_candidates(width: u32, current: &BigInt) -> Vec<BigInt> {
    let zero = BigInt::from(0u8);
    let one = BigInt::from(1u8);
    let all_ones: BigInt = (BigInt::one() << width) - 1;

    let mut candidates = vec![zero, one, all_ones.clone()];

    // Nearest power of 2: find the highest set bit position in current value
    // and generate 2^k for that position.
    if *current > BigInt::from(1u8) {
        let bits = current.bits();
        // 2^(bits-1) is the nearest (lower) power of 2
        let pow2 = BigInt::one() << (bits - 1);
        if !candidates.contains(&pow2) {
            candidates.push(pow2);
        }
        // Also try 2^bits (nearest upper power of 2) if it fits in width
        if bits < u64::from(width) {
            let pow2_upper = BigInt::one() << bits;
            if pow2_upper <= all_ones && !candidates.contains(&pow2_upper) {
                candidates.push(pow2_upper);
            }
        }
    }

    candidates
}

/// Generate Int minimization candidates for a given current value.
///
/// Candidate order: 0, 1, -1, then powers of 10 up to the magnitude of the
/// current value (ascending). The caller picks the first feasible candidate.
fn int_candidates(current: &BigInt) -> Vec<BigInt> {
    let mut candidates = vec![BigInt::from(0), BigInt::from(1), BigInt::from(-1)];

    // Add powers of 10 up to the magnitude of the current value.
    let magnitude = if current.sign() == num_bigint::Sign::Minus {
        -current
    } else {
        current.clone()
    };

    let mut pow10 = BigInt::from(10);
    while pow10 <= magnitude {
        if !candidates.contains(&pow10) {
            candidates.push(pow10.clone());
        }
        let neg = -pow10.clone();
        if !candidates.contains(&neg) {
            candidates.push(neg);
        }
        pow10 *= 10;
    }

    candidates
}

impl Solver {
    /// Minimize the current SAT model by pinning declared bitvector variables to
    /// simpler values when those choices preserve satisfiability.
    ///
    /// Candidate priority for BV: 0x0, 0x1, 0xFF...F, nearest power of 2,
    /// then original value. Integer variables are also minimized toward 0, 1,
    /// -1, and powers of 10.
    ///
    /// This method must be called after a SAT result is available. On success,
    /// it pushes one new scope and leaves that scope active with equality
    /// assertions pinning each declared variable to its minimized value.
    /// Call [`try_pop`](Self::try_pop) to discard the minimization scope.
    ///
    /// The method refreshes the model after each permanent pin so later
    /// variables are minimized against the current pinned state rather than the
    /// original pre-minimization model.
    ///
    /// A budget of 1000 incremental checks is enforced. Once exhausted,
    /// remaining variables keep their current values.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError::NoResult`] if no solve has been performed, or
    /// [`SolverError::NotSat`] if the last result was not SAT.
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_minimize_model(&mut self) -> Result<(), SolverError> {
        // Collect BV variables: (name, term_id, width).
        let bv_vars: Vec<(String, Term, u32)> = self
            .declared_variables()
            .filter_map(|(name, term)| match self.var_sorts.get(&term.0) {
                Some(Sort::BitVec(bv)) if bv.width > 0 => Some((name.to_string(), term, bv.width)),
                _ => None,
            })
            .collect();

        // Collect Int variables: (name, term_id).
        let int_vars: Vec<(String, Term)> = self
            .declared_variables()
            .filter_map(|(name, term)| match self.var_sorts.get(&term.0) {
                Some(Sort::Int) => Some((name.to_string(), term)),
                _ => None,
            })
            .collect();

        // A non-empty minimization may issue many decision probes. Reject that
        // operation before consulting last-result state: an earlier mutation or
        // rejected composite query legitimately retires the result, but the
        // process-wide single-query exporter must still invalidate any stale
        // artifact and return its typed boundary error. The empty-variable case
        // performs no probes and remains an allowed no-op after a SAT result.
        if !bv_vars.is_empty() || !int_vars.is_empty() {
            self.reject_composite_bv_cnf_export("try_minimize_model")?;
        }

        let last_result = self.executor.last_result().ok_or(SolverError::NoResult)?;
        if !last_result.is_sat() {
            return Err(SolverError::NotSat);
        }

        if bv_vars.is_empty() && int_vars.is_empty() {
            return Ok(());
        }

        // Push a minimization scope so the caller can pop to restore.
        self.try_push()?;
        let result = self.minimize_vars(&bv_vars, &int_vars);

        if let Err(ref _err) = result {
            // Roll back the minimization scope on failure.
            let _ = self.try_pop();
        }
        result
    }

    /// Inner loop: try to simplify each variable, pinning the result.
    /// Respects `MINIMIZATION_BUDGET` for total incremental checks.
    fn minimize_vars(
        &mut self,
        bv_vars: &[(String, Term, u32)],
        int_vars: &[(String, Term)],
    ) -> Result<(), SolverError> {
        // Re-check to refresh the model inside the new scope.
        if self.check_sat() != SolveResult::Sat {
            return Err(SolverError::ModelGenerationFailed(
                "failed to refresh SAT model before minimization".to_string(),
            ));
        }

        let mut budget_remaining = MINIMIZATION_BUDGET;

        // Minimize BV variables first.
        for (name, term, width) in bv_vars {
            if budget_remaining == 0 {
                break;
            }
            let current = self.try_get_value(*term)?;
            let (current_value, model_width) = current.try_bv()?;
            if model_width != *width {
                return Err(SolverError::ModelGenerationFailed(format!(
                    "bitvector width mismatch for `{name}`: \
                     sort has width {width}, model has width {model_width}"
                )));
            }
            let current_value = current_value.clone();

            let candidates = bv_candidates(*width, &current_value);
            let mut chosen = None;
            for candidate in &candidates {
                if *candidate == current_value {
                    // Already at this value, no need to re-check.
                    chosen = Some(candidate.clone());
                    break;
                }
                if budget_remaining == 0 {
                    break;
                }
                budget_remaining -= 1;
                let candidate_term = self.try_bv_const_bigint(candidate, *width)?;
                let equality = self.try_eq(*term, candidate_term)?;
                if check_sat_with_assertion(self, equality)? {
                    chosen = Some(candidate.clone());
                    break;
                }
            }

            let chosen = chosen.unwrap_or(current_value);
            pin_bv_value(self, *term, &chosen, *width)?;

            // Re-check to refresh the model for subsequent variables.
            if self.check_sat() != SolveResult::Sat {
                return Err(SolverError::ModelGenerationFailed(format!(
                    "model minimization produced a non-sat state while pinning `{name}`"
                )));
            }
        }

        // Minimize Int variables.
        for (name, term) in int_vars {
            if budget_remaining == 0 {
                break;
            }
            let current = self.try_get_value(*term)?;
            let current_value = current.try_int()?.clone();

            let candidates = int_candidates(&current_value);
            let mut chosen = None;
            for candidate in &candidates {
                if *candidate == current_value {
                    chosen = Some(candidate.clone());
                    break;
                }
                if budget_remaining == 0 {
                    break;
                }
                budget_remaining -= 1;
                let candidate_term = self.int_const_bigint(candidate);
                let equality = self.try_eq(*term, candidate_term)?;
                if check_sat_with_assertion(self, equality)? {
                    chosen = Some(candidate.clone());
                    break;
                }
            }

            let chosen = chosen.unwrap_or(current_value);
            pin_int_value(self, *term, &chosen)?;

            // Re-check to refresh the model for subsequent variables.
            if self.check_sat() != SolveResult::Sat {
                return Err(SolverError::ModelGenerationFailed(format!(
                    "model minimization produced a non-sat state while pinning `{name}`"
                )));
            }
        }

        Ok(())
    }

    /// Return a projection of the current model onto the requested variable names.
    ///
    /// This is a pure filter over [`model_map`](Self::model_map): it performs no
    /// additional solving or model recomputation. If no current model is
    /// available, an empty map is returned.
    #[must_use]
    pub fn project_model(&self, vars: &[&str]) -> HashMap<String, ModelValue> {
        if vars.is_empty() {
            return HashMap::default();
        }

        let Some(model) = self.model_map() else {
            return HashMap::default();
        };

        let filter: HashSet<&str> = vars.iter().copied().collect();
        model
            .into_iter()
            .filter(|(name, _)| filter.contains(name.as_str()))
            .collect()
    }

    /// Heuristically identify "relevant" (input) variables by excluding variables
    /// that are defined purely as functions of other variables.
    ///
    /// The heuristic: a declared variable is "relevant" if it is not an internal
    /// encoding variable (names starting with `!` or containing `@` are
    /// typically solver-generated). All user-declared variables (those registered
    /// via [`declare_const`](Self::declare_const)) that do not match internal
    /// naming patterns are considered relevant.
    ///
    /// Returns the names of relevant variables in declaration order.
    #[must_use]
    pub fn infer_relevant_vars(&self) -> Vec<String> {
        self.declared_variables()
            .filter(|(name, _)| !is_internal_var_name(name))
            .map(|(name, _)| name.to_string())
            .collect()
    }

    /// Convenience: minimize the model and then project to inferred relevant
    /// variables in one call.
    ///
    /// Equivalent to calling `try_minimize_model()` followed by
    /// `project_model()` with `infer_relevant_vars()`.
    ///
    /// # Errors
    ///
    /// Returns the same errors as [`try_minimize_model`](Self::try_minimize_model).
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_minimize_and_project(&mut self) -> Result<HashMap<String, ModelValue>, SolverError> {
        self.try_minimize_model()?;
        let relevant: Vec<String> = self.infer_relevant_vars();
        let refs: Vec<&str> = relevant.iter().map(String::as_str).collect();
        Ok(self.project_model(&refs))
    }
}

/// Returns true if `name` looks like a solver-internal variable name.
///
/// Internal variables typically start with `!` or `@`, or contain `@` as a
/// separator (e.g., `!0`, `@aux_3`, `bv_ext@42`).
fn is_internal_var_name(name: &str) -> bool {
    name.starts_with('!') || name.starts_with('@') || name.contains('@')
}
