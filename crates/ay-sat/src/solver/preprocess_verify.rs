// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Model verification helpers.
//!
//! Split from `preprocess.rs` for file-size compliance (#5142).
//! Contains SAT model verification against clause DB and original formula.

use super::*;
use crate::solver::preprocess::ModelViolation;

impl Solver {
    /// Get the current model from vals[] (#3758 Phase 3).
    pub(super) fn get_model(&self) -> Vec<bool> {
        (0..self.num_vars).map(|v| self.vals[v * 2] > 0).collect()
    }

    /// Get model from saved phases (used when walk finds SAT)
    pub(super) fn get_model_from_phases(&self) -> Vec<bool> {
        self.phase.iter().map(|&p| p >= 0).collect()
    }

    /// Verify that a model satisfies all original clauses.
    ///
    /// This is a soundness check that verifies the model against:
    /// 1. All non-deleted clauses in the clause database
    /// 2. All clauses removed by BVE (stored in reconstruction stack)
    ///
    /// REQUIRES: model.len() >= num_vars (one entry per variable)
    /// ENSURES: returns true iff every non-deleted clause in clause_db AND
    ///          every removed clause in reconstruction stack has at least one
    ///          literal satisfied by model
    ///
    /// Returns true if the model is valid, false if any clause is unsatisfied.
    pub(super) fn verify_model(&self, model: &[bool]) -> bool {
        // Precondition: model must cover all variables
        debug_assert!(
            model.len() >= self.num_vars,
            "BUG: verify_model model.len()={} < num_vars={}",
            model.len(),
            self.num_vars,
        );
        self.first_model_violation(model, false).is_none()
    }

    #[cfg(debug_assertions)]
    pub(super) fn verify_clause_db_only(&self, model: &[bool], skip_eliminated: bool) -> bool {
        self.verify_clause_db_impl(model, skip_eliminated)
    }

    /// Verify that no clause in the active clause database is falsified by the
    /// current partial assignment (vals[]).
    ///
    /// Used for domain-restricted IC3 SAT results (#8649) where `finalize_sat_model`
    /// is bypassed. A clause is "falsified" if ALL of its literals are assigned
    /// false. Unassigned literals (typical for non-domain variables) do not
    /// falsify the clause — they could still satisfy it.
    ///
    /// This catches BCP bugs that produce an inconsistent partial model without
    /// requiring a full model over all variables.
    pub(super) fn verify_domain_restricted_model(&self) -> bool {
        // live_indices (husk adjudication): a falsified garbage-kept husk is
        // logically deleted and must not reject a genuine domain-restricted
        // SAT (same skip `should_skip_clause_verification` applies elsewhere).
        for idx in self.arena.live_indices() {
            let lits = self.arena.literals(idx);
            let mut all_false = true;
            for &lit in lits {
                match self.lit_value(lit) {
                    Some(true) => {
                        // Clause is satisfied by this literal.
                        all_false = false;
                        break;
                    }
                    Some(false) => {
                        // This literal is false, continue checking.
                    }
                    None => {
                        // Unassigned literal — clause is not falsified.
                        all_false = false;
                        break;
                    }
                }
            }
            if all_false && !lits.is_empty() {
                tracing::error!(
                    clause_idx = idx,
                    clause_len = lits.len(),
                    "domain-restricted model verification: clause falsified"
                );
                return false;
            }
        }
        true
    }

    /// Return the first clause violated by `model`, if any.
    ///
    /// When `skip_inprocessing` is true, clauses containing any variable that
    /// is either removed (eliminated/substituted) or an internal extension
    /// variable (index >= `user_num_vars`) are skipped. This is necessary
    /// after reconstruction: conditioning/BVE/factorization produce derived
    /// clauses with internal variables. Reconstruction flips variables to
    /// satisfy removed clauses, which can break these derived clauses.
    /// CaDiCaL does not verify clause_db after extend() -- only the original
    /// formula is checked (#5058).
    pub(super) fn first_model_violation(
        &self,
        model: &[bool],
        skip_inprocessing: bool,
    ) -> Option<ModelViolation> {
        for idx in self.arena.indices() {
            if self.should_skip_clause_verification(idx, skip_inprocessing) {
                continue;
            }

            let lits = self.arena.literals(idx);

            // After reconstruction, skip clauses containing inprocessing
            // artifacts: eliminated variables or extension variables created
            // by factorization (index >= user_num_vars). Reconstruction
            // restores the original formula's satisfiability -- derived
            // arena clauses may not be satisfied. verify_against_original
            // checks the immutable original formula as the authoritative
            // correctness gate for reconstruction (#4999: always-on).
            if skip_inprocessing
                && lits.iter().any(|lit| {
                    let vi = lit.variable().index();
                    vi >= self.user_num_vars
                        || (vi < self.var_lifecycle.len() && self.var_lifecycle.is_removed(vi))
                })
            {
                continue;
            }

            if !Self::clause_satisfied(lits, model) {
                return Some(ModelViolation::ClauseDb {
                    clause_index: idx,
                    clause_dimacs: Self::clause_dimacs(lits),
                });
            }
        }

        // CaDiCaL does NOT verify the model against removed (reconstruction
        // stack) clauses after extend(). With gate-based restricted resolution,
        // the reconstruction stack contains only gate clauses; non-gate clauses
        // are not on the stack and their satisfaction is implied by the gate
        // definition + resolvents. Individual gate clauses may also become
        // unsatisfied when inter-variable reconstruction flips shared variables.
        // `verify_against_original` checks the original formula (#4818, #4999).
        None
    }

    /// Domain-aware model verification (#8473).
    ///
    /// Same as `first_model_violation` but treats a clause as satisfied if it
    /// contains any literal whose variable is outside the active domain. In
    /// domain-restricted solving (IC3/PDR), non-domain variables are don't-cares
    /// that can take any value, so clauses mentioning them are trivially
    /// satisfiable. Without this, domain-restricted SAT results fail model
    /// verification because non-domain variables default to false in the model.
    pub(super) fn first_model_violation_domain_aware(
        &self,
        model: &[bool],
        domain: &[bool],
    ) -> Option<ModelViolation> {
        for idx in self.arena.indices() {
            if self.should_skip_clause_verification(idx, false) {
                continue;
            }

            let lits = self.arena.literals(idx);

            // A clause is satisfied under domain semantics if:
            // 1. Any literal is true in the model, OR
            // 2. Any literal's variable is outside the domain (don't-care).
            let satisfied = Self::clause_satisfied(lits, model)
                || lits.iter().any(|lit| {
                    let vi = lit.variable().index();
                    vi >= domain.len() || !domain[vi]
                });

            if !satisfied {
                return Some(ModelViolation::ClauseDb {
                    clause_index: idx,
                    clause_dimacs: Self::clause_dimacs(lits),
                });
            }
        }
        None
    }

    /// Build a diagnostic string for a SAT-model contract violation.
    ///
    /// Includes source location (live DB or reconstruction), clause DIMACS
    /// form, and per-literal model evaluation to make the failing assignment
    /// immediately actionable in logs/panics.
    #[cfg(test)]
    pub(super) fn describe_model_violation(
        &self,
        model: &[bool],
        violation: &ModelViolation,
    ) -> String {
        let (source, index, clause_dimacs) = match violation {
            ModelViolation::ClauseDb {
                clause_index,
                clause_dimacs,
            } => ("clause_db", *clause_index, clause_dimacs.as_slice()),
        };

        let literal_evals = clause_dimacs
            .iter()
            .map(|&lit| Self::format_model_literal_eval(lit, model))
            .collect::<Vec<_>>()
            .join(", ");

        format!(
            "{source}[{index}] unsatisfied; clause={clause_dimacs:?}; literal_evals=[{literal_evals}]",
        )
    }

    /// Verify model against the immutable original-formula ledger.
    ///
    /// Unlike `verify_model()` which checks the mutable clause DB + reconstruction
    /// stack, this checks against an immutable copy of every clause as it was added
    /// before any preprocessing/inprocessing. This catches bugs where a pass deletes
    /// an irredundant clause without a proper reconstruction entry.
    #[cfg(test)]
    pub(super) fn verify_against_original(&self, model: &[bool]) -> Option<usize> {
        self.cold
            .original_ledger
            .iter_clauses()
            .position(|clause| !Self::clause_satisfied(clause, model))
    }

    /// Verify a (possibly truncated) external model satisfies all original clauses.
    ///
    /// This is the debug_assertions counterpart of the always-on original-formula
    /// check in `finalize_sat_model`. It works on external-space models that may
    /// be truncated to `user_num_vars`, skipping clauses containing scope-selector
    /// variables. Returns true if every non-scoped original clause is satisfied.
    ///
    /// Unlike `verify_model()` (which checks the mutable clause DB and requires
    /// `model.len() >= num_vars`), this checks against the immutable original
    /// clauses and tolerates truncated models where extension/internal variables
    /// have been removed.
    ///
    /// Used as an always-on belt-and-suspenders check at every `SatResult::Sat`
    /// and `AssumeResult::Sat` construction site (#7912, #8819 — verification gap #1).
    ///
    /// Runs in release builds. Returns `true` if every non-scoped original
    /// clause is satisfied; `false` otherwise. Callers (declare_sat_*) downgrade
    /// to `Unknown` on failure rather than returning an unsound SAT.
    pub(super) fn verify_external_model(&self, model: &[bool]) -> bool {
        for (ci, clause) in self.cold.original_ledger.iter_clauses().enumerate() {
            #[cfg(not(debug_assertions))]
            let _ = ci;

            // Skip clauses containing scope selector variables (same logic as
            // finalize_sat_model).
            if self.cold.has_ever_scoped {
                let has_scope = clause.iter().any(|lit| {
                    let vi = lit.variable().index();
                    vi < self.cold.was_scope_selector.len() && self.cold.was_scope_selector[vi]
                });
                if has_scope {
                    continue;
                }
            }
            if !clause.iter().any(|&lit| {
                let vi = lit.variable().index();
                vi < model.len() && (model[vi] == lit.is_positive())
            }) {
                #[cfg(debug_assertions)]
                {
                    let clause_dimacs: Vec<i32> = clause
                        .iter()
                        .map(|&lit| {
                            let v = lit.variable().0 as i32 + 1;
                            if lit.is_positive() {
                                v
                            } else {
                                -v
                            }
                        })
                        .collect();
                    let lit_vals: Vec<String> = clause
                        .iter()
                        .map(|&lit| {
                            let vi = lit.variable().index();
                            let model_val = if vi < model.len() {
                                Some(model[vi])
                            } else {
                                None
                            };
                            format!("var{}=model:{:?}(pos={})", vi, model_val, lit.is_positive())
                        })
                        .collect();
                    eprintln!(
                        "verify_external_model FAIL: clause {ci}/{}: dimacs={clause_dimacs:?}, lits=[{}], model_len={}, has_ever_scoped={}, scope_selectors_len={}",
                        self.cold.original_ledger.num_clauses(),
                        lit_vals.join(", "),
                        model.len(),
                        self.cold.has_ever_scoped,
                        self.cold.scope_selectors.len(),
                    );
                }
                return false;
            }
        }
        true
    }

    /// Whether a clause at `idx` should be skipped during model verification.
    ///
    /// Returns true for empty, garbage, or pending-garbage clauses (logically
    /// deleted), and when `skip_inprocessing` is set, also for clauses containing
    /// eliminated or extension variables.
    fn should_skip_clause_verification(&self, idx: usize, skip_inprocessing: bool) -> bool {
        if self.arena.is_empty_clause(idx) || self.arena.is_garbage_any(idx) {
            return true;
        }
        if skip_inprocessing {
            let lits = self.arena.literals(idx);
            return lits.iter().any(|lit| {
                let vi = lit.variable().index();
                vi >= self.user_num_vars
                    || (vi < self.var_lifecycle.len() && self.var_lifecycle.is_removed(vi))
            });
        }
        false
    }

    /// Check if all non-deleted clauses in clause_db are satisfied by model.
    ///
    /// When `skip_inprocessing` is true, clauses containing removed or
    /// extension variables (>= `user_num_vars`) are skipped. Safe after
    /// reconstruction — see `first_model_violation` for rationale.
    #[cfg(debug_assertions)]
    fn verify_clause_db_impl(&self, model: &[bool], skip_inprocessing: bool) -> bool {
        for idx in self.arena.indices() {
            if self.should_skip_clause_verification(idx, skip_inprocessing) {
                continue;
            }
            let lits = self.arena.literals(idx);
            if !Self::clause_satisfied(lits, model) {
                let is_learned = self.arena.is_learned(idx);
                safe_eprintln!(
                    "BUG: Clause {} not satisfied by model: {:?} (learned={}, len={}, num_vars={}, user_num_vars={})",
                    idx,
                    Self::clause_dimacs(lits),
                    is_learned,
                    lits.len(),
                    self.num_vars,
                    self.user_num_vars,
                );
                // Check watched literal values in the vals array
                if lits.len() >= 2 {
                    let w0 = lits[0];
                    let w1 = lits[1];
                    let v0_val = if w0.index() < self.vals.len() {
                        self.vals[w0.index()]
                    } else {
                        -1
                    };
                    let v1_val = if w1.index() < self.vals.len() {
                        self.vals[w1.index()]
                    } else {
                        -1
                    };
                    let v0_removed = w0.variable().index() < self.var_lifecycle.len()
                        && self.var_lifecycle.is_removed(w0.variable().index());
                    let v1_removed = w1.variable().index() < self.var_lifecycle.len()
                        && self.var_lifecycle.is_removed(w1.variable().index());
                    safe_eprintln!(
                        "  watch0: dimacs={}, vals={}, removed={}; watch1: dimacs={}, vals={}, removed={}",
                        w0.to_dimacs(), v0_val, v0_removed,
                        w1.to_dimacs(), v1_val, v1_removed,
                    );
                }
                for lit in lits {
                    let v = lit.variable().index();
                    let in_range = v < model.len();
                    let val = if in_range { Some(model[v]) } else { None };
                    let removed = v < self.var_lifecycle.len() && self.var_lifecycle.is_removed(v);
                    let vals_entry = if lit.index() < self.vals.len() {
                        self.vals[lit.index()]
                    } else {
                        -1
                    };
                    safe_eprintln!(
                        "  lit: dimacs={}, var_idx={}, positive={}, in_range={}, model_val={:?}, removed={}, vals={}",
                        lit.to_dimacs(),
                        v,
                        lit.is_positive(),
                        in_range,
                        val,
                        removed,
                        vals_entry,
                    );
                }
                return false;
            }
        }

        true
    }

    /// Check if at least one literal in `clause` is satisfied by `model`.
    #[inline]
    pub(super) fn clause_satisfied(clause: &[Literal], model: &[bool]) -> bool {
        clause.iter().any(|lit| {
            let var_idx = lit.variable().index();
            var_idx < model.len() && (model[var_idx] == lit.is_positive())
        })
    }

    /// Render one DIMACS literal against a candidate model for diagnostics.
    #[cfg(test)]
    #[inline]
    fn format_model_literal_eval(lit: i32, model: &[bool]) -> String {
        let var_abs = lit.unsigned_abs() as usize;
        if var_abs == 0 {
            return format!("{lit}@v?=U->F");
        }

        let var_idx = var_abs - 1;
        match model.get(var_idx).copied() {
            Some(assigned) => {
                let lit_true = if lit > 0 { assigned } else { !assigned };
                let assigned_char = if assigned { 'T' } else { 'F' };
                let lit_char = if lit_true { 'T' } else { 'F' };
                format!("{lit}@v{var_idx}={assigned_char}->{lit_char}")
            }
            None => format!("{lit}@v{var_idx}=U->F"),
        }
    }

    /// Format clause literals as DIMACS integers (for debug messages).
    pub(super) fn clause_dimacs(clause: &[Literal]) -> Vec<i32> {
        clause.iter().map(|l| l.to_dimacs()).collect()
    }
}
