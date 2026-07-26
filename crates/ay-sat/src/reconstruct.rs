// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Model reconstruction for equisatisfiable transformations (BVE, BCE, sweep).
//!
//! Witness-based reconstruction: each removed clause is stored with a witness
//! set (the conditional autarky). Steps processed in reverse order — if clause
//! already satisfied, skip; otherwise flip false witness literals.
//!
//! Multi-round BVE correctness: reverse chronological order ensures each
//! variable's reconstruction sees already-reconstructed later-eliminated values.
//!
//! Reference: CaDiCaL `extend.cpp:121-204`.

use crate::literal::{Literal, Variable};
use std::mem::size_of;

#[cfg(test)]
mod tests;
#[cfg(kani)]
mod verification;

/// Result of draining witness entries from the reconstruction stack.
///
/// Carries both the restored clauses and the exact variable indices that
/// appeared in the drained witness entries. Callers use `reactivate_vars`
/// to scope reactivation to only the variables whose elimination obligations
/// were actually restored.
#[derive(Debug, Clone)]
pub(crate) struct WitnessDrainResult {
    /// Deduplicated variable indices from drained witness/clause literals.
    /// Used by `reset_search_state()` for targeted reactivation (#3644).
    pub(crate) reactivate_vars: Vec<usize>,
}

/// A removed clause with its witness literal.
///
/// Used for both BVE (witness = pivot, the eliminated variable's literal)
/// and BCE (witness = blocking literal). In the general conditional-autarky
/// case, `witness` can contain multiple literals (CaDiCaL `extend.cpp`).
#[derive(Debug, Clone)]
pub(crate) struct WitnessClause {
    /// Conditional autarky witness literals for this removed clause.
    pub(crate) witness: Vec<Literal>,
    /// The full clause that was removed
    pub(crate) clause: Vec<Literal>,
}

/// A single reconstruction step.
#[derive(Debug, Clone)]
pub(crate) enum ReconstructionStep {
    /// A clause removed by BVE or BCE, with its witness literal.
    Witness(WitnessClause),
    /// Sweeping: variables were merged due to equivalence.
    #[allow(dead_code)] // audited-unused: kept pending the next dead-code cleanup slice
    Sweep {
        /// Number of variables in the original formula
        num_vars: usize,
        /// Mapping from literal index to canonical literal
        lit_map: Vec<Literal>,
    },
}

/// Stack of reconstruction steps (applied in reverse order).
#[derive(Debug, Clone, Default)]
pub(crate) struct ReconstructionStack {
    /// Steps in order they were applied (reconstruction reverses this)
    steps: Vec<ReconstructionStep>,
}

impl ReconstructionStack {
    /// Create an empty reconstruction stack.
    pub(crate) fn new() -> Self {
        Self { steps: Vec::new() }
    }

    /// Number of reconstruction steps.
    pub(crate) fn len(&self) -> usize {
        self.steps.len()
    }

    /// Estimated heap memory usage in bytes.
    ///
    /// Includes the Vec<ReconstructionStep> backbone and the heap allocations
    /// within each step (witness and clause Vecs for Witness entries, lit_map
    /// for Sweep entries).
    pub(crate) fn memory_bytes(&self) -> usize {
        let backbone = self.steps.capacity() * size_of::<ReconstructionStep>();
        let step_contents: usize = self
            .steps
            .iter()
            .map(|step| match step {
                ReconstructionStep::Witness(wc) => {
                    wc.witness.capacity() * size_of::<Literal>()
                        + wc.clause.capacity() * size_of::<Literal>()
                }
                ReconstructionStep::Sweep { lit_map, .. } => {
                    lit_map.capacity() * size_of::<Literal>()
                }
            })
            .sum();
        // 24 bytes for the Vec header of `steps`.
        24 + backbone + step_contents
    }

    /// Whether there are no reconstruction steps.
    #[cfg(kani)]
    pub(crate) fn is_empty(&self) -> bool {
        self.steps.is_empty()
    }

    /// Remove all reconstruction steps (used by Kani proofs only).
    #[cfg(kani)]
    pub(crate) fn clear(&mut self) {
        self.steps.clear();
    }

    /// Drain witness entries from the reconstruction stack, preserving non-witness steps.
    ///
    /// Returns a `WitnessDrainResult` containing deduplicated variable indices
    /// from the witness and clause literals of drained entries. Used by
    /// `reset_search_state()` for targeted variable reactivation.
    ///
    /// Non-witness steps (e.g., `Sweep`) are retained in the stack.
    pub(crate) fn drain_witness_entries(&mut self) -> WitnessDrainResult {
        let mut var_set = std::collections::BTreeSet::new();

        // Partition: retain non-witness steps, drain witness steps.
        let mut retained = Vec::new();
        for step in self.steps.drain(..) {
            match step {
                ReconstructionStep::Witness(wc) => {
                    for &lit in &wc.witness {
                        var_set.insert(lit.variable().index());
                    }
                    for &lit in &wc.clause {
                        var_set.insert(lit.variable().index());
                    }
                }
                other => retained.push(other),
            }
        }
        self.steps = retained;

        WitnessDrainResult {
            reactivate_vars: var_set.into_iter().collect(),
        }
    }

    /// Drain witness entries from `start_idx` onwards (#8369).
    ///
    /// Like `drain_witness_entries()` but only removes entries at indices
    /// >= `start_idx`. Non-witness steps (Sweep) in the tail are retained
    /// > and re-appended. Returns the variable indices that appeared in
    /// > drained witness entries.
    pub(crate) fn drain_witness_entries_from(&mut self, start_idx: usize) -> WitnessDrainResult {
        let mut var_set = std::collections::BTreeSet::new();
        if start_idx >= self.steps.len() {
            return WitnessDrainResult {
                reactivate_vars: Vec::new(),
            };
        }
        let tail = self.steps.split_off(start_idx);
        let mut retained_tail = Vec::new();
        for step in tail {
            match step {
                ReconstructionStep::Witness(wc) => {
                    for &lit in &wc.witness {
                        var_set.insert(lit.variable().index());
                    }
                    for &lit in &wc.clause {
                        var_set.insert(lit.variable().index());
                    }
                }
                other => retained_tail.push(other),
            }
        }
        self.steps.extend(retained_tail);
        WitnessDrainResult {
            reactivate_vars: var_set.into_iter().collect(),
        }
    }

    /// Count (witness, sweep) steps (debug only).
    #[cfg(debug_assertions)]
    #[allow(dead_code)] // audited-unused: kept pending the next dead-code cleanup slice
    pub(crate) fn debug_counts(&self) -> (usize, usize) {
        self.steps.iter().fold((0, 0), |(w, s), step| match step {
            ReconstructionStep::Witness(_) => (w + 1, s),
            ReconstructionStep::Sweep { .. } => (w, s + 1),
        })
    }

    /// Push BVE elimination steps (CaDiCaL witness approach).
    /// Reference: CaDiCaL `elim.cpp:624-663`.
    #[cfg(test)]
    pub(crate) fn push_bve(
        &mut self,
        variable: Variable,
        pos_clauses: Vec<Vec<Literal>>,
        neg_clauses: Vec<Vec<Literal>>,
    ) {
        let pos_lit = Literal::positive(variable);
        let neg_lit = Literal::negative(variable);
        debug_assert!(
            pos_clauses.iter().all(|c| c.contains(&pos_lit)),
            "BUG: push_bve: positive clause missing {pos_lit:?}"
        );
        debug_assert!(
            neg_clauses.iter().all(|c| c.contains(&neg_lit)),
            "BUG: push_bve: negative clause missing {neg_lit:?}"
        );
        // CaDiCaL elim.cpp:623-663: push positive clauses first, then
        // negative clauses. Reconstruction reverses this order.
        for clause in pos_clauses {
            self.push_witness_clause(vec![pos_lit], clause);
        }
        for clause in neg_clauses {
            self.push_witness_clause(vec![neg_lit], clause);
        }
    }

    /// Push a BCE (blocked clause elimination) step.
    pub(crate) fn push_bce(&mut self, blocking_literal: Literal, clause: Vec<Literal>) {
        debug_assert!(
            clause.contains(&blocking_literal),
            "BUG: BCE blocking literal {blocking_literal:?} not in clause {clause:?}"
        );
        self.push_witness_clause(vec![blocking_literal], clause);
    }

    /// Push a witness-clause reconstruction entry (CaDiCaL conditional autarky
    /// format). Witness may contain one or more literals.
    pub(crate) fn push_witness_clause(&mut self, witness: Vec<Literal>, clause: Vec<Literal>) {
        debug_assert!(
            !witness.is_empty(),
            "BUG: empty witness in reconstruction entry"
        );
        debug_assert!(
            !clause.is_empty(),
            "BUG: empty clause in reconstruction entry"
        );
        self.steps.push(ReconstructionStep::Witness(WitnessClause {
            witness,
            clause,
        }));
    }

    /// Push sweep (equivalence merging) as per-equivalence binary clause
    /// entries, matching CaDiCaL's decompose.cpp:450-470 approach.
    ///
    /// For each equivalence `idx ≡ other` (where `other` is the
    /// representative), CaDiCaL pushes two binary clauses:
    ///   1. `[-idx, other]` with witness `-idx`
    ///   2. `[idx, -other]` with witness `idx`
    ///
    /// These entries participate naturally in the conditional autarky
    /// during reverse reconstruction, interacting correctly with BVE
    /// entries that may change the representative's value.
    ///
    /// Previously AY used a bulk `Sweep` step that force-mapped all
    /// non-representatives to their representative's current value.
    /// This broke when BVE reconstruction changed a representative's
    /// value BEFORE the sweep step was processed (reverse order),
    /// causing cascading variable flip violations (#8179, #8356).
    pub(crate) fn push_sweep(&mut self, num_vars: usize, lit_map: Vec<Literal>) {
        debug_assert!(
            lit_map.len() >= num_vars * 2,
            "BUG: push_sweep: lit_map len {} < 2*num_vars ({})",
            lit_map.len(),
            num_vars * 2
        );
        // Convert the lit_map into per-equivalence binary clause entries.
        // For each variable `idx` mapped to a different representative
        // `repr`, push two entries:
        //   witness=[-idx], clause=[-idx, repr]    (if idx true & repr false: flip idx to false)
        //   witness=[idx],  clause=[idx, -repr]    (if idx false & -repr false: flip idx to true)
        for var_idx in 0..num_vars {
            let pos_lit = Literal::positive(Variable(var_idx as u32));
            let pos_idx = pos_lit.index();

            if pos_idx >= lit_map.len() {
                continue;
            }

            let mapped_lit = lit_map[pos_idx];
            let mapped_var_idx = mapped_lit.variable().index();

            // Skip identity mappings (variable is its own representative).
            if mapped_var_idx == var_idx {
                continue;
            }

            // CaDiCaL decompose.cpp:450:
            //   push_binary_clause_on_extension_stack(id1, -idx, other)
            //   → clause = [-idx, other], witness = -idx
            // CaDiCaL decompose.cpp:470:
            //   push_binary_clause_on_extension_stack(id2, idx, -other)
            //   → clause = [idx, -other], witness = idx
            //
            // For positive mapping (idx → repr): other = repr
            // For negative mapping (idx → -repr): other = -repr (negated repr)
            let neg_lit = pos_lit.negated();
            let repr_lit = mapped_lit; // could be positive or negative
            let neg_repr = repr_lit.negated();

            // Entry 1: witness = -idx, clause = [-idx, repr]
            self.push_witness_clause(vec![neg_lit], vec![neg_lit, repr_lit]);
            // Entry 2: witness = idx, clause = [idx, -repr]
            self.push_witness_clause(vec![pos_lit], vec![pos_lit, neg_repr]);
        }
    }

    /// Reconstruct a model by replaying steps in reverse order.
    ///
    /// Reference: CaDiCaL `extend.cpp:121-204`.
    pub(crate) fn reconstruct(&self, model: &mut Vec<bool>) {
        // Single-pass reverse reconstruction, matching CaDiCaL extend.cpp:121-204.
        //
        // Process ALL steps in reverse order regardless of type. This preserves
        // the ordering invariant: steps pushed later are processed first.
        //
        // CaDiCaL pushes equivalences as individual witness clauses (not bulk
        // sweeps), so its single-pass approach works naturally. AY's Sweep steps
        // require careful ordering: they must be processed at their stack position,
        // not deferred to a separate phase. Two-phase reconstruction (previously
        // used here) broke the ordering invariant by processing all BVE/BCE steps
        // before any sweep steps, causing cascading variable flip violations on
        // large formulas (IBM12 #5696).
        for step in self.steps.iter().rev() {
            match step {
                ReconstructionStep::Witness(wc) => {
                    reconstruct_witness(model, &wc.witness, &wc.clause);
                }
                ReconstructionStep::Sweep { num_vars, lit_map } => {
                    reconstruct_sweep(model, *num_vars, lit_map);
                }
            }
        }
    }

    /// Get a reference to the steps slice for diagnostic replay (#8485).
    pub(crate) fn steps_ref(&self) -> &[ReconstructionStep] {
        &self.steps
    }

    /// Iterate over all reconstruction steps.
    ///
    /// Used by debug invariant validation and by `finalize_sat_model` for
    /// diagnostic information in model verification errors.
    #[cfg(debug_assertions)]
    pub(crate) fn iter_steps(&self) -> impl Iterator<Item = &ReconstructionStep> {
        self.steps.iter()
    }

    /// Iterate over all removed clauses (BVE and BCE).
    #[cfg(test)]
    pub(crate) fn iter_removed_clauses(&self) -> impl Iterator<Item = &[Literal]> {
        self.steps.iter().filter_map(|step| match step {
            ReconstructionStep::Witness(wc) => Some(wc.clause.as_slice()),
            ReconstructionStep::Sweep { .. } => None,
        })
    }

    /// Verify that sweep equivalences hold in a reconstructed model (#3477).
    ///
    /// For each Sweep step, every variable `x` mapped to representative `r`
    /// must satisfy: `model[x] == model[r]` (positive mapping) or
    /// `model[x] == !model[r]` (negative mapping). A violation indicates
    /// a bug in `reconstruct_sweep()` or in the sweep/congruence equivalence
    /// detection that produced the lit_map.
    ///
    /// Returns `None` if all sweep equivalences are consistent, or
    /// `Some((step_idx, var_idx, expected, actual))` for the first violation.
    #[cfg(any(test, debug_assertions))]
    pub(crate) fn verify_sweep_consistency(
        &self,
        model: &[bool],
    ) -> Option<(usize, usize, bool, bool)> {
        for (step_idx, step) in self.steps.iter().enumerate() {
            if let ReconstructionStep::Sweep { num_vars, lit_map } = step {
                for var_idx in 0..*num_vars {
                    let pos_lit = Literal::positive(Variable(var_idx as u32));
                    let pos_idx = pos_lit.index();

                    if pos_idx >= lit_map.len() {
                        continue;
                    }

                    let mapped_lit = lit_map[pos_idx];
                    let mapped_var_idx = mapped_lit.variable().index();

                    // Skip identity mappings
                    if mapped_var_idx == var_idx {
                        continue;
                    }

                    // Both variables must be in range
                    if var_idx >= model.len() || mapped_var_idx >= model.len() {
                        continue;
                    }

                    let expected = if mapped_lit.is_positive() {
                        model[mapped_var_idx]
                    } else {
                        !model[mapped_var_idx]
                    };

                    if model[var_idx] != expected {
                        return Some((step_idx, var_idx, expected, model[var_idx]));
                    }
                }
            }
        }
        None
    }
}

/// Reconstruct a removed clause using the witness literal.
/// Reference: CaDiCaL `extend.cpp:150-198`.
///
/// Public for diagnostic replay in `finalize_sat_model` (#8485).
pub(crate) fn reconstruct_witness_pub(
    model: &mut Vec<bool>,
    witness: &[Literal],
    clause: &[Literal],
) {
    reconstruct_witness(model, witness, clause);
}

fn reconstruct_witness(model: &mut Vec<bool>, witness: &[Literal], clause: &[Literal]) {
    for &w in witness {
        let var_idx = w.variable().index();
        if var_idx >= model.len() {
            model.resize(var_idx + 1, false);
        }
    }

    let already_sat = clause.iter().any(|&lit| {
        let v = lit.variable().index();
        if v >= model.len() {
            false
        } else if lit.is_positive() {
            model[v]
        } else {
            !model[v]
        }
    });

    if already_sat {
        return;
    }

    // CaDiCaL-style conditional autarky: for each witness literal, if it is
    // currently false under the model, flip its variable assignment.
    for &w in witness {
        let var_idx = w.variable().index();
        let lit_satisfied = if w.is_positive() {
            model[var_idx]
        } else {
            !model[var_idx]
        };
        if !lit_satisfied {
            model[var_idx] = !model[var_idx];
        }
    }

    // Post-condition: clause must be satisfied after witness flipping.
    // Reference: CaDiCaL extend.cpp:200 has the same assertion.
    debug_assert!(
        clause.iter().any(|&lit| {
            let v = lit.variable().index();
            v < model.len() && (model[v] == lit.is_positive())
        }),
        "BUG: reconstruct_witness postcondition: clause={clause:?} witness={witness:?}"
    );
}

/// Public for diagnostic replay in `finalize_sat_model` (#8485).
pub(crate) fn reconstruct_sweep_pub(model: &mut Vec<bool>, num_vars: usize, lit_map: &[Literal]) {
    reconstruct_sweep(model, num_vars, lit_map);
}

fn reconstruct_sweep(model: &mut Vec<bool>, num_vars: usize, lit_map: &[Literal]) {
    if num_vars > model.len() {
        model.resize(num_vars, false);
    }

    for var_idx in 0..num_vars {
        let pos_lit = Literal::positive(Variable(var_idx as u32));
        let pos_idx = pos_lit.index();

        if pos_idx >= lit_map.len() {
            continue;
        }

        let mapped_lit = lit_map[pos_idx];
        let mapped_var_idx = mapped_lit.variable().index();

        if mapped_var_idx != var_idx && mapped_var_idx < model.len() {
            let mapped_value = model[mapped_var_idx];
            model[var_idx] = if mapped_lit.is_positive() {
                mapped_value
            } else {
                !mapped_value
            };
        }
    }
}
