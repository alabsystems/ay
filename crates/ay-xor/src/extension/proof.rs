// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

// Textually included by `extension.rs`; keeps certificate machinery out of the
// extension's hot-path implementation while retaining private-field access.

impl XorExtension {
    /// Whether every retained component can emit its complete DRAT ladder
    /// within a certified budget — monolithically (the historical envelope)
    /// or via Tseitin-chunked chains over fresh extension variables (enabled
    /// by [`Self::set_proof_fresh_var_base`]).
    ///
    /// Proof-mode preprocessors must check this before removing the original
    /// XOR clauses. A false result requires falling back to the ordinary SAT
    /// proof route over the untouched formula.
    pub fn has_complete_proof_ladders(&self) -> bool {
        self.proof_ladders_complete || self.chunked.is_some()
    }

    /// Enable Tseitin-chunked proof emission for traces outside the
    /// monolithic ladder envelope, allocating fresh DRAT extension variables
    /// from `num_vars` (the DIMACS header variable count) upward.
    ///
    /// No-op when the monolithic envelope already fits (its byte-identical
    /// emission is preserved), when chunking was already enabled, or when
    /// even the chunked budget (`MAX_XOR_CHUNKED_PROOF_TOTAL_CLAUSES`) is
    /// exceeded — the route then falls back exactly as before.
    ///
    /// The caller owns the variable-collision contract: fresh variables are
    /// proof-only, but they must not collide with any OTHER mechanism that
    /// invents variables in the same proof. The certified DIMACS route
    /// qualifies: extension solves disable every variable-introducing
    /// inprocessing pass (`disable_extension_inprocessing`: SBVA, factor,
    /// BVE, ...), and the oneshot symmetry constructions are aux-free.
    pub fn set_proof_fresh_var_base(&mut self, num_vars: VarId) {
        if self.proof_ladders_complete || self.chunked.is_some() {
            return;
        }
        let mut total: u64 = 0;
        let mut comps = Vec::with_capacity(self.components.len());
        for component in &self.components {
            let Some(state) = component.solver.build_chunked_component_state() else {
                return;
            };
            let Some(next) = total.checked_add(state.total_additions()) else {
                return;
            };
            if next > MAX_XOR_CHUNKED_PROOF_TOTAL_CLAUSES {
                return;
            }
            total = next;
            comps.push(state);
        }
        if comps.is_empty() {
            return;
        }
        // Defensive: fresh variables must clear every constraint variable
        // even if a caller passes an understated header count.
        let mut base = num_vars;
        for constraint in &self.constraints {
            for &var in &constraint.vars {
                base = base.max(var.saturating_add(1));
            }
        }
        self.chunked = Some(ChunkedProofState {
            comps,
            next_fresh: base,
        });
    }

    /// Whether chunked (Tseitin-chain) proof emission is active.
    #[cfg(test)]
    pub(crate) fn chunked_proof_active(&self) -> bool {
        self.chunked.is_some()
    }

    /// Map a global RREF row id (component `row_offset` + local index) back
    /// to `(component, local_row)`.
    fn global_row_to_target(&self, global: usize) -> Option<(usize, usize)> {
        for (idx, component) in self.components.iter().enumerate() {
            let rows = component.solver.rows.len();
            if global >= component.row_offset && global < component.row_offset + rows {
                return Some((idx, global - component.row_offset));
            }
        }
        None
    }

    /// Emit the not-yet-emitted chunked derivation cones for the given
    /// `(component, local_row)` targets (latched per step — repeats are
    /// no-ops). Returns the proof-only script to prepend to this batch.
    fn drain_chunked_targets(&mut self, targets: &[(usize, usize)]) -> Vec<ExtProofStep> {
        let Some(ChunkedProofState { comps, next_fresh }) = self.chunked.as_mut() else {
            return Vec::new();
        };
        let mut out = Vec::new();
        for &(comp_idx, local_row) in targets {
            comps[comp_idx].emit_row_cone(
                &self.components[comp_idx].solver,
                local_row,
                next_fresh,
                &mut out,
            );
        }
        out
    }

    fn components_have_complete_proof_ladders(components: &[ComponentSolver]) -> bool {
        let mut total = 0usize;
        for component in components {
            let Some(component_total) = component.solver.complete_proof_ladder_clause_count()
            else {
                return false;
            };
            let Some(next_total) = total.checked_add(component_total) else {
                return false;
            };
            if next_total > crate::gaussian::MAX_XOR_PROOF_TOTAL_CLAUSES {
                return false;
            }
            total = next_total;
        }
        true
    }

    /// Emit every component's not-yet-emitted elimination rows atomically.
    /// A derived conflict/reason is RUP only after these ladder clauses.
    fn drain_new_proof_clauses(&mut self) -> Option<Vec<Vec<Literal>>> {
        if !self.proof_ladders_complete {
            return None;
        }
        let mut out = Vec::new();
        let mut new_lengths = Vec::with_capacity(self.components.len());
        for (idx, comp) in self.components.iter().enumerate() {
            let start = self.emitted_proof_rows[idx];
            let (clauses, new_len) = comp.solver.generate_proof_clauses_from(start)?;
            new_lengths.push(new_len);
            out.extend(clauses);
        }
        // Do not lose earlier components when a later materialization fails.
        self.emitted_proof_rows.copy_from_slice(&new_lengths);
        Some(out)
    }
}
