// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl Solver {
    pub(super) fn replace_with_empty_clause_lrat(
        &mut self,
        clause_idx: usize,
        new_lits: &[Literal],
        extra_lrat_hints: &[u64],
        explicit_only: bool,
        old_clause_id: u64,
        old_lits: &[Literal],
    ) -> ReplaceResult {
        let proof_hints = if self.cold.lrat_enabled {
            self.ensure_level0_unit_proof_ids();
            let mut hints = Vec::with_capacity(old_lits.len() + extra_lrat_hints.len() + 1);
            let old_clause_first_in_checker = old_lits.len() <= 1;

            if !old_clause_first_in_checker {
                Self::push_lrat_hint(&mut hints, old_clause_id);
            }
            for &hint in extra_lrat_hints {
                if hint != old_clause_id {
                    Self::push_lrat_hint(&mut hints, hint);
                }
            }
            if !explicit_only {
                let mut signed_unit_hints = Vec::new();
                let mut signed_units_complete = true;

                for &old_lit in old_lits {
                    let required_lit = old_lit.negated();
                    if let Some(id) = self.level0_unit_chain_proof_id_for_lit(required_lit) {
                        if id != old_clause_id && !signed_unit_hints.contains(&id) {
                            signed_unit_hints.push(id);
                        }
                    } else {
                        let var_idx = old_lit.variable().index();
                        if var_idx < self.num_vars
                            && self.var_data[var_idx].level == 0
                            && self.has_any_proof_id(var_idx)
                        {
                            signed_units_complete = false;
                            break;
                        }
                    }
                }

                if !signed_units_complete {
                    return ReplaceResult::Skipped;
                }

                for &id in &signed_unit_hints {
                    Self::push_lrat_hint(&mut hints, id);
                }
            }
            if old_clause_first_in_checker {
                Self::push_lrat_hint(&mut hints, old_clause_id);
            }
            Self::lrat_reverse_hints(&hints)
        } else if old_clause_id != 0 {
            vec![old_clause_id]
        } else {
            Vec::new()
        };

        if self.cold.lrat_enabled {
            self.materialize_level0_unit_proofs();
            if !self.lrat_replacement_level0_reason_units_ready(
                clause_idx,
                old_lits,
                new_lits,
                old_clause_id,
            ) {
                return ReplaceResult::Skipped;
            }
        }
        self.mark_empty_clause_with_hints(&proof_hints);
        ReplaceResult::Empty
    }

    pub(super) fn build_replacement_lrat_hints(
        &mut self,
        old_lits: &[Literal],
        reordered: &[Literal],
        extra_lrat_hints: &[u64],
        explicit_only: bool,
        old_clause_id: u64,
    ) -> Option<Vec<u64>> {
        // Proof logging: add-before-delete ordering (DRAT/LRAT requirement)
        let proof_hints = if self.cold.lrat_enabled {
            // Materialize unit proof IDs for level-0 variables so that
            // level0_var_proof_id() (used by collect_level0_unit_chain) can
            // find them in LRAT mode (#7108).
            self.ensure_level0_unit_proof_ids();
            let mut hints = Vec::with_capacity(old_lits.len() + extra_lrat_hints.len() + 1);
            let removed_lits: Vec<Literal> = old_lits
                .iter()
                .copied()
                .filter(|old_lit| !reordered.contains(old_lit))
                .collect();
            let removed_count = removed_lits.len();
            let old_clause_first_in_checker = removed_count <= 1;

            if !old_clause_first_in_checker {
                Self::push_lrat_hint(&mut hints, old_clause_id);
            }
            // Include explicitly captured reason chain (vivify probe chain,
            // subsumption hints, etc.).  After reversal these appear before
            // the old clause in the checker's processing order.
            for &hint in extra_lrat_hints {
                if hint != old_clause_id {
                    Self::push_lrat_hint(&mut hints, hint);
                }
            }
            if !explicit_only {
                let require_all_signed_units = extra_lrat_hints.is_empty() || reordered.len() == 1;
                let mut signed_unit_hints = Vec::new();
                let mut signed_units_complete = true;

                for &old_lit in &removed_lits {
                    let required_lit = old_lit.negated();
                    if let Some(id) = self.level0_unit_chain_proof_id_for_lit(required_lit) {
                        if id != old_clause_id && !signed_unit_hints.contains(&id) {
                            signed_unit_hints.push(id);
                        }
                    } else {
                        let var_idx = old_lit.variable().index();
                        let needs_signed_unit = require_all_signed_units
                            || (var_idx < self.num_vars
                                && self.var_data[var_idx].level == 0
                                && self.has_any_proof_id(var_idx));
                        if needs_signed_unit {
                            signed_units_complete = false;
                            break;
                        }
                    }
                }

                if !signed_units_complete {
                    return None;
                }

                for &id in &signed_unit_hints {
                    Self::push_lrat_hint(&mut hints, id);
                }
            }
            // For single-removal: push old clause LAST in pre-reversal so it
            // becomes FIRST after reversal (immediately unit under RUP negation).
            // For multi-removal: old clause was already pushed first.
            if old_clause_first_in_checker {
                Self::push_lrat_hint(&mut hints, old_clause_id);
            }
            Self::lrat_reverse_hints(&hints)
        } else if old_clause_id != 0 {
            vec![old_clause_id]
        } else {
            Vec::new()
        };
        Some(proof_hints)
    }
}
