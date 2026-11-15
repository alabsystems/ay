// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Bounded read-only observation of existing bit-blaster provenance.

use super::*;

impl BvSolver<'_> {
    /// Watch one actual registration; inspect at most 256 bit cells.
    /// No solver/proof state is changed and no registration is manufactured.
    pub fn watch_variable_registration(&mut self, variable: CnfLit) {
        if ay_core::misc_cli_flags().probe_cert_reject && variable > 0 {
            self.variable_registration_watch = Some((variable, 256));
        }
    }

    pub(super) fn probe_new_term_bits(&mut self, term: TermId, bits: &[CnfLit]) {
        let Some((variable, remaining)) = self.variable_registration_watch else {
            return;
        };
        let count = remaining.min(bits.len());
        let found = bits[..count]
            .iter()
            .position(|literal| literal.unsigned_abs() == variable as u32);
        if let Some(bit) = found {
            ay_core::safe_eprintln!(
                "c sat-variable-first-registration bv_instance={:p} owner=BvSolver::get_bits namespace=bv-local-dimacs1 variable={} term={:?} bit={} local_literal={} existing_term_count={} proof_authority=none",
                self,
                variable,
                term,
                bit,
                bits[bit],
                self.terms.len(),
            );
            self.variable_registration_watch = None;
        } else if count == remaining {
            ay_core::safe_eprintln!(
                "c sat-variable-first-registration bv_instance={:p} variable={} disposition=diagnostic-bit-limit limit=256 proof_authority=none",
                self,
                variable,
            );
            self.variable_registration_watch = None;
        } else {
            self.variable_registration_watch = Some((variable, remaining - count));
        }
    }

    /// Observe one positive, local DIMACS variable in this existing encoding.
    ///
    /// The caller supplies the actual namespace conversion. Output observes
    /// allocation-owner caches and real registrations; it neither synthesizes
    /// a TermId nor grants a mapping, source binding, or proof authority.
    /// Addresses join observations only during this borrowed instance's lifetime.
    /// Registration lookup is deliberately partial: at most 32 terms/256 bits
    /// and 32 entries from each Boolean map, with at most 8 matches printed.
    pub fn probe_variable_provenance(&self, variable: CnfLit) {
        if !ay_core::misc_cli_flags().probe_cert_reject || variable <= 0 {
            return;
        }
        ay_core::safe_eprintln!(
            "c sat-variable-origin bv_instance={:p} namespace=bv-local-dimacs1 variable={} allocated={} cached_false={} constant_owner=BvSolver::fresh_false and_children={:?} and_owner=BvSolver::mk_and xor_children={:?} mux_children={:?} xor_mux_capture_enabled={} source_bool_registration=not-inferred",
            self,
            variable,
            variable as u32 <= self.num_vars(),
            self.cached_false_lit == Some(variable),
            self.and_children.get(&variable),
            self.xor_children.get(&variable),
            self.mux_children.get(&variable),
            self.capture_gate_provenance,
        );
        let (mut bit_work, mut term_work, mut matches) = (0usize, 0usize, 0usize);
        for (&term, bits) in self.term_to_bits.iter().take(32) {
            term_work += 1;
            for (bit, &literal) in bits.iter().enumerate().take(256 - bit_work) {
                bit_work += 1;
                if literal.unsigned_abs() == variable as u32 {
                    ay_core::safe_eprintln!(
                        "c sat-variable-registration bv_instance={:p} owner=BvSolver::get_bits relation=term-bit term={:?} bit={} local_literal={} source_bool_mapping=none",
                        self,
                        term,
                        bit,
                        literal,
                    );
                    matches += 1;
                    if matches == 8 {
                        break;
                    }
                }
            }
            if bit_work == 256 || matches == 8 {
                break;
            }
        }
        for (owner, map) in [
            ("BvSolver::bitblast_predicate", &self.predicate_to_var),
            ("BvSolver::bitblast_bool", &self.bool_to_var),
        ] {
            for (&term, &literal) in map.iter().take(32) {
                if literal.unsigned_abs() == variable as u32 && matches < 8 {
                    ay_core::safe_eprintln!(
                        "c sat-variable-registration bv_instance={:p} owner={} relation=bool-literal term={:?} local_literal={} proof_authority=none",
                        self,
                        owner,
                        term,
                        literal,
                    );
                    matches += 1;
                }
            }
        }
        ay_core::safe_eprintln!(
            "c sat-variable-registration-coverage bv_instance={:p} terms_inspected={} terms_total={} bit_cells_inspected={} bit_cell_limit=256 bool_entry_limit_each=32 predicate_entries={} bool_entries={} matches={} match_limit=8 completeness=partial proof_authority=none",
            self,
            term_work,
            self.term_to_bits.len(),
            bit_work,
            self.predicate_to_var.len(),
            self.bool_to_var.len(),
            matches,
        );
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn observed_missing_foreign_and_real_variables_preserve_encoding_and_next_gate() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::bitvec(4));
        let y = terms.mk_var("y", Sort::bitvec(4));
        let term_count = terms.len();
        let mut baseline = BvSolver::new(&terms);
        let mut observed = BvSolver::new(&terms);
        let mut observed_vars = Vec::new();
        for (watch, solver) in [(false, &mut baseline), (true, &mut observed)] {
            let _flags = ay_core::misc_test_override::set(ay_core::MiscCliFlags {
                probe_cert_reject: watch,
                ..Default::default()
            });
            if watch {
                solver.watch_variable_registration(1);
            }
            let x_bits = solver.ensure_term_bits(x).expect("typed x");
            let y_bits = solver.ensure_term_bits(y).expect("typed y");
            let constant = solver.fresh_false();
            let gate = solver.mk_and(x_bits[0], y_bits[0]);
            observed_vars = vec![0, -1, i32::MAX, constant, gate, x_bits[0]];
        }
        let before = observed.clause_batch();
        let vars_before = observed.num_vars();
        let entries_before = observed.minted_entries_estimate();
        {
            let _flags = ay_core::misc_test_override::set(ay_core::MiscCliFlags {
                probe_cert_reject: true,
                ..Default::default()
            });
            for variable in observed_vars {
                observed.watch_variable_registration(variable);
                observed.probe_variable_provenance(variable);
            }
        }
        assert_eq!(observed.num_vars(), vars_before);
        assert_eq!(observed.minted_entries_estimate(), entries_before);
        assert_eq!(observed.clause_batch(), before);
        let baseline_next = baseline.mk_xor(1, 5);
        let observed_next = observed.mk_xor(1, 5);
        assert_eq!(observed_next, baseline_next);
        assert_eq!(observed.clause_batch(), baseline.clause_batch());
        assert_eq!(terms.len(), term_count);
    }

    #[test]
    fn canonical_false_hint_is_actual_positive_live_allocation() {
        let terms = TermStore::new();
        let mut solver = BvSolver::new(&terms);
        assert_eq!(solver.canonical_false_literal(), None);
        let literal = solver.fresh_false();
        assert_eq!(solver.canonical_false_literal(), Some(literal));
        assert_eq!(solver.clauses()[0].literals(), &[-literal]);
        solver.cached_false_lit = Some(-literal);
        assert_eq!(solver.canonical_false_literal(), None);
        solver.cached_false_lit = Some(i32::MAX);
        assert_eq!(solver.canonical_false_literal(), None);
        solver.cached_false_lit = Some(literal);
        solver.set_next_var(1);
        assert_eq!(solver.canonical_false_literal(), None);
    }
}
