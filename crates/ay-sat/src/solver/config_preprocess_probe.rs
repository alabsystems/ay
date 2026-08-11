// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl Solver {
    pub(super) fn run_preprocess_probe_pass(&mut self, skip_congruence: bool) -> bool {
        self.set_diagnostic_pass(DiagnosticPass::Probe);
        self.ensure_level0_unit_proof_ids();
        let failed_before = self.inproc.prober.stats().failed;
        if self.run_preprocess_probe_search_loop() {
            self.clear_diagnostic_pass();
            return true;
        }
        self.clear_diagnostic_pass();

        if self.inproc.prober.stats().failed > failed_before
            && self.inproc_ctrl.decompose.enabled
            && !skip_congruence
        {
            self.set_diagnostic_pass(DiagnosticPass::Decompose);
            self.decompose();
            self.clear_diagnostic_pass();
            if self.propagate_check_unsat() {
                return true;
            }
        }

        false
    }

    fn run_preprocess_probe_search_loop(&mut self) -> bool {
        self.inproc.prober.ensure_num_vars(self.num_vars);
        self.inproc
            .prober
            .generate_probes(&self.arena, &self.vals, self.fixed_count);
        let probe_props_limit = self
            .num_propagations
            .saturating_add(PREPROCESS_PROBE_MAX_PROPAGATIONS);
        let mut preprocess_probes_tried: usize = 0;
        while let Some(probe_lit) = self.inproc.prober.next_probe() {
            if preprocess_probes_tried >= MAX_PREPROCESS_PROBES {
                break;
            }
            if self.is_interrupted() || self.preprocess_timed_out() {
                break;
            }
            if self.num_propagations >= probe_props_limit {
                break;
            }
            let var_idx = probe_lit.variable().index();
            if var_idx >= self.num_vars
                || self.var_is_assigned(var_idx)
                || self.var_lifecycle.is_removed(var_idx)
            {
                continue;
            }

            preprocess_probes_tried += 1;
            self.decide(probe_lit);

            if let Some(conflict_ref) = self.search_propagate() {
                let failed_lit = probe_lit.negated();
                let hints = self.collect_probe_conflict_lrat_hints(
                    conflict_ref,
                    probe_lit,
                    Some(failed_lit),
                );
                self.backtrack(0);
                let proof_id = self
                    .proof_emit_add(&[failed_lit], &hints, ProofAddKind::Derived)
                    .unwrap_or(0);
                if proof_id != 0 {
                    self.record_level0_proof_id_for_lit(failed_lit, proof_id);
                }
                self.enqueue(failed_lit, None);
                self.inproc.prober.record_failed();

                if self.propagate_check_unsat() {
                    return true;
                }
            } else {
                self.backtrack(0);
            }
            self.inproc.prober.mark_probed(probe_lit, self.fixed_count);
        }
        self.inproc.prober.record_round();
        false
    }
}
