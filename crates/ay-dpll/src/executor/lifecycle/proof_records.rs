// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::super::Executor;

impl Executor {
    pub(in crate::executor) fn clear_preprocessing_proof_records(&mut self) {
        self.quant_expansion_records.clear();
        self.ematching_proof_records.clear();
        self.consequence_replay_attempts.set(0);
        self.negated_exists_ground_inst_attempts.set(0);
        self.skolem_instance_records.clear();
        self.skolem_witness_records.clear();
        self.bv_mbqi_false_instance_records.clear();
        self.mbqi_refinement_instance_records.clear();
        self.qpf_premise_forced_instance_records.clear();
        self.dt_context_conflict_records.clear();
        if ay_core::misc_cli_flags().debug_cert
            && (!self.propagated_value_provenance.entries.is_empty()
                || !self.propagated_value_provenance.rewrites.is_empty())
        {
            eprintln!(
                "CERT/proof-records cleared: propagation entries={} rewrites={} exec={:p}",
                self.propagated_value_provenance.entries.len(),
                self.propagated_value_provenance.rewrites.len(),
                self as *const _,
            );
        }
        self.propagated_value_provenance = Default::default();
    }
}
