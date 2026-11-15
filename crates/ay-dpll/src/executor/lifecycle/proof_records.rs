// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ay_core::{Sort, TermId};

use super::super::{EmatchingProofRecord, Executor};

pub(in crate::executor) struct ConsequenceReplayState {
    ematching: Vec<EmatchingProofRecord>,
    attempts: u8,
    direct: Option<(u64, u8)>,
    /// A nested same-executor scope starts with an empty witness ledger and
    /// hands the outer decision's ledger back untouched
    /// (#negated-exists-cegqi-witness-hints).
    cegqi_witness_hints: Vec<(Sort, TermId)>,
    /// Same contract for the enumerated and E-matched binder values
    /// (#iff-split-implied-authority).
    instance_witness_hints: Vec<(Sort, TermId)>,
}

impl Executor {
    pub(in crate::executor) fn take_consequence_replay_state(&mut self) -> ConsequenceReplayState {
        ConsequenceReplayState {
            ematching: std::mem::take(&mut self.ematching_proof_records),
            attempts: self.consequence_replay_attempts.replace(0),
            direct: self.consequence_replay_direct_state.replace(None),
            cegqi_witness_hints: std::mem::take(&mut self.cegqi_witness_hints),
            instance_witness_hints: std::mem::take(&mut self.instance_witness_hints),
        }
    }

    pub(in crate::executor) fn restore_consequence_replay_state(
        &mut self,
        state: ConsequenceReplayState,
    ) {
        self.ematching_proof_records = state.ematching;
        self.consequence_replay_attempts.set(state.attempts);
        self.consequence_replay_direct_state.set(state.direct);
        self.cegqi_witness_hints = state.cegqi_witness_hints;
        self.instance_witness_hints = state.instance_witness_hints;
    }

    pub(in crate::executor) fn clear_preprocessing_proof_records(&mut self) {
        self.quant_expansion_records.clear();
        self.ematching_proof_records.clear();
        self.consequence_replay_attempts.set(0);
        self.consequence_replay_direct_state.set(None);
        self.negated_exists_ground_inst_attempts.set(0);
        self.implied_forall_ground_inst_attempts.set(0);
        self.exists_bridge_chain_attempts.set(0);
        self.authored_skeleton_refutation_attempts.set(0);
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
                std::ptr::from_ref(self),
            );
        }
        self.propagated_value_provenance = Default::default();
    }
}
