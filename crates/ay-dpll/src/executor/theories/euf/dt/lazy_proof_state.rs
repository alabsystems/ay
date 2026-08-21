// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::TermId;

use crate::executor::{
    BvMbqiFalseInstanceRecord, DtContextConflictSink, EmatchingProofRecord,
    QpfPremiseForcedInstanceRecord, QuantExpansionRecord, SkolemInstanceRecord,
    SkolemWitnessRecord,
};
use crate::preprocess::PropagationRecords;

use super::Executor;

pub(super) struct DtLazyProofState {
    problem_assertions: Option<super::super::super::solve_harness::ProofProblemAssertionProvenance>,
    quant_expansions: Vec<QuantExpansionRecord>,
    ematching: Vec<EmatchingProofRecord>,
    skolem_instances: Vec<SkolemInstanceRecord>,
    skolem_witnesses: Vec<SkolemWitnessRecord>,
    bv_mbqi_false_instances: Vec<BvMbqiFalseInstanceRecord>,
    qpf_premise_forced_instances: Vec<QpfPremiseForcedInstanceRecord>,
    dt_context_conflicts: DtContextConflictSink,
    propagated_values: PropagationRecords,
    rebuild_originals: Vec<TermId>,
    term_overrides: Option<HashMap<TermId, String>>,
    reconstruction_suppressed: bool,
    translation_incomplete: bool,
}

impl DtLazyProofState {
    pub(super) fn capture(executor: &Executor) -> Self {
        Self {
            problem_assertions: executor.proof_problem_assertion_provenance.clone(),
            quant_expansions: executor.quant_expansion_records.clone(),
            ematching: executor.ematching_proof_records.clone(),
            skolem_instances: executor.skolem_instance_records.clone(),
            skolem_witnesses: executor.skolem_witness_records.clone(),
            bv_mbqi_false_instances: executor.bv_mbqi_false_instance_records.clone(),
            qpf_premise_forced_instances: executor.qpf_premise_forced_instance_records.clone(),
            dt_context_conflicts: executor.dt_context_conflict_records.clone(),
            propagated_values: executor.propagated_value_provenance.clone(),
            rebuild_originals: executor.last_proof_rebuild_originals.clone(),
            term_overrides: executor.last_proof_term_overrides.clone(),
            reconstruction_suppressed: executor.last_unsat_proof_reconstruction_suppressed,
            translation_incomplete: executor.quantified_proof_translation_incomplete,
        }
    }

    pub(super) fn restore(self, executor: &mut Executor) {
        executor.proof_problem_assertion_provenance = self.problem_assertions;
        executor.quant_expansion_records = self.quant_expansions;
        executor.ematching_proof_records = self.ematching;
        executor.skolem_instance_records = self.skolem_instances;
        executor.skolem_witness_records = self.skolem_witnesses;
        executor.bv_mbqi_false_instance_records = self.bv_mbqi_false_instances;
        executor.qpf_premise_forced_instance_records = self.qpf_premise_forced_instances;
        executor.dt_context_conflict_records = self.dt_context_conflicts;
        executor.propagated_value_provenance = self.propagated_values;
        executor.last_proof_rebuild_originals = self.rebuild_originals;
        executor.last_proof_term_overrides = self.term_overrides;
        executor.last_unsat_proof_reconstruction_suppressed = self.reconstruction_suppressed;
        executor.quantified_proof_translation_incomplete = self.translation_incomplete;
    }
}
