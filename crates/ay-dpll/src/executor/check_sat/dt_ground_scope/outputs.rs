// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Owned outputs of a private ground solve. Resource meters are not outputs.

use ay_core::kani_compat::{DetHashMap, DetHashSet};
use ay_core::{ClausificationProof, TermId, TheoryLemmaKind, TheoryLemmaProof};
use ay_sat::{ClauseTrace, SatUnknownReason};

use crate::executor::bv_mbqi::CheckedBvFullDomainSatAuthority;
use crate::executor::mbqi::{ConstInterpWitnessState, FiniteTableWitnessState};
use crate::executor::model::QuantifiedModelConfirmation;
use crate::executor::proof::CheckedFiniteEnumPigeonholeProof;
use crate::executor::proof_resolution::CheckedSatRefutation;
use crate::executor::quantifier_loop::CegqiUfRecompletionGrant;
use crate::executor::{
    BvMbqiFalseInstanceRecord, DtContextConflictSink, EmatchingProofRecord, Executor,
    FiniteEnumPigeonholeWitness, ProofDeclineMechanism, QpfPremiseForcedInstanceRecord,
    QuantExpansionRecord, QuantifiedSatAuthorityGrant, SkolemInstanceRecord, SkolemWitnessRecord,
    UnsatCertificate,
};
use crate::preprocess::PropagationRecords;

// Every listed field is moved, not cloned. Keeping the typed inventory next
// to its take/restore operations makes a large proof or clause trace cost a
// pointer move and prevents a reset/take_proof inside the window aliasing an
// outer ledger. No deadline, policy, source-work or search meter is listed.
macro_rules! owned_outputs {
    ($name:ident { $($field:ident: $kind:ty,)* }) => {
        pub(super) struct $name { $($field: $kind,)* }
        impl $name {
            pub(super) fn take(executor: &mut Executor) -> Self {
                Self { $($field: std::mem::take(&mut executor.$field),)* }
            }
            pub(super) fn restore(self, executor: &mut Executor) {
                $(executor.$field = self.$field;)*
            }
        }
    };
}

owned_outputs!(GroundProofOutputs {
    quant_expansion_records: Vec<QuantExpansionRecord>,
    ematching_proof_records: Vec<EmatchingProofRecord>,
    skolem_instance_records: Vec<SkolemInstanceRecord>,
    skolem_witness_records: Vec<SkolemWitnessRecord>,
    bv_mbqi_false_instance_records: Vec<BvMbqiFalseInstanceRecord>,
    qpf_premise_forced_instance_records: Vec<QpfPremiseForcedInstanceRecord>,
    dt_context_conflict_records: DtContextConflictSink,
    propagated_value_provenance: PropagationRecords,
    last_proof_rebuild_originals: Vec<TermId>,
    last_proof_raw_original_assertions: Vec<TermId>,
    last_proof_expanded_let_sources: Vec<(TermId, usize, String)>,
    quantified_proof_translation_incomplete: bool,
    last_clause_trace: Option<ClauseTrace>,
    last_var_to_term: Option<DetHashMap<u32, TermId>>,
    last_trail_provenance: Option<DetHashMap<u32, (u32, bool, Vec<u32>)>>,
    last_negations: Option<DetHashMap<TermId, TermId>>,
    last_clausification_proofs: Option<Vec<Option<ClausificationProof>>>,
    last_original_clause_theory_proofs: Option<Vec<Option<TheoryLemmaProof>>>,
    last_checked_sat_refutation: Option<CheckedSatRefutation>,
    last_finite_enum_pigeonhole: Option<FiniteEnumPigeonholeWitness>,
    last_checked_finite_enum_pigeonhole: Option<CheckedFiniteEnumPigeonholeProof>,
    last_lrat_certificate: Option<Vec<u8>>,
    last_proof_surface_withheld: Option<ProofDeclineMechanism>,
    last_bv_drat_self_cert: bool,
    last_unsat_certificate: Option<UnsatCertificate>,
    last_assumption_core: Option<Vec<TermId>>,
    pending_sat_unknown_reason: Option<SatUnknownReason>,
    injected_axiom_theory_kinds: DetHashMap<TermId, TheoryLemmaKind>,
    dt_solver_added_axiom_terms: DetHashSet<TermId>,
});

// Model-relative grants are parked for the whole transaction, not restored
// onto a fresh ground candidate. Only the full original certificate may
// create authority for the installed candidate. The Model object and its
// own identity seals are separately moved by CheckedModelInstallSnapshot.
owned_outputs!(GroundModelAuthority {
    quantified_model_confirmation: Option<QuantifiedModelConfirmation>,
    dt_cert_grant_active: bool,
    dt_cert_query_grant: Option<QuantifiedSatAuthorityGrant>,
    finite_table_cert_grant_active: bool,
    const_interp_cert_grant_active: bool,
    mbqi_sat_cert_grant_active: bool,
    mbqi_sat_cert_query_grant: Option<QuantifiedSatAuthorityGrant>,
    cegqi_uf_recompletion_grant: Option<CegqiUfRecompletionGrant>,
    bv_quantifier_full_domain_proof: bool,
    bv_quantifier_full_domain_pending_evidence: Option<CheckedBvFullDomainSatAuthority>,
    bv_quantifier_full_domain_query_grant: Option<QuantifiedSatAuthorityGrant>,
    finite_table_cert_witness_state: Option<FiniteTableWitnessState>,
    const_interp_cert_witness_state: Option<ConstInterpWitnessState>,
    sat_validated_by_mod_div_or_branch: bool,
    dt_array_injectivity_gate_bypass: bool,
});
