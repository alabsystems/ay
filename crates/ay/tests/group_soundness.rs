// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Grouped soundness and regression integration tests.

#[path = "common/spawn.rs"]
pub mod spawn;

#[path = "common/corpus.rs"]
pub mod corpus;

#[path = "group_soundness/arrays_as_array_extensionality.rs"]
mod arrays_as_array_extensionality;

#[path = "group_soundness/arrays_row2_regression.rs"]
mod arrays_row2_regression;

#[path = "group_soundness/arrays_z3_6303_8729.rs"]
mod arrays_z3_6303_8729;

#[path = "group_soundness/auflia_8745.rs"]
mod auflia_8745;

#[path = "group_soundness/auflia_quantifier_extensionality.rs"]
mod auflia_quantifier_extensionality;

#[path = "group_soundness/ufdt_enum_forall_distinctness.rs"]
mod ufdt_enum_forall_distinctness;

#[path = "group_soundness/bv_check_sat_assuming_regression.rs"]
mod bv_check_sat_assuming_regression;

#[path = "group_soundness/chc_array_bmc_8734.rs"]
mod chc_array_bmc_8734;

#[path = "group_soundness/chc_false_safe_barthe.rs"]
mod chc_false_safe_barthe;

#[path = "group_soundness/chc_false_safe_faulty_barthe.rs"]
mod chc_false_safe_faulty_barthe;

#[path = "group_soundness/chc_false_unsafe_pc_sfifo.rs"]
mod chc_false_unsafe_pc_sfifo;

#[path = "group_soundness/chc_empty_acyclic_safe_rigor.rs"]
mod chc_empty_acyclic_safe_rigor;

#[path = "group_soundness/dimacs_unsat_corpus_soundness.rs"]
mod dimacs_unsat_corpus_soundness;

#[path = "group_soundness/decompose_live_binaries_5314fd6c.rs"]
mod decompose_live_binaries_5314fd6c;

#[path = "group_soundness/frame_condition_regression.rs"]
mod frame_condition_regression;

#[path = "group_soundness/incremental_scoping_regression.rs"]
mod incremental_scoping_regression;

#[path = "group_soundness/intsat_soundness_8744.rs"]
mod intsat_soundness_8744;

#[path = "group_soundness/model_disequality_regression.rs"]
mod model_disequality_regression;

#[path = "group_soundness/nia_regression.rs"]
mod nia_regression;

#[path = "group_soundness/nia_negative_factor_soundness.rs"]
mod nia_negative_factor_soundness;

#[path = "group_soundness/dioph_2x2_fresh_var_leak.rs"]
mod dioph_2x2_fresh_var_leak;

#[path = "group_soundness/qf_auflia_storeinv_8804.rs"]
mod qf_auflia_storeinv_8804;

#[path = "group_soundness/qf_lia_direct_enum_regression.rs"]
mod qf_lia_direct_enum_regression;

#[path = "group_soundness/qf_lia_algebraic_substitution_51.rs"]
mod qf_lia_algebraic_substitution_51;

#[path = "group_soundness/qf_lia_puzzles_8762.rs"]
mod qf_lia_puzzles_8762;

#[path = "group_soundness/qf_lra_finalize_sat_fail_poison_8754.rs"]
mod qf_lra_finalize_sat_fail_poison_8754;

#[path = "group_soundness/qf_lra_model_validation_5534.rs"]
mod qf_lra_model_validation_5534;

#[path = "group_soundness/qf_lra_rebuild_8256.rs"]
mod qf_lra_rebuild_8256;

#[path = "group_soundness/qf_lra_stale_reason_8764.rs"]
mod qf_lra_stale_reason_8764;

#[path = "group_soundness/realloc_stale_pointer_9227.rs"]
mod realloc_stale_pointer_9227;

#[path = "group_soundness/qf_slia_8779.rs"]
mod qf_slia_8779;

#[path = "group_soundness/qf_uf_hwbench_soundness.rs"]
mod qf_uf_hwbench_soundness;

#[path = "group_soundness/qf_auflia_storecomm_8785.rs"]
mod qf_auflia_storecomm_8785;

#[path = "group_soundness/qf_nra_horner_refining.rs"]
mod qf_nra_horner_refining;

#[path = "group_soundness/vendored_fixture_integrity.rs"]
mod vendored_fixture_integrity;

#[path = "group_soundness/qf_uflia_8783.rs"]
mod qf_uflia_8783;

#[path = "group_soundness/qf_uflia_regression.rs"]
mod qf_uflia_regression;

#[path = "group_soundness/qf_uflia_seq_dense_ghost_vec_8784.rs"]
mod qf_uflia_seq_dense_ghost_vec_8784;

#[path = "group_soundness/qf_uflra_regression.rs"]
mod qf_uflra_regression;

#[path = "group_soundness/strict_proofs_8759.rs"]
mod strict_proofs_8759;

#[path = "group_soundness/provenance_assume_gate_leak2.rs"]
mod provenance_assume_gate_leak2;

#[path = "group_soundness/string_bv_format_8333.rs"]
mod string_bv_format_8333;

#[path = "group_soundness/uart_23_8758.rs"]
mod uart_23_8758;

#[path = "group_soundness/z3_open_bugs.rs"]
mod z3_open_bugs;

#[path = "group_soundness/resident_session_history.rs"]
mod resident_session_history;

#[path = "group_soundness/resident_session_reset.rs"]
mod resident_session_reset;

#[path = "group_soundness/external_codegen_consumer_certificates.rs"]
mod external_codegen_consumer_certificates;

#[path = "group_soundness/external_codegen_resident_word_level.rs"]
mod external_codegen_resident_word_level;

#[path = "group_soundness/alethe_dialect_disclosure.rs"]
mod alethe_dialect_disclosure;

#[path = "group_soundness/alethe_undeclared_application_head.rs"]
mod alethe_undeclared_application_head;

#[path = "group_soundness/zero_extend_reliance.rs"]
mod zero_extend_reliance;

#[path = "group_soundness/carcara_surface_problem_reading.rs"]
mod carcara_surface_problem_reading;

#[path = "group_soundness/strict_certificate_publication.rs"]
mod strict_certificate_publication;

#[path = "group_soundness/strict_admission_routes.rs"]
mod strict_admission_routes;

#[path = "group_soundness/strict_authored_spelling_bridges.rs"]
mod strict_authored_spelling_bridges;
#[path = "group_soundness/strict_definition_premise.rs"]
mod strict_definition_premise;
#[path = "group_soundness/strict_folded_premise.rs"]
mod strict_folded_premise;

#[path = "group_soundness/real_only_numeral_premise.rs"]
mod real_only_numeral_premise;
#[path = "group_soundness/strict_admission_spellings.rs"]
mod strict_admission_spellings;
#[path = "group_soundness/strict_default_publication.rs"]
mod strict_default_publication;
#[path = "group_soundness/strict_publication_after_error.rs"]
mod strict_publication_after_error;
#[path = "group_soundness/unsat_evidence_labels.rs"]
mod unsat_evidence_labels;

#[path = "group_soundness/strict_chc_spellings.rs"]
mod strict_chc_spellings;

#[path = "group_soundness/strict_chc_race_trace.rs"]
mod strict_chc_race_trace;

#[path = "group_soundness/nested_array_model_witness.rs"]
mod nested_array_model_witness;

#[path = "group_soundness/array_valued_uf_printed_model.rs"]
mod array_valued_uf_printed_model;

#[path = "group_soundness/array_refuted_model_resolve_cli.rs"]
mod array_refuted_model_resolve_cli;

#[path = "group_soundness/vacuous_binder_strict_proofs.rs"]
mod vacuous_binder_strict_proofs;

#[path = "group_soundness/refused_surface_step_hole.rs"]
mod refused_surface_step_hole;

#[path = "group_soundness/reordered_row_store_hole.rs"]
mod reordered_row_store_hole;

#[path = "group_soundness/signed_symbol_verdicts.rs"]
mod signed_symbol_verdicts;

#[path = "group_soundness/lnh_on_off_agreement.rs"]
mod lnh_on_off_agreement;

#[path = "group_soundness/model_checker_consumer_bmc_walker_original.rs"]
mod model_checker_consumer_bmc_walker_original;
