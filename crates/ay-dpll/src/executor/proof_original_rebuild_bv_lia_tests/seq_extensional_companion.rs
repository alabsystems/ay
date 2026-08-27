// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

const SEQ_EXTENSIONAL_COMPANION_QUERY: &str = r#"
(set-option :produce-unsat-cores true)
(set-logic ALL)
(declare-const len_b Int)
(declare-const seed_a (_ BitVec 32))
(declare-const seed_b (_ BitVec 32))
(declare-const len_a Int)
(declare-const b (Array (_ BitVec 64) (_ BitVec 32)))
(declare-const a (Array (_ BitVec 64) (_ BitVec 32)))
(declare-const idx4 (_ BitVec 64))
(declare-const idx5 (_ BitVec 64))
(declare-const idx9 (_ BitVec 64))
(declare-const idx10 (_ BitVec 64))
(declare-const idx12 (_ BitVec 64))
(declare-const idx13 (_ BitVec 64))
(assert (! (<= 0 len_a) :named dn0))
(assert (! (<= 0 len_b) :named dn1))
(assert (! (or (= len_a (bv2nat idx4)) (not (<= 0 len_a))) :named dn2))
(assert (! (or (= len_b (bv2nat idx5)) (not (<= 0 len_b))) :named dn3))
(assert (! (and (= len_a len_b)
  (forall ((i (_ BitVec 64))) (or (= (select a i) (select b i)) (not (bvult i idx4))))
  (or (= (select a (bvsub ((_ int2bv 64) len_a) #x0000000000000001))
         (select b (bvsub ((_ int2bv 64) len_b) #x0000000000000001)))
      (not (< 0 len_a)))) :named dn4))
(assert (! (= (select a #x0000000000000000) seed_a) :named dn5))
(assert (! (= (select b #x0000000000000000) seed_b) :named dn6))
(assert (! (or (not (<= 0 len_a)) (= len_a (bv2nat idx9))) :named dn7))
(assert (! (or (not (<= 0 len_b)) (= len_b (bv2nat idx10))) :named dn8))
(assert (! (and (<= 0 len_a) (<= len_a 18446744073709551615)) :named dn9))
(assert (! (and (<= 0 len_b) (<= len_b 18446744073709551615)) :named dn10))
(assert (! (or (not (<= 0 len_a)) (= len_a (bv2nat idx12))) :named dn11))
(assert (! (or (not (<= 0 len_b)) (= len_b (bv2nat idx13))) :named dn12))
(assert (! (or (not (= len_a len_b))
  (and (< 0 len_a)
       (not (= (select a (bvsub ((_ int2bv 64) len_a) #x0000000000000001))
               (select b (bvsub ((_ int2bv 64) len_b) #x0000000000000001)))))
  (not (forall ((i (_ BitVec 64)))
    (or (= (select a i) (select b i)) (not (bvult i idx12)))))) :named dn13))
"#;

const GUARDED_BV2NAT_CARRIER_QUERY: &str = r#"
(set-option :produce-unsat-cores true)
(set-logic ALL)
(declare-const len_a Int)
(declare-const len_b Int)
(declare-const idx_a (_ BitVec 64))
(declare-const idx_b (_ BitVec 64))
(assert (! (<= 0 len_a) :named carrier_lower_a))
(assert (! (<= 0 len_b) :named carrier_lower_b))
(assert (! (or (= len_a (bv2nat idx_a)) (not (<= 0 len_a))) :named carrier_pin_a))
(assert (! (or (= len_b (bv2nat idx_b)) (not (<= 0 len_b))) :named carrier_pin_b))
(assert (! (or (not (<= 0 len_a))
               (not (<= len_a 18446744073709551615))) :named carrier_exclusion_a))
"#;

const EXACT_BV_CONTRADICTION_QUERY: &str = r#"
(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(assert (= x #x00))
(assert (= x #x01))
"#;

const EXACT_BV_SAT_QUERY: &str = r#"
(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(assert (= x #x00))
"#;

#[cfg(test)]
fn exact_public_executor(script: &str) -> Executor {
    let commands = ay_frontend::parse(script).expect("exact public fixture must parse");
    let mut executor = Executor::new();
    executor
        .execute_all(&commands)
        .expect("exact public fixture must elaborate");
    executor.begin_external_decision_query(false);
    executor.bind_materialized_public_query();
    executor.bind_unsat_query_assumptions(&[]);
    executor
}

#[test]
fn provisional_unsat_authenticates_complete_guarded_bv2nat_carrier_query() {
    let mut executor = exact_public_executor(GUARDED_BV2NAT_CARRIER_QUERY);
    let proposed = executor.try_complete_authenticated_seq_extensional_result(SolveResult::unsat());
    assert!(proposed.is_unsat());
    let proof = executor
        .last_proof
        .as_ref()
        .expect("the exact carrier contradiction installs a proof");
    assert!(proof.steps.iter().any(|step| matches!(
        step,
        ProofStep::TheoryLemma {
            kind: TheoryLemmaKind::BvLiaTautology,
            ..
        }
    )));
    ay_proof::check_proof_strict(proof, &executor.ctx.terms)
        .expect("the carrier proof must pass independent strict replay");
    assert!(executor
        .certify_unsat_for_publication(proposed, &[])
        .is_unsat());
}

#[test]
fn provisional_unsat_rejects_satisfiable_mismatched_carrier_guard() {
    let satisfiable = GUARDED_BV2NAT_CARRIER_QUERY
        .replace("(= len_a (bv2nat idx_a))", "(= len_b (bv2nat idx_a))");
    let mut executor = exact_public_executor(&satisfiable);
    let proposed = executor.try_complete_authenticated_seq_extensional_result(SolveResult::unsat());
    assert!(
        proposed.is_unsat(),
        "a decline preserves the provisional enum"
    );
    assert!(
        executor.last_proof.is_none(),
        "a satisfiable exact scope must not gain proof authority"
    );
    assert!(executor
        .certify_unsat_for_publication(proposed, &[])
        .is_unknown());
}

#[cfg(test)]
fn seq_extensional_companion_executor(extra_option: &str) -> Executor {
    let script = format!("{extra_option}\n{SEQ_EXTENSIONAL_COMPANION_QUERY}");
    let commands = ay_frontend::parse(&script).expect("sequence companion fixture must parse");
    let mut executor = Executor::new();
    executor
        .execute_all(&commands)
        .expect("sequence companion fixture must elaborate");
    executor
}

#[cfg(test)]
fn seq_extensional_companion_executor_without_parsed_surface() -> Executor {
    let commands = ay_frontend::parse(SEQ_EXTENSIONAL_COMPANION_QUERY)
        .expect("sequence companion fixture must parse");
    let mut executor = Executor::new();
    executor.ctx.set_retain_parsed_assertions(false);
    executor
        .execute_all(&commands)
        .expect("sequence companion fixture must elaborate");
    assert!(
        executor.ctx.assertions_parsed().is_empty(),
        "the fixture must model a native API query with no SMT-LIB surface AST"
    );
    executor
}

#[test]
fn native_terms_without_parsed_surface_authorize_exact_seq_discharge() {
    let mut executor = seq_extensional_companion_executor_without_parsed_surface();
    executor.begin_external_decision_query(false);
    executor.bind_materialized_public_query();
    executor.bind_unsat_query_assumptions(&[]);
    executor.last_unknown_reason = Some(UnknownReason::QuantifierUnhandled);

    let proposed = executor.try_complete_authenticated_seq_extensional_result(SolveResult::Unknown);
    assert!(proposed.is_unsat());
    assert!(executor
        .certify_unsat_for_publication(proposed, &[])
        .is_unsat());
}

#[test]
fn provisional_seq_unsat_is_reproved_for_the_restored_whole_query() {
    let mut executor = seq_extensional_companion_executor_without_parsed_surface();
    executor.begin_external_decision_query(false);
    executor.bind_materialized_public_query();
    executor.bind_unsat_query_assumptions(&[]);
    executor.last_proof = None;
    executor.last_unsat_proof_reconstruction_suppressed = true;

    let proposed = executor.try_complete_authenticated_seq_extensional_result(SolveResult::unsat());
    assert!(proposed.is_unsat());
    assert!(
        !executor.last_unsat_proof_reconstruction_suppressed,
        "the independently reconstructed whole-query proof supersedes nested suppression"
    );
    assert!(executor.unsat_proof_self_certified());
    assert!(executor
        .certify_unsat_for_publication(proposed, &[])
        .is_unsat());
}

#[test]
fn native_solver_publishes_authenticated_seq_extensional_companion_unsat() {
    use crate::api::{Logic, Solver};

    let mut solver = Solver::new(Logic::All);
    solver
        .parse_smtlib2(SEQ_EXTENSIONAL_COMPANION_QUERY)
        .expect("native API fixture must parse and assert");
    let details = solver.check_sat_with_details();
    assert!(
        details.result.is_unsat(),
        "the public native boundary must retain the live query epoch: {details:?}"
    );
    assert!(
        details.verification.unsat_proof_strictly_verified,
        "the exact theorem must publish only through a strict-checked proof"
    );
}

#[test]
fn named_public_query_discharge_is_strict_complete_and_preserves_core_tracking() {
    let mut executor = seq_extensional_companion_executor("");
    executor.begin_external_decision_query(false);
    executor.bind_materialized_public_query();
    executor.bind_unsat_query_assumptions(&[]);
    executor.last_assumptions = Some(executor.ctx.assertions.clone());
    executor.last_core_term_to_name = Some(
        executor
            .ctx
            .named_terms_iter()
            .map(|(name, term)| (term, name.to_string()))
            .collect(),
    );
    let core_names = executor.last_core_term_to_name.clone();
    assert_eq!(
        executor
            .authenticated_plain_query_assertions_after_named_core_redirect()
            .expect("the restored named query is authenticated")
            .len(),
        14
    );
    executor.last_unknown_reason = Some(UnknownReason::QuantifierUnhandled);

    let proposed = executor.try_complete_authenticated_seq_extensional_result(SolveResult::Unknown);
    let published = executor.certify_unsat_for_publication(proposed, &[]);
    assert!(published.is_unsat());
    let proof = executor
        .last_proof
        .as_ref()
        .expect("strict proof installed");
    assert!(executor.is_current_authenticated_seq_extensional_companion_proof(proof));
    let assume_count = proof
        .steps
        .iter()
        .filter(|step| matches!(step, ProofStep::Assume(_)))
        .count();
    assert_eq!(assume_count, 5, "the exact theorem has five premise leaves");
    assert_eq!(
        executor.last_assumptions.as_deref(),
        Some(executor.ctx.assertions.as_slice())
    );
    assert_eq!(executor.last_core_term_to_name, core_names);
    let published = executor.admit_command_solve_result(published);
    executor.last_result = Some(published);
    let core = executor.unsat_core();
    assert!(core.contains("dn4") && core.contains("dn13"), "{core}");
}

#[test]
fn seq_unknown_discharge_declines_near_miss_and_nonquantifier_reason() {
    let near_miss = SEQ_EXTENSIONAL_COMPANION_QUERY.replace("(bvult i idx12)", "(bvule i idx12)");
    let commands = ay_frontend::parse(&near_miss).expect("near miss parses");
    let mut executor = Executor::new();
    executor
        .execute_all(&commands)
        .expect("near miss elaborates");
    executor.begin_external_decision_query(false);
    executor.bind_materialized_public_query();
    executor.bind_unsat_query_assumptions(&[]);
    executor.last_unknown_reason = Some(UnknownReason::QuantifierUnhandled);
    let proposed = executor.try_complete_authenticated_seq_extensional_result(SolveResult::Unknown);
    let result = executor.certify_unsat_for_publication(proposed, &[]);
    assert!(result.is_unknown());
    assert_eq!(
        executor.last_unknown_reason,
        Some(UnknownReason::QuantifierUnhandled)
    );

    let mut wrong_reason = seq_extensional_companion_executor("");
    wrong_reason.begin_external_decision_query(false);
    wrong_reason.bind_materialized_public_query();
    wrong_reason.bind_unsat_query_assumptions(&[]);
    wrong_reason.last_unknown_reason = Some(UnknownReason::Incomplete);
    let proposed =
        wrong_reason.try_complete_authenticated_seq_extensional_result(SolveResult::Unknown);
    let result = wrong_reason.certify_unsat_for_publication(proposed, &[]);
    assert!(result.is_unknown());
    assert_eq!(
        wrong_reason.last_unknown_reason,
        Some(UnknownReason::Incomplete)
    );
}

#[test]
fn explicit_strict_wire_policy_rejects_native_sequence_theorem() {
    let mut executor = seq_extensional_companion_executor("(set-option :check-proofs-strict true)");
    executor.begin_external_decision_query(false);
    executor.bind_materialized_public_query();
    executor.bind_unsat_query_assumptions(&[]);
    executor.last_unknown_reason = Some(UnknownReason::QuantifierUnhandled);
    let proposed = executor.try_complete_authenticated_seq_extensional_result(SolveResult::Unknown);
    let result = executor.certify_unsat_for_publication(proposed, &[]);
    assert!(result.is_unknown());
    assert_eq!(
        executor.last_unknown_reason,
        Some(UnknownReason::ProofTrusted)
    );
    assert!(
        executor.last_proof.is_none(),
        "wire-rejected proof is revoked"
    );
}

#[test]
fn seq_unknown_discharge_rejects_forged_tracking_and_public_assumptions() {
    let mut forged = seq_extensional_companion_executor("");
    forged.begin_external_decision_query(false);
    forged.bind_materialized_public_query();
    forged.bind_unsat_query_assumptions(&[]);
    let foreign = forged
        .ctx
        .terms
        .mk_var("foreign_named_tracking_assumption", Sort::Bool);
    forged.last_assumptions = Some(vec![foreign]);
    forged.last_core_term_to_name = Some([(foreign, "forged".to_string())].into_iter().collect());
    forged.last_unknown_reason = Some(UnknownReason::QuantifierUnhandled);
    let proposed = forged.try_complete_authenticated_seq_extensional_result(SolveResult::Unknown);
    assert!(forged
        .certify_unsat_for_publication(proposed, &[])
        .is_unknown());

    let mut assumed = seq_extensional_companion_executor("");
    let public_assumption = assumed.ctx.terms.true_term();
    assumed.begin_external_decision_query(false);
    assumed.bind_materialized_public_query();
    assumed.bind_unsat_query_assumptions(&[public_assumption]);
    assumed.last_assumptions = Some(vec![public_assumption]);
    assumed.last_unknown_reason = Some(UnknownReason::QuantifierUnhandled);
    let proposed = assumed.try_complete_authenticated_seq_extensional_result(SolveResult::Unknown);
    assert!(assumed
        .certify_unsat_for_publication(proposed, &[public_assumption])
        .is_unknown());
}

#[test]
fn successful_seq_unknown_discharge_revokes_stale_sat_artifacts() {
    let mut executor = seq_extensional_companion_executor("");
    executor.begin_external_decision_query(false);
    executor.bind_materialized_public_query();
    executor.bind_unsat_query_assumptions(&[]);
    executor.last_model = Some(crate::executor::model::Model::empty());
    executor.last_model_validated = true;
    executor.last_proof_quality = Some(ay_proof::ProofQuality::default());
    executor.last_unknown_reason = Some(UnknownReason::QuantifierUnhandled);
    let proposed = executor.try_complete_authenticated_seq_extensional_result(SolveResult::Unknown);
    assert!(executor
        .certify_unsat_for_publication(proposed, &[])
        .is_unsat());
    assert!(executor.last_model.is_none());
    assert!(!executor.last_model_validated);
    assert!(executor
        .last_proof_quality
        .as_ref()
        .is_some_and(ay_proof::ProofQuality::is_complete));
}

#[test]
fn exact_ite_uf_rejection_notifier_requires_semantic_unsat_of_exact_scope() {
    let mut sat = exact_public_executor(EXACT_BV_SAT_QUERY);
    sat.ite_uf_definition_recovery.armed = true;
    sat.note_exact_ite_uf_definition_model_rejection("ite_uf_definition");
    assert!(
        sat.ite_uf_definition_recovery.attempted,
        "an exact bounded SAT scope reaches the semantic checker"
    );
    assert!(
        !sat.ite_uf_definition_recovery.rejected,
        "shape alone must not arm the restored-scope recovery"
    );

    let mut contradiction = exact_public_executor(EXACT_BV_CONTRADICTION_QUERY);
    contradiction.ite_uf_definition_recovery.armed = true;
    contradiction.note_exact_ite_uf_definition_model_rejection("ite_uf_definition");
    assert!(contradiction.ite_uf_definition_recovery.attempted);
    assert!(
        contradiction.ite_uf_definition_recovery.rejected,
        "only independently authenticated UNSAT may set the routing marker"
    );

    let mut foreign_scope = exact_public_executor(EXACT_BV_CONTRADICTION_QUERY);
    foreign_scope
        .proof_problem_assertion_provenance
        .as_mut()
        .expect("the public fixture installs proof provenance")
        .original_problem_assertions
        .pop();
    foreign_scope.ite_uf_definition_recovery.armed = true;
    foreign_scope.note_exact_ite_uf_definition_model_rejection("ite_uf_definition");
    assert!(
        !foreign_scope.ite_uf_definition_recovery.rejected,
        "proof provenance naming a strict subset of the frozen roots must fail closed"
    );
}

#[test]
fn exact_ite_uf_completion_declines_sat_subset_and_assumption_scopes_atomically() {
    let mut sat = exact_public_executor(EXACT_BV_SAT_QUERY);
    sat.last_model = Some(crate::executor::model::Model::empty());
    sat.last_model_validated = true;
    sat.last_lrat_certificate = Some(vec![7]);
    assert!(sat
        .try_complete_exact_ite_uf_definition_rejection(SolveResult::Unknown)
        .is_unknown());
    assert!(sat.last_proof.is_none());
    assert!(sat.last_model.is_some());
    assert!(sat.last_model_validated);
    assert_eq!(sat.last_lrat_certificate.as_deref(), Some([7].as_slice()));

    let mut subset = exact_public_executor(EXACT_BV_CONTRADICTION_QUERY);
    subset.ctx.assertions.pop();
    subset.last_lrat_certificate = Some(vec![11]);
    assert!(subset
        .try_complete_exact_ite_uf_definition_rejection(SolveResult::Unknown)
        .is_unknown());
    assert!(subset.last_proof.is_none());
    assert_eq!(subset.last_lrat_certificate.as_deref(), Some([11].as_slice()));

    let mut assumed = exact_public_executor(EXACT_BV_CONTRADICTION_QUERY);
    let assumption = assumed.ctx.terms.true_term();
    assumed.bind_unsat_query_assumptions(&[assumption]);
    assumed.last_assumptions = Some(vec![assumption]);
    assert!(assumed
        .try_complete_exact_ite_uf_definition_rejection(SolveResult::Unknown)
        .is_unknown());
    assert!(assumed.last_proof.is_none());
}

#[test]
fn exact_ite_uf_completion_kill_switch_declines_without_artifacts() {
    let _guard = ay_core::misc_test_override::set(ay_core::MiscCliFlags {
        no_consequence_replay: true,
        ..Default::default()
    });
    let mut executor = exact_public_executor(EXACT_BV_CONTRADICTION_QUERY);
    assert!(executor
        .try_complete_exact_ite_uf_definition_rejection(SolveResult::Unknown)
        .is_unknown());
    assert!(executor.last_proof.is_none());
}

#[test]
fn exact_ite_uf_completion_revokes_every_incompatible_artifact() {
    let mut executor = exact_public_executor(EXACT_BV_CONTRADICTION_QUERY);
    executor.last_model = Some(crate::executor::model::Model::empty());
    executor.last_model_validated = true;
    executor.last_validation_stats = Some(Default::default());
    executor.last_lrat_certificate = Some(vec![13]);
    executor.last_proof_term_overrides = Some(Default::default());
    executor.last_clause_trace = Some(ay_sat::ClauseTrace::new());
    executor.last_var_to_term = Some(Default::default());
    executor.last_trail_provenance = Some(Default::default());
    executor.last_negations = Some(Default::default());
    executor.last_clausification_proofs = Some(Vec::new());
    executor.last_original_clause_theory_proofs = Some(Vec::new());
    executor.last_bv_drat_self_cert = true;
    executor.plant_stale_sat_certificate_for_test();
    executor.plant_stale_checked_sat_refutation_for_test();
    executor.plant_stale_finite_enum_sidecars_for_test();

    assert!(executor
        .try_complete_exact_ite_uf_definition_rejection(SolveResult::Unknown)
        .is_unsat());
    assert!(executor.last_proof.is_some());
    assert!(executor.last_model.is_none());
    assert!(!executor.last_model_validated);
    assert!(executor.last_validation_stats.is_none());
    assert!(executor.last_sat_certificate.is_none());
    assert!(executor.last_lrat_certificate.is_none());
    assert!(executor.last_proof_term_overrides.is_none());
    assert!(executor.last_clause_trace.is_none());
    assert!(executor.last_checked_sat_refutation.is_none());
    assert!(executor.last_var_to_term.is_none());
    assert!(executor.last_trail_provenance.is_none());
    assert!(executor.last_negations.is_none());
    assert!(executor.last_clausification_proofs.is_none());
    assert!(executor.last_original_clause_theory_proofs.is_none());
    assert!(!executor.last_bv_drat_self_cert);
    assert!(executor.last_finite_enum_pigeonhole.is_none());
    assert!(executor.last_checked_finite_enum_pigeonhole.is_none());
}
