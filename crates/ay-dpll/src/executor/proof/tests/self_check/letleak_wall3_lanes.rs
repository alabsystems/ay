// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `executor::proof::tests` to preserve test FQNs.
//
// The #letleak wall 3 driver query and the three publication lanes that read
// the same refutation differently: `--self-check` (independently verified
// truth), an explicit artifact demand (the translated document itself), and
// the default best-effort text lane — plus the collection-only flag those
// lanes are wired through.

/// The deductive-checks letleak driver query (#letleak wall 3), verbatim as targo
/// emitted it: named assertions + `:produce-unsat-cores` (which triggers the
/// named→assumption redirect and its folded rescue solve), a conjunction
/// carrying the authored `forall`, and a ground refutation conjunct whose
/// encoder substitutes the entailed `len = 1` below every provenance seam.
/// The refutation the funnel publishes is the checked SAT-refutation sidecar,
/// whose exact-fragment bridge closes the substituted instance with a
/// strictly-validated `ground_equality_substitution` lemma.
#[cfg(feature = "proof-checker")]
const LETLEAK_WALL3_DRIVER_QUERY: &str = r#"
(set-option :produce-unsat-cores true)
(set-logic ALL)
(declare-const a (Array (_ BitVec 64) (_ BitVec 8)))
(declare-const __ground_seed___deductive_checks_collection_ctor_deductive_checks_types_Seq_u8_empty (_ BitVec 8))
(declare-const __ground_seed_a (_ BitVec 8))
(declare-const __deductive_checks_len_a Int)
(declare-const __deductive_checks_collection_ctor_deductive_checks_types_Seq_u8_empty (Array (_ BitVec 64) (_ BitVec 8)))
(declare-const __deductive_checks_refute_forall___deductive_checks_ext_seq_idx_6 (_ BitVec 64))
(assert (! (<= 0 __deductive_checks_len_a) :named dn0))
(assert (! true :named dn1))
(assert (! true :named dn2))
(assert (! true :named dn3))
(assert (! true :named dn4))
(assert (! true :named dn5))
(assert (! true :named dn6))
(assert (! (and (= __deductive_checks_len_a 1) (forall ((__deductive_checks_ext_seq_idx_3 (_ BitVec 64))) (or (not (< (bv2nat __deductive_checks_ext_seq_idx_3) __deductive_checks_len_a)) (= (select a __deductive_checks_ext_seq_idx_3) (select (store __deductive_checks_collection_ctor_deductive_checks_types_Seq_u8_empty #x0000000000000000 #x01) __deductive_checks_ext_seq_idx_3))))) :named dn7))
(assert (! (= (select __deductive_checks_collection_ctor_deductive_checks_types_Seq_u8_empty #x0000000000000000) __ground_seed___deductive_checks_collection_ctor_deductive_checks_types_Seq_u8_empty) :named dn8))
(assert (! (= (select a #x0000000000000000) __ground_seed_a) :named dn9))
(assert (! true :named dn10))
(assert (! true :named dn11))
(assert (! true :named dn12))
(assert (! true :named dn13))
(assert (! true :named dn14))
(assert (! true :named dn15))
(assert (! true :named dn16))
(assert (! (or (not (= __deductive_checks_len_a 1)) (and (< (bv2nat __deductive_checks_refute_forall___deductive_checks_ext_seq_idx_6) __deductive_checks_len_a) (not (= (select a __deductive_checks_refute_forall___deductive_checks_ext_seq_idx_6) (select (store __deductive_checks_collection_ctor_deductive_checks_types_Seq_u8_empty #x0000000000000000 #x01) __deductive_checks_refute_forall___deductive_checks_ext_seq_idx_6))))) :named dn17))
(check-sat)
"#;

/// #letleak wall 3, the self-check half: `--self-check` demands independently
/// verified truth, not the exported Alethe document, so a current checked
/// SAT-refutation sidecar for the exact query publishes `unsat` even while
/// the raw export still carries a residual trust step. This is the CLI's
/// exact wiring: `set_self_check` + `set_mandatory_proof_collection`.
#[cfg(feature = "proof-checker")]
#[test]
#[timeout(120000)]
fn self_check_publishes_letleak_unsat_on_checked_sat_refutation_authority() {
    let commands = parse(LETLEAK_WALL3_DRIVER_QUERY).unwrap();
    let mut exec = Executor::new();
    exec.set_self_check(true);
    exec.set_mandatory_proof_collection();

    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["unsat"]);
}

/// The dual ruling: an EXPLICIT artifact demand (`--proof`/`:produce-proofs`)
/// promises the translated document itself, so the residual trust step keeps
/// withholding `unsat` — the independent certification lanes must not launder
/// a hole-bearing artifact past a caller who asked for that artifact.
#[cfg(feature = "proof-checker")]
#[test]
#[timeout(120000)]
fn explicit_proof_demand_still_withholds_letleak_unsat() {
    let commands = parse(LETLEAK_WALL3_DRIVER_QUERY).unwrap();
    let mut exec = Executor::new();
    exec.set_self_check(true);
    exec.set_produce_proofs(true);

    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["unknown"]);
}

/// The default text lane (best-effort synthesized certificate) publishes the
/// same verdict through `take_unsat_certificate`'s folded named-assumption
/// leg: the rescue solve binds `roots = base ++ A` with an empty assumption
/// vector while the outer command's `last_assumptions` still names `A`, and
/// the exact tail match admits precisely that shape.
#[cfg(feature = "proof-checker")]
#[test]
#[timeout(120000)]
fn default_lane_publishes_letleak_unsat_via_folded_assumption_certificate() {
    let commands = parse(LETLEAK_WALL3_DRIVER_QUERY).unwrap();
    let mut exec = Executor::new();
    exec.set_best_effort_produce_proofs(1_000_000);

    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["unsat"]);
}

/// `set_mandatory_proof_collection` is collection-only: unbudgeted mandatory
/// reconstruction with NO explicit-artifact demand, and order-independent
/// with a real artifact demand arriving later.
#[test]
fn mandatory_proof_collection_does_not_demand_artifact() {
    let mut exec = Executor::new();
    exec.set_mandatory_proof_collection();

    assert!(exec.is_producing_proofs());
    assert!(!exec.proof_artifact_required);
    assert!(exec.proof_reconstruction_step_budget.is_none());

    exec.set_produce_proofs(true);
    assert!(exec.proof_artifact_required);
}
