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

/// The driver query with `bv2nat` spelled `ubv_to_int`, the SMT-LIB 2.7 name
/// AY elaborates to the same term. `--self-check` claims an external-style
/// check, and pinned Carcara defines only `ubv_to_int`, so the verbatim
/// spelling is withheld (`self_check_withholds_letleak_unsat_carcara_cannot_parse`).
#[cfg(feature = "proof-checker")]
fn letleak_wall3_query_in_carcara_spelling() -> String {
    LETLEAK_WALL3_DRIVER_QUERY.replace("(bv2nat ", "(ubv_to_int ")
}

/// Self-check accepts the checked refutation for the exact original query.
/// This is the CLI's collection-only wiring: `set_self_check` followed by
/// `set_mandatory_proof_collection`.
#[cfg(feature = "proof-checker")]
#[test]
#[timeout(120000)]
fn self_check_publishes_letleak_unsat_on_checked_sat_refutation_authority() {
    let commands = parse(&letleak_wall3_query_in_carcara_spelling()).unwrap();
    let mut exec = Executor::new();
    exec.set_self_check(true);
    exec.set_mandatory_proof_collection();

    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["unsat"]);
}

/// An explicit artifact demand must publish the complete translated proof.
/// Authored quantified roots and ground literal spellings now have explicit
/// Alethe derivations, independently replayed against the original query.
///
/// Without `--self-check`: the verbatim query spells `bv2nat`, which pinned
/// Carcara does not define, so a lane claiming an external-style check
/// withholds it (`self_check_withholds_letleak_unsat_carcara_cannot_parse`),
/// and the document discloses that surface instead. The `ubv_to_int` spelling
/// is no substitute here: the printer spells the elaborated conversion
/// `bv2nat`, so the `and_pos` conjunct no longer matches its authored source
/// and the export is refused (measured; the proof-side vocabulary follow-up).
#[cfg(feature = "proof-checker")]
#[test]
#[timeout(120000)]
fn explicit_proof_demand_exports_complete_letleak_unsat() {
    let commands = parse(LETLEAK_WALL3_DRIVER_QUERY).unwrap();
    let mut exec = Executor::new();
    exec.set_produce_proofs(true);

    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["unsat"]);
    assert!(exec
        .last_unsat_proof_carcara_surface()
        .and_then(|surface| surface.unsupported_reason().map(str::to_string))
        .is_some_and(|reason| reason.contains("`bv2nat`")));
    assert!(!exec.unsat_proof_has_known_wire_gap());
    let wire = exec
        .try_export_last_proof_alethe_for_problem_scope()
        .expect("the exact query retains its proof")
        .expect("the authored proof must be exportable");
    assert!(!wire.contains(":rule hole"), "{wire}");
    assert!(!wire.contains(":rule trust"), "{wire}");
    assert_eq!(exec.get_proof(), wire);
}

/// The verbatim targo spelling: its problem uses `bv2nat`, which pinned
/// Carcara does not define, so `--self-check` withholds the UNSAT and names
/// that surface, both in the CLI's collection-only wiring and beside an
/// explicit artifact demand (the combination the explicit-demand test used
/// before). Before the certificate surface read the authored problem it was
/// disclosed `supported` and published.
#[cfg(feature = "proof-checker")]
#[test]
#[timeout(120000)]
fn self_check_withholds_letleak_unsat_carcara_cannot_parse() {
    let commands = parse(LETLEAK_WALL3_DRIVER_QUERY).unwrap();
    for explicit_demand in [false, true] {
        let mut exec = Executor::new();
        exec.set_self_check(true);
        if explicit_demand {
            exec.set_produce_proofs(true);
        } else {
            exec.set_mandatory_proof_collection();
        }

        let outputs = exec.execute_all(&commands).unwrap();

        assert_eq!(
            outputs,
            vec!["unknown"],
            "explicit demand: {explicit_demand}"
        );
        let detail = exec.unknown_detail().unwrap_or_default();
        assert!(detail.contains("`bv2nat`"), "{detail}");
    }
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
