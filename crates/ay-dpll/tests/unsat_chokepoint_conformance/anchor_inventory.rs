// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The anchor inventory for the UNSAT chokepoint conformance suite.

/// THE META-GUARD.
///
/// Every anchor this suite resolves must be listed here, and every listed
/// anchor must resolve EXACTLY ONCE across its logical module. `locate` already
/// enforces uniqueness at each call, but only for the calls a given run
/// reaches; this re-resolves the whole inventory in one place and — by reading
/// the suite's own source — refuses to let a new anchor arrive uninventoried.
///
/// A duplicate anchor is as dangerous as a missing one: the guard would bind to
/// whichever site sorted first and quietly check the wrong code.
/// `begin_public_solve` already exists twice in this crate.
#[test]
fn every_conformance_anchor_resolves_exactly_once_in_its_logical_module() {
    const INVENTORY: &[(&str, &[&str])] = &[
        (
            "src/executor/unsat_cert.rs",
            &[
                "fn bind_unsat_certification_source(",
                "Ok(UnsatCertificate(kind))",
                "fn checked_exact_semantic_is_current(",
                "pub(crate) fn strict_proof_verified(",
                "fn emit_checked_exact_unsat(",
                "pub(in crate::executor) fn emit_checked_exact_exists_unsat(",
                "fn mint_unsat_certificate(",
                "pub(crate) fn certify_unsat_for_publication(",
                "fn check_strict_unsat_presentation(",
                "fn authenticate_unsat_query_scope(",
                "fn mint_competition_raw_certificate(",
                "pub(crate) fn take_unsat_certificate(",
                "UnsatCertificateKind::CheckedSatRefutation { checked, scope } =>",
                "UnsatCertificateKind::CheckedBoolBv(checked) =>",
                "fn reconfirms_unsat_within(",
                "fn redecides_definitive_sat_within(",
                "fn tighter_optional_limit(",
                "/// True while",
                "fn is_deferred_discharge_rejection(",
                "fn is_trust_kind_rejection(",
                "fn authored_corroboration_scope(",
                "fn discharge_trust_steps_for_certification(",
            ],
        ),
        (
            "src/api/proofs.rs",
            &[
                "fn executor_reports_plain_strict_unsat(",
                "pub(crate) fn discharge_trust_clause(",
            ],
        ),
        (
            "src/api/solving/check.rs",
            &[
                "fn native_publication_controls_at(",
                "fn earliest_optional<",
                "pub(super) fn install_solve_controls(",
                "pub(super) fn restore_solve_controls(",
                "pub(super) fn classify_unknown_reason(",
                "fn check_sat_with_authority_origin(",
                "pub fn check_sat_interruptible<",
                "fn check_sat_interruptible_with_authority_origin<",
                "pub fn check_sat_with_timeout(",
                "pub fn check_sat_assuming(",
            ],
        ),
        (
            "src/api/solving/optimize.rs",
            &["pub fn optimize_check(", "pub fn get_objective_value("],
        ),
        (
            "src/api/solving/maxsmt.rs",
            &[
                "pub fn check_sat_max(",
                "fn decline_maxsmt_definite_on_external_stop(",
            ],
        ),
        (
            "src/executor/optimization.rs",
            &["struct ParetoFrontExhaustionExtension"],
        ),
        (
            "src/executor/lifecycle.rs",
            &[
                "pub(crate) fn begin_public_solve(",
                "pub(crate) fn begin_external_decision_query(",
                "fn configure_public_solve_proof_posture(",
            ],
        ),
    ];

    super::conformance_source::inventory::assert_anchor_inventory(
        &[
            "tests/unsat_chokepoint_conformance.rs",
            "tests/unsat_chokepoint_conformance/anchor_inventory.rs",
            "tests/unsat_chokepoint_conformance/post_rebase.rs",
        ],
        INVENTORY,
    );
}
