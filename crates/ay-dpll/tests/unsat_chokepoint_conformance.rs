// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Conformance pin for mandatory public UNSAT certification.

use ay_dpll::api::{Logic, Solver, Sort};

mod conformance_source;

#[path = "unsat_chokepoint_conformance/anchor_inventory.rs"]
mod anchor_inventory;

#[path = "unsat_chokepoint_conformance/post_rebase.rs"]
mod post_rebase;

use conformance_source::LogicalModule;

/// The logical module a guard addresses — the named file PLUS its submodule
/// directory. Every anchor lookup resolves across the whole module and must
/// resolve exactly once; every region stays inside one file. See
/// `tests/conformance_source/mod.rs` for why.
fn module(rel: &str) -> LogicalModule {
    LogicalModule::load(rel)
}

#[test]
fn public_boolean_unsat_carries_strict_emission_witness() {
    let mut solver = Solver::new(Logic::QfUf);
    let p = solver.declare_const("p", Sort::Bool);
    let not_p = solver.not(p);
    solver.assert_term(p);
    solver.assert_term(not_p);

    let result = solver.check_sat();
    assert!(
        result.is_unsat(),
        "a strict-valid contradiction must remain UNSAT"
    );
    assert!(
        result.has_unsat_emission_witness(),
        "public UNSAT must consume the private exact-query capability"
    );
    assert!(result.was_unsat_strictly_verified());
    assert_eq!(result.accept_for_consumer(), Ok(result.result()));
}

#[test]
fn assumption_unsat_certificate_is_bound_to_temporary_literal() {
    let mut solver = Solver::new(Logic::QfUf);
    let p = solver.declare_const("p", Sort::Bool);
    solver.assert_term(p);
    let not_p = solver.not(p);

    let result = solver.check_sat_assuming(&[not_p]);
    assert!(result.is_unsat());
    assert!(result.has_unsat_emission_witness());
    assert!(result.was_unsat_strictly_verified());

    // The assumption is query-local. Its removal must start a different epoch
    // and may not reuse the preceding UNSAT capability.
    let followup = solver.check_sat();
    assert!(followup.is_sat());
    assert!(!followup.has_unsat_emission_witness());
}

#[test]
fn quantified_ufbv_unsat_is_exactly_certified_or_fails_closed() {
    let mut solver = Solver::new(Logic::All);
    let bv4 = Sort::bitvec(4);
    let x = solver.fresh_var("x", bv4.clone());
    let f = solver.declare_fun("f", std::slice::from_ref(&bv4), bv4.clone());
    let fx = solver.apply(&f, &[x]);
    let reflexive = solver.eq(fx, fx);
    let impossible = solver.not(reflexive);
    let forall = solver.forall(&[x], impossible);
    solver.assert_term(forall);

    let result = solver.check_sat();
    assert!(!result.is_sat(), "forall x. f(x) != f(x) must never be SAT");
    if result.is_unsat() {
        assert!(result.has_unsat_emission_witness());
        assert_eq!(
            usize::from(result.was_unsat_strictly_verified())
                + usize::from(result.was_unsat_independently_verified())
                + usize::from(result.was_unsat_exact_semantically_verified()),
            1,
            "public UNSAT must retain exactly one sealed certification class"
        );
    } else {
        assert!(result.is_unknown());
        assert!(!result.has_unsat_emission_witness());
    }
}

#[test]
fn token_is_minted_only_after_epoch_and_strict_proof_checks() {
    let unsat = module("src/executor/unsat_cert.rs");
    post_rebase::assert_certificate_mint_sites(&unsat);
    post_rebase::assert_mint_authentication(&unsat);

    post_rebase::assert_certificate_consumption(&unsat);

    post_rebase::assert_publication_stop_dominance(&unsat);
}

#[test]
fn cli_native_and_text_paths_route_through_unsat_funnel() {
    let executor = module("src/executor.rs");
    assert!(
        executor.count("self.certify_unsat_for_publication(sat_result,") >= 2,
        "both SMT-LIB check-sat variants must use the UNSAT funnel"
    );

    let native = module("src/api/solving/check.rs");
    assert!(
        native.count(".certify_unsat_for_publication(result,") >= 3,
        "plain, interruptible, and assumption native checks must use the funnel"
    );
    assert!(
        native.contains("pub(super) fn finish_verified_result(")
            && native.contains("let unsat_certificate = self.executor.take_unsat_certificate();"),
        "the sole native result boundary must consume the one-shot token"
    );
    let planner = native.region(
        "fn native_publication_controls_at(",
        "fn earliest_optional<",
    );
    assert!(
        native.contains("self.native_publication_controls_at(Instant::now())")
            && planner.contains("let previous_deadline = self.executor.current_solve_deadline();")
            && planner.contains("now.checked_add(timeout)")
            && planner.contains(".executor\n            .timeout()")
            && planner.contains("Self::earliest_optional(")
            && planner.contains("let previous_memory_limit = self.executor.memory_limit();")
            && planner
                .contains("Self::earliest_optional(previous_memory_limit, self.memory_limit)"),
        "native publication controls must sample time once and preserve the earliest API, parsed, \
         and pre-existing deadline plus the tightest RSS ceiling"
    );
    let install_body = native.region(
        "pub(super) fn install_solve_controls(",
        "pub(super) fn restore_solve_controls(",
    );
    let restore_body = native.region(
        "pub(super) fn restore_solve_controls(",
        "pub(super) fn classify_unknown_reason(",
    );
    assert!(
        install_body.contains("set_memory_limit(controls.effective_memory_limit)")
            && install_body
                .contains("set_solve_controls(Some(self.interrupt.clone()), controls.deadline)")
            && restore_body.contains("set_solve_controls(None, controls.previous_deadline)")
            && restore_body.contains("set_memory_limit(controls.previous_memory_limit)"),
        "installation must apply the immutable effective envelope and restoration must recover \
         the executor-owned deadline and RSS settings"
    );
    // `check-sat-assuming` is the last method of its `impl`, so its region is
    // bounded by the block's own closing brace rather than by a following
    // declaration. That is at least as tight as the `#[cfg(test)]` marker it
    // used to use, and unlike that marker it cannot bind to the wrong site.
    let native_regions = [
        (
            native.region(
                "fn check_sat_with_authority_origin(",
                "pub fn check_sat_interruptible<",
            ),
            "plain native check-sat",
        ),
        (
            native.region(
                "fn check_sat_interruptible_with_authority_origin<",
                "pub fn check_sat_with_timeout(",
            ),
            "interruptible native check-sat",
        ),
        (
            native.region_to_item_end("pub fn check_sat_assuming("),
            "native check-sat-assuming",
        ),
    ];
    for (body, name) in native_regions {
        let plan = body.offset_of(
            "let controls = self.native_publication_controls();",
            &format!("{name} must plan one immutable control envelope"),
        );
        let preflight = body.offset_of(
            "self.preflight_check(controls)",
            &format!("{name} must preflight that control envelope"),
        );
        let install = body.offset_of(
            "self.install_solve_controls(controls);",
            &format!("{name} must install caller controls"),
        );
        let certify = body.offset_of(
            "certify_unsat_for_publication(result,",
            &format!("{name} must certify UNSAT"),
        );
        let classify = body.offset_of(
            "self.classify_unknown_reason(controls);",
            &format!("{name} must classify stops from the same envelope"),
        );
        let admission = body.offset_of(
            "self.finish_verified_result(result)",
            &format!("{name} must use native token admission"),
        );
        let restore = body.offset_of(
            "self.restore_solve_controls(controls);",
            &format!("{name} must restore executor-owned controls"),
        );
        assert!(
            plan < preflight
                && preflight < install
                && install < certify
                && certify < classify
                && classify < admission
                && admission < restore,
            "{name} must retain one absolute deadline/interrupt/RSS envelope through \
             certification and token admission, then restore prior executor controls"
        );
        if name == "interruptible native check-sat" {
            let transaction = body.offset_of(
                ".with_interruptible_publication_controls(",
                "interruptible publication must have one callback-control transaction",
            );
            assert!(
                install < transaction
                    && transaction < certify
                    && certify < admission
                    && admission < restore,
                "the callback watchdog/flag must enclose certification while the outer immutable \
                 control envelope remains installed through admission"
            );
        }
    }

    let optimize = module("src/api/solving/optimize.rs");
    let optimize_body = optimize.region("pub fn optimize_check(", "pub fn get_objective_value(");
    let optimize_plan = optimize_body.offset_of(
        "let controls = self.native_publication_controls();",
        "native optimization must plan one control envelope",
    );
    let optimize_preflight = optimize_body.offset_of(
        "self.preflight_check(controls)",
        "native optimization must preflight its control envelope",
    );
    let optimize_install = optimize_body.offset_of(
        "self.install_solve_controls(controls);",
        "native optimization must install its control envelope",
    );
    let optimize_execute = optimize_body.offset_of(
        "self.executor.execute_native_optimization_check_sat()",
        "native optimization must execute inside its control envelope",
    );
    let optimize_admit = optimize_body.offset_of(
        "self.finish_verified_result(result)",
        "native optimization must consume the final result capability",
    );
    let optimize_restore = optimize_body.offset_of(
        "self.restore_solve_controls(controls);",
        "native optimization must restore executor-owned controls",
    );
    assert!(
        optimize_plan < optimize_preflight
            && optimize_preflight < optimize_install
            && optimize_install < optimize_execute
            && optimize_execute < optimize_admit
            && optimize_admit < optimize_restore,
        "native optimization must retain one deadline/interrupt/RSS envelope through all nested \
         feasibility checks and final capability admission"
    );

    let maxsmt = module("src/api/solving/maxsmt.rs");
    let maxsmt_body = maxsmt.region(
        "pub fn check_sat_max(",
        "fn decline_maxsmt_definite_on_external_stop(",
    );
    let maxsmt_plan = maxsmt_body.offset_of(
        "let controls = self.native_publication_controls();",
        "native MaxSMT must plan one control envelope",
    );
    let maxsmt_preflight = maxsmt_body.offset_of(
        "self.preflight_check(controls)",
        "native MaxSMT must preflight its control envelope",
    );
    let maxsmt_install = maxsmt_body.offset_of(
        "self.install_solve_controls(controls);",
        "native MaxSMT must install its control envelope",
    );
    let maxsmt_outcome = maxsmt_body.offset_of(
        "let outcome = (|| -> Result<MaxSmtResult, SolverError>",
        "native MaxSMT must close all publication paths in one transaction",
    );
    let maxsmt_optimal = maxsmt_body.offset_of(
        "Ok(MaxSmtResult::optimal(",
        "native MaxSMT must have an authenticated optimal publication point",
    );
    let maxsmt_restore = maxsmt_body.offset_of(
        "self.restore_solve_controls(controls);",
        "native MaxSMT must restore executor-owned controls",
    );
    let maxsmt_return = maxsmt_body.last_offset_of(
        "\n        outcome",
        "native MaxSMT must return only after control restoration",
    );
    assert!(
        maxsmt_body.count("decline_maxsmt_definite_on_external_stop(") >= 2
            && maxsmt_plan < maxsmt_preflight
            && maxsmt_preflight < maxsmt_install
            && maxsmt_install < maxsmt_outcome
            && maxsmt_outcome < maxsmt_optimal
            && maxsmt_optimal < maxsmt_restore
            && maxsmt_restore < maxsmt_return,
        "native MaxSMT must retain one deadline/interrupt/RSS envelope through engine admission, \
         objective authentication, and the final late-stop check"
    );

    let result = module("src/api/types/results.rs");
    assert!(
        result.contains("pub(crate) fn certified_unsat(")
            && result.contains("certificate: UnsatCertificate")
            && result.contains("certificate.strict_proof_verified()")
            && result.contains("certificate.independently_verified()")
            && result.contains("certificate.exact_semantic_verified()")
            && !result.contains("pub(crate) fn from_validated("),
        "VerifiedSolveResult must have no token-free definite UNSAT constructor"
    );

    let text_admission = module("src/executor/model/sat_emit.rs");
    assert!(
        text_admission.contains("if let Some(certificate) = self.take_unsat_certificate()"),
        "the SMT-LIB text boundary must consume and classify the sealed token"
    );

    let cross_check = module("src/api/solving/cross_check.rs");
    assert!(
        cross_check.contains(".execute_authored(&solve_command)")
            && cross_check.contains("run.verification.unsat_proof_strictly_verified")
            && cross_check.contains("run.verification.unsat_independently_verified")
            && cross_check.contains("run.verification.unsat_exact_semantically_verified"),
        "cross-check replay must use the authored boundary and accept only an explicitly sealed UNSAT class"
    );
}

#[test]
fn deferred_trust_reconfirmation_requires_a_plain_strict_proof() {
    let proof_api = module("src/api/proofs.rs");
    post_rebase::assert_proof_api_reconfirmation(&proof_api);

    let unsat = module("src/executor/unsat_cert.rs");
    post_rebase::assert_whole_problem_reconfirmation(&unsat);

    post_rebase::assert_forged_sat_guard(&unsat);

    let check_sat = module("src/executor/check_sat.rs");
    assert!(
        check_sat.normalized_contains(
            "if self.solve_deadline.get().is_none() && self.quantifier_deadline_policy != super::QuantifierDeadlinePolicy::Exact"
        ),
        "Exact reconfirmation policy must preserve an absent inherited deadline instead of installing a private safety wall"
    );
    assert!(
        !unsat.contains("WHOLE_PROBLEM_RESOLVE_BUDGET_MS"),
        "the obsolete load-sensitive whole-problem wall budget must stay removed"
    );

    let discharge_body = unsat.region(
        "fn discharge_trust_steps_for_certification(",
        "pub(crate) fn certify_unsat_for_publication(",
    );
    let forged_sat = discharge_body.offset_of(
        "if self.redecides_definitive_sat_within(",
        "forged-SAT guard must run in deferred-trust discharge",
    );
    // `9a9f65d7d proof(dt): authenticate exact typed member signatures` moved
    // this call from `check_proof_collecting_trust_with_context` to the
    // `_with_typed_context` variant, which additionally carries the executor's
    // exact datatype member signatures. Same position in the discharge order,
    // strictly more context authenticated.
    let collect_trust = discharge_body.offset_of(
        "ay_proof::check_proof_collecting_trust_with_typed_context(",
        "trust collection must run in deferred-trust discharge",
    );
    let whole_problem = discharge_body.offset_of(
        "if self.reconfirms_unsat_within(",
        "whole-problem fallback must run in deferred-trust discharge",
    );
    assert!(
        forged_sat < collect_trust && collect_trust < whole_problem,
        "definitive SAT must dominate every deferred-trust acceptance path, and the \
         whole-problem fallback must remain last"
    );
}

#[test]
fn pareto_unsat_extension_is_opaque_and_query_scoped() {
    let optimization = module("src/executor/optimization.rs");
    // Bounded to the struct's own declaration: three of these field spellings
    // also occur on unrelated types in this module, so a whole-module
    // containment check could be satisfied without this package existing.
    let package = optimization.region_to_item_end("struct ParetoFrontExhaustionExtension");
    assert!(
        package.contains("query_epoch: QueryAuthorityEpoch")
            && package.contains("hard_roots: Box<[TermId]>")
            && package.contains("objectives: Box<[ay_frontend::Objective]>")
            && optimization.contains("self.declare_pareto_front_exhaustion_extension(exhaustion)"),
        "Pareto exhaustion must pass an opaque exact-query blocker package"
    );

    let unsat = module("src/executor/unsat_cert.rs");
    assert!(
        unsat.contains("extension: super::optimization::ParetoFrontExhaustionExtension")
            && !unsat.contains(
                "fn declare_pareto_front_exhaustion_extension(&mut self, blocking: &[TermId])"
            ),
        "the UNSAT epoch must expose no arbitrary-term Pareto extension setter"
    );
}

#[test]
fn proof_output_opt_out_does_not_disable_internal_certification() {
    let lifecycle = module("src/executor/lifecycle.rs");
    // `7d448bb9c3` moved `begin_public_solve` into `lifecycle/public_solve.rs`
    // AND extracted its proof-posture block into
    // `configure_public_solve_proof_posture`. Both halves are pinned: the entry
    // must CALL the posture helper before it freezes the epoch, and the helper
    // must be the thing that enables the tracker. Bounding the entry by the
    // next declaration in its own file is tighter than the old
    // `note_api_assertion_mutation` bound, which spanned three functions.
    let body = lifecycle.region(
        "pub(crate) fn begin_public_solve(",
        "pub(crate) fn begin_external_decision_query(",
    );
    let tracking = body.offset_of(
        "self.configure_public_solve_proof_posture();",
        "public solve must configure mandatory internal proof tracking",
    );
    let epoch = body.offset_of(
        "self.begin_unsat_query_epoch(&authored_assertions);",
        "public solve must freeze the UNSAT query epoch",
    );
    let provenance = body.offset_of(
        "self.install_proof_source_provenance(&authored_assertions);",
        "public solve must install authored proof provenance",
    );
    assert!(tracking < epoch && epoch < provenance);

    let posture = lifecycle.region(
        "fn configure_public_solve_proof_posture(",
        "pub(crate) fn begin_public_solve(",
    );
    assert!(
        posture.contains("self.proof_tracker.enable();"),
        "the posture helper must enable mandatory internal proof tracking"
    );
    // The ONLY opt-out is competition shedding (#proof-capability B1), and it
    // is an explicit branch rather than an absent `enable()`. Pinning both arms
    // keeps the invariant readable as "tracking on, unless shedding" and stops
    // a future edit from disabling tracking on some third condition without
    // this guard noticing.
    assert!(
        posture.contains("if self.competition_shedding_active() {")
            && posture.contains("self.proof_tracker.disable();"),
        "internal proof tracking may be shed only by the explicit competition opt-out"
    );

    let proof = module("src/executor/proof.rs");
    assert!(
        proof.contains("if !self.is_producing_proofs()"),
        "mandatory internal tracking must not opt users into `(get-proof)`"
    );
}
