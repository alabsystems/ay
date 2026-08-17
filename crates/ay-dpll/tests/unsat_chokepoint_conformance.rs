// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Conformance pin for mandatory public UNSAT certification.

use std::path::PathBuf;

use ay_dpll::api::{Logic, Solver, Sort};

#[path = "unsat_chokepoint_conformance/post_rebase.rs"]
mod post_rebase;

fn read(rel: &str) -> String {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join(rel);
    std::fs::read_to_string(&path)
        .unwrap_or_else(|error| panic!("cannot read {}: {error}", path.display()))
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
    let source = read("src/executor/unsat_cert.rs");
    let bind_source = read("src/executor/unsat_cert/certification_source.rs");
    post_rebase::assert_certificate_mint_sites(&source, &bind_source);
    post_rebase::assert_mint_authentication(&source, &bind_source);

    post_rebase::assert_certificate_consumption(&source);

    post_rebase::assert_publication_stop_dominance(&source);
}

#[test]
fn cli_native_and_text_paths_route_through_unsat_funnel() {
    let executor = read("src/executor.rs");
    assert!(
        executor
            .matches("self.certify_unsat_for_publication(sat_result,")
            .count()
            >= 2,
        "both SMT-LIB check-sat variants must use the UNSAT funnel"
    );

    let native = read("src/api/solving/check.rs");
    assert!(
        native
            .matches(".certify_unsat_for_publication(result,")
            .count()
            >= 3,
        "plain, interruptible, and assumption native checks must use the funnel"
    );
    assert!(
        native.contains("pub(super) fn finish_verified_result(")
            && native.contains("let unsat_certificate = self.executor.take_unsat_certificate();"),
        "the sole native result boundary must consume the one-shot token"
    );
    let planner = native
        .find("fn native_publication_controls_at(")
        .expect("native publication-control planner must exist");
    let planner_end = native[planner..]
        .find("fn earliest_optional<")
        .map(|offset| planner + offset)
        .expect("native publication-control planner must have a bounded source region");
    let planner_body = &native[planner..planner_end];
    assert!(
        native.contains("self.native_publication_controls_at(Instant::now())")
            && planner_body
                .contains("let previous_deadline = self.executor.current_solve_deadline();")
            && planner_body.contains("now.checked_add(timeout)")
            && planner_body.contains(".executor\n            .timeout()")
            && planner_body.contains("Self::earliest_optional(")
            && planner_body.contains("let previous_memory_limit = self.executor.memory_limit();")
            && planner_body
                .contains("Self::earliest_optional(previous_memory_limit, self.memory_limit)"),
        "native publication controls must sample time once and preserve the earliest API, parsed, \
         and pre-existing deadline plus the tightest RSS ceiling"
    );
    let install_controls = native
        .find("pub(super) fn install_solve_controls(")
        .expect("native control installer must exist");
    let restore_controls = native
        .find("pub(super) fn restore_solve_controls(")
        .expect("native control restorer must exist");
    let classify_controls = native
        .find("pub(super) fn classify_unknown_reason(")
        .expect("native control classification must exist");
    let install_body = &native[install_controls..restore_controls];
    let restore_body = &native[restore_controls..classify_controls];
    assert!(
        install_body.contains("set_memory_limit(controls.effective_memory_limit)")
            && install_body
                .contains("set_solve_controls(Some(self.interrupt.clone()), controls.deadline)")
            && restore_body.contains("set_solve_controls(None, controls.previous_deadline)")
            && restore_body.contains("set_memory_limit(controls.previous_memory_limit)"),
        "installation must apply the immutable effective envelope and restoration must recover \
         the executor-owned deadline and RSS settings"
    );
    let native_regions = [
        (
            "fn check_sat_with_authority_origin(",
            "pub fn check_sat_interruptible<",
            "plain native check-sat",
        ),
        (
            "fn check_sat_interruptible_with_authority_origin<",
            "pub fn check_sat_with_timeout(",
            "interruptible native check-sat",
        ),
        (
            "pub fn check_sat_assuming(",
            "\n}\n\n#[cfg(test)]",
            "native check-sat-assuming",
        ),
    ];
    for (start, end, name) in native_regions {
        let start = native
            .find(start)
            .unwrap_or_else(|| panic!("{name} must exist"));
        let end = native[start..]
            .find(end)
            .map(|offset| start + offset)
            .unwrap_or_else(|| panic!("{name} must have a bounded source region"));
        let body = &native[start..end];
        let plan = body
            .find("let controls = self.native_publication_controls();")
            .unwrap_or_else(|| panic!("{name} must plan one immutable control envelope"));
        let preflight = body
            .find("self.preflight_check(controls)")
            .unwrap_or_else(|| panic!("{name} must preflight that control envelope"));
        let install = body
            .find("self.install_solve_controls(controls);")
            .unwrap_or_else(|| panic!("{name} must install caller controls"));
        let certify = body
            .find("certify_unsat_for_publication(result,")
            .unwrap_or_else(|| panic!("{name} must certify UNSAT"));
        let classify = body
            .find("self.classify_unknown_reason(controls);")
            .unwrap_or_else(|| panic!("{name} must classify stops from the same envelope"));
        let admission = body
            .find("self.finish_verified_result(result)")
            .unwrap_or_else(|| panic!("{name} must use native token admission"));
        let restore = body
            .find("self.restore_solve_controls(controls);")
            .unwrap_or_else(|| panic!("{name} must restore executor-owned controls"));
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
            let transaction = body
                .find(".with_interruptible_publication_controls(")
                .expect("interruptible publication must have one callback-control transaction");
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

    let optimize = read("src/api/solving/optimize.rs");
    let optimize_start = optimize
        .find("pub fn optimize_check(")
        .expect("native optimization entrypoint must exist");
    let optimize_end = optimize[optimize_start..]
        .find("pub fn get_objective_value(")
        .map(|offset| optimize_start + offset)
        .expect("native optimization entrypoint must have a bounded source region");
    let optimize_body = &optimize[optimize_start..optimize_end];
    let optimize_plan = optimize_body
        .find("let controls = self.native_publication_controls();")
        .expect("native optimization must plan one control envelope");
    let optimize_preflight = optimize_body
        .find("self.preflight_check(controls)")
        .expect("native optimization must preflight its control envelope");
    let optimize_install = optimize_body
        .find("self.install_solve_controls(controls);")
        .expect("native optimization must install its control envelope");
    let optimize_execute = optimize_body
        .find("self.executor.execute_native_optimization_check_sat()")
        .expect("native optimization must execute inside its control envelope");
    let optimize_admit = optimize_body
        .find("self.finish_verified_result(result)")
        .expect("native optimization must consume the final result capability");
    let optimize_restore = optimize_body
        .find("self.restore_solve_controls(controls);")
        .expect("native optimization must restore executor-owned controls");
    assert!(
        optimize_plan < optimize_preflight
            && optimize_preflight < optimize_install
            && optimize_install < optimize_execute
            && optimize_execute < optimize_admit
            && optimize_admit < optimize_restore,
        "native optimization must retain one deadline/interrupt/RSS envelope through all nested \
         feasibility checks and final capability admission"
    );

    let maxsmt = read("src/api/solving/maxsmt.rs");
    let maxsmt_start = maxsmt
        .find("pub fn check_sat_max(")
        .expect("native MaxSMT entrypoint must exist");
    let maxsmt_end = maxsmt[maxsmt_start..]
        .find("fn decline_maxsmt_definite_on_external_stop(")
        .map(|offset| maxsmt_start + offset)
        .expect("native MaxSMT entrypoint must have a bounded source region");
    let maxsmt_body = &maxsmt[maxsmt_start..maxsmt_end];
    let maxsmt_plan = maxsmt_body
        .find("let controls = self.native_publication_controls();")
        .expect("native MaxSMT must plan one control envelope");
    let maxsmt_preflight = maxsmt_body
        .find("self.preflight_check(controls)")
        .expect("native MaxSMT must preflight its control envelope");
    let maxsmt_install = maxsmt_body
        .find("self.install_solve_controls(controls);")
        .expect("native MaxSMT must install its control envelope");
    let maxsmt_outcome = maxsmt_body
        .find("let outcome = (|| -> Result<MaxSmtResult, SolverError>")
        .expect("native MaxSMT must close all publication paths in one transaction");
    let maxsmt_optimal = maxsmt_body
        .find("Ok(MaxSmtResult::optimal(")
        .expect("native MaxSMT must have an authenticated optimal publication point");
    let maxsmt_restore = maxsmt_body
        .find("self.restore_solve_controls(controls);")
        .expect("native MaxSMT must restore executor-owned controls");
    let maxsmt_return = maxsmt_body
        .rfind("\n        outcome")
        .expect("native MaxSMT must return only after control restoration");
    assert!(
        maxsmt_body
            .matches("decline_maxsmt_definite_on_external_stop(")
            .count()
            >= 2
            && maxsmt_plan < maxsmt_preflight
            && maxsmt_preflight < maxsmt_install
            && maxsmt_install < maxsmt_outcome
            && maxsmt_outcome < maxsmt_optimal
            && maxsmt_optimal < maxsmt_restore
            && maxsmt_restore < maxsmt_return,
        "native MaxSMT must retain one deadline/interrupt/RSS envelope through engine admission, \
         objective authentication, and the final late-stop check"
    );

    let result = read("src/api/types/results.rs");
    assert!(
        result.contains("pub(crate) fn certified_unsat(")
            && result.contains("certificate: UnsatCertificate")
            && result.contains("certificate.strict_proof_verified()")
            && result.contains("certificate.independently_verified()")
            && result.contains("certificate.exact_semantic_verified()")
            && !result.contains("pub(crate) fn from_validated("),
        "VerifiedSolveResult must have no token-free definite UNSAT constructor"
    );

    let text_admission = read("src/executor/model/sat_emit.rs");
    assert!(
        text_admission.contains("if let Some(certificate) = self.take_unsat_certificate()"),
        "the SMT-LIB text boundary must consume and classify the sealed token"
    );

    let cross_check = read("src/api/solving/cross_check.rs");
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
    let proof_api = read("src/api/proofs.rs");
    post_rebase::assert_proof_api_reconfirmation(&proof_api);

    let unsat = read("src/executor/unsat_cert.rs");
    post_rebase::assert_whole_problem_reconfirmation(&unsat);

    post_rebase::assert_forged_sat_guard(&unsat);

    let check_sat = read("src/executor/check_sat.rs");
    let normalized = check_sat.split_whitespace().collect::<Vec<_>>().join(" ");
    assert!(
        normalized.contains(
            "if self.solve_deadline.get().is_none() && self.quantifier_deadline_policy != super::QuantifierDeadlinePolicy::Exact"
        ),
        "Exact reconfirmation policy must preserve an absent inherited deadline instead of installing a private safety wall"
    );
    assert!(
        !unsat.contains("WHOLE_PROBLEM_RESOLVE_BUDGET_MS"),
        "the obsolete load-sensitive whole-problem wall budget must stay removed"
    );

    let discharge = unsat
        .find("fn discharge_trust_steps_for_certification(")
        .expect("deferred-trust discharge must exist");
    let publication = unsat[discharge..]
        .find("pub(crate) fn certify_unsat_for_publication(")
        .map(|offset| discharge + offset)
        .expect("UNSAT publication funnel must follow deferred-trust discharge");
    let discharge_body = &unsat[discharge..publication];
    let forged_sat = discharge_body
        .find("if self.redecides_definitive_sat_within(")
        .expect("forged-SAT guard must run in deferred-trust discharge");
    // `9a9f65d7d proof(dt): authenticate exact typed member signatures` moved
    // this call from `check_proof_collecting_trust_with_context` to the
    // `_with_typed_context` variant, which additionally carries the executor's
    // exact datatype member signatures. Same position in the discharge order,
    // strictly more context authenticated.
    let collect_trust = discharge_body
        .find("ay_proof::check_proof_collecting_trust_with_typed_context(")
        .expect("trust collection must run in deferred-trust discharge");
    let whole_problem = discharge_body
        .find("if self.reconfirms_unsat_within(")
        .expect("whole-problem fallback must run in deferred-trust discharge");
    assert!(
        forged_sat < collect_trust && collect_trust < whole_problem,
        "definitive SAT must dominate every deferred-trust acceptance path, and the \
         whole-problem fallback must remain last"
    );
}

#[test]
fn pareto_unsat_extension_is_opaque_and_query_scoped() {
    let optimization = read("src/executor/optimization.rs");
    assert!(
        optimization.contains("struct ParetoFrontExhaustionExtension")
            && optimization.contains("query_epoch: QueryAuthorityEpoch")
            && optimization.contains("hard_roots: Box<[TermId]>")
            && optimization.contains("objectives: Box<[ay_frontend::Objective]>")
            && optimization.contains("self.declare_pareto_front_exhaustion_extension(exhaustion)"),
        "Pareto exhaustion must pass an opaque exact-query blocker package"
    );

    let unsat = read("src/executor/unsat_cert.rs");
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
    let lifecycle = read("src/executor/lifecycle.rs");
    let begin = lifecycle
        .find("pub(crate) fn begin_public_solve(")
        .expect("public solve lifecycle entry must exist");
    let mutation = lifecycle[begin..]
        .find("pub(crate) fn note_api_assertion_mutation")
        .map(|offset| begin + offset)
        .expect("public solve entry must have a bounded source region");
    let body = &lifecycle[begin..mutation];
    let tracking = body
        .find("self.proof_tracker.enable();")
        .expect("public solve must enable mandatory internal proof tracking");
    let epoch = body
        .find("self.begin_unsat_query_epoch(&authored_assertions);")
        .expect("public solve must freeze the UNSAT query epoch");
    let provenance = body
        .find("self.install_proof_source_provenance(&authored_assertions);")
        .expect("public solve must install authored proof provenance");
    assert!(tracking < epoch && epoch < provenance);

    let proof = read("src/executor/proof.rs");
    assert!(
        proof.contains("if !self.is_producing_proofs()"),
        "mandatory internal tracking must not opt users into `(get-proof)`"
    );
}
