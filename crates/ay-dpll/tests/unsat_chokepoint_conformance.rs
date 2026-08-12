// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Conformance pin for mandatory public UNSAT certification.

use std::path::PathBuf;

use ay_dpll::api::{Logic, Solver, Sort};

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
    assert_eq!(
        source.matches("Ok(UnsatCertificate(kind))").count(),
        1,
        "the proof-backed UNSAT capability must have one common mint site"
    );
    assert_eq!(
        source.matches("self.emit_checked_exact_unsat(").count(),
        5,
        "every exact semantic theorem wrapper must delegate to the common mint"
    );
    assert_eq!(
        source
            .matches("self.last_unsat_certificate = Some(UnsatCertificate(")
            .count(),
        0,
        "exact theorem wrappers must not construct capabilities directly"
    );
    let semantic_mint = source
        .find("fn emit_checked_exact_unsat(")
        .expect("common exact-semantic mint must exist");
    let first_semantic_wrapper = source[semantic_mint..]
        .find("pub(in crate::executor) fn emit_checked_exact_exists_unsat(")
        .map(|offset| semantic_mint + offset)
        .expect("exact-semantic mint must precede its theorem wrappers");
    let semantic_body = &source[semantic_mint..first_semantic_wrapper];
    let semantic_capability = semantic_body
        .find("let certificate = UnsatCertificate(kind);")
        .expect("common semantic mint must construct the private capability");
    let semantic_scope = semantic_body
        .find("certificate.checked_exact_semantic_is_current(self)")
        .expect("common semantic mint must authenticate the exact theorem scope");
    let presentation = semantic_body
        .find("self.strict_unsat_presentation_required()")
        .expect("common semantic mint must preserve explicit proof authority");
    let semantic_publish = semantic_body
        .find("self.last_unsat_certificate = Some(certificate);")
        .expect("common semantic mint must publish the checked capability");
    assert!(
        semantic_capability < semantic_scope
            && semantic_scope < presentation
            && presentation < semantic_publish,
        "exact semantic scope and proof-presentation policy must be checked before publication"
    );
    let mint = source
        .find("fn mint_unsat_certificate(")
        .expect("mandatory mint function must exist");
    let funnel = source
        .find("pub(crate) fn certify_unsat_for_publication(")
        .expect("public UNSAT funnel must exist");
    let body = &source[mint..funnel];
    let bound = body
        .find("if bound != assumptions")
        .expect("mint must bind exact assumptions");
    let provenance = body
        .find("provenance.original_problem_assertions != epoch.assertions")
        .expect("mint must bind exact authored assertions");
    let proof = body
        .find(".check_proof_strict_with_datatypes(proof)")
        .expect("mint must invoke the strict proof checker");
    let capability = body
        .find("Ok(UnsatCertificate(kind))")
        .expect("mint must construct the capability");
    assert!(
        bound < provenance && provenance < proof && proof < capability,
        "exact assumptions/assertions and strict proof must be checked before minting"
    );

    let consume = source
        .find("pub(crate) fn take_unsat_certificate(")
        .expect("authority consumer must exist");
    let consume_body = &source[consume..];
    assert!(
        consume_body.contains("scope.is_current(self)")
            && consume_body.contains("checked.is_current_for(")
            && consume_body.contains("evidence.is_current(self)"),
        "consumption must revalidate every sealed class against its exact current scope"
    );
    let checked_branch = consume_body
        .find("UnsatCertificateKind::CheckedSatRefutation { checked, scope } =>")
        .expect("checked SAT-refutation consumption branch must exist");
    let checked_end = consume_body[checked_branch..]
        .find("UnsatCertificateKind::CheckedBoolBv(checked) =>")
        .map(|offset| checked_branch + offset)
        .expect("checked SAT-refutation branch must have a bounded source region");
    let checked_body = &consume_body[checked_branch..checked_end];
    assert!(
        checked_body.contains("scope.is_current(self)")
            && checked_body.contains("epoch.is_current(self)")
            && checked_body.contains("epoch.declared_extension.is_empty()")
            && checked_body.contains("epoch.declared_extension_entries.is_empty()")
            && checked_body.contains("epoch.declared_extension_objectives.is_none()")
            && checked_body.contains("epoch.declared_extension_objective_entries.is_none()")
            && checked_body.contains("self.last_assumptions.as_deref()")
            && checked_body.contains("Some(bound_assumptions)")
            && checked_body
                .contains("bound_assumptions.is_empty() && self.last_assumptions.is_none()")
            && checked_body.contains("provenance.original_problem_assertions == epoch.assertions")
            && checked_body.contains("&epoch.authority_epoch,")
            && checked_body.contains("&epoch.source_context_stamp,")
            && checked_body.contains("&epoch.assertions,")
            && checked_body.contains("bound_assumptions,"),
        "checked SAT-refutation consumption must reject stale authority/source state, any query \
         extension, mismatched assumptions or proof roots, and a sidecar from another exact scope"
    );

    let funnel = source
        .find("pub(crate) fn certify_unsat_for_publication(")
        .expect("public UNSAT funnel must exist");
    let funnel_body = &source[funnel..consume];
    assert!(
        funnel_body
            .matches("self.stop_declines_unsat_publication()")
            .count()
            >= 3,
        "UNSAT publication must check external stops before certification, before prechecked acceptance, and after fresh minting"
    );
    let mint_call = funnel_body
        .find("let minted = self.mint_unsat_certificate(assumptions);")
        .expect("the funnel must mint into a local capability");
    let postflight = funnel_body[mint_call..]
        .find("self.stop_declines_unsat_publication()")
        .map(|offset| mint_call + offset)
        .expect("fresh certificate minting must have an external-stop postflight");
    let retain = funnel_body
        .find("self.last_unsat_certificate = Some(certificate);")
        .expect("the funnel must retain a checked certificate");
    assert!(
        mint_call < postflight && postflight < retain,
        "late external stops must be checked before a freshly minted UNSAT token is retained"
    );
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
    let helper = proof_api
        .find("fn executor_reports_plain_strict_unsat(")
        .expect("generic trust discharge must have one strict re-solve helper");
    let discharge = proof_api
        .find("pub(crate) fn discharge_trust_clause(")
        .expect("trust-clause discharge must exist");
    let helper_body = &proof_api[helper..discharge];
    assert!(
        helper_body.contains("exec.begin_public_solve(false);")
            && helper_body.contains("exec.bind_unsat_query_assumptions(&[]);")
            && helper_body.contains("exec.check_proof_strict_with_datatypes(proof).is_ok()"),
        "a repeated raw solver verdict must not certify a deferred trust step"
    );
    let discharge_body = &proof_api[discharge..];
    assert!(
        discharge_body
            .matches("executor_reports_plain_strict_unsat(&mut exec)")
            .count()
            >= 2,
        "both contextual and standalone generic trust probes must require strict proof evidence"
    );

    let unsat = read("src/executor/unsat_cert.rs");
    let reconfirm = unsat
        .find("fn reconfirms_unsat_within(")
        .expect("whole-problem trust fallback must exist");
    let forged_guard = unsat[reconfirm..]
        .find("fn redecides_definitive_sat_within(")
        .map(|offset| reconfirm + offset)
        .expect("whole-problem fallback must have a bounded source region");
    let reconfirm_body = &unsat[reconfirm..forged_guard];
    let tighter = unsat
        .find("fn tighter_optional_limit(")
        .expect("deterministic limit composition helper must exist");
    // Anchored on the next item's doc comment, NOT on the exact blank-line run
    // before it: a rustfmt pass that drops the blank line is a formatting
    // change, and it should not read as "the deterministic limit helper has
    // vanished". It did exactly that, and the resulting panic fired before this
    // test reached a single one of its real assertions.
    let tighter_end = unsat[tighter..]
        .find("/// True while")
        .map(|offset| tighter + offset)
        .expect("deterministic limit composition helper must have a bounded source region");
    let tighter_body = &unsat[tighter..tighter_end];
    assert!(
        tighter_body.contains("(Some(left), Some(right)) => Some(left.min(right))")
            && tighter_body.contains("(Some(limit), None) | (None, Some(limit)) => Some(limit)")
            && tighter_body.contains("(None, None) => None"),
        "optional deterministic limits must compose by minimum without inventing a finite limit"
    );
    assert!(
        reconfirm_body.contains("exec.begin_public_solve(false);")
            && reconfirm_body.contains("exec.bind_unsat_query_assumptions(&[]);")
            && reconfirm_body.contains(
                "tighter_optional_limit(self.resource_limit(), Some(limits.max_conflicts))"
            )
            && reconfirm_body.contains(
                "tighter_optional_limit(self.decision_limit(), Some(limits.max_decisions))"
            )
            && reconfirm_body.contains("if conflict_limit == Some(0) || decision_limit == Some(0)")
            && reconfirm_body.contains("exec.set_resource_limit(conflict_limit);")
            && reconfirm_body.contains("exec.set_decision_limit(decision_limit);")
            && reconfirm_body
                .contains("exec.set_quantifier_deadline_policy(QuantifierDeadlinePolicy::Exact);")
            && reconfirm_body.contains("exec.set_memory_limit(self.memory_limit());")
            && reconfirm_body.contains(
                "exec.set_solve_controls(self.solve_interrupt.clone(), self.solve_deadline.get());"
            )
            && reconfirm_body.contains("exec.check_proof_strict_with_datatypes(proof)")
            && reconfirm_body.contains("Err(error) => Self::is_trust_kind_rejection(error)"),
        "whole-problem trust fallback must compose its deterministic caps with tighter caller \
         limits, inherit outer solve controls, and must screen the re-solve's proof for \
         STRUCTURAL defects"
    );
    // The screen must stay a screen. Demanding `is_ok()` here — i.e. demanding
    // the twin proof be TRUST-FREE — made this arm unreachable for the only
    // class it serves: step (4) runs BECAUSE the original proof carries a trust
    // step, and the same engine on the same problem re-derives the same trust
    // step. A trust-kind rejection is the entry condition, not evidence against
    // it. Structural defects must still decline, which is what the predicate
    // above enumerates and this pin protects.
    assert!(
        !reconfirm_body.contains("strict.is_ok()\n    }"),
        "the re-solve proof screen must not demand trust-freeness of the twin proof — that is \
         this fallback's own entry condition and made it decline every time"
    );
    assert!(
        !reconfirm_body.contains("exec.set_deadline(")
            && !reconfirm_body.contains("Duration::from_millis"),
        "the accepting whole-problem trust fallback must not use a private wall-clock cutoff"
    );

    let discharge = unsat[forged_guard..]
        .find("fn discharge_trust_steps_for_certification(")
        .map(|offset| forged_guard + offset)
        .expect("forged-SAT guard must have a bounded source region");
    let forged_body = &unsat[forged_guard..discharge];
    let compose_conflicts = forged_body
        .find("tighter_optional_limit(self.resource_limit(), local_conflict_limit)")
        .expect("forged-SAT guard must compose the caller conflict limit");
    let compose_decisions = forged_body
        .find("tighter_optional_limit(self.decision_limit(), local_decision_limit)")
        .expect("forged-SAT guard must compose the caller decision limit");
    let install_conflicts = forged_body
        .find("exec.set_resource_limit(conflict_limit);")
        .expect("forged-SAT guard must install the composed conflict limit");
    let install_decisions = forged_body
        .find("exec.set_decision_limit(decision_limit);")
        .expect("forged-SAT guard must install the composed decision limit");
    let disable_fresh_default = forged_body
        .find("exec.set_ground_budget_enabled(false);")
        .expect("forged-SAT guard must disable the fresh executor default after composition");
    assert!(
        forged_body.contains("effective_conflict_allowance(None, self.ground_budget_enabled())")
            && forged_body
                .contains("effective_decision_allowance(None, self.ground_budget_enabled())")
            && forged_body.contains("if conflict_limit == Some(0) || decision_limit == Some(0)")
            && compose_conflicts < install_conflicts
            && compose_decisions < install_decisions
            && install_conflicts < disable_fresh_default
            && install_decisions < disable_fresh_default,
        "the forged-SAT guard must compose local defaults with tighter caller limits, install the \
         effective values, and only then disable the fresh executor's independent defaults"
    );
    assert!(
        unsat.contains(
            "fn control_lifetime_tiny_outer_rlimit_declines_strict_unsat_reconfirmation()"
        ) && unsat.contains(
            "fn control_lifetime_exhausted_outer_decision_limit_declines_forged_unsat_guard()"
        ),
        "focused regressions must pin tighter caller limits in both accepting reconfirmation and \
         the downgrade-only forged-SAT guard"
    );

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
    let collect_trust = discharge_body
        .find("ay_proof::check_proof_collecting_trust_with_context(")
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
