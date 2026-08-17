// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

pub(super) fn assert_certificate_mint_sites(source: &str, bind_source: &str) {
    assert_eq!(
        source.matches("Ok(UnsatCertificate(kind))").count()
            + bind_source.matches("Ok(UnsatCertificate(kind))").count(),
        1,
        "the proof-backed UNSAT capability must have one common mint site"
    );
    let bind_fn = bind_source
        .find("fn bind_unsat_certification_source(")
        .expect("the extracted capability binder must exist");
    let bind_capability = bind_source[bind_fn..]
        .find("Ok(UnsatCertificate(kind))")
        .map(|offset| bind_fn + offset)
        .expect("the binder must construct the capability");
    assert!(
        bind_source[bind_fn..bind_capability].contains("let kind = match source {"),
        "the capability must be constructed only from a bound certification source"
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
}

pub(super) fn assert_mint_authentication(source: &str, bind_source: &str) {
    let mint = source
        .find("fn mint_unsat_certificate(")
        .expect("mandatory mint function must exist");
    let funnel = source
        .find("pub(crate) fn certify_unsat_for_publication(")
        .expect("public UNSAT funnel must exist");
    let body = &source[mint..funnel];
    let authenticate = body
        .find("self.authenticate_unsat_query_scope(assumptions, true)?")
        .expect("mint must authenticate the exact query scope");
    let proof = body
        .find("self.check_strict_unsat_presentation()")
        .expect("mint must invoke the strict proof presentation check");
    let capability = body
        .find("self.bind_unsat_certification_source(certification_source, authenticated_scope)")
        .expect("mint must delegate capability construction to the common binder");
    assert!(
        authenticate < proof && proof < capability,
        "the exact query scope and the strict proof must be checked before minting"
    );
    assert!(
        !body.contains("UnsatCertificate("),
        "the mint must not construct a capability itself — it delegates to the binder"
    );
    assert!(
        bind_source
            .find("fn check_strict_unsat_presentation(")
            .is_some_and(|start| bind_source[start..]
                .find("fn ")
                .is_some_and(|_| bind_source[start..]
                    .contains("self.check_proof_strict_with_datatypes(proof)"))),
        "the presentation check must invoke the strict datatype-aware proof checker"
    );
    let scope_start = source
        .find("fn authenticate_unsat_query_scope(")
        .expect("exact query-scope authentication must exist");
    let scope_end = source[scope_start..]
        .find("fn mint_competition_raw_certificate(")
        .map(|offset| scope_start + offset)
        .expect("query-scope authentication must precede the raw competition mint");
    let scope_body = &source[scope_start..scope_end];
    let bound = scope_body
        .find("if bound != assumptions")
        .expect("query-scope authentication must bind exact assumptions");
    let provenance = scope_body
        .find("provenance.original_problem_assertions != epoch.assertions")
        .expect("query-scope authentication must bind exact authored assertions");
    assert!(
        bound < provenance,
        "exact assumptions must be bound before exact authored assertions"
    );
}

pub(super) fn assert_certificate_consumption(source: &str) {
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
        "checked SAT-refutation consumption must reject stale authority/source state, any query extension, mismatched assumptions or proof roots, and a sidecar from another exact scope"
    );
}

pub(super) fn assert_publication_stop_dominance(source: &str) {
    let consume = source
        .find("pub(crate) fn take_unsat_certificate(")
        .expect("authority consumer must exist");
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
    let retain = funnel_body[mint_call..]
        .find("self.last_unsat_certificate = Some(certificate);")
        .map(|offset| mint_call + offset)
        .expect("the funnel must retain a checked certificate");
    assert!(
        mint_call < postflight && postflight < retain,
        "late external stops must be checked before a freshly minted UNSAT token is retained"
    );
    let retentions = funnel_body
        .match_indices("self.last_unsat_certificate = Some(certificate);")
        .map(|(offset, _)| offset)
        .collect::<Vec<_>>();
    assert!(
        retentions.len() >= 2,
        "the funnel must retain through both the ordinary mint and the raw competition branch: {retentions:?}"
    );
    for (index, &retain_at) in retentions.iter().enumerate() {
        let stop_at = funnel_body[..retain_at]
            .rfind("self.stop_declines_unsat_publication()")
            .unwrap_or_else(|| {
                panic!("retention {index} is not dominated by an external-stop check")
            });
        let previous_retention = index.checked_sub(1).map(|prior| retentions[prior]);
        assert!(
            previous_retention.is_none_or(|prior| prior < stop_at),
            "retention {index} reuses an earlier branch's stop check instead of performing its own"
        );
    }
}

pub(super) fn assert_proof_api_reconfirmation(proof_api: &str) {
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
}

pub(super) fn assert_whole_problem_reconfirmation(unsat: &str) {
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
        "whole-problem trust fallback must compose its deterministic caps with tighter caller limits, inherit outer solve controls, and must screen the re-solve's proof for STRUCTURAL defects"
    );
    assert!(
        !reconfirm_body.contains("strict.is_ok()\n    }"),
        "the re-solve proof screen must not demand trust-freeness of the twin proof — that is this fallback's own entry condition and made it decline every time"
    );
    assert!(
        !reconfirm_body.contains("exec.set_deadline(")
            && !reconfirm_body.contains("Duration::from_millis"),
        "the accepting whole-problem trust fallback must not use a private wall-clock cutoff"
    );
}

pub(super) fn assert_forged_sat_guard(unsat: &str) {
    let forged_guard = unsat
        .find("fn redecides_definitive_sat_within(")
        .expect("forged-SAT guard must exist");
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
        "the forged-SAT guard must compose local defaults with tighter caller limits, install the effective values, and only then disable the fresh executor's independent defaults"
    );
    assert!(
        unsat.contains(
            "fn control_lifetime_tiny_outer_rlimit_declines_strict_unsat_reconfirmation()"
        ) && unsat.contains(
            "fn control_lifetime_exhausted_outer_decision_limit_declines_forged_unsat_guard()"
        ),
        "focused regressions must pin tighter caller limits in both accepting reconfirmation and the downgrade-only forged-SAT guard"
    );
}
