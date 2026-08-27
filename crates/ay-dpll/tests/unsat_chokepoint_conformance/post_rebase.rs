// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::conformance_source::LogicalModule;

pub(super) fn assert_certificate_mint_sites(unsat: &LogicalModule) {
    assert_eq!(
        unsat.count("Ok(UnsatCertificate(kind))"),
        1,
        "the proof-backed UNSAT capability must have one common mint site"
    );
    // `bind_unsat_certification_source` lives in the `unsat_cert/` submodule
    // directory; both endpoints resolve inside that one file, so this region is
    // still a contiguous stretch of a single source file.
    let bind = unsat.region(
        "fn bind_unsat_certification_source(",
        "Ok(UnsatCertificate(kind))",
    );
    assert!(
        bind.contains("let kind = match source {"),
        "the capability must be constructed only from a bound certification source"
    );
    // Every exact-semantic theorem wrapper must delegate to the common mint,
    // and every wrapper's kind must be authenticated by its own evidence in
    // `checked_exact_semantic_is_current`. Both are DERIVED from the wrappers
    // that exist rather than pinned to a hand-maintained count: `75630763f`
    // added a sixth wrapper (`emit_checked_exact_finite_expansion_unsat`) that
    // delegates correctly and is covered by the authority invariant, and the
    // literal `5` reported that correct change as a defect. Nothing is
    // loosened — the count equality still forbids a wrapper that mints
    // directly, and the per-wrapper checks below are strictly stronger than a
    // whole-file total, which one wrapper delegating twice could have
    // satisfied while another delegated not at all.
    let wrappers = unsat.windows("pub(in crate::executor) fn emit_checked_exact_");
    // Floor at the count that exists today, not at the count the stale literal
    // named. Adding a wrapper is ordinary work and must not trip this; REMOVING
    // one retires a published exact-semantic theorem and is exactly the event
    // that deserves a review, so it stays pinned.
    assert!(
        wrappers.len() >= 6,
        "the exact-semantic theorem lane must retain its published wrappers, found {}",
        wrappers.len()
    );
    assert_eq!(
        unsat.count("self.emit_checked_exact_unsat("),
        wrappers.len(),
        "every exact semantic theorem wrapper must delegate to the common mint"
    );
    let semantic_current = unsat.region(
        "fn checked_exact_semantic_is_current(",
        "pub(crate) fn strict_proof_verified(",
    );
    for (index, wrapper) in wrappers.iter().enumerate() {
        assert_eq!(
            wrapper.count("self.emit_checked_exact_unsat("),
            1,
            "exact semantic theorem wrapper {index} must delegate to the common mint exactly once"
        );
        let kind_at = wrapper.offset_of(
            "UnsatCertificateKind::",
            &format!("wrapper {index} must name the exact certificate kind it mints"),
        ) + "UnsatCertificateKind::".len();
        let kind = wrapper.text()[kind_at..]
            .split(|character: char| !character.is_alphanumeric() && character != '_')
            .next()
            .filter(|kind| !kind.is_empty())
            .unwrap_or_else(|| panic!("wrapper {index} must name a certificate kind identifier"));
        // A `=> false` arm is written `Kind(_)`, so requiring `(evidence) =>`
        // cannot be satisfied by the denied group.
        let arm = semantic_current
            .text()
            .split(&format!("UnsatCertificateKind::{kind}(evidence) => "))
            .nth(1)
            .unwrap_or_else(|| {
                panic!(
                    "exact theorem kind {kind} has no live authority arm in \
                     checked_exact_semantic_is_current — the common mint must not \
                     be able to accept a theorem the invariant does not authenticate"
                )
            });
        assert!(
            arm.trim_start()
                .trim_start_matches('{')
                .trim_start()
                .starts_with("evidence.is_current(executor)"),
            "exact theorem kind {kind} must be authenticated by its own sealed evidence"
        );
    }
    assert_eq!(
        unsat.count("self.last_unsat_certificate = Some(UnsatCertificate("),
        0,
        "exact theorem wrappers must not construct capabilities directly"
    );
    let semantic = unsat.region(
        "fn emit_checked_exact_unsat(",
        "pub(in crate::executor) fn emit_checked_exact_exists_unsat(",
    );
    let semantic_capability = semantic.offset_of(
        "let certificate = UnsatCertificate(kind);",
        "common semantic mint must construct the private capability",
    );
    let semantic_scope = semantic.offset_of(
        "certificate.checked_exact_semantic_is_current(self)",
        "common semantic mint must authenticate the exact theorem scope",
    );
    let presentation = semantic.offset_of(
        "self.strict_unsat_presentation_required()",
        "common semantic mint must preserve explicit proof authority",
    );
    let semantic_publish = semantic.offset_of(
        "self.last_unsat_certificate = Some(certificate);",
        "common semantic mint must publish the checked capability",
    );
    assert!(
        semantic_capability < semantic_scope
            && semantic_scope < presentation
            && presentation < semantic_publish,
        "exact semantic scope and proof-presentation policy must be checked before publication"
    );
}

pub(super) fn assert_mint_authentication(unsat: &LogicalModule) {
    let mint = unsat.region(
        "fn mint_unsat_certificate(",
        "pub(crate) fn certify_unsat_for_publication(",
    );
    let authenticate = mint.offset_of(
        "self.authenticate_unsat_query_scope(assumptions, true)?",
        "mint must authenticate the exact query scope",
    );
    let proof = mint.offset_of(
        "self.check_strict_unsat_presentation()",
        "mint must invoke the strict proof presentation check",
    );
    let capability = mint.offset_of(
        "self.bind_unsat_certification_source(certification_source, authenticated_scope)",
        "mint must delegate capability construction to the common binder",
    );
    assert!(
        authenticate < proof && proof < capability,
        "the exact query scope and the strict proof must be checked before minting"
    );
    assert!(
        !mint.contains("UnsatCertificate("),
        "the mint must not construct a capability itself — it delegates to the binder"
    );
    // Bounded to the presentation check's own item rather than "everything
    // after it to the end of the file": the strict datatype-aware checker must
    // be invoked BY this function, not merely somewhere below it.
    let presentation = unsat.region_to_item_end("fn check_strict_unsat_presentation(");
    assert!(
        presentation.contains("self.check_proof_strict_with_datatypes(proof)"),
        "the presentation check must invoke the strict datatype-aware proof checker"
    );
    let scope = unsat.region(
        "fn authenticate_unsat_query_scope(",
        "fn mint_competition_raw_certificate(",
    );
    let bound = scope.offset_of(
        "if bound != assumptions",
        "query-scope authentication must bind exact assumptions",
    );
    let provenance = scope.offset_of(
        "provenance.original_problem_assertions != epoch.assertions",
        "query-scope authentication must bind exact authored assertions",
    );
    assert!(
        bound < provenance,
        "exact assumptions must be bound before exact authored assertions"
    );
}

pub(super) fn assert_certificate_consumption(unsat: &LogicalModule) {
    // `7d448bb9c3` moved the one-shot consumer into
    // `unsat_cert/query_epoch_access.rs`. Bounding it by its own item end is
    // TIGHTER than the previous "anchor to end of file", which ran through the
    // whole `#[cfg(test)] mod tests` and could have been satisfied by a test.
    let consume = unsat.region_to_item_end("pub(crate) fn take_unsat_certificate(");
    assert!(
        consume.contains("scope.is_current(self)")
            && consume.contains("checked.is_current_for(")
            && consume.contains("evidence.is_current(self)"),
        "consumption must revalidate every sealed class against its exact current scope"
    );
    let checked = unsat.region(
        "UnsatCertificateKind::CheckedSatRefutation { checked, scope } =>",
        "UnsatCertificateKind::CheckedBoolBv(checked) =>",
    );
    assert!(
        checked.contains("scope.is_current(self)")
            && checked.contains("epoch.is_current(self)")
            && checked.contains("epoch.declared_extension.is_empty()")
            && checked.contains("epoch.declared_extension_entries.is_empty()")
            && checked.contains("epoch.declared_extension_objectives.is_none()")
            && checked.contains("epoch.declared_extension_objective_entries.is_none()")
            && checked.contains("provenance.original_problem_assertions == epoch.assertions")
            && checked.contains("&epoch.authority_epoch,")
            && checked.contains("&epoch.source_context_stamp,")
            && checked.contains("&epoch.assertions,")
            && checked.contains("bound_assumptions,"),
        "checked SAT-refutation consumption must reject stale authority/source state, any query extension, mismatched proof roots, and a sidecar from another exact scope"
    );
    // THE ASSUMPTION-MATCH SHAPES, PINNED ONE BY ONE.
    //
    // This used to be a single `bound_assumptions.is_empty() &&
    // self.last_assumptions.is_none()` conjunct. `ad5acf0993 feat(cert):
    // letleak wall 3` REPLACED that with a wider third shape — the "folded
    // named-assumption rescue", where the redirect solved `roots = base ++ A`
    // with an empty assumption vector while the outer `check-sat-assuming A`
    // left `last_assumptions = A`. That widening landed while this guard was
    // already RED for the unrelated module-split drift, so nothing reviewed it
    // here.
    //
    // It is pinned SHAPE BY SHAPE rather than by the old literal, because the
    // rescue is sound only through conditions that a coarser check would not
    // see: the tail must be NON-EMPTY and must be a POSITIONAL SUFFIX of the
    // epoch's authored roots (`ends_with`), and `checked.is_current_for` above
    // authenticates that full root vector — so the sidecar's theorem is exactly
    // `base ∧ A ⊢ ⊥`, the claim the outer command publishes. Drop either
    // condition and the rescue would admit a sidecar proved about a different
    // assumption set.
    assert!(
        checked.contains("self.last_assumptions.as_deref()")
            && checked.contains("== Some(bound_assumptions)"),
        "shape 1: the solver's assumption vector must match the bound one exactly"
    );
    assert!(
        checked.contains("bound_assumptions.is_empty()") && checked.contains("None => true,"),
        "shape 2: no assumptions anywhere must remain an admissible shape"
    );
    assert!(
        checked.contains("Some(last) => !last.is_empty() && epoch.assertions.ends_with(last),"),
        "shape 3 (the folded named-assumption rescue) must stay bounded by a NON-EMPTY, \
         POSITIONALLY EXACT suffix of the epoch's authored roots — a permuted, widened or \
         truncated tail must not match"
    );
}

pub(super) fn assert_publication_stop_dominance(unsat: &LogicalModule) {
    // Bounded by the end of the funnel's own `impl` block. It used to be
    // bounded by `take_unsat_certificate`, which `7d448bb9c3` moved into a
    // submodule; the item bound covers the funnel, `certify_unsat_presentation`
    // and `publish_competition_raw_unsat` — a strict SUBSET of what the old
    // bound covered, which also swept up two unrelated epoch accessors.
    let funnel = unsat.region_to_item_end("pub(crate) fn certify_unsat_for_publication(");
    assert!(
        funnel.count("self.stop_declines_unsat_publication()") >= 3,
        "UNSAT publication must check external stops before certification, before prechecked acceptance, and after fresh minting"
    );
    let mint_call = funnel.offset_of(
        "let minted = self.mint_unsat_certificate(assumptions);",
        "the funnel must mint into a local capability",
    );
    let postflight = funnel.text()[mint_call..]
        .find("self.stop_declines_unsat_publication()")
        .map(|offset| mint_call + offset)
        .expect("fresh certificate minting must have an external-stop postflight");
    let retain = funnel.text()[mint_call..]
        .find("self.last_unsat_certificate = Some(certificate);")
        .map(|offset| mint_call + offset)
        .expect("the funnel must retain a checked certificate");
    assert!(
        mint_call < postflight && postflight < retain,
        "late external stops must be checked before a freshly minted UNSAT token is retained"
    );
    let retentions = funnel
        .text()
        .match_indices("self.last_unsat_certificate = Some(certificate);")
        .map(|(offset, _)| offset)
        .collect::<Vec<_>>();
    assert!(
        retentions.len() >= 2,
        "the funnel must retain through both the ordinary mint and the raw competition branch: {retentions:?}"
    );
    for (index, &retain_at) in retentions.iter().enumerate() {
        let stop_at = funnel.text()[..retain_at]
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

pub(super) fn assert_proof_api_reconfirmation(proof_api: &LogicalModule) {
    let helper = proof_api.region(
        "fn executor_reports_plain_strict_unsat(",
        "pub(crate) fn discharge_trust_clause(",
    );
    assert!(
        helper.contains("exec.begin_public_solve(false);")
            && helper.contains("exec.bind_unsat_query_assumptions(&[]);")
            && helper.contains("exec.check_proof_strict_with_datatypes(proof).is_ok()"),
        "a repeated raw solver verdict must not certify a deferred trust step"
    );
    let discharge = proof_api.region_to_item_end("pub(crate) fn discharge_trust_clause(");
    assert!(
        discharge.count("executor_reports_plain_strict_unsat(&mut exec)") >= 2,
        "both contextual and standalone generic trust probes must require strict proof evidence"
    );
}

pub(super) fn assert_whole_problem_reconfirmation(unsat: &LogicalModule) {
    let reconfirm = unsat.region(
        "fn reconfirms_unsat_within(",
        "fn redecides_definitive_sat_within(",
    );
    let tighter = unsat.region("fn tighter_optional_limit(", "/// True while");
    assert!(
        tighter.contains("(Some(left), Some(right)) => Some(left.min(right))")
            && tighter.contains("(Some(limit), None) | (None, Some(limit)) => Some(limit)")
            && tighter.contains("(None, None) => None"),
        "optional deterministic limits must compose by minimum without inventing a finite limit"
    );
    assert!(
        reconfirm.contains("exec.begin_public_solve(false);")
            && reconfirm.contains("exec.bind_unsat_query_assumptions(&[]);")
            && reconfirm.contains(
                "tighter_optional_limit(self.resource_limit(), Some(limits.max_conflicts))"
            )
            && reconfirm.contains(
                "tighter_optional_limit(self.decision_limit(), Some(limits.max_decisions))"
            )
            && reconfirm.contains("if conflict_limit == Some(0) || decision_limit == Some(0)")
            && reconfirm.contains("exec.set_resource_limit(conflict_limit);")
            && reconfirm.contains("exec.set_decision_limit(decision_limit);")
            && reconfirm
                .contains("exec.set_quantifier_deadline_policy(QuantifierDeadlinePolicy::Exact);")
            && reconfirm.contains("exec.set_memory_limit(self.memory_limit());")
            && reconfirm.contains(
                "exec.set_solve_controls(self.solve_interrupt.clone(), self.solve_deadline.get());"
            )
            && reconfirm.contains("exec.check_proof_strict_with_datatypes(proof)"),
        "whole-problem trust fallback must compose its deterministic caps with tighter caller limits and inherit outer solve controls"
    );
    // THE STRUCTURAL SCREEN, PINNED BY ITS FAMILY RATHER THAN BY A NAME.
    //
    // This used to demand the literal `Err(error) =>
    // Self::is_trust_kind_rejection(error)`. `2dedaab8a5 fix(cert): route a
    // metered ResourceLimit into the deferred-trust discharge lane` replaced
    // that with the WIDER `is_deferred_discharge_rejection`, and this guard has
    // been RED on that conjunct ever since — so it never reviewed the widening,
    // it only failed next to it.
    //
    // Pinned here as the family itself, which is strictly more than the old
    // identifier check could say:
    //   * the accepting arm delegates to the single-sourced family predicate,
    //     so the gate that ROUTES a proof into deferred discharge and the
    //     screen that ACCEPTS its result cannot drift apart again;
    //   * the family is exactly the trust kinds plus `ResourceLimit` — a
    //     calibration verdict, not a structural defect;
    //   * `Cancelled` is NOT a member, so a caller stop still fails closed;
    //   * `is_trust_kind_rejection` keeps its narrow meaning, so nothing that
    //     reads "trust-kind" silently acquires the resource member.
    // Every structural rejection therefore still declines.
    assert!(
        reconfirm.contains("Err(error) => Self::is_deferred_discharge_rejection(error),"),
        "the re-solve proof screen must delegate to the single-sourced deferred-discharge family"
    );
    let family = unsat.region(
        "fn is_deferred_discharge_rejection(",
        "fn is_trust_kind_rejection(",
    );
    assert!(
        family.contains("Self::is_trust_kind_rejection(error)")
            && family.contains("matches!(error, ay_proof::ProofCheckError::ResourceLimit)")
            && !family.contains("ProofCheckError::Cancelled"),
        "the deferred-discharge family must be the trust kinds plus the metered ResourceLimit \
         calibration verdict and nothing else — a caller stop must keep failing closed"
    );
    let trust_family = unsat.region(
        "fn is_trust_kind_rejection(",
        "fn authored_corroboration_scope(",
    );
    assert!(
        !trust_family.contains("ResourceLimit") && !trust_family.contains("Cancelled"),
        "the trust family proper must not acquire the resource or stop members"
    );
    assert!(
        unsat
            .contains("fn deferred_discharge_family_admits_budget_refusal_but_not_a_caller_stop()")
            && unsat.contains("fn trust_kind_family_excludes_the_resource_member()"),
        "both rejection families must keep their focused behavioural regressions"
    );
    assert!(
        !reconfirm.contains("strict.is_ok()\n    }"),
        "the re-solve proof screen must not demand trust-freeness of the twin proof — that is this fallback's own entry condition and made it decline every time"
    );
    assert!(
        !reconfirm.contains("exec.set_deadline(") && !reconfirm.contains("Duration::from_millis"),
        "the accepting whole-problem trust fallback must not use a private wall-clock cutoff"
    );
}

pub(super) fn assert_forged_sat_guard(unsat: &LogicalModule) {
    let forged = unsat.region(
        "fn redecides_definitive_sat_within(",
        "fn discharge_trust_steps_for_certification(",
    );
    let compose_conflicts = forged.offset_of(
        "tighter_optional_limit(self.resource_limit(), local_conflict_limit)",
        "forged-SAT guard must compose the caller conflict limit",
    );
    let compose_decisions = forged.offset_of(
        "tighter_optional_limit(self.decision_limit(), local_decision_limit)",
        "forged-SAT guard must compose the caller decision limit",
    );
    let install_conflicts = forged.offset_of(
        "exec.set_resource_limit(conflict_limit);",
        "forged-SAT guard must install the composed conflict limit",
    );
    let install_decisions = forged.offset_of(
        "exec.set_decision_limit(decision_limit);",
        "forged-SAT guard must install the composed decision limit",
    );
    let disable_fresh_default = forged.offset_of(
        "exec.set_ground_budget_enabled(false);",
        "forged-SAT guard must disable the fresh executor default after composition",
    );
    assert!(
        forged.contains("effective_conflict_allowance(None, self.ground_budget_enabled())")
            && forged.contains("effective_decision_allowance(None, self.ground_budget_enabled())")
            && forged.contains("if conflict_limit == Some(0) || decision_limit == Some(0)")
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
