// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//
//! Conformance pins for sealed SAT emission (#sat-chokepoint).
//!
//! `sat_emit.rs` alone can construct `SatCertificate`. Ordinary proposed SAT
//! results route through `emit_sat_verdict`; the restricted quantified UFBV lane
//! routes through `emit_checked_projection_sat` and must consume sealed semantic,
//! declaration/source, and caller-authored-query evidence. These tests pin both
//! complete paths and the private certificate kinds.

use std::path::PathBuf;

#[path = "sat_chokepoint_conformance/post_rebase.rs"]
mod post_rebase;

fn read(rel: &str) -> String {
    let p = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join(rel);
    std::fs::read_to_string(&p).unwrap_or_else(|e| panic!("cannot read {}: {e}", p.display()))
}

fn normalize_whitespace(text: &str) -> String {
    text.split_whitespace().collect::<Vec<_>>().join(" ")
}

fn rust_sources_below(root: &std::path::Path, output: &mut Vec<PathBuf>) {
    for entry in std::fs::read_dir(root)
        .unwrap_or_else(|error| panic!("cannot enumerate {}: {error}", root.display()))
    {
        let entry = entry.expect("workspace source directory entry");
        let path = entry.path();
        if path.is_dir() {
            let name = path.file_name().and_then(|name| name.to_str());
            if !matches!(name, Some(".git" | "target" | "reference")) {
                rust_sources_below(&path, output);
            }
        } else if path.extension().and_then(|extension| extension.to_str()) == Some("rs") {
            output.push(path);
        }
    }
}

fn is_chokepoint_source_fixture(relative: &str) -> bool {
    matches!(
        relative,
        "crates/ay-dpll/tests/sat_chokepoint_conformance.rs"
            | "crates/ay-dpll/tests/unsat_chokepoint_conformance.rs"
            | "crates/ay-dpll/tests/sat_chokepoint_conformance/post_rebase.rs"
    )
}

/// (a) The funnel runs the exact strict -> quantified -> independent -> authoritative ->
/// formula-neutral output completion -> validation-postcondition sequence and
/// only then mints the witness token.
#[test]
fn emit_sat_verdict_has_strict_independent_authoritative_postcondition_sequence() {
    let src = read("src/executor/model/sat_emit.rs");
    let funnel_start = src
        .find("pub(in crate::executor) fn emit_sat_verdict(")
        .expect("sat_emit.rs must define the single funnel `emit_sat_verdict`");
    let funnel_end = src[funnel_start..]
        .find("fn apply_sat_validation_postcondition(")
        .map(|offset| funnel_start + offset)
        .expect("sat_emit.rs must define the release-mode SAT postcondition");
    let funnel = &src[funnel_start..funnel_end];

    // The STRICT gate (full validation when unvalidated, else the strict gate).
    let strict = funnel
        .find("finalize_sat_model_validation()")
        .expect("emit_sat_verdict must run the strict gate (finalize_sat_model_validation)");
    let strict_alt = funnel
        .find("apply_strict_model_gate(")
        .expect("emit_sat_verdict must run apply_strict_model_gate for already-validated models");
    let quantified = funnel
        .find("apply_quantified_model_failclosed_gate(")
        .expect("emit_sat_verdict must run the quantified-model certificate gate");
    let independent = funnel
        .find("apply_independent_model_gate(")
        .expect("emit_sat_verdict must run the INDEPENDENT model-check gate");
    let authoritative = funnel
        .find("apply_authoritative_failclosed_gate(")
        .expect("emit_sat_verdict must run the AUTHORITATIVE-failclosed gate");
    let output_completion = funnel
        .rfind("complete_unconstrained_functions_for_output(")
        .expect("emit_sat_verdict must finalize formula-neutral function output");
    let postcondition = funnel
        .find("apply_sat_validation_postcondition(")
        .expect("emit_sat_verdict must enforce the SAT validation-evidence postcondition");
    let nontrivial_mint = funnel
        .rfind("SatCertificate(SatCertificateKind::ValidatedModel)")
        .expect("emit_sat_verdict must mint the non-trivial witness token");

    // Ordering: strict (both forms) precede the quantified certificate, which
    // precedes the compositional independent evaluator and its defenses.
    assert!(
        strict < quantified && strict_alt < quantified,
        "the strict gate must run BEFORE the quantified certificate in emit_sat_verdict"
    );
    assert!(
        quantified < independent,
        "the quantified certificate must run BEFORE the independent evaluator so only certified quantified leaves can be composed out"
    );
    assert!(
        independent < authoritative,
        "the independent gate must run BEFORE the authoritative-failclosed gate in \
         emit_sat_verdict (the latter is retained as defense in depth)"
    );
    assert!(
        authoritative < output_completion && output_completion < postcondition,
        "formula-neutral output completion must run after every model gate and before the postcondition"
    );
    assert!(
        postcondition < nontrivial_mint,
        "a non-trivial SatCertificate must be minted only after the validation postcondition"
    );

    // The unforgeable witness token is minted only here.
    assert!(
        funnel.contains("SatCertificate(SatCertificateKind::ValidatedModel)"),
        "emit_sat_verdict must mint the SatCertificate witness token"
    );
}

/// (a1) The constructive quantified lane consumes combined evidence, installs
/// only its checked total model, rechecks after output completion, and mints a
/// distinct private certificate kind last.
#[test]
fn checked_projection_lane_rechecks_evidence_and_model_before_mint() {
    let sat_emit = read("src/executor/model/sat_emit.rs");
    let start = sat_emit
        .find("pub(in crate::executor) fn emit_checked_projection_sat(")
        .expect("sat_emit must define the constructive quantified chokepoint");
    let end = sat_emit[start..]
        .find("fn reject_checked_projection_sat(")
        .map(|offset| start + offset)
        .expect("constructive emission must have one fail-closed cleanup");
    let lane = &sat_emit[start..end];

    let revoke = lane
        .find("self.last_sat_certificate = None;")
        .expect("constructive emission must revoke the predecessor token first");
    let first_current = lane
        .find("if !evidence.is_current(self)")
        .expect("constructive evidence must be current at entry");
    let install = lane
        .find("self.install_authorized_projection_model(&evidence)")
        .expect("constructive emission must use the authorized installer");
    let completion = lane
        .find("complete_checked_projection_model_for_output(")
        .expect("constructive models must use the bounded proof-specific completion pass");
    assert!(
        !lane.contains("complete_unconstrained_constants_for_output(")
            && !lane.contains("complete_unconstrained_functions_for_output("),
        "ordinary repair/completion is outside the constructive projection proof"
    );
    let installed_match = lane
        .find("model.projection_ufs.matches_checked(evidence.semantics())")
        .expect("the final symbolic model must match the sealed semantics");
    let final_current = lane
        .rfind("if !evidence.is_current(self)")
        .expect("query/source evidence must be current after completion");
    let validated = lane
        .find("self.last_model_validated = true;")
        .expect("constructive evidence must mark the final witness validated");
    assert_eq!(
        lane.matches("self.last_result = Some(SolveResult::Sat);")
            .count(),
        1,
        "constructive completion must not expose a provisional cached SAT result"
    );
    let publish_sat = lane
        .find("self.last_result = Some(SolveResult::Sat);")
        .expect("constructive emission must publish its cached SAT result exactly once");
    let mint = lane
        .find("SatCertificate(SatCertificateKind::CheckedProjection)")
        .expect("constructive emission must mint its private certificate kind");
    assert!(
        revoke < first_current
            && first_current < install
            && install < completion
            && completion < installed_match
            && installed_match < final_current
            && final_current < validated
            && validated < publish_sat
            && publish_sat < mint,
        "constructive SAT order must be revoke -> check -> install -> complete -> recheck -> mint"
    );
    assert_eq!(
        lane.matches("return Ok(self.stop_checked_projection_sat());")
            .count(),
        3,
        "every pre-install, mid-completion, and post-completion external stop must retire provisional SAT state"
    );
    let stop_cleanup = lane
        .split("fn stop_checked_projection_sat(")
        .nth(1)
        .expect("constructive emission must define external-stop cleanup");
    assert!(
        stop_cleanup.contains("self.last_result = Some(SolveResult::Unknown);")
            && stop_cleanup.contains("self.last_model = None;")
            && stop_cleanup.contains("self.last_sat_certificate = None;"),
        "external-stop cleanup must keep the cached result, model, and certificate aligned"
    );

    let dispatch = read("src/executor/check_sat.rs");
    let authority_branch = dispatch
        .find("if let Some(permit) = projection_authority")
        .expect("constructive dispatch must consume optional query authority");
    let dispatch_tail = &dispatch[authority_branch..];
    let reset = dispatch_tail
        .find("self.prepare_check_sat_internal_state()")
        .expect("constructive dispatch must clear every per-solve internal state");
    let authorize = dispatch_tail
        .find("match self.try_authorize_projection_sat(permit)")
        .expect("constructive dispatch must independently authorize the candidate");
    let emit = dispatch_tail
        .find("self.emit_checked_projection_sat(*evidence)")
        .expect("constructive dispatch must use the sealed emission lane");
    assert!(
        reset < authorize && authorize < emit,
        "constructive dispatch must reset -> authorize -> emit under one consumed permit"
    );
}

/// The text/CLI boundary cannot bypass the typed native result wrapper by
/// formatting a bare internal `SolveResult::Sat`.
#[test]
fn text_command_publication_consumes_private_sat_authority() {
    let executor = read("src/executor.rs");
    let executor_normalized = normalize_whitespace(&executor);
    post_rebase::assert_command_boundary(&executor_normalized);

    let sat_emit = read("src/executor/model/sat_emit.rs");
    let start = sat_emit
        .find("pub(in crate::executor) fn admit_command_solve_result(")
        .expect("sat emission module must define command-result admission");
    let end = sat_emit[start..]
        .find("pub(in crate::executor) fn emit_checked_projection_sat(")
        .map(|offset| start + offset)
        .expect("command admission must precede the constructive minting lane");
    let admission = &sat_emit[start..end];
    post_rebase::assert_command_admission_order(admission);

    // `2014dd6f5 refactor: modularize solver internals` moved the plain
    // accessors, including this one-shot consumer, out of `executor.rs` into
    // `executor/accessors.rs`. The pinned body is unchanged.
    let accessors = read("src/executor/accessors.rs");
    let sat_consumer_start = accessors
        .find("pub(crate) fn take_sat_certificate(&mut self) -> Option<SatCertificate> {")
        .expect("Executor must define the one-shot SAT authority consumer");
    let sat_consumer_end = accessors[sat_consumer_start..]
        .find("pub(crate) fn last_maxsmt_outcome(")
        .map(|offset| sat_consumer_start + offset)
        .expect("SAT authority consumer must have a bounded source region");
    let sat_consumer = &accessors[sat_consumer_start..sat_consumer_end];
    assert!(
        sat_consumer.contains("self.last_sat_certificate.take()?")
            && sat_consumer.contains("certificate.is_current_for(self).then_some(certificate)"),
        "the SAT helper used by text admission must consume and epoch-check its private token"
    );

    let unsat_cert = read("src/executor/unsat_cert.rs");
    let unsat_consumer_start = unsat_cert
        .find("pub(crate) fn take_unsat_certificate(&mut self) -> Option<UnsatCertificate> {")
        .expect("Executor must define the one-shot UNSAT authority consumer");
    let unsat_consumer = &unsat_cert[unsat_consumer_start..];
    assert!(
        unsat_consumer.contains("self.last_unsat_certificate.take()?")
            && unsat_consumer.contains("let epoch = self.unsat_query_epoch.as_ref()?")
            && unsat_consumer.contains("current.then_some(certificate)"),
        "the UNSAT helper used by text admission must consume and epoch-check its private token"
    );
    assert!(
        admission.contains("SolveResult::Unknown"),
        "a missing command token must fail closed"
    );
    assert!(
        admission.contains("self.reject_unadmitted_sat_publication("),
        "text admission failure must use the canonical public Unknown transition"
    );

    let shared_start = sat_emit
        .find("pub(crate) fn reject_unadmitted_sat_publication(")
        .expect("sat emission must define one shared publication rejection");
    let shared_end = sat_emit[shared_start..]
        .find("pub(in crate::executor) fn admit_command_solve_result(")
        .map(|offset| shared_start + offset)
        .expect("shared rejection must precede text admission");
    let shared = &sat_emit[shared_start..shared_end];
    assert!(
        shared.contains("replace_last_result_with_unknown(UnknownReason::InternalError)")
            && shared.contains("\"unknown.phase\", \"sat-publication-admission\""),
        "shared rejection must revoke state and record one consistent diagnostic"
    );

    let lifecycle = read("src/executor/lifecycle.rs");
    let publish_start = lifecycle
        .find("pub(crate) fn publish_unknown_from_origin(")
        .expect("lifecycle must define canonical typed Unknown publication");
    let publish_end = lifecycle[publish_start..]
        .find("pub fn replace_last_result_with_unknown(")
        .map(|offset| publish_start + offset)
        .expect("typed Unknown publication must precede its compatibility wrapper");
    let publish = &lifecycle[publish_start..publish_end];
    assert!(
        publish.contains("self.detach_persistent_decision_trace_writers();")
            && publish.contains("self.invalidate_last_check_result();")
            && publish.contains("self.last_result = Some(SolveResult::Unknown);"),
        "canonical publication rejection must detach incompatible traces and clear every stale artefact"
    );
    let replace_start = publish_end;
    let replace_end = lifecycle[replace_start..]
        .find("pub fn reject_last_unsat_as_unknown(")
        .map(|offset| replace_start + offset)
        .expect("Unknown replacement must precede UNSAT rejection");
    let replace = &lifecycle[replace_start..replace_end];
    assert!(
        replace.contains("self.publish_unknown_from_origin(reason.origin());"),
        "the compatibility wrapper must delegate to the typed canonical publication transition"
    );
}

/// Native optimization reuses command routing without publishing command text.
/// Its SAT certificate must cross exactly one boundary: executor -> native
/// `VerifiedSolveResult`. A missing token must also canonicalize executor state
/// so model/objective consumers cannot disagree with the returned verdict.
#[test]
fn native_optimization_transfers_sat_authority_once() {
    let executor = read("src/executor.rs");
    let command_boundary = read("src/executor/command_boundary.rs");
    let native_start = command_boundary
        .find("pub(crate) fn execute_native_optimization_check_sat(")
        .expect("executor must expose one narrow unpublished optimization route");
    let native_end = command_boundary[native_start..]
        .find("/// Continue an already-started native MaxSMT query")
        .map(|offset| native_start + offset)
        .expect("native optimization route must precede the MaxSMT continuation");
    let native = &command_boundary[native_start..native_end];
    assert!(
        native.contains("CommandExecutionBoundary::NativeOptimization")
            && !native.contains("CommandExecutionBoundary::AuthoredText"),
        "native optimization must preserve the certificate without minting authored-query authority"
    );

    assert!(
        command_boundary.contains("enum CommandExecutionBoundary {")
            && !command_boundary.contains("enum CommandAuthorityOrigin")
            && !command_boundary.contains("enum CommandResultSurface"),
        "origin and publication must be one closed type so authored-native execution is unrepresentable"
    );
    assert_eq!(
        executor
            .matches("CommandExecutionBoundary::NativeOptimization")
            .count()
            + command_boundary
                .matches("CommandExecutionBoundary::NativeOptimization")
                .count(),
        5,
        "the native selector, neutral query continuation, early command guard, and two exhaustive admissions are an audited closed allowlist"
    );

    let workspace = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(std::path::Path::parent)
        .expect("ay-dpll lives below the workspace root")
        .to_path_buf();
    let mut sources = Vec::new();
    rust_sources_below(&workspace.join("crates"), &mut sources);
    let allowed = [
        "crates/ay-dpll/src/api/solving/optimize.rs",
        "crates/ay-dpll/src/executor.rs",
        "crates/ay-dpll/src/executor/command_boundary.rs",
    ];
    for source in sources {
        let relative = source
            .strip_prefix(&workspace)
            .expect("enumerated source is below workspace")
            .to_string_lossy();
        if is_chokepoint_source_fixture(relative.as_ref()) {
            // Chokepoint audits necessarily name guarded entrypoints. Their
            // source-search strings are not executable callsites and must not
            // teach either fixture's allowlist to accept itself.
            continue;
        }
        let text = std::fs::read_to_string(&source)
            .unwrap_or_else(|error| panic!("cannot read {}: {error}", source.display()));
        if !text.contains("execute_native_optimization_check_sat") {
            continue;
        }
        assert!(
            allowed.contains(&relative.as_ref()),
            "new raw native-optimization caller requires an explicit admission-boundary audit: {relative}"
        );
    }

    let optimize = read("src/api/solving/optimize.rs");
    assert!(
        optimize.contains("self.executor.execute_native_optimization_check_sat()")
            && optimize.contains("self.finish_verified_result(result)")
            && !optimize.contains("self.executor.execute(&Command::CheckSat)"),
        "native optimize must use the unpublished route and one shared admission boundary"
    );
    let plan_controls = optimize
        .find("let controls = self.native_publication_controls();")
        .expect("native optimize must plan one immutable publication envelope");
    let preflight = optimize
        .find("self.preflight_check(controls)")
        .expect("native optimize must preflight the planned envelope");
    let install_controls = optimize
        .find("self.install_solve_controls(controls);")
        .expect("native optimize must install the planned envelope");
    let execute = optimize
        .find("self.executor.execute_native_optimization_check_sat()")
        .expect("native optimize must execute under the planned envelope");
    let finish = optimize
        .find("self.finish_verified_result(result)")
        .expect("native optimize must admit its result under live controls");
    let restore_controls = optimize
        .find("self.restore_solve_controls(controls);")
        .expect("native optimize must restore the enclosing control state");
    assert!(
        plan_controls < preflight
            && preflight < install_controls
            && install_controls < execute
            && execute < finish
            && finish < restore_controls,
        "native optimize must plan -> preflight -> install -> execute -> admit -> restore"
    );

    let check = read("src/api/solving/check.rs");
    let envelope_start = check
        .find("pub(super) struct NativePublicationControls {")
        .expect("native publication controls must be one explicit value");
    let envelope_end = check[envelope_start..]
        .find("}\n")
        .map(|offset| envelope_start + offset)
        .expect("native publication control declaration must be bounded");
    let envelope = &check[envelope_start..envelope_end];
    assert!(
        envelope.contains("deadline: Option<Instant>,")
            && envelope.contains("effective_memory_limit: Option<usize>,")
            && envelope.contains("previous_deadline: Option<Instant>,")
            && envelope.contains("previous_memory_limit: Option<usize>,"),
        "the immutable native envelope must carry effective controls and the exact enclosing state"
    );
    let admission_start = check
        .find("pub(super) fn finish_verified_result(")
        .expect("native result admission must be centralized");
    let admission_end = check[admission_start..]
        .find("fn reject_native_array_ext_witness_capture(")
        .map(|offset| admission_start + offset)
        .expect("native admission must have a bounded source region");
    let admission = &check[admission_start..admission_end];
    let term_memory = admission
        .find(".term_memory_limit")
        .expect("native admission must check its Solver-local term budget");
    let term_memory_unknown = admission
        .find(".publish_unknown_from_origin(crate::UnknownOrigin::MemoryBudget)")
        .expect("late term-memory exhaustion must publish typed MemoryBudget Unknown");
    let live_stop = admission
        .find(".decline_definite_publication_on_external_stop(result)")
        .expect("native admission must reject a live external stop");
    let sat_take = admission
        .find("let sat_certificate = self.executor.take_sat_certificate();")
        .expect("native admission must consume SAT authority");
    let unsat_take = admission
        .find("let unsat_certificate = self.executor.take_unsat_certificate();")
        .expect("native admission must consume UNSAT authority");
    assert!(
        term_memory < term_memory_unknown
            && term_memory_unknown < live_stop
            && live_stop < sat_take
            && live_stop < unsat_take,
        "native admission must inspect term memory and shared live controls before consuming either definite token"
    );
    assert!(
        admission.contains("let sat_certificate = self.executor.take_sat_certificate();")
            && admission
                .contains("let unsat_certificate = self.executor.take_unsat_certificate();")
            && admission.contains("reject_uncertified_verdict_for_publication(")
            && admission.contains("VerifiedSolveResult::certified_sat(certificate)")
            && admission.contains("VerifiedSolveResult::certified_unsat(proof, certificate)"),
        "native admission must consume exact SAT/UNSAT authority and fail closed when either is missing"
    );

    let controls_start = check
        .find("pub(super) fn install_solve_controls(")
        .expect("native control installation must be centralized");
    let controls_end = check[controls_start..]
        .find("pub(super) fn classify_unknown_reason(")
        .map(|offset| controls_start + offset)
        .expect("native control installation must have a bounded source region");
    let controls = &check[controls_start..controls_end];
    let install_memory = controls
        .find("set_memory_limit(controls.effective_memory_limit);")
        .expect("native controls must install the effective RSS ceiling");
    let install_deadline = controls
        .find("set_solve_controls(Some(self.interrupt.clone()), controls.deadline);")
        .expect("native controls must install the absolute deadline");
    let restore_deadline = controls
        .find("set_solve_controls(None, controls.previous_deadline);")
        .expect("native controls must restore the enclosing deadline");
    let restore_memory = controls
        .find("set_memory_limit(controls.previous_memory_limit);")
        .expect("native controls must restore the enclosing RSS ceiling");
    assert!(
        install_memory < install_deadline
            && install_deadline < restore_deadline
            && restore_deadline < restore_memory,
        "native controls must install the effective RSS/deadline envelope and restore the enclosing executor state"
    );
}

/// (a1.1) The linear permit and combined evidence are structurally sealed, and
/// the authored entrypoints stay on an explicit source allowlist. This is a
/// live-code conformance pin, not a formal refinement proof.
#[test]
fn checked_projection_authority_is_linear_and_origin_allowlisted() {
    let query = read("src/executor/query_authority.rs");
    assert!(
        query.contains(
            "#[derive(Debug)]\npub(in crate::executor) struct AuthoredPlainHardQueryPermit",
        ) && !query.contains(
            "#[derive(Clone, Debug)]\npub(in crate::executor) struct AuthoredPlainHardQueryPermit"
        ),
        "the exact authored-query permit must remain opaque and non-Clone"
    );
    let combined = read("src/executor/quantified_sat.rs");
    assert!(
        combined.contains(
            "#[derive(Debug)]\npub(in crate::executor) struct CheckedProjectionSatEvidence"
        ) && !combined.contains(
            "#[derive(Clone, Debug)]\npub(in crate::executor) struct CheckedProjectionSatEvidence"
        ) && combined.contains("authored_query: AuthoredPlainHardQueryPermit,")
            && combined.contains("checked_source: CheckedProjectionSourceEvidence,"),
        "combined SAT authority must own both opaque evidence layers and remain non-Clone"
    );

    post_rebase::assert_authored_entrypoint_allowlist();

    assert!(
        query.contains("struct AuthoredPlainHardQuery<'a>")
            && query.contains("executor: &'a mut Executor,")
            && query.contains("fn begin_authored_plain_hard_query(")
            && query.contains("pub(crate) fn solve_authored_plain_hard_query(")
            && !query.contains("pub(crate) fn try_mint_authored_plain_hard_query("),
        "authored authority must be captured and consumed under one exclusive executor borrow"
    );

    let cross_check = read("src/api/solving/cross_check.rs");
    let cross_check_start = cross_check
        .find("fn run_cross_check(")
        .expect("cross-check must define one replay boundary");
    let cross_check_end = cross_check[cross_check_start..]
        .find("fn build_verification_summary(")
        .map(|offset| cross_check_start + offset)
        .expect("cross-check replay must precede result summarization");
    let cross_check_run = &cross_check[cross_check_start..cross_check_end];
    let setup = cross_check_run
        .find("executor.execute(&command)")
        .expect("cross-check setup commands must remain internal");
    let authored_solve = cross_check_run
        .find(".execute_authored(&solve_command)")
        .expect("cross-check decision must enter the authored boundary");
    let observe_result = cross_check_run
        .find(".last_result()")
        .expect("cross-check must observe only the admitted command result");
    assert!(
        setup < authored_solve && authored_solve < observe_result,
        "cross-check must elaborate setup internally, solve through authored authority, then observe the admitted verdict"
    );

    let native_check = read("src/api/solving/check.rs");
    assert!(
        native_check.contains("fn check_sat_interruptible_with_authority_origin<F>(")
            && native_check.contains("NativeCheckAuthorityOrigin::AuthoredPlain,")
            && native_check.contains("NativeCheckAuthorityOrigin::Internal,")
            && native_check.contains(".with_interruptible_publication_controls(")
            && native_check.contains("executor.solve_authored_plain_hard_query(&native_softs)")
            && native_check.contains("executor.check_sat()"),
        "interruptible authored and internal queries must select authority through an explicit origin while retaining callback controls through publication"
    );
}

/// (a2) Empty-formula SAT carries explicit vacuous evidence only after its
/// final output-visible unconstrained model has been constructed and completed.
#[test]
fn empty_sat_completes_final_model_before_vacuous_evidence_and_mint() {
    let src = read("src/executor/model/sat_emit.rs");
    let start = src
        .find("if self.ctx.assertions.is_empty() && roots.is_empty()")
        .expect("SAT funnel must define its vacuous empty-formula branch");
    let tail = &src[start..];
    let create = tail
        .find("self.last_model = Some(super::Model::empty());")
        .expect("empty SAT must construct a model before consumer publication");
    let constants = tail
        .find("self.complete_unconstrained_constants_for_output(roots);")
        .expect("empty SAT must complete unconstrained constants");
    let functions = tail
        .find("self.complete_unconstrained_functions_for_output(roots)")
        .expect("empty SAT must complete unconstrained functions");
    let evidence = tail
        .find("self.last_model_validated = true;")
        .expect("empty SAT must record explicit vacuous evidence");
    let mint = tail
        .find("Some(SatCertificate(SatCertificateKind::ValidatedModel));")
        .expect("empty SAT must mint its private capability");
    assert!(
        create < constants && constants < functions && functions < evidence && evidence < mint,
        "empty SAT order must be create -> complete constants/functions -> vacuous evidence -> mint"
    );
}

/// (b) Assumptions are installed as real assertions for the entire model-
/// mutation/validation/mint scope, and the persistent assertion stack is
/// restored only after that scope returns. No assumption validator or output
/// completion may mutate the model after emission.
#[test]
fn assumptions_share_one_restored_pre_mint_validation_scope() {
    let sat_emit = read("src/executor/model/sat_emit.rs");
    let funnel_start = sat_emit
        .find("pub(in crate::executor) fn emit_sat_verdict(")
        .expect("sat_emit must define emit_sat_verdict");
    let funnel_end = sat_emit[funnel_start..]
        .find("fn apply_sat_validation_postcondition(")
        .map(|offset| funnel_start + offset)
        .expect("sat_emit must define its validation postcondition");
    let funnel = &sat_emit[funnel_start..funnel_end];

    let combine = funnel
        .find("combined.extend_from_slice(roots);")
        .expect("assumption roots must be installed as validation assertions");
    let completion = funnel
        .find("complete_unconstrained_constants_for_output(roots)")
        .expect("combined-scope output completion must run");
    let strict = funnel
        .find("finalize_sat_model_validation()")
        .expect("combined-scope canonical validation must run when evidence is stale");
    let mint = funnel
        .rfind("SatCertificate(SatCertificateKind::ValidatedModel)")
        .expect("combined scope must mint its certificate");
    let restore = funnel
        .rfind("self.ctx.assertions = assertions;")
        .expect("combined validation scope must restore the persistent assertion stack");
    assert!(
        combine < completion && completion < strict && strict < mint && mint < restore,
        "assertions + assumptions must remain active through completion, validation, and mint, then restore"
    );

    let assuming = read("src/executor/check_sat_assuming.rs");
    assert!(
        !assuming.contains("let validated = self.emit_sat_verdict"),
        "check-sat-assuming must not run a model-mutating validator after a provisional certificate"
    );
    assert!(
        !assuming.contains("complete_unconstrained_functions_for_output("),
        "check-sat-assuming must not mutate output models after certificate minting"
    );
    let plain = read("src/executor/check_sat.rs");
    assert!(
        !plain.contains("complete_unconstrained_functions_for_output("),
        "plain check-sat must not mutate output models after certificate minting"
    );
}

/// (c) A control flag that merely suppresses model evaluation is not validation
/// evidence. In particular, the public BV+LIA fallback routes may leave this
/// flag set after a failed model-validation attempt; the final funnel must
/// still fail closed in release builds.
#[test]
fn sat_postcondition_does_not_accept_skip_model_eval_as_evidence() {
    let src = read("src/executor/model/sat_emit.rs");
    let postcondition_start = src
        .find("fn apply_sat_validation_postcondition(")
        .expect("sat_emit.rs must define the release-mode SAT postcondition");
    let tests_start = src[postcondition_start..]
        .find("#[cfg(test)]")
        .map(|offset| postcondition_start + offset)
        .unwrap_or(src.len());
    let postcondition = &src[postcondition_start..tests_start];

    assert!(
        !postcondition.contains("|| self.skip_model_eval"),
        "skip_model_eval suppresses work but is not validation evidence; accepting it can make
         public BV+LIA model-validation failures escape as Sat"
    );
}

/// (d) A strict repair of an already-validated array model invalidates the old
/// evidence. A silent re-verdict must flow into full validation; a rejecting
/// re-verdict must replace the stale original violation.
#[test]
fn post_validation_array_retry_propagates_both_outcomes_and_revalidates() {
    let pipeline = read("src/executor/model/validation/pipeline.rs");
    let repair_start = pipeline
        .find("fn repair_asserted_array_read_pins(&mut self)")
        .expect("pipeline must define the shared array-repair primitive");
    let repair_end = pipeline[repair_start..]
        .find("fn unit_clause_contradiction(")
        .map(|offset| repair_start + offset)
        .expect("array repair must precede the unit-clause helper");
    let repair = &pipeline[repair_start..repair_end];
    let semantic_repair = repair
        .find("if total_applied > 0 || total_shifted > 0 || resynced > 0 {")
        .expect("array repair must distinguish semantic mutation from marker bookkeeping");
    let evidence_invalidation = repair[semantic_repair..]
        .find("self.last_model_validated = false;")
        .map(|offset| semantic_repair + offset)
        .expect("every actual array repair must invalidate prior validation evidence");
    let dependent_authority_revocation = repair[semantic_repair..]
        .find("self.revoke_cegqi_uf_recompletion_authority();")
        .map(|offset| semantic_repair + offset)
        .expect("array repair must revoke dependent recompletion authority");
    assert!(
        semantic_repair < evidence_invalidation
            && evidence_invalidation < dependent_authority_revocation,
        "every semantic array repair must invalidate validation evidence and dependent authority before returning"
    );

    let completion = read("src/executor/model/completion.rs");
    let validation_completion_start = completion
        .find("fn complete_model_for_validation(")
        .expect("completion must define complete_model_for_validation");
    let validation_completion_end = completion[validation_completion_start..]
        .find("fn complete_uninterpreted_sort_model(")
        .map(|offset| validation_completion_start + offset)
        .expect("model completion must precede uninterpreted-sort completion");
    let validation_completion = &completion[validation_completion_start..validation_completion_end];
    let invalidate = validation_completion
        .find("self.last_model_validated = false;")
        .expect("general model completion must invalidate prior evidence");
    let take = validation_completion
        .find("self.last_model.take()")
        .expect("general model completion must take the selected model");
    assert!(
        invalidate < take,
        "general completion must invalidate evidence before taking or mutating the model"
    );

    let strict_start = pipeline
        .find("pub(in crate::executor) fn apply_strict_model_gate(")
        .expect("pipeline must define apply_strict_model_gate");
    let strict_end = pipeline[strict_start..]
        .find("fn find_unwitnessed_array_disequality(")
        .map(|offset| strict_start + offset)
        .expect("strict gate must precede the array-disequality helper");
    let strict_gate = &pipeline[strict_start..strict_end];

    let initial_verdict = strict_gate
        .find("let mut strict = match self.verify_model_strict()")
        .expect("strict gate must retain its initial current-model verdict");
    let retry = strict_gate
        .find("if !self.qfax_retry_done {")
        .expect("strict gate must bound array repair to one retry");
    let retry_tail = &strict_gate[retry..];
    let retry_invalidation = retry_tail
        .find("self.last_model_validated = false;")
        .map(|offset| retry + offset)
        .expect("array retry must invalidate the old model evidence");
    let retry_marker_mutation = retry_tail
        .find("euf.term_values.remove(&TermId(u32::MAX - 7));")
        .map(|offset| retry + offset)
        .expect("array retry must reopen the per-model repair marker");
    let retry_repair = retry_tail
        .find("self.repair_asserted_array_read_pins();")
        .map(|offset| retry + offset)
        .expect("array retry must rerun the repair primitive");
    let retry_verdict = retry_tail
        .find("strict = self.verify_model_strict();")
        .map(|offset| retry + offset)
        .expect("array retry must retain the current strict verdict");
    let retry_release = retry_tail
        .find("self.qfax_retry_done = false;")
        .map(|offset| retry + offset)
        .expect("array retry must release its recursion guard");
    let silent_retry = retry_tail
        .find("if strict.is_none()")
        .map(|offset| retry + offset)
        .expect("a silent retry must clear the stale rejection target");
    assert!(
        initial_verdict < retry
            && retry < retry_invalidation
            && retry_invalidation < retry_marker_mutation
            && retry_marker_mutation < retry_repair
            && retry_repair < retry_verdict
            && retry_verdict < retry_release
            && retry_release < silent_retry,
        "array retry must invalidate old evidence before mutation, then repair -> reverify -> release before using the current verdict"
    );
    assert!(
        strict_gate.contains("if strict.is_none()")
            && strict_gate.contains("if let Some((idx, oracle, assertion)) = strict"),
        "a silent retry must continue, while a changed rejecting retry must report the new verdict"
    );
    assert!(
        !strict_gate.contains("return SolveResult::Sat;"),
        "a silent strict retry must not escape before the final validation pipeline"
    );

    let sat_emit = read("src/executor/model/sat_emit.rs");
    let funnel_start = sat_emit
        .find("pub(in crate::executor) fn emit_sat_verdict(")
        .expect("sat_emit must define emit_sat_verdict");
    let funnel_end = sat_emit[funnel_start..]
        .find("fn apply_sat_validation_postcondition(")
        .map(|offset| funnel_start + offset)
        .expect("sat_emit must define its validation postcondition");
    let funnel = &sat_emit[funnel_start..funnel_end];
    let strict_call = funnel
        .find("let strict = self.apply_strict_model_gate(SolveResult::Sat);")
        .expect("already-validated witnesses must still run the strict gate");
    let post_repair = &funnel[strict_call..];
    assert!(
        post_repair.contains("strict == SolveResult::Sat && !self.last_model_validated")
            && post_repair.contains("self.finalize_sat_model_validation()?"),
        "a successful repair must rerun full validation before SAT certification"
    );
}

/// (e) The two historically-ungated verdict paths emit `Sat` ONLY via
/// `emit_sat_verdict` — no bare `Ok(SolveResult::Sat)` escape remains.
#[test]
fn assuming_and_optimize_emit_sat_only_through_the_funnel() {
    post_rebase::assert_funnelled_sat_sources();

    let optimization = read("src/executor/optimization.rs");
    let finalizer_start = optimization
        .find("fn finalize_optimization(")
        .expect("optimization must define its public SAT finalizer");
    let finalizer = &optimization[finalizer_start..];
    let evidence_invalidation = finalizer
        .find("self.last_model_validated = false;")
        .expect("optimization must invalidate probe evidence for its selected witness");
    let emit = finalizer
        .find("self.emit_sat_verdict(SolveResult::Sat, &value_roots)")
        .expect("optimization must use the SAT emission funnel with objective-value roots");
    let reaccount = finalizer
        .find("self.optimization_final_values_match(finite_values)")
        .expect("optimization must re-account finite values against the final model");
    let publish = finalizer
        .find("self.finite_objective_values\n            .extend(finite_values.iter().cloned());")
        .expect("optimization must publish indexed finite values only after admission");
    assert!(
        evidence_invalidation < emit,
        "optimization must invalidate probe evidence before validating and certifying its selected witness"
    );
    assert!(
        emit < reaccount && reaccount < publish,
        "optimization order must be exact-root emission -> final re-accounting -> indexed publication"
    );
    assert!(
        optimization.contains(
            "self.last_model_validated = false;\n        self.last_model = captured_model;"
        ),
        "MaxSMT must invalidate evidence before replacing the most recent probe model"
    );
}

/// (f) MaxSMT may capture an optimum from an earlier temporary probe. Replacing
/// the probe model invalidates its evidence, and the captured witness must pass
/// through the restored hard scope plus its exact soft-classification roots,
/// then be re-accounted from the final model before any cost is published.
#[test]
fn maxsmt_revalidates_captured_witness_before_publishing_optimum() {
    let optimization = read("src/executor/optimization.rs");
    let maxsmt_start = optimization
        .find("pub(in crate::executor) fn maxsmt_check_sat(")
        .expect("optimization must define maxsmt_check_sat");
    let maxsmt_end = optimization[maxsmt_start..]
        .find("fn maxsmt_assert(&mut self")
        .map(|offset| maxsmt_start + offset)
        .expect("maxsmt_check_sat must precede its assertion helper");
    let maxsmt = &optimization[maxsmt_start..maxsmt_end];

    let invalidate = maxsmt
        .find("self.last_model_validated = false;")
        .expect("MaxSMT must invalidate the last probe's validation evidence");
    let reinstall = maxsmt
        .find("self.last_model = captured_model;")
        .expect("MaxSMT must install its captured optimal witness");
    let classify = maxsmt
        .find("self.maxsmt_classification_roots(&softs, &captured_violations)")
        .expect("MaxSMT must turn its captured soft partition into validation roots");
    let emit = maxsmt
        .find("self.emit_sat_verdict(captured_result, &classification_roots)")
        .expect("MaxSMT must certify the captured witness against hard + classification roots");
    let reaccount = maxsmt
        .find("self.maxsmt_final_witness_accounting(&softs)")
        .expect("MaxSMT must recompute cost and partition from the final public model");
    let publish_cost = maxsmt
        .find("self.last_soft_cost = Some(captured_cost);")
        .expect("MaxSMT must publish cost only after witness admission");
    assert!(
        invalidate < reinstall
            && reinstall < classify
            && classify < emit
            && emit < reaccount
            && reaccount < publish_cost,
        "MaxSMT order must be invalidate -> replace witness -> bind partition -> validate/mint -> final re-account -> publish optimum"
    );
    assert!(
        maxsmt.contains("self.last_sat_certificate = None;")
            && maxsmt.contains("self.last_model = None;")
            && maxsmt.contains("self.last_soft_cost = None;")
            && maxsmt.contains("self.objective_certificates.clear();")
            && maxsmt.contains("Err(error) =>"),
        "a MaxSMT validation downgrade or error must clear witness, certificate, and optimum artefacts"
    );
}

/// (f2) Optimization transactions must restore the user assertion stack and
/// revoke probe artefacts on every non-admission path.
#[test]
fn optimization_transactions_restore_scope_and_fail_closed_on_errors() {
    let optimization = read("src/executor/optimization.rs");

    let lex_start = optimization
        .find("fn optimize_lex(&mut self")
        .expect("optimization must define optimize_lex");
    let lex_end = optimization[lex_start..]
        .find("fn optimize_box(&mut self")
        .map(|offset| lex_start + offset)
        .expect("optimize_lex must precede optimize_box");
    let lex = &optimization[lex_start..lex_end];
    let snapshot = lex
        .find("let assertion_snapshot = self.ctx.assertions.len();")
        .expect("lex must snapshot the user assertion stack");
    let commit = lex
        .find("self.optimization_assert(commit);")
        .expect("lex commits must keep parsed/elaborated assertion stacks aligned");
    let restore = lex
        .find("self.ctx.truncate_assertions(assertion_snapshot);")
        .expect("lex must restore transient commits on every closure exit");
    let finalize = lex
        .find("self.finalize_optimization(&finite_values, true)")
        .expect("lex must certify its selected optimum after restoration");
    assert!(
        snapshot < commit && commit < restore && restore < finalize,
        "lex order must be snapshot -> transient commit -> restore -> public certification"
    );
    assert!(
        lex.contains("Err(error) => {")
            && lex.contains("self.invalidate_last_check_result();")
            && lex.contains("Ok(false) => Ok(self.optimization_inconclusive())"),
        "lex errors and inconclusive probes must revoke partial admission state"
    );

    assert!(
        !optimization.contains("self.ctx.assertions.push(commit);")
            && !optimization.contains("self.ctx.assertions.push(b);")
            && optimization.contains("self.optimization_assert(b);"),
        "all transient lex/Pareto assertions must use the aligned assertion helper"
    );

    let inconclusive_start = optimization
        .find("fn optimization_inconclusive(&mut self)")
        .expect("optimization must define its inconclusive cleanup");
    let inconclusive_end = optimization[inconclusive_start..]
        .find("fn finalize_optimization(")
        .map(|offset| inconclusive_start + offset)
        .expect("inconclusive cleanup must precede finalization");
    let inconclusive = &optimization[inconclusive_start..inconclusive_end];
    for required in [
        "self.last_sat_certificate = None;",
        "self.last_model_validated = false;",
        "self.last_model = None;",
        "self.unbounded_objectives.clear();",
        "self.unavailable_objectives.clear();",
        "self.finite_objective_values.clear();",
        "self.objective_certificates.clear();",
        "self.pareto_state = None;",
        "self.last_result = Some(SolveResult::Unknown);",
    ] {
        assert!(
            inconclusive.contains(required),
            "inconclusive optimization must revoke `{required}`"
        );
    }
}

/// (f3) MaxSMT must not use `?` to escape from an engine outcome after an
/// internal relaxed-scope probe, and every later fallible exit must clean first.
#[test]
fn maxsmt_cleans_every_fallible_pre_admission_exit() {
    let optimization = read("src/executor/optimization.rs");
    let maxsmt_start = optimization
        .find("pub(in crate::executor) fn maxsmt_check_sat(")
        .expect("optimization must define maxsmt_check_sat");
    let maxsmt_end = optimization[maxsmt_start..]
        .find("fn maxsmt_assert(&mut self")
        .map(|offset| maxsmt_start + offset)
        .expect("maxsmt_check_sat must precede its assertion helper");
    let maxsmt = &optimization[maxsmt_start..maxsmt_end];

    assert!(
        !maxsmt.contains("= outcome?;"),
        "MaxSMT engine errors may follow successful probes and must not bypass cleanup via `?`"
    );
    let outcome_match = maxsmt
        .find("match outcome {")
        .expect("MaxSMT must explicitly classify its engine outcome");
    let outcome_error = maxsmt[outcome_match..]
        .find("Err(error) => {")
        .map(|offset| outcome_match + offset)
        .expect("MaxSMT must handle engine errors explicitly");
    let outcome_cleanup = maxsmt[outcome_error..]
        .find("self.invalidate_last_check_result();")
        .map(|offset| outcome_error + offset)
        .expect("MaxSMT engine errors must revoke probe artefacts");
    let outcome_return = maxsmt[outcome_error..]
        .find("return Err(error);")
        .map(|offset| outcome_error + offset)
        .expect("MaxSMT engine error must propagate");
    assert!(outcome_cleanup < outcome_return);

    assert!(
        maxsmt.contains("if hard_result.is_err() {")
            && maxsmt.contains("self.invalidate_last_check_result();"),
        "hard-only proof rerun errors must also revoke partial MaxSMT state"
    );

    let optimize_wrapper_start = optimization
        .find("pub(in crate::executor) fn optimize_check_sat(")
        .expect("optimization must define its fallible public wrapper");
    let optimize_wrapper = &optimization[optimize_wrapper_start..];
    assert!(
        optimize_wrapper.contains("if result.is_err() {")
            && optimize_wrapper.contains("self.invalidate_last_check_result();"),
        "every objective-engine error must revoke internal probe artefacts"
    );
}

/// (f4) The native MaxSMT API must reuse the executor transaction, restore the
/// parsed soft owner before handling the command result, and fail closed unless
/// the executor supplies independently checked exact accounting.
#[test]
fn native_maxsmt_is_transactional_exact_and_has_no_duplicate_solver() {
    let api = read("src/api/solving/maxsmt.rs");
    assert!(
        !api.contains("try_push(")
            && !api.contains("assert_at_most_k")
            && !api.contains("find_violated_softs"),
        "native MaxSMT must not reintroduce a duplicate relaxation/cardinality solver"
    );

    let query_start = api
        .find("pub fn check_sat_max(&mut self)")
        .expect("native API must define check_sat_max");
    let query_end = api[query_start..]
        .find("fn decline_maxsmt_definite_on_external_stop(")
        .map(|offset| query_start + offset)
        .expect("native MaxSMT query must precede its stop helper");
    let query = &api[query_start..query_end];
    let retire = query
        .find("self.clear_last_solve_state(true, false);")
        .expect("native MaxSMT must retire the preceding query at entry");
    let reject = query
        .find("self.reject_composite_bv_cnf_export(\"check_sat_max\")?")
        .expect("native MaxSMT must reject unsupported artifact export");
    assert!(
        retire < reject,
        "retirement must precede fallible preflight"
    );

    let install = query
        .find(".replace_soft_constraints(native_softs)")
        .expect("native MaxSMT must transactionally install API softs");
    let execute = query
        .find("self.executor.execute_native_maxsmt_check_sat()")
        .expect("native MaxSMT must reuse the sealed executor CheckSat continuation");
    let restore_softs = query
        .find(".replace_soft_constraints(parsed_softs)")
        .expect("native MaxSMT must restore the parsed soft set");
    let propagate_error = query
        .find("if let Err(error) = execution")
        .expect("native MaxSMT must handle executor errors after restoration");
    assert!(
        install < execute && execute < restore_softs && restore_softs < propagate_error,
        "native soft ownership order must be install -> execute -> restore -> classify"
    );

    let workspace = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(std::path::Path::parent)
        .expect("ay-dpll lives below the workspace root")
        .to_path_buf();
    let mut sources = Vec::new();
    rust_sources_below(&workspace.join("crates"), &mut sources);
    let allowed = [
        "crates/ay-dpll/src/api/solving/maxsmt.rs",
        "crates/ay-dpll/src/executor/command_boundary.rs",
    ];
    for source in sources {
        let relative = source
            .strip_prefix(&workspace)
            .expect("enumerated source is below workspace")
            .to_string_lossy();
        if is_chokepoint_source_fixture(relative.as_ref()) {
            continue;
        }
        let text = std::fs::read_to_string(&source)
            .unwrap_or_else(|error| panic!("cannot read {}: {error}", source.display()));
        if text.contains("execute_native_maxsmt_check_sat") {
            assert!(
                allowed.contains(&relative.as_ref()),
                "new MaxSMT continuation caller requires an explicit query-boundary audit: {relative}"
            );
        }
    }

    let plan_controls = query
        .find("let controls = self.native_publication_controls();")
        .expect("native MaxSMT must plan one immutable publication envelope");
    let install_controls = query
        .find("self.install_solve_controls(controls);")
        .expect("native MaxSMT must install caller controls");
    let outcome_transaction = query
        .find("let outcome = (|| -> Result<MaxSmtResult, SolverError> {")
        .expect("native MaxSMT must contain every post-install return in a transaction");
    let first_stop = query
        .find("self.decline_maxsmt_definite_on_external_stop(result)")
        .expect("native MaxSMT must reject a stop before reading accounting");
    let construct_hard_unsat = query[first_stop..]
        .find("return Ok(MaxSmtResult::hard_unsatisfiable());")
        .map(|offset| first_stop + offset)
        .expect("native MaxSMT must construct hard UNSAT only after its stop gate");
    let final_stop = query
        .find(".decline_maxsmt_definite_on_external_stop(SolveResult::Sat)")
        .expect("native MaxSMT must reject a stop after authenticating accounting");
    let construct_optimal = query[final_stop..]
        .find("Ok(MaxSmtResult::optimal(")
        .map(|offset| final_stop + offset)
        .expect("native MaxSMT must construct its optimal result explicitly");
    let restore_controls = query
        .find("self.restore_solve_controls(controls);")
        .expect("native MaxSMT must restore the enclosing control state");
    let return_outcome = query[restore_controls..]
        .find("outcome\n")
        .map(|offset| restore_controls + offset)
        .expect("native MaxSMT must return the completed transaction after restoration");
    assert!(
        plan_controls < install_controls
            && install_controls < execute
            && execute < outcome_transaction
            && outcome_transaction < restore_softs
            && execute < first_stop
            && first_stop < construct_hard_unsat
            && construct_hard_unsat < final_stop
            && first_stop < final_stop
            && final_stop < construct_optimal
            && construct_optimal < restore_controls
            && restore_controls < return_outcome
            && !query.contains("clear_solve_controls"),
        "native MaxSMT controls must enclose execution, transaction/accounting authentication, and final publication before restoring the enclosing state"
    );

    assert!(
        query.contains("MAXSMT_EXACT_MAX_TOTAL_WEIGHT")
            && query.contains("soft.group.is_some()")
            && query.contains("if !optimal")
            && query.contains("self.executor.last_maxsmt_outcome()")
            && query.contains("recomputed_violated_weight != Some(violated_weight)")
            && query.contains("installed_native_softs != expected_native_softs"),
        "native MaxSMT must reject grouped/large/approximate/accounting- or transaction-inconsistent outcomes"
    );

    let result_type = read("src/api/types/maxsmt.rs");
    assert!(
        result_type.contains("pub violated_weight: u64")
            && result_type.contains("pub fn violated_weight(&self) -> u64")
            && result_type.contains("self.violated_weight"),
        "MaxSmtResult must store and return real violated-weight accounting"
    );

    let executor = read("src/executor/optimization.rs");
    assert!(
        executor.contains("self.last_soft_violations = Some(captured_violations);")
            && executor.contains("self.last_soft_violations = None;"),
        "executor must publish violated indices only with an admitted MaxSMT witness"
    );
}

/// (f5) Objective declarations, not term DAG nodes, own public outcomes. This
/// prevents duplicate same-term max/min objectives from overwriting finite box
/// values, infinities, or independently verified certificates.
#[test]
fn objective_outcomes_are_keyed_by_declaration_identity() {
    let executor = read("src/executor.rs");
    assert!(
        executor.contains("unbounded_objectives: HashMap<usize,")
            && executor.contains("objective_certificates: HashMap<usize,")
            && executor.contains("finite_objective_values: HashMap<usize,"),
        "all per-objective public artefacts must be keyed by declaration index"
    );

    let optimization = read("src/executor/optimization.rs");
    assert!(
        optimization.contains("fn objective_optimum(&self, objective_index: usize)")
            && optimization.contains(".extend(finite_values.iter().cloned())")
            && optimization.contains(".insert(objective_index, cert)")
            && optimization.contains(".insert(objective_index, ObjectiveDirection::Maximize)")
            && optimization.contains(".insert(objective_index, ObjectiveDirection::Minimize)"),
        "optimizer writes must preserve objective declaration identity"
    );

    // `2014dd6f5 refactor: modularize solver internals` split the objective
    // readers out of `model/output.rs` into `model/output_objectives.rs`. The
    // pinned reads below are unchanged; only their home moved.
    let output = read("src/executor/model/output_objectives.rs");
    let api = read("src/api/solving/optimize.rs");
    assert!(
        output.contains("for (objective_index, obj) in self.ctx.objectives().iter().enumerate()")
            && output.contains("self.finite_objective_values.get(&objective_index)")
            && output.contains("self.objective_certificates.get(&objective_index)")
            && api.contains("self.executor.objective_optimum(idx)"),
        "SMT-LIB and native reads must use the same declaration index"
    );
}

/// (f6) A lexicographic suffix after an unbounded objective has no scalar exact
/// outcome. AY must stop, mark the suffix unavailable, and clear that marker on
/// every lifecycle/inconclusive path rather than independently optimizing it.
#[test]
fn unbounded_lex_prefix_never_fabricates_suffix_optima() {
    let optimization = read("src/executor/optimization.rs");
    let lex_start = optimization
        .find("fn optimize_lex(&mut self")
        .expect("optimization must define optimize_lex");
    let lex_end = optimization[lex_start..]
        .find("fn optimize_box(&mut self")
        .map(|offset| lex_start + offset)
        .expect("optimize_lex must precede optimize_box");
    let lex = &optimization[lex_start..lex_end];
    assert!(
        lex.contains("self.unbounded_objectives.contains_key(&objective_index)")
            && lex.contains(".extend((objective_index + 1)..objectives.len())")
            && lex.contains("return Ok(true);"),
        "lex must terminate and mark every suffix objective after an unbounded prefix"
    );

    // Objective readers now live in `model/output_objectives.rs` (see the
    // relocation note in `objective_outcomes_are_keyed_by_declaration_identity`).
    let output = read("src/executor/model/output_objectives.rs");
    assert!(
        optimization.contains("self.unavailable_objectives.contains(&objective_index)")
            && output.contains("self.unavailable_objectives.contains(&objective_index)"),
        "native and SMT-LIB objective readers must reject unavailable suffix values"
    );

    let lifecycle = read("src/executor/lifecycle.rs");
    let invalidation_start = lifecycle
        .find("pub(super) fn invalidate_last_check_result(&mut self)")
        .expect("lifecycle must define canonical query-artifact invalidation");
    let invalidation_end = lifecycle[invalidation_start..]
        .find("fn detach_persistent_decision_trace_writers(&mut self)")
        .map(|offset| invalidation_start + offset)
        .expect("canonical invalidation must precede trace detachment");
    let invalidation = &lifecycle[invalidation_start..invalidation_end];
    let reset = &lifecycle[lifecycle
        .find("pub fn reset(&mut self)")
        .expect("lifecycle must define direct reset")..];
    assert!(
        invalidation.contains("self.unavailable_objectives.clear();")
            && reset.contains("self.invalidate_last_check_result();")
            && lifecycle.contains("unavailable_objectives: HashSet::default()"),
        "unavailable suffix state must be initialized and cleared with query artefacts"
    );
}

/// (f6b) An UNATTAINED (infinitesimal, #opt-epsilon) optimum is published only
/// behind BOTH full-solver twins, and it flows through the same
/// no-fabrication discipline as an unbounded one: the lex suffix is marked
/// unavailable (never independently optimized), every reader resolves the
/// epsilon record BEFORE the finite map, the native API maps it to
/// "no scalar" rather than a fabricated number, and the state clears with
/// every query artefact.
#[test]
fn epsilon_outcome_requires_twin_proofs_and_never_fabricates_scalars() {
    let optimization = read("src/executor/optimization.rs");
    post_rebase::assert_epsilon_publication_twins(&optimization);

    // Lex: an infinitesimal prefix terminates the search and marks the whole
    // suffix unavailable, exactly like the unbounded case (f6).
    let lex_start = optimization
        .find("fn optimize_lex(&mut self")
        .expect("optimize_lex present");
    let lex_end = optimization[lex_start..]
        .find("fn optimize_box(&mut self")
        .map(|offset| lex_start + offset)
        .expect("optimize_lex delimited");
    let lex = &optimization[lex_start..lex_end];
    assert!(
        lex.contains("self.infinitesimal_objectives.contains_key(&objective_index)"),
        "lex must stop at an unattained prefix instead of committing its sup"
    );

    // Readers resolve the epsilon record BEFORE the finite map, in both the
    // SMT-LIB renderer and the structured native reader.
    // Objective readers now live in `model/output_objectives.rs` (see the
    // relocation note in `objective_outcomes_are_keyed_by_declaration_identity`).
    let output = read("src/executor/model/output_objectives.rs");
    for (name, source) in [
        ("output_objectives.rs", &output),
        ("optimization.rs", &optimization),
    ] {
        let eps = source
            .find("infinitesimal_objectives.get(&objective_index)")
            .unwrap_or_else(|| panic!("{name} must read the epsilon record"));
        let finite = source
            .find("finite_objective_values.get(&objective_index)")
            .unwrap_or_else(|| panic!("{name} must read the finite map"));
        assert!(
            eps < finite,
            "{name}: epsilon outcomes must resolve before finite ones"
        );
    }

    // The native/FFI surface never fabricates a scalar for an epsilon outcome.
    let api = read("src/api/solving/optimize.rs");
    assert!(
        api.contains("ObjectiveOutcome::Epsilon { .. } => None"),
        "the native API must report no scalar for an unattained optimum"
    );

    // State lifecycle: initialized and cleared with every query artefact.
    let lifecycle = read("src/executor/lifecycle.rs");
    let invalidation_start = lifecycle
        .find("pub(super) fn invalidate_last_check_result(&mut self)")
        .expect("lifecycle must define canonical query-artifact invalidation");
    let invalidation_end = lifecycle[invalidation_start..]
        .find("fn detach_persistent_decision_trace_writers(&mut self)")
        .map(|offset| invalidation_start + offset)
        .expect("canonical invalidation must precede trace detachment");
    let invalidation = &lifecycle[invalidation_start..invalidation_end];
    let reset = &lifecycle[lifecycle
        .find("pub fn reset(&mut self)")
        .expect("lifecycle must define direct reset")..];
    assert!(
        invalidation.contains("self.infinitesimal_objectives.clear();")
            && reset.contains("self.invalidate_last_check_result();")
            && lifecycle.contains("infinitesimal_objectives: HashMap::default()"),
        "epsilon state must be initialized and cleared with query artefacts"
    );
    assert!(
        optimization
            .matches("self.infinitesimal_objectives.clear();")
            .count()
            >= 3,
        "epsilon state must clear on fresh-optimization, inconclusive, and \
         maxsmt-downgrade paths"
    );
}

/// (f7) The Z3 compatibility layer must capture the exact consumer-admissible
/// optimized witness. Re-solving selected softs after certification would sever
/// the exposed model from the MaxSMT accounting.
#[test]
fn ffi_optimize_captures_admitted_witness_without_reconstruction() {
    let ffi = read("../ay-ffi/src/z3_compat/optimize.rs");
    assert!(
        !ffi.contains("reconstruct_optimal_model")
            && ffi.matches("ctx.solver.model_for_consumer()").count() >= 2,
        "FFI arithmetic and MaxSMT lanes must capture the admitted model directly"
    );
    assert!(
        ffi.contains("has_objectives && (has_parsed_softs || has_api_softs)")
            && ffi.contains(
                "joint arithmetic-objective + soft-constraint optimization is not implemented"
            ),
        "unsupported mixed optimization must fail closed instead of ignoring one class"
    );
}

/// (g) A certificate is a one-query capability: lifecycle invalidation, public
/// solve entry, and funnel entry all revoke the old token before any fallible
/// work can run.
#[test]
fn prior_sat_certificate_is_revoked_before_new_fallible_work() {
    let lifecycle = read("src/executor/lifecycle.rs");
    let invalidation_start = lifecycle
        .find("pub(super) fn invalidate_last_check_result(&mut self)")
        .expect("lifecycle must define result invalidation");
    let public_solve_start = lifecycle[invalidation_start..]
        .find("pub(crate) fn begin_public_solve(")
        .map(|offset| invalidation_start + offset)
        .expect("lifecycle must define public-solve invalidation");
    let invalidation = &lifecycle[invalidation_start..public_solve_start];
    assert!(
        invalidation.contains("self.last_sat_certificate = None;"),
        "assertion/objective mutations must revoke the preceding SAT certificate"
    );

    let sat_emit = read("src/executor/model/sat_emit.rs");
    let funnel_start = sat_emit
        .find("pub(in crate::executor) fn emit_sat_verdict(")
        .expect("sat_emit must define the funnel");
    let funnel_end = sat_emit[funnel_start..]
        .find("fn apply_sat_validation_postcondition(")
        .map(|offset| funnel_start + offset)
        .expect("sat_emit must define its postcondition");
    let funnel = &sat_emit[funnel_start..funnel_end];
    let revoke = funnel
        .find("self.last_sat_certificate = None;")
        .expect("funnel entry must revoke the preceding certificate");
    let fallible_validation = funnel
        .find("self.finalize_sat_model_validation()?")
        .expect("funnel must contain fallible validation");
    let mint = funnel
        .rfind("Some(SatCertificate(SatCertificateKind::ValidatedModel));")
        .expect("funnel must mint only after admission");
    assert!(
        revoke < fallible_validation && fallible_validation < mint,
        "the funnel must revoke before fallible validation and mint only afterward"
    );

    let executor = read("src/executor.rs");
    assert!(
        executor.contains("if matches!(cmd, Command::CheckSat | Command::CheckSatAssuming(_)) {")
            && executor.contains("self.begin_external_decision_query(true);")
            && executor.contains("self.begin_public_solve(true)"),
        "SMT-LIB decision commands must retire stale artefacts before elaboration"
    );
}

/// (g2) The public result wrapper must not expose a caller-chosen validation
/// bit. Tests may fabricate rejection cases only inside ay-dpll, while ay-ffi
/// injects an already-rejected outcome through a cfg(test)-only local helper.
#[test]
fn verified_result_exposes_no_public_sat_fabrication_capability() {
    let results = read("src/api/types/results.rs");
    assert!(
        !results.contains("pub fn for_testing("),
        "VerifiedSolveResult must not ship a public caller-chosen validation constructor"
    );
    assert!(
        results.contains("#[cfg(test)]\n    pub(crate) fn for_testing("),
        "the fabrication helper must be both cfg(test) and crate-private"
    );
    assert!(
        results.contains("pub(crate) fn certified_sat(_certificate: SatCertificate)")
            && results.contains("pub(crate) fn certified_unsat(")
            && results.contains("pub(crate) fn unknown()")
            && !results.contains("pub(crate) fn from_validated("),
        "definite construction must stay crate-private and require an exact capability"
    );
    assert!(
        !results.contains(
            "result: SolveResult,\n        model_validated: bool,\n        sat_certificate: Option<SatCertificate>"
        ) && results.contains("model_validated: true"),
        "SAT validation provenance must be derived from the consumed certificate, not a caller-supplied bool"
    );
    assert!(
        results.contains("```compile_fail")
            && results.contains("VerifiedSolveResult::for_testing(SolveResult::Sat, true)"),
        "the public API must carry a negative compile test for SAT fabrication"
    );

    let ffi_solver = read("../ay-ffi/src/z3_compat/solver.rs");
    assert!(
        ffi_solver.contains(
            "#[cfg(test)]\npub(super) fn solve_lbool_from_consumer_rejection_for_testing("
        ),
        "ay-ffi may inject a rejection only through a non-shipping local helper"
    );
    let ffi_tests = read("../ay-ffi/src/z3_compat/tests.rs");
    assert!(
        !ffi_tests.contains("VerifiedSolveResult::for_testing"),
        "cross-crate tests must not require a production SAT-fabrication capability"
    );

    let sat_emit = read("src/executor/model/sat_emit.rs");
    assert!(
        sat_emit
            .contains("#[derive(Debug)]\npub(crate) struct SatCertificate(SatCertificateKind);")
            && !sat_emit.contains("#[derive(Debug, Clone)]\npub(crate) struct SatCertificate"),
        "the one-shot SAT capability must not be clonable"
    );
}

/// (g3) A tactic wrapper performs fallible transformation work before the
/// ordinary Solver entrypoint. It must therefore retire the preceding query at
/// wrapper entry and again after any partially-solving composite tactic fails.
#[test]
fn tactic_query_failures_cannot_reuse_preceding_solve_artefacts() {
    let tactics = read("src/api/solving/tactics.rs");
    let wrapper_start = tactics
        .find("impl TacticSolver {")
        .expect("tactics must define TacticSolver");
    let apply_start = tactics[wrapper_start..]
        .find("impl Solver {")
        .map(|offset| wrapper_start + offset)
        .expect("TacticSolver methods must precede Solver tactic helpers");
    let wrappers = &tactics[wrapper_start..apply_start];

    for (entry, next_entry, first_fallible_work) in [
        (
            "pub fn check_sat(&mut self)",
            Some("pub fn check_sat_assuming(&mut self, assumptions: &[Term])"),
            "apply_tactic(&self.tactic)",
        ),
        (
            "pub fn check_sat_assuming(&mut self, assumptions: &[Term])",
            None,
            "resolve_terms(\"tactic_check_sat_assuming\", assumptions)",
        ),
    ] {
        let start = wrappers
            .find(entry)
            .unwrap_or_else(|| panic!("TacticSolver must define {entry}"));
        let end = next_entry
            .and_then(|next| wrappers[start..].find(next).map(|offset| start + offset))
            .unwrap_or(wrappers.len());
        let body = &wrappers[start..end];
        let retire = body
            .find("clear_last_solve_state(true, false)")
            .unwrap_or_else(|| panic!("{entry} must retire the preceding public result"));
        let fallible_work = body
            .find(first_fallible_work)
            .unwrap_or_else(|| panic!("{entry} must perform {first_fallible_work}"));
        let transform = body
            .find("apply_tactic(&self.tactic)")
            .unwrap_or_else(|| panic!("{entry} must apply its tactic in its own method region"));
        assert!(
            retire < fallible_work && retire < transform,
            "{entry} must revoke stale artefacts and assumptions before fallible handle/tactic work"
        );
    }

    let error_helper = tactics
        .find("pub(crate) fn set_internal_error_unknown(&mut self, detail: &str)")
        .expect("tactic errors must use a shared fail-closed helper");
    let error_tail = &tactics[error_helper..];
    let revoke = error_tail
        .find("self.executor.begin_public_solve(false);")
        .expect("a failed composite tactic must revoke partial internal solves");
    let replace_executor_result = error_tail
        .find(".replace_last_result_with_unknown(UnknownReason::InternalError);")
        .expect("failed tactics must replace the executor result with InternalError");
    let diagnose = error_tail
        .find("self.last_unknown_reason = Some(UnknownReason::InternalError);")
        .expect("failed tactics must publish an InternalError reason");
    assert!(
        revoke < replace_executor_result && replace_executor_result < diagnose,
        "partial tactic solve artefacts must be revoked before executor/API Unknown is diagnosed"
    );
}

/// (h) Trivial string fast paths install their final witness before marking it
/// validated.  Validation evidence must never be allowed to describe the model
/// that happened to precede the current public solve.
#[test]
fn trivial_string_fast_paths_validate_the_model_they_publish() {
    for rel in [
        "src/executor/theories/strings.rs",
        "src/executor/theories/strings_lia.rs",
    ] {
        let src = read(rel);
        let install = src
            .find("self.last_model = Some(super::super::model::Model")
            .unwrap_or_else(|| panic!("{rel} must install its trivial-SAT model"));
        let validate = src
            .find("self.last_model_validated = true;")
            .unwrap_or_else(|| panic!("{rel} must record trivial-SAT validation evidence"));
        let return_sat = src[validate..]
            .find("return Ok(SolveResult::Sat);")
            .map(|offset| validate + offset)
            .unwrap_or_else(|| panic!("{rel} must return its trivial SAT verdict"));

        assert!(
            install < validate && validate < return_sat,
            "{rel} must install the final witness before attaching validation evidence"
        );
    }
}

/// (i) The funnel's authoritative gate is reachable from the independent gate's
/// module and routes its downgrade through the proven `gate_keeps_sat` core.
#[test]
fn authoritative_gate_routes_through_the_proven_core() {
    let gate = read("src/executor/model/independent_gate.rs");
    assert!(
        gate.contains("fn apply_authoritative_failclosed_gate(")
            && gate.contains("fn assertion_is_authoritatively_ground("),
        "independent_gate.rs must define the authoritative-failclosed gate and its \
         authoritative-ground predicate"
    );
    assert!(
        gate.contains("gate_keeps_sat(true, /* confirmed = */ false, ENFORCE_ON_REFUTATION)"),
        "the authoritative gate must route its keep/downgrade decision through the proven \
         `gate_keeps_sat` core with unconditional enforcement"
    );
}
