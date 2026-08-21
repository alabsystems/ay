// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

/// (g) A certificate is a one-query capability: lifecycle invalidation, public
/// solve entry, and funnel entry all revoke the old token before any fallible
/// work can run.
#[test]
fn prior_sat_certificate_is_revoked_before_new_fallible_work() {
    let lifecycle = read("src/executor/lifecycle.rs");
    assert!(
        lifecycle.contains("mod public_solve;"),
        "lifecycle must compile the public-solve entrypoints"
    );
    let invalidation_start = lifecycle
        .find("pub(super) fn invalidate_last_check_result(&mut self)")
        .expect("lifecycle must define result invalidation");
    let invalidation_end = lifecycle[invalidation_start..]
        .find("pub(in crate::executor) fn clear_quantified_sat_authority(")
        .map(|offset| invalidation_start + offset)
        .expect("result invalidation must have a bounded source region");
    let invalidation = &lifecycle[invalidation_start..invalidation_end];
    assert!(
        invalidation.contains("self.last_sat_certificate = None;"),
        "assertion/objective mutations must revoke the preceding SAT certificate"
    );

    let public_solve = read("src/executor/lifecycle/public_solve.rs");
    let public_solve_start = public_solve
        .find("pub(crate) fn begin_public_solve(")
        .expect("lifecycle must define public-solve invalidation");
    let public_solve_end = public_solve[public_solve_start..]
        .find("pub(crate) fn begin_external_decision_query(")
        .map(|offset| public_solve_start + offset)
        .expect("public-solve invalidation must have a bounded source region");
    assert!(
        public_solve[public_solve_start..public_solve_end]
            .contains("self.invalidate_last_check_result();"),
        "public solve entry must revoke the preceding SAT certificate"
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
