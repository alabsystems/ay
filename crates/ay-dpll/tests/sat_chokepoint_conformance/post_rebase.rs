// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use std::path::PathBuf;

use super::{is_chokepoint_source_fixture, normalize_whitespace, read, rust_sources_below};

pub(super) fn assert_command_boundary(executor_normalized: &str) {
    // `NativeMaxSmtTextContinuation` is an admitting boundary. Native
    // optimization remains the sole non-admitting boundary because its typed
    // wrapper consumes the linear result itself.
    let text_admission = "CommandExecutionBoundary::GenericText | CommandExecutionBoundary::AuthoredText | CommandExecutionBoundary::NativeMaxSmtTextContinuation => { self.admit_command_solve_result(sat_result)";
    assert_eq!(
        executor_normalized.matches(text_admission).count(),
        2,
        "plain check-sat and check-sat-assuming must both admit before formatting"
    );
    let boundary = read("src/executor/command_boundary.rs");
    let variants = boundary
        .split("pub(super) enum CommandExecutionBoundary {")
        .nth(1)
        .and_then(|tail| tail.split('}').next())
        .expect("the command boundary enum must be readable")
        .lines()
        .filter_map(|line| line.trim().strip_suffix(','))
        .collect::<Vec<_>>();
    assert_eq!(
        variants,
        [
            "GenericText",
            "AuthoredText",
            "NativeMaxSmtTextContinuation",
            "NativeOptimization",
        ],
        "a new publication boundary must be classified here before it can format a verdict"
    );
    for branch in executor_normalized.split(text_admission).skip(1) {
        let display = branch
            .find("let display = sat_result.to_string();")
            .expect("admitted command result must be the value rendered to SMT-LIB");
        let publish = branch
            .find("self.last_result = Some(sat_result);")
            .expect("admitted command result must become the recorded public result");
        assert!(display < publish);
    }
}

pub(super) fn assert_command_admission_order(admission: &str) {
    let live_stop = admission
        .find("decline_definite_publication_on_external_stop(result)")
        .expect("text admission must reject a live external stop");
    let reset_unsat_admission = admission
        .find("self.last_command_unsat_admission = None;")
        .expect("text admission must revoke the preceding UNSAT command admission");
    let unsat_branch = admission
        .find("if result.is_unsat() {")
        .expect("text admission must authenticate UNSAT separately");
    let nondefinite_branch = admission
        .find("if result != SolveResult::Sat {")
        .expect("text admission must revoke tokens for non-definite results");
    let sat_take = admission
        .find(".take_sat_certificate()")
        .expect("text admission must consume SAT authority");
    let unsat_takes = admission
        .match_indices(".take_unsat_certificate()")
        .map(|(offset, _)| offset)
        .collect::<Vec<_>>();
    let sat_revocations = admission
        .match_indices("self.last_sat_certificate = None;")
        .map(|(offset, _)| offset)
        .collect::<Vec<_>>();
    assert_eq!(
        admission.matches(".take_sat_certificate()").count(),
        1,
        "text SAT authority must have exactly one consumer"
    );
    assert_eq!(
        unsat_takes.len(),
        3,
        "UNSAT authority must be consumed on UNSAT, non-definite, and SAT paths"
    );
    assert_eq!(
        sat_revocations.len(),
        2,
        "UNSAT and non-definite paths must revoke incompatible SAT authority"
    );
    let confirm_sat = admission
        .find("certificate.confirms_sat_emission()")
        .expect("text admission must validate consumed SAT authority");
    let reject_sat = admission
        .find("self.reject_unadmitted_sat_publication(")
        .expect("missing SAT authority must fail closed");
    assert!(
        live_stop < reset_unsat_admission
            && reset_unsat_admission < unsat_branch
            && unsat_branch < sat_revocations[0]
            && sat_revocations[0] < unsat_takes[0]
            && unsat_takes[0] < nondefinite_branch
            && nondefinite_branch < sat_revocations[1]
            && sat_revocations[1] < unsat_takes[1]
            && unsat_takes[1] < unsat_takes[2]
            && unsat_takes[2] < sat_take
            && sat_take < confirm_sat
            && confirm_sat < reject_sat,
        "text admission must stop-gate, revoke incompatible authority, consume exactly the active token, validate it, then fail closed"
    );
}

pub(super) fn assert_authored_entrypoint_allowlist() {
    let workspace = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(std::path::Path::parent)
        .expect("ay-dpll lives below the workspace root")
        .to_path_buf();
    let mut sources = Vec::new();
    rust_sources_below(&workspace.join("crates"), &mut sources);
    let allowed = [
        "crates/ay-dpll/src/api/solving/check.rs",
        "crates/ay-dpll/src/api/solving/cross_check.rs",
        "crates/ay-dpll/src/executor.rs",
        "crates/ay-dpll/src/executor/quantifier_loop/projection_candidate.rs",
        "crates/ay-dpll/src/executor/query_authority.rs",
        "crates/ay-dpll/tests/common/mod.rs",
        "crates/ay-dpll/tests/group_quantifiers/ufbv_checked_projection_sat.rs",
        "crates/ay/src/run.rs",
    ];
    let test_only_allowed = [
        "crates/ay-dpll/src/executor/check_sat.rs",
        "crates/ay-dpll/src/executor/quantifier_loop/result_mapping.rs",
        "crates/ay-dpll/src/executor/unsat_cert.rs",
        "crates/ay-dpll/src/executor/check_sat_assuming/nested_publication_tests.rs",
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
        if !text.contains("solve_authored_plain_hard_query")
            && !text.contains("solve_interruptible_authored_plain_hard_query")
            && !text.contains("execute_authored")
        {
            continue;
        }
        let test_only_callsite = test_only_allowed.contains(&relative.as_ref())
            && (text.find("#[cfg(test)]").is_some_and(|test_start| {
                let production = &text[..test_start];
                !production.contains("solve_authored_plain_hard_query")
                    && !production.contains("solve_interruptible_authored_plain_hard_query")
                    && !production.contains("execute_authored")
            }) || cfg_test_module_file(&workspace, relative.as_ref()));
        assert!(
            allowed.contains(&relative.as_ref()) || test_only_callsite,
            "new authored-authority callsite requires an explicit boundary audit: {relative}"
        );
    }
}

fn cfg_test_module_file(workspace: &std::path::Path, relative: &str) -> bool {
    let path = std::path::Path::new(relative);
    let Some(stem) = path.file_stem().and_then(|stem| stem.to_str()) else {
        return false;
    };
    let Some(parent_dir) = path.parent() else {
        return false;
    };
    let parent = workspace.join(parent_dir.with_extension("rs"));
    let Ok(text) = std::fs::read_to_string(parent) else {
        return false;
    };
    normalize_whitespace(&text).contains(&format!("#[cfg(test)] mod {stem};"))
}

pub(super) fn assert_funnelled_sat_sources() {
    let assuming_rel = "src/executor/check_sat_assuming.rs";
    let publication_rel = "src/executor/check_sat_assuming/publication.rs";
    let assuming = read(assuming_rel);
    let publication = read(publication_rel);
    let optimization = read("src/executor/optimization.rs");
    assert!(
        assuming.contains(
            "#[path = \"check_sat_assuming/publication.rs\"]\n\
             mod publication;\n\
             pub(in crate::executor) use publication::AssumptionSatPublication;"
        ),
        "check_sat_assuming must wire its audited SAT-publication module by the pinned path"
    );

    for (rel, src) in [
        (assuming_rel, assuming.as_str()),
        (publication_rel, publication.as_str()),
        ("src/executor/optimization.rs", optimization.as_str()),
    ] {
        if rel != assuming_rel {
            assert!(
                src.contains("emit_sat_verdict("),
                "{rel} must emit its SAT verdict via emit_sat_verdict"
            );
        }
        let deferral_arm_lines = if rel == publication_rel {
            let fn_start = src
                .find("fn publish_or_defer_assumption_sat(")
                .expect("the publication module must decide assumption SAT ownership in one place");
            let arm_start = src[fn_start..]
                .find("AssumptionSatPublication::DeferToPlainCheckSat => {")
                .map(|offset| fn_start + offset)
                .expect("the publication decision must name its deferral arm");
            let arm_end = src[arm_start..]
                .find("\n            }")
                .map(|offset| arm_start + offset)
                .expect("the deferral arm must be delimited");
            let arm = &src[arm_start..arm_end];
            assert!(
                arm.contains("self.last_sat_certificate = None;"),
                "the deferral arm must return an UNMINTED Sat — minting stays \
                 with the plain check-sat funnel that owns the verdict"
            );
            assert!(
                assuming.contains("fn check_sat_assuming_deferred_to_plain_check_sat(")
                    && read("src/executor/check_sat.rs").contains(
                        "self.check_sat_assuming_deferred_to_plain_check_sat(&named_assumptions)"
                    ),
                "the deferral must be entered only from the plain check-sat \
                 named-core redirect, whose caller is funnelled by check_sat_guarded"
            );
            src[..arm_start].matches('\n').count()..=src[..arm_end].matches('\n').count()
        } else {
            1..=0
        };
        for (lineno, line) in src.lines().enumerate() {
            if !line.contains("Ok(SolveResult::Sat)") {
                continue;
            }
            let trimmed = line.trim_start();
            let is_match_arm = line.contains("=>");
            let is_comment = trimmed.starts_with("//") || trimmed.starts_with('*');
            let is_audited_deferral = deferral_arm_lines.contains(&lineno);
            assert!(
                is_match_arm || is_comment || is_audited_deferral,
                "{rel}:{} emits a bare `Ok(SolveResult::Sat)` — route every SAT verdict through emit_sat_verdict so the independent + authoritative gates run:\n  {line}",
                lineno + 1,
            );
        }
    }
}

pub(super) fn assert_epsilon_publication_twins(optimization: &str) {
    for (fn_start, fn_end) in [
        ("fn maximize_real_objective(", "fn minimize_real_objective("),
        ("fn minimize_real_objective(", "fn mk_real_gt("),
    ] {
        let start = optimization.find(fn_start).expect("objective fn present");
        let end = optimization[start..]
            .find(fn_end)
            .map(|offset| start + offset)
            .expect("objective fn delimited");
        let body = &optimization[start..end];
        let arm_start = body
            .find("SimplexOpt::OptimalInf")
            .expect("OptimalInf arm present");
        let insert_at = body[arm_start..]
            .find("self.infinitesimal_objectives")
            .map(|offset| arm_start + offset)
            .expect("OptimalInf arm publishes the epsilon record");
        let arm_before_insert = &body[arm_start..insert_at];
        assert!(
            arm_before_insert
                .matches("self.checked_optimization_unsat(&[")
                .count()
                == 1
                && arm_before_insert
                    .matches("self.checked_optimization_decision(&[")
                    .count()
                    == 1
                && arm_before_insert.contains("CheckedOptimizationDecision::Sat")
                && arm_before_insert.find("self.checked_optimization_unsat(&[")
                    < arm_before_insert.find("self.checked_optimization_decision(&["),
            "the epsilon record must be published only after the refutation AND the δ-closeness full-solver twins: {fn_start}"
        );
    }
    assert!(
        optimization.contains("lra.has_strict_var_bound() && certificate.is_none()")
            && optimization.matches("needs_maximality_twin").count() >= 4,
        "strict-bound Optimal outcomes must carry the maximality-twin obligation"
    );
}
