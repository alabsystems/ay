// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use std::path::PathBuf;

use super::{
    code_without_comments, is_chokepoint_source_fixture, normalize_whitespace, read,
    rust_sources_below,
};

/// A finite-model witness is established exactly once, before strict
/// validation, and cannot replace another current affine certificate owner.
#[test]
fn finite_model_producer_precedes_strict_and_quantified_gate_is_consult_only() {
    let sat_emit = read("src/executor/model/sat_emit.rs");
    let funnel_start = sat_emit
        .find("pub(in crate::executor) fn emit_sat_verdict(")
        .expect("sat_emit must define emit_sat_verdict");
    let funnel_end = sat_emit[funnel_start..]
        .find("fn apply_sat_validation_postcondition(")
        .map(|offset| funnel_start + offset)
        .expect("sat_emit must define its postcondition");
    let funnel = &sat_emit[funnel_start..funnel_end];
    let producer = funnel
        .find("self.try_install_unowned_finite_model_sat_certificate(&publication_roots);")
        .expect("the finite-model producer must have one publication hook");
    let strict = funnel
        .find("self.apply_strict_gate_to_affine_certificate_model()")
        .expect("certificate models must pass the affine strict gate");
    assert!(
        producer < strict,
        "model replacement must precede strict validation"
    );
    assert_eq!(
        funnel
            .matches("self.try_install_unowned_finite_model_sat_certificate(&publication_roots);")
            .count(),
        1,
        "the SAT funnel must have one finite-model establishment point"
    );

    assert!(
        sat_emit.contains("mod finite_model_owner;"),
        "the owner guard must remain a dedicated SAT-emission submodule"
    );
    let owner_source = read("src/executor/model/sat_emit/finite_model_owner.rs");
    let helper_start = owner_source
        .find("fn try_install_unowned_finite_model_sat_certificate(")
        .expect("the finite-model owner module must define the current-owner guard");
    let helper_end = owner_source[helper_start..]
        .find("#[cfg(test)]")
        .map(|offset| helper_start + offset)
        .expect("the owner guard must end before its tests");
    let owner_guard = &owner_source[helper_start..helper_end];
    for owner in [
        "finite_table_owner_current",
        "const_interp_owner_current",
        "bv_owner_current",
        "cegqi_owner_current",
        "has_current_model_free_mbqi_sat_authority",
        "has_current_model_bound_quantified_sat_authority",
    ] {
        assert!(
            owner_guard.contains(owner),
            "missing current owner `{owner}`"
        );
    }
    assert!(
        owner_guard
            .contains("!quantified_owner_current && self.try_finite_model_sat_certificate()"),
        "the finite producer must be current-owner gated"
    );

    let independent = read("src/executor/model/independent_gate.rs");
    let gate_start = independent
        .find("pub(in crate::executor) fn apply_quantified_model_failclosed_gate(")
        .expect("independent gate must define the quantified publication gate");
    assert!(
        !independent[gate_start..].contains("try_finite_model_sat_certificate("),
        "the post-strict quantified gate must remain consult-only"
    );

    let finite_model = read("src/executor/finite_model_mbqi.rs");
    let scope_start = finite_model
        .find("fn finite_model_plain_sat_scope(")
        .expect("finite-model lane must define one optimization-scope guard");
    let scope = &finite_model[scope_start..];
    assert!(
        scope.contains("self.ctx.objectives().is_empty()")
            && scope.contains("self.ctx.soft_constraints().is_empty()")
            && finite_model
                .matches("self.finite_model_plain_sat_scope()")
                .count()
                == 2
            && finite_model
                .matches("finite_model_certificate_pass(")
                .count()
                == 3,
        "every certificate-pass entry must decline optimization scope"
    );

    // Native API softs live above the frontend context at rest. Pin their
    // transaction ordering so the scope guard sees them for the whole solve.
    let native_maxsmt = read("src/api/solving/maxsmt.rs");
    let install_native = native_maxsmt
        .find(".replace_soft_constraints(native_softs)")
        .expect("native MaxSMT must install its soft set");
    let execute = native_maxsmt
        .find("self.executor.execute_native_maxsmt_check_sat()")
        .expect("native MaxSMT must enter the executor once");
    let restore_parsed = native_maxsmt
        .find(".replace_soft_constraints(parsed_softs)")
        .expect("native MaxSMT must restore parsed softs");
    assert!(
        install_native < execute && execute < restore_parsed,
        "native softs must remain visible throughout the executor solve"
    );
}

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
        // BOUNDARY AUDIT, 2026-08-25. One callsite, `exec.execute_authored(&command)`
        // at `command_deadline_tests.rs:115`, inside
        // `#[test] fn control_lifetime_command_publication_restores_deadline_after_
        // elaboration_error`, asserting `.is_err()` on an undeclared assumption.
        // It exercises an ERROR path and publishes nothing. The whole file is
        // `#[test]` items and reaches the build only through
        // `include!("check_sat/command_deadline_tests.rs")` at `check_sat.rs:5169`,
        // which sits inside the `#[cfg(test)]` item opened at `check_sat.rs:5030`.
        // It therefore cannot widen a production authority boundary.
        "crates/ay-dpll/src/executor/check_sat/command_deadline_tests.rs",
    ];
    for source in sources {
        let relative = source
            .strip_prefix(&workspace)
            .expect("enumerated source is below workspace")
            .to_string_lossy();
        if is_chokepoint_source_fixture(relative.as_ref()) {
            continue;
        }
        let raw = std::fs::read_to_string(&source)
            .unwrap_or_else(|error| panic!("cannot read {}: {error}", source.display()));
        // Audit CODE. A doc comment naming an entrypoint is not a callsite —
        // `executor/query_role.rs` links `Executor::execute_authored` purely to
        // explain why that entrypoint is a method rather than a command.
        let text = code_without_comments(&raw);
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
    if normalize_whitespace(&text).contains(&format!("#[cfg(test)] mod {stem};")) {
        return true;
    }
    // Second mechanism, same guarantee: the parent pulls the file in with
    // `include!` from a site that lies INSIDE a `#[cfg(test)]` item, so the
    // file reaches only test builds exactly as a `#[cfg(test)] mod` would.
    //
    // Checked POSITIONALLY, never as "the parent mentions cfg(test) somewhere":
    // a production `include!` in a file that also happens to carry a test module
    // must still require an explicit audit. Comments are stripped first so a
    // commented-out attribute cannot open a span.
    let Some(dir_name) = parent_dir.file_name().and_then(|name| name.to_str()) else {
        return false;
    };
    include_site_is_cfg_test(
        &code_without_comments(&text),
        &format!("{dir_name}/{stem}.rs"),
    )
}

/// True when `include!("<needle>")` appears inside a `#[cfg(test)]` item.
fn include_site_is_cfg_test(code: &str, needle: &str) -> bool {
    let Some(site) = code.find(&format!("include!(\"{needle}\")")) else {
        return false;
    };
    cfg_test_spans(code)
        .into_iter()
        .any(|(open, close)| site > open && site < close)
}

/// Byte ranges of every `#[cfg(test)]` item body in `code`, as `(open, close)`
/// offsets of its outermost braces.
fn cfg_test_spans(code: &str) -> Vec<(usize, usize)> {
    const ATTR: &str = "#[cfg(test)]";
    let bytes = code.as_bytes();
    let mut spans = Vec::new();
    let mut cursor = 0usize;
    while let Some(offset) = code[cursor..].find(ATTR) {
        let attr = cursor + offset;
        cursor = attr + ATTR.len();
        let Some(brace) = code[cursor..].find('{') else {
            break;
        };
        let open = cursor + brace;
        let mut depth = 0usize;
        for (index, byte) in bytes.iter().enumerate().skip(open) {
            match byte {
                b'{' => depth += 1,
                b'}' => {
                    depth -= 1;
                    if depth == 0 {
                        spans.push((open, index));
                        break;
                    }
                }
                _ => {}
            }
        }
    }
    spans
}

#[test]
fn cfg_test_include_recognition_is_positional_not_incidental() {
    // ACCEPTED: the include site is inside the `#[cfg(test)]` item.
    let inside = "#[cfg(test)]\nmod tests {\n    include!(\"d/f.rs\");\n}\n";
    assert!(include_site_is_cfg_test(inside, "d/f.rs"));

    // REFUSED: a production include in a file that ALSO carries a test module.
    // This is the vacuity the positional check exists to prevent.
    let outside = "include!(\"d/f.rs\");\n#[cfg(test)]\nmod tests {\n    fn t() {}\n}\n";
    assert!(
        !include_site_is_cfg_test(outside, "d/f.rs"),
        "a production include! must still require an explicit boundary audit"
    );

    // REFUSED: the include sits after the test item has closed.
    let after = "#[cfg(test)]\nmod tests {\n    fn t() {}\n}\ninclude!(\"d/f.rs\");\n";
    assert!(!include_site_is_cfg_test(after, "d/f.rs"));

    // REFUSED: a different file's include does not vouch for this one.
    assert!(!include_site_is_cfg_test(inside, "d/other.rs"));
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
            Some(src[..arm_start].matches('\n').count()..=src[..arm_end].matches('\n').count())
        } else {
            None
        };
        for (lineno, line) in src.lines().enumerate() {
            if !line.contains("Ok(SolveResult::Sat)") {
                continue;
            }
            let trimmed = line.trim_start();
            let is_match_arm = line.contains("=>");
            let is_comment = trimmed.starts_with("//") || trimmed.starts_with('*');
            let is_audited_deferral = deferral_arm_lines
                .as_ref()
                .is_some_and(|lines| lines.contains(&lineno));
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
