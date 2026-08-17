// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! End-to-end external validation of conjunctive provenance-OR emission.

use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::{AletheRule, Proof, ProofStep, TheoryLemmaKind};
use ntest::timeout;

use super::and_conflict_fixture::{equality, four_branch_fixture, numeral, plan_fixture, symbol};
use super::ProvenanceOrPlan;
use crate::executor::proof_surface_syntax::collect_surface_term_overrides;
use crate::executor::proof_trust_surgery_provenance::ProvenanceSurfaceAudit;

static TEMP_FILE_SEQUENCE: AtomicU64 = AtomicU64::new(0);

const PROBLEM: &str = r#"
(set-logic QF_LIA)
(declare-const v0 Int)
(declare-const v1 Int)
(declare-const v0_1 Int)
(declare-const v1_1 Int)
(declare-const p Bool)
(declare-const q Bool)
(declare-const r Bool)
(declare-const and_or_goal_left Bool)
(declare-const and_or_goal_right Bool)
(assert
  (or
    (and (= v0 0) (ite p q r) (= v1_1 1) (= v0_1 0))
    (and (= v0 0) (= v1_1 1) (= v0_1 0) (= v1 1))
    (and (or p q) (= v1 1) (= v0_1 1))
    (and (ite p q r) (= v0 1) (= v1_1 1))))
(assert (= v0 0))
(assert (= v1 0))
(assert (= v0_1 1))
(assert (not (or and_or_goal_left and_or_goal_right)))
(check-sat)
"#;

fn workspace_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .expect("workspace root")
        .to_path_buf()
}

fn find_carcara() -> Option<PathBuf> {
    if let Ok(path) = std::env::var("CARCARA_PATH") {
        let path = PathBuf::from(path);
        if path.is_file() {
            return Some(path);
        }
    }
    for candidate in [
        workspace_root().join("bin/carcara"),
        workspace_root().join("reference/carcara/target/release/carcara"),
        workspace_root().join("reference/carcara/target/researcher_20/release/carcara"),
        PathBuf::from("/tmp/carcara/target/release/carcara"),
        PathBuf::from("/usr/local/bin/carcara"),
        PathBuf::from("/opt/homebrew/bin/carcara"),
    ] {
        if candidate.is_file() {
            return Some(candidate);
        }
    }
    let path = std::env::var_os("PATH")?;
    std::env::split_paths(&path)
        .map(|directory| directory.join("carcara"))
        .find(|candidate| candidate.is_file())
}

fn require_carcara_or_skip() -> Option<PathBuf> {
    if let Some(path) = find_carcara() {
        return Some(path);
    }
    assert!(
        std::env::var_os("CI").is_none(),
        "carcara is mandatory in CI for the conjunctive provenance-OR external test",
    );
    eprintln!("carcara not found; skipping conjunctive provenance-OR external test");
    None
}

fn keep_artifacts() -> bool {
    ay_core::misc_cli_flags().keep_alethe_artifacts
}

fn assert_carcara_valid(carcara: &Path, proof: &str) {
    let sequence = TEMP_FILE_SEQUENCE.fetch_add(1, Ordering::Relaxed);
    let stem = format!(
        "ay_conjunctive_provenance_or_{}_{}",
        std::process::id(),
        sequence,
    );
    let problem_path = std::env::temp_dir().join(format!("{stem}.smt2"));
    let proof_path = std::env::temp_dir().join(format!("{stem}.alethe"));
    std::fs::write(&problem_path, PROBLEM).expect("write conjunctive OR problem");
    std::fs::write(&proof_path, proof).expect("write conjunctive OR proof");

    let output = std::process::Command::new(carcara)
        .arg("check")
        .arg("--expand-let-bindings")
        .arg("--")
        .arg(&proof_path)
        .arg(&problem_path)
        .output()
        .expect("run trust-free carcara check");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    let valid = output.status.success() && stdout.trim() == "valid";
    if keep_artifacts() || !valid {
        eprintln!(
            "Preserving conjunctive OR artifacts: smt2={} alethe={}",
            problem_path.display(),
            proof_path.display(),
        );
    } else {
        let _ = std::fs::remove_file(&problem_path);
        let _ = std::fs::remove_file(&proof_path);
    }
    assert!(
        valid,
        "carcara rejected conjunctive provenance-OR proof: status={:?} stdout={} stderr={}",
        output.status.code(),
        stdout.trim(),
        stderr.trim(),
    );
}

#[test]
#[timeout(60_000)]
fn conjunctive_provenance_or_plan_emits_trust_free_carcara_proof() {
    let mut fixture = four_branch_fixture();
    assert_eq!(
        ay_proof::format_term_alethe(&fixture.executor.ctx.terms, fixture.not_goal),
        "(not (or and_or_goal_left and_or_goal_right))",
        "the raw downstream premise must match the external problem assertion",
    );
    let expected_pairs = [
        (("v0_1", "0"), ("v0_1", "1")),
        (("v0_1", "0"), ("v0_1", "1")),
        (("v1", "1"), ("v1", "0")),
        (("v0", "1"), ("v0", "0")),
    ];
    let expected_terms = expected_pairs.map(|((row, row_value), (support, support_value))| {
        let row = equality(symbol(row), numeral(row_value));
        let support = equality(symbol(support), numeral(support_value));
        (
            fixture
                .executor
                .ctx
                .elaborate_surface_subterm(&row)
                .expect("selected row elaborates"),
            fixture
                .executor
                .ctx
                .elaborate_surface_subterm(&support)
                .expect("selected support elaborates"),
        )
    });
    let concrete = plan_fixture(&mut fixture);
    assert_eq!(concrete.authored_sources, fixture.provenance_sources);
    assert_eq!(concrete.refutations.len(), expected_terms.len());
    for (refutation, &(row, support)) in concrete.refutations.iter().zip(&expected_terms) {
        assert_eq!(refutation.conjunct, row);
        assert_eq!(refutation.lemma.supports, [support]);
        assert_eq!(refutation.lemma.clause.len(), 2);
        assert_eq!(refutation.lemma.farkas.coefficients.len(), 2);
    }
    let plan = ProvenanceOrPlan::ConjunctiveConflict(concrete);

    let mut proof = Proof::new();
    let mut authored_assumes = HashMap::default();
    for &source in plan.authored_sources() {
        authored_assumes.insert(source, proof.add_assume(source, None));
    }
    let terminal = fixture
        .executor
        .emit_provenance_or(&mut proof, &plan, &authored_assumes)
        .expect("production conjunctive OR emitter accepts its checked plan");
    let not_goal = proof.add_assume(fixture.not_goal, None);
    proof.add_resolution(Vec::new(), fixture.goal, terminal, not_goal);
    assert!(matches!(
        proof.steps.last(),
        Some(ProofStep::Resolution { clause, .. }) if clause.is_empty()
    ));
    let quality = ay_proof::check_proof_strict_with_context(
        &proof,
        &fixture.executor.ctx.terms,
        None,
        None,
        Some(&fixture.problem_scope),
    )
    .expect("native strict checker accepts the complete contextual proof");
    assert_eq!(quality.trust_count, 0);
    assert_eq!(
        proof
            .steps
            .iter()
            .filter(|step| matches!(
                step,
                ProofStep::Step {
                    rule: AletheRule::AndPos(_),
                    ..
                }
            ))
            .count(),
        4,
    );
    assert_eq!(
        proof
            .steps
            .iter()
            .filter(|step| matches!(
                step,
                ProofStep::Step {
                    rule: AletheRule::Or,
                    ..
                }
            ))
            .count(),
        1,
    );
    assert_eq!(
        proof
            .steps
            .iter()
            .filter(|step| matches!(
                step,
                ProofStep::TheoryLemma {
                    kind: TheoryLemmaKind::LraFarkas,
                    clause,
                    farkas: Some(_),
                    ..
                } if clause.len() == 2
            ))
            .count(),
        4,
    );

    let mut overrides = HashMap::default();
    let mut audit = ProvenanceSurfaceAudit::default();
    for (canonical, parsed) in &fixture.originals {
        assert!(collect_surface_term_overrides(
            &mut fixture.executor.ctx,
            *canonical,
            parsed,
            &mut overrides,
        ));
        assert!(audit.require_original(&mut fixture.executor.ctx, &fixture.originals, *canonical,));
    }
    plan.protect_surface_operands(&mut audit, &mut fixture.executor.ctx.terms);
    assert!(audit.active_map_is_bounded(&overrides));
    assert!(audit.validate_effective(&fixture.executor.ctx.terms, &overrides));

    let rendered = ay_proof::try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        &fixture.executor.ctx.terms,
        &fixture.problem_scope,
        Some(&overrides),
    )
    .expect("surface-audited conjunctive OR proof exports fallibly");
    assert!(!rendered.contains(":rule trust"));
    assert!(!rendered.contains(":rule hole"));
    assert_eq!(
        rendered
            .lines()
            .filter(|line| line.contains(":rule or :premises"))
            .count(),
        1,
        "expected one authenticated source-OR decomposition:\n{rendered}",
    );
    let la_lines: Vec<_> = rendered
        .lines()
        .filter(|line| line.contains(":rule la_generic"))
        .collect();
    assert_eq!(
        la_lines.len(),
        4,
        "expected four Farkas conflicts:\n{rendered}"
    );
    let and_lines: Vec<_> = rendered
        .lines()
        .filter(|line| line.contains(":rule and_pos"))
        .collect();
    assert_eq!(
        and_lines.len(),
        4,
        "expected four AND projections:\n{rendered}"
    );
    let expected_surface_pairs = [
        ("(= v0_1 0)", "(= v0_1 1)"),
        ("(= v0_1 0)", "(= v0_1 1)"),
        ("(= v1 1)", "(= v1 0)"),
        ("(= v0 1)", "(= v0 0)"),
    ];
    for ((line, and_line), &(row, support)) in
        la_lines.iter().zip(&and_lines).zip(&expected_surface_pairs)
    {
        let negated_row = format!("(not {row})");
        let negated_support = format!("(not {support})");
        assert!(
            line.contains(&negated_row) && line.contains(&negated_support),
            "wrong support-bearing Farkas row for {row}: {line}",
        );
        assert!(
            and_line.contains("(and ") && and_line.contains(row),
            "wrong authenticated AND projection for {row}: {and_line}",
        );
    }
    let Some(carcara) = require_carcara_or_skip() else {
        return;
    };
    assert_carcara_valid(&carcara, &rendered);
}
