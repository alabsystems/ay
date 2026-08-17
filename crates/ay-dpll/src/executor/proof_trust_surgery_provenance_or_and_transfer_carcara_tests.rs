// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! External validation of the real conjunctive-transfer planner and emitter.

use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::{AletheRule, Proof, ProofStep, TheoryLemmaKind};
use ntest::timeout;

use super::super::ProvenanceOrPlan;
use super::tests::{plan_fixture, transfer_fixture};
use crate::executor::proof_surface_syntax::collect_surface_term_overrides;
use crate::executor::proof_trust_surgery_provenance::ProvenanceSurfaceAudit;

static TEMP_FILE_SEQUENCE: AtomicU64 = AtomicU64::new(0);

const PROBLEM: &str = r#"
(set-logic QF_LIA)
(declare-const transfer_x Int)
(declare-const transfer_y Int)
(declare-const transfer_p Bool)
(declare-const transfer_q Bool)
(assert
  (or
    (and (= transfer_x 0) (= transfer_y 0) transfer_p)
    (and (= transfer_x 1) transfer_q)))
(assert (= transfer_x 0))
(assert (= transfer_y 0))
(assert
  (not
    (or
      (and true true transfer_p)
      (and false transfer_q))))
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
        "carcara is mandatory in CI for conjunctive-transfer export",
    );
    eprintln!("carcara not found; skipping conjunctive-transfer external test");
    None
}

fn assert_carcara_valid(carcara: &Path, proof: &str) {
    let sequence = TEMP_FILE_SEQUENCE.fetch_add(1, Ordering::Relaxed);
    let stem = format!(
        "ay_conjunctive_transfer_{}_{}",
        std::process::id(),
        sequence,
    );
    let problem_path = std::env::temp_dir().join(format!("{stem}.smt2"));
    let proof_path = std::env::temp_dir().join(format!("{stem}.alethe"));
    std::fs::write(&problem_path, PROBLEM).expect("write transfer problem");
    std::fs::write(&proof_path, proof).expect("write transfer proof");
    let output = std::process::Command::new(carcara)
        .arg("check")
        .arg("--expand-let-bindings")
        .arg("--")
        .arg(&proof_path)
        .arg(&problem_path)
        .output()
        .expect("run carcara");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    let valid = output.status.success() && stdout.trim() == "valid";
    if valid && !ay_core::misc_cli_flags().keep_alethe_artifacts {
        let _ = std::fs::remove_file(&problem_path);
        let _ = std::fs::remove_file(&proof_path);
    } else {
        eprintln!(
            "Preserving transfer artifacts: smt2={} alethe={}",
            problem_path.display(),
            proof_path.display(),
        );
    }
    assert!(
        valid,
        "carcara rejected transfer proof: status={:?} stdout={} stderr={}",
        output.status.code(),
        stdout.trim(),
        stderr.trim(),
    );
}

#[test]
#[timeout(60_000)]
fn conjunctive_transfer_plan_emits_trust_free_carcara_proof() {
    let mut fixture = transfer_fixture();
    assert_eq!(
        ay_proof::format_term_alethe(&fixture.executor.ctx.terms, fixture.not_goal),
        "(not (or (and true true transfer_p) (and false transfer_q)))",
    );
    let concrete = plan_fixture(&mut fixture);
    let plan = ProvenanceOrPlan::ConjunctiveTransfer(concrete);
    let mut proof = Proof::new();
    let mut authored_assumes = HashMap::default();
    for &source in plan.authored_sources() {
        authored_assumes.insert(source, proof.add_assume(source, None));
    }
    let terminal = fixture
        .executor
        .emit_provenance_or(&mut proof, &plan, &authored_assumes)
        .expect("production transfer emitter accepts its checked plan");
    let not_goal = proof.add_assume(fixture.not_goal, None);
    proof.add_resolution(Vec::new(), fixture.goal, terminal, not_goal);
    let quality = ay_proof::check_proof_strict_with_context(
        &proof,
        &fixture.executor.ctx.terms,
        None,
        None,
        Some(&fixture.problem_scope),
    )
    .expect("contextual strict checker accepts transfer proof");
    assert_eq!(quality.trust_count, 0);
    assert!(proof.steps.iter().any(|step| matches!(
        step,
        ProofStep::Step {
            rule: AletheRule::AndNeg,
            ..
        }
    )));
    assert!(proof.steps.iter().any(|step| matches!(
        step,
        ProofStep::TheoryLemma {
            kind: TheoryLemmaKind::LraFarkas,
            ..
        }
    )));

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
    assert!(audit.validate_effective(&fixture.executor.ctx.terms, &overrides));
    let rendered = ay_proof::try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        &fixture.executor.ctx.terms,
        &fixture.problem_scope,
        Some(&overrides),
    )
    .expect("surface-audited transfer exports");
    assert!(!rendered.contains(":rule trust"));
    assert!(!rendered.contains(":rule hole"));
    for marker in [
        ":rule or :premises",
        ":rule and_pos",
        ":rule and_neg",
        ":rule true",
        ":rule or_neg",
        ":rule la_generic",
    ] {
        assert!(rendered.contains(marker), "missing {marker}:\n{rendered}");
    }
    assert!(
        rendered.contains("(and true true transfer_p)"),
        "and_neg must preserve duplicate true operands:\n{rendered}",
    );
    let Some(carcara) = require_carcara_or_skip() else {
        return;
    };
    assert_carcara_valid(&carcara, &rendered);
}
