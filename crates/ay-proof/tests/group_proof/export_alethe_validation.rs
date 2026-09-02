// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering};

use ay_core::kani_compat::{det_hash_map_new, DetHashMap};
use ay_core::{FarkasAnnotation, LiaAnnotation, Proof, Sort, TermId, TermStore, TheoryLemmaKind};
use ay_proof::{
    check_alethe_document, check_proof_strict, export_alethe, export_alethe_with_problem_scope,
    export_alethe_with_problem_scope_and_overrides, ProblemScope,
};
use num_bigint::BigInt;

static TEMP_FILE_SEQ: AtomicU64 = AtomicU64::new(0);

const QF_BOOL_AND_UNSAT: &str = r#"
(set-logic QF_BOOL)
(declare-const a Bool)
(declare-const b Bool)
(assert (and a b))
(assert (not b))
(check-sat)
"#;

const QF_LRA_UNSAT: &str = r#"
(set-logic QF_LRA)
(declare-const x Real)
(assert (<= x 5.0))
(assert (<= 10.0 x))
(check-sat)
"#;

const QF_LIA_UNSAT: &str = r#"
(set-logic QF_LIA)
(declare-const x Int)
(assert (<= x 5))
(assert (<= 10 x))
(check-sat)
"#;

#[test]
fn exports_clausification_rule_args_in_alethe_syntax() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let and_ab = terms.mk_and(vec![a, b]);
    let or_ab = terms.mk_or(vec![a, b]);
    let not_and_ab = terms.mk_not_raw(and_ab);
    let not_b = terms.mk_not(b);

    let mut proof = Proof::new();
    proof.add_rule_step(
        ay_core::AletheRule::AndPos(1),
        vec![not_and_ab, b],
        vec![],
        vec![and_ab],
    );
    proof.add_rule_step(
        ay_core::AletheRule::OrNeg,
        vec![or_ab, not_b],
        vec![],
        vec![or_ab],
    );

    let output = export_alethe(&proof, &terms);
    assert!(
        output.contains("(step t0 (cl (not (and a b)) b) :rule and_pos :args (1))"),
        "{output}"
    );
    assert!(
        output.contains("(step t1 (cl (or a b) (not b)) :rule or_neg :args (1))"),
        "{output}"
    );
    assert!(
        !output.contains(":args ((and a b))"),
        "internal source-term arg must not leak into Alethe output:\n{output}"
    );
    assert!(
        !output.contains(":args ((or a b))"),
        "internal source-term arg must not leak into Alethe output:\n{output}"
    );
}

#[test]
fn exports_boolean_and_certificate_that_carcara_accepts() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let and_ab = terms.mk_and(vec![a, b]);
    let not_and_ab = terms.mk_not_raw(and_ab);
    let not_b = terms.mk_not(b);

    let mut proof = Proof::new();
    let h0 = proof.add_assume(and_ab, None);
    let t1 = proof.add_rule_step(
        ay_core::AletheRule::AndPos(1),
        vec![not_and_ab, b],
        vec![],
        vec![and_ab],
    );
    let t2 = proof.add_resolution(vec![b], and_ab, h0, t1);
    let h3 = proof.add_assume(not_b, None);
    proof.add_resolution(vec![], b, t2, h3);

    check_proof_strict(&proof, &terms).expect("Boolean proof should validate strictly");

    let alethe = export_alethe_with_problem_scope(&proof, &terms, &[and_ab, not_b]);
    assert!(
        alethe.contains(":rule and_pos :args (1)"),
        "expected translated and_pos args:\n{alethe}"
    );
    assert_carcara_accepts("bool_and", QF_BOOL_AND_UNSAT, &alethe);
}

include!("export_alethe_validation/linear_arithmetic.rs");
include!("export_alethe_validation/let_bridge_resolution.rs");

const QF_EQ_TRANS_DISTINCT_UNSAT: &str = r#"
(set-logic QF_UFLIA)
(declare-const i0 Int)
(declare-const i1 Int)
(declare-const i2 Int)
(assert (= i0 i1))
(assert (distinct i2 i0))
(assert (= i1 i2))
(check-sat)
"#;

const QF_EQ_TRANS_SYMM_UNSAT: &str = r#"
(set-logic QF_UFLIA)
(declare-const i0 Int)
(declare-const i1 Int)
(assert (distinct i0 i1))
(assert (= i1 i0))
(check-sat)
"#;

/// A three-hypothesis `eq_transitive` theory lemma whose middle hypothesis
/// prints in AY's `(distinct i1 i2)` surface spelling (the internal
/// `(not (= i1 i2))`). Carcara rejects `eq_transitive` and `th_resolution`
/// over the opaque `distinct` atom directly; the printer must resugar the
/// chain into `eq_transitive` over `(not (= …))` forms plus `distinct_elim`/
/// `equiv2` bridges (this is exactly the arrays-uf `A4_rand_15` refutation).
#[test]
fn exports_eq_transitive_distinct_certificate_that_carcara_accepts() {
    let mut terms = TermStore::new();
    let i0 = terms.mk_var("i0", Sort::Int);
    let i1 = terms.mk_var("i1", Sort::Int);
    let i2 = terms.mk_var("i2", Sort::Int);
    let eq_i0_i1 = terms.mk_eq(i0, i1);
    let eq_i2_i0 = terms.mk_eq(i2, i0);
    let eq_i1_i2 = terms.mk_eq(i1, i2);
    let eq_i0_i2 = terms.mk_eq(i0, i2);
    let not_eq_i0_i1 = terms.mk_not(eq_i0_i1);
    let not_eq_i2_i0 = terms.mk_not(eq_i2_i0); // printed `(distinct i2 i0)`
    let not_eq_i1_i2 = terms.mk_not(eq_i1_i2); // printed `(distinct i1 i2)`

    let mut proof = Proof::new();
    let t0 = proof.add_assume(eq_i0_i1, None);
    let t1 = proof.add_assume(not_eq_i2_i0, None);
    let t2 = proof.add_assume(eq_i1_i2, None);
    let t3 = proof.add_theory_lemma_with_kind(
        "EUF",
        vec![not_eq_i0_i1, not_eq_i1_i2, eq_i0_i2],
        TheoryLemmaKind::EufTransitive,
    );
    let t4 = proof.add_rule_step(
        ay_core::AletheRule::ThResolution,
        vec![not_eq_i1_i2, eq_i0_i2],
        vec![t3, t0],
        vec![],
    );
    let t5 = proof.add_rule_step(
        ay_core::AletheRule::ThResolution,
        vec![eq_i0_i2],
        vec![t4, t2],
        vec![],
    );
    proof.add_rule_step(
        ay_core::AletheRule::ThResolution,
        vec![],
        vec![t5, t1],
        vec![],
    );

    let mut overrides: DetHashMap<TermId, String> = det_hash_map_new();
    overrides.insert(not_eq_i2_i0, "(distinct i2 i0)".to_string());
    overrides.insert(not_eq_i1_i2, "(distinct i1 i2)".to_string());

    let alethe = export_alethe_with_problem_scope_and_overrides(
        &proof,
        &terms,
        &[eq_i0_i1, not_eq_i2_i0, eq_i1_i2],
        Some(&overrides),
    );
    assert!(
        !alethe.contains("(distinct i1 i2) (= i0 i2)) :rule eq_transitive"),
        "invented distinct-form eq_transitive must be resugared:\n{alethe}"
    );
    assert!(
        alethe.contains(":rule eq_transitive")
            && alethe.contains(":rule distinct_elim")
            && alethe.contains(":rule equiv2"),
        "expected resugared eq_transitive + distinct bridge:\n{alethe}"
    );
    assert_carcara_accepts(
        "eq_transitive_distinct",
        QF_EQ_TRANS_DISTINCT_UNSAT,
        &alethe,
    );
}

/// The degenerate two-literal symmetry tautology `(cl (not (= i0 i1))
/// (= i1 i0))` that AY labels `eq_transitive` — Carcara rejects it because
/// `eq_transitive` needs at least two hypotheses. The printer must pad it
/// with a reflexive hypothesis and an `eq_reflexive` unit (the arrays-uf
/// `A4_rand_13` refutation).
#[test]
fn exports_degenerate_eq_transitive_certificate_that_carcara_accepts() {
    let mut terms = TermStore::new();
    let i0 = terms.mk_var("i0", Sort::Int);
    let i1 = terms.mk_var("i1", Sort::Int);
    let eq_i0_i1 = terms.mk_eq(i0, i1);
    let eq_i1_i0 = terms.mk_eq(i1, i0);
    let not_eq_i0_i1 = terms.mk_not(eq_i0_i1); // printed `(distinct i0 i1)`

    let mut proof = Proof::new();
    let t0 = proof.add_assume(not_eq_i0_i1, None);
    let t1 = proof.add_assume(eq_i1_i0, None);
    let t2 = proof.add_theory_lemma_with_kind(
        "EUF",
        vec![not_eq_i0_i1, eq_i1_i0],
        TheoryLemmaKind::EufTransitive,
    );
    let t3 = proof.add_rule_step(
        ay_core::AletheRule::ThResolution,
        vec![eq_i1_i0],
        vec![t2, t1],
        vec![],
    );
    proof.add_rule_step(
        ay_core::AletheRule::ThResolution,
        vec![],
        vec![t3, t0],
        vec![],
    );

    let mut overrides: DetHashMap<TermId, String> = det_hash_map_new();
    overrides.insert(not_eq_i0_i1, "(distinct i0 i1)".to_string());

    let alethe = export_alethe_with_problem_scope_and_overrides(
        &proof,
        &terms,
        &[not_eq_i0_i1, eq_i1_i0],
        Some(&overrides),
    );
    assert!(
        alethe.contains(":rule eq_reflexive"),
        "degenerate eq_transitive must be padded with a reflexive hypothesis:\n{alethe}"
    );
    assert_carcara_accepts("degenerate_eq_transitive", QF_EQ_TRANS_SYMM_UNSAT, &alethe);
}

const QF_BOOL_RENESTED_AND_UNSAT: &str = r#"
(set-logic QF_BOOL)
(declare-const a Bool)
(declare-const b Bool)
(declare-const c Bool)
(assert (and a (and b c)))
(assert (not c))
(check-sat)
"#;

const QF_BOOL_FLATTENED_AND_UNSAT: &str = r#"
(set-logic QF_BOOL)
(declare-const a Bool)
(declare-const b Bool)
(declare-const c Bool)
(assert (and a b c))
(assert (not (and b c)))
(check-sat)
"#;

/// A raw-gate `and_pos` over AY's FLAT internal conjunction whose surface
/// override re-nests the authored grouping `(and a (and b c))`: the indexed
/// conjunct is a deeper printed operand, bridged by the printed-nesting
/// navigator. The exported document must be spec-valid Alethe end to end.
#[test]
fn exports_renested_surface_and_pos_certificate_that_carcara_accepts() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let c = terms.mk_var("c", Sort::Bool);
    let source = terms.mk_and(vec![a, b, c]);
    let gate = terms.mk_not_raw(source);
    let not_c = terms.mk_not_raw(c);

    let mut proof = Proof::new();
    let h0 = proof.add_assume(source, None);
    let t1 = proof.add_rule_step(
        ay_core::AletheRule::AndPos(2),
        vec![gate, c],
        vec![],
        vec![source],
    );
    let t2 = proof.add_resolution(vec![c], source, h0, t1);
    let h3 = proof.add_assume(not_c, None);
    proof.add_resolution(vec![], c, t2, h3);
    check_proof_strict(&proof, &terms).expect("re-nested surface proof should validate strictly");

    let mut overrides: DetHashMap<TermId, String> = det_hash_map_new();
    overrides.insert(source, "(and a (and b c))".to_string());
    let alethe = export_alethe_with_problem_scope_and_overrides(
        &proof,
        &terms,
        &[source, not_c],
        Some(&overrides),
    );
    assert!(
        alethe.contains(
            "(step t1.g0 (cl (not (and a (and b c))) (and b c)) :rule and_pos :args (1))"
        ),
        "expected the navigator hop chain:\n{alethe}"
    );
    assert!(!alethe.contains(":rule hole"), "{alethe}");
    assert!(!alethe.contains(":rule trust"), "{alethe}");
    // The strict publication gate (`--proof-self-check`) refuses any
    // document AY's own round-trip checker rejects; a bridge that only
    // carcara accepts would still fail publication.
    check_alethe_document(
        &alethe,
        &ProblemScope::from_smtlib_source(QF_BOOL_RENESTED_AND_UNSAT),
    )
    .expect("AY's native round-trip checker must accept the navigator bridge");
    assert_carcara_accepts("renested_and_pos", QF_BOOL_RENESTED_AND_UNSAT, &alethe);
}

/// A raw-gate `and_pos` whose indexed conjunct is an and-term ERASED by
/// surface flattening (`(and a (and b c))` printed `(and a b c)`): projected
/// child-by-child off the flat surface and reassembled via `and_neg` +
/// resolution. The exported document must be spec-valid Alethe end to end.
#[test]
fn exports_flattened_conjunct_and_pos_certificate_that_carcara_accepts() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let c = terms.mk_var("c", Sort::Bool);
    let inner = terms.mk_app(ay_core::Symbol::named("and"), vec![b, c], Sort::Bool);
    let source = terms.mk_app(ay_core::Symbol::named("and"), vec![a, inner], Sort::Bool);
    let gate = terms.mk_not_raw(source);
    let not_inner = terms.mk_not_raw(inner);

    let mut proof = Proof::new();
    let h0 = proof.add_assume(source, None);
    let t1 = proof.add_rule_step(
        ay_core::AletheRule::AndPos(1),
        vec![gate, inner],
        vec![],
        vec![source],
    );
    let t2 = proof.add_resolution(vec![inner], source, h0, t1);
    let h3 = proof.add_assume(not_inner, None);
    proof.add_resolution(vec![], inner, t2, h3);
    check_proof_strict(&proof, &terms).expect("flattened-conjunct proof should validate strictly");

    let mut overrides: DetHashMap<TermId, String> = det_hash_map_new();
    overrides.insert(source, "(and a b c)".to_string());
    let alethe = export_alethe_with_problem_scope_and_overrides(
        &proof,
        &terms,
        &[source, not_inner],
        Some(&overrides),
    );
    assert!(
        alethe.contains("(step t1.fa (cl (and b c) (not b) (not c)) :rule and_neg)"),
        "expected the and_neg reassembly bridge:\n{alethe}"
    );
    assert!(!alethe.contains(":rule hole"), "{alethe}");
    assert!(!alethe.contains(":rule trust"), "{alethe}");
    // The strict publication gate (`--proof-self-check`) refuses any
    // document AY's own round-trip checker rejects; a bridge that only
    // carcara accepts would still fail publication.
    check_alethe_document(
        &alethe,
        &ProblemScope::from_smtlib_source(QF_BOOL_FLATTENED_AND_UNSAT),
    )
    .expect("AY's native round-trip checker must accept the and_neg reassembly bridge");
    assert_carcara_accepts("flattened_and_pos", QF_BOOL_FLATTENED_AND_UNSAT, &alethe);
}

fn assert_carcara_accepts(label: &str, problem: &str, proof: &str) {
    assert_carcara_verdict(label, problem, proof, "valid");
}

fn assert_carcara_verdict(label: &str, problem: &str, proof: &str, expected: &str) {
    let Some(carcara) = find_carcara() else {
        eprintln!("carcara not found, skipping external Alethe validation for {label}");
        return;
    };

    let (problem_path, proof_path) = write_problem_and_proof(label, problem, proof);
    let output = Command::new(carcara)
        .arg("check")
        .arg("--")
        .arg(&proof_path)
        .arg(&problem_path)
        .output()
        .expect("run carcara check");

    let _ = std::fs::remove_file(&problem_path);
    let _ = std::fs::remove_file(&proof_path);

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    let status_matches = output.status.success() || expected == "invalid";
    assert!(
        status_matches && stdout.trim() == expected,
        "carcara verdict mismatch for generated Alethe proof ({label})\n\
         expected: {expected}\nstdout: {stdout}\nstderr: {stderr}\nproof:\n{proof}"
    );
}

fn find_carcara() -> Option<PathBuf> {
    if let Ok(path) = std::env::var("CARCARA_PATH") {
        let path = PathBuf::from(path);
        if path.is_file() {
            return Some(path);
        }
    }

    let candidates = [
        PathBuf::from("/usr/local/bin/carcara"),
        PathBuf::from("/opt/homebrew/bin/carcara"),
    ];
    for candidate in candidates {
        if candidate.is_file() {
            return Some(candidate);
        }
    }

    let path_var = std::env::var_os("PATH")?;
    for dir in std::env::split_paths(&path_var) {
        let candidate = dir.join("carcara");
        if candidate.is_file() {
            return Some(candidate);
        }
    }
    None
}

fn write_problem_and_proof(label: &str, problem: &str, proof: &str) -> (PathBuf, PathBuf) {
    let run_id = TEMP_FILE_SEQ.fetch_add(1, Ordering::Relaxed);
    let suffix = format!("{}_{}_{}", label, std::process::id(), run_id);
    let problem_path = std::env::temp_dir().join(format!("ay_proof_problem_{suffix}.smt2"));
    let proof_path = std::env::temp_dir().join(format!("ay_proof_proof_{suffix}.alethe"));

    std::fs::write(&problem_path, problem).unwrap_or_else(|e| {
        panic!(
            "failed to write problem file {}: {e}",
            display_path(&problem_path)
        )
    });
    std::fs::write(&proof_path, proof).unwrap_or_else(|e| {
        panic!(
            "failed to write proof file {}: {e}",
            display_path(&proof_path)
        )
    });

    (problem_path, proof_path)
}

fn display_path(path: &Path) -> String {
    path.display().to_string()
}
