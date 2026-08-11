// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::print_stderr)]

use ay_dpll::Executor;
use ay_frontend::parse;
use ntest::timeout;
use std::collections::BTreeSet;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::Arc;

static TEMP_FILE_SEQ: AtomicU64 = AtomicU64::new(0);

const QF_BOOL_UNSAT: &str = r#"
(set-logic QF_BOOL)
(declare-const a Bool)
(assert a)
(assert (not a))
(check-sat)
"#;

const QF_LRA_UNSAT: &str = r#"
(set-logic QF_LRA)
(declare-const x Real)
(assert (<= x 5.0))
(assert (>= x 10.0))
(check-sat)
"#;

const QF_UF_UNSAT: &str = r#"
(set-logic QF_UF)
(declare-sort U 0)
(declare-fun a () U)
(declare-fun b () U)
(declare-fun c () U)
(assert (= a b))
(assert (= b c))
(assert (not (= a c)))
(check-sat)
"#;

const QF_DT_FINITE_ENUM_PIGEONHOLE_UNSAT: &str = r#"
(set-logic QF_DT)
(declare-datatype Unit ((u0) (u1) (u2)))
(declare-const p0 Unit)
(declare-const p1 Unit)
(declare-const p2 Unit)
(declare-const p3 Unit)
(assert (not (= p0 p1)))
(assert (not (= p0 p2)))
(assert (not (= p0 p3)))
(assert (not (= p1 p2)))
(assert (not (= p1 p3)))
(assert (not (= p2 p3)))
(check-sat)
"#;

// Carcara 1.1.0 has no datatype parser or exhaustiveness rule. Give its proof
// checker the exact six authored assumptions over an uninterpreted carrier so
// it can validate every `assume` and resolution around the explicit `hole`.
// AY still solves and natively checks the real datatype problem above; this
// erased checker scope cannot turn the missing exhaustiveness inference into a
// valid external proof, and the required verdict remains `holey`.
const QF_DT_FINITE_ENUM_PIGEONHOLE_CARCARA_SCOPE: &str = r#"
(set-logic QF_UF)
(declare-sort Unit 0)
(declare-const p0 Unit)
(declare-const p1 Unit)
(declare-const p2 Unit)
(declare-const p3 Unit)
(assert (not (= p0 p1)))
(assert (not (= p0 p2)))
(assert (not (= p0 p3)))
(assert (not (= p1 p2)))
(assert (not (= p1 p3)))
(assert (not (= p2 p3)))
(check-sat)
"#;

const QF_UF_COMPOSED_AUTHORED_ROOT_UNSAT: &str = r#"
(set-logic QF_UF)
(declare-const x Int)
(declare-const y Int)
(declare-const z Int)
(assert (not (=> (and (= x y) (= y z)) (= x z))))
(check-sat)
"#;

const QF_LIA_COMPOSED_AUTHORED_ROOT_UNSAT: &str = r#"
(set-logic QF_LIA)
(declare-const x Int)
(declare-const y Int)
(assert (not (=> (and (= x 2) (= y 3)) (= (+ x y) 5))))
(check-sat)
"#;

const QF_AUFLIA_COMPOSED_ROW2_ROOT_UNSAT: &str = r#"
(set-logic QF_AUFLIA)
(declare-const a (Array Int Int))
(declare-const i Int)
(declare-const j Int)
(declare-const v Int)
(assert
  (not
    (=> (not (= i j))
        (= (select (store a i v) j) (select a j)))))
(check-sat)
"#;

const QF_LIA_LINEAR_AND_FOLD_UNSAT: &str = r#"
(set-logic QF_LIA)
(declare-fun x0 () Int)
(declare-fun x1 () Int)
(assert (and (<= (+ (* 1 x0) (* (- 1) x0)) (- 1))
             (<= (+ (* 1 x1) (* 0 x0)) 0)))
(check-sat)
"#;

const QF_LIA_LITERAL_FALSE_UNSAT: &str = r#"
(set-logic QF_LIA)
(assert false)
(check-sat)
"#;

const QF_LIA_MOD_ASSUMING_UNSAT: &str = r#"
(set-logic QF_LIA)
(declare-const x Int)
(assert (= (mod x 2) 0))
(check-sat-assuming ((= (mod x 2) 1)))
"#;

// Carcara 1.1.0 does not expose `check-sat-assuming` literals as original
// premises to its Alethe checker.  Replay the same active query scope as
// assertions so the independent checker can authenticate every `assume`
// command emitted for the query.  AY still produces the proof from the
// `check-sat-assuming` problem above, so this does not weaken its per-query
// authority boundary.
const QF_LIA_MOD_ASSUMING_CARCARA_SCOPE: &str = r#"
(set-logic QF_LIA)
(declare-const x Int)
(assert (= (mod x 2) 0))
(assert (= (mod x 2) 1))
(check-sat)
"#;

const QF_AUFLIA_LINEAR_ASSUMING_UNSAT: &str = r#"
(set-logic QF_AUFLIA)
(declare-const a (Array Int Int))
(declare-const x Int)
(assert (= (select a 0) x))
(check-sat-assuming ((> x 0) (<= (select a 0) 0)))
"#;

const QF_AUFLIA_LINEAR_ASSUMING_CARCARA_SCOPE: &str = r#"
(set-logic QF_AUFLIA)
(declare-const a (Array Int Int))
(declare-const x Int)
(assert (= (select a 0) x))
(assert (< 0 x))
(assert (<= (select a 0) 0))
(check-sat)
"#;

const QF_LRA_GUARDED_SPLIT_UNSAT: &str = r#"
(set-logic QF_LRA)
(declare-const gate Bool)
(declare-const x Real)
(declare-const y Real)
(declare-const z Real)
(assert (= x 1.0))
(assert (= y 0.0))
(assert (= z 1.0))
(assert (not gate))
(assert (or gate (not (= (+ x y) z))))
(check-sat)
"#;

const QF_LIA_LET_LINEAR_AND_FOLD_UNSAT: &str = r#"
(set-logic QF_LIA)
(declare-fun x0 () Int)
(declare-fun x1 () Int)
(assert (let ((?v_0 (* 1 x0)) (?v_1 (* (- 1) x0)))
  (and (<= (+ ?v_0 ?v_1) (- 1))
       (<= (+ (* 1 x1) (* 0 x0)) 0))))
(check-sat)
"#;

const QF_LIA_UNSAT: &str = r#"
(set-logic QF_LIA)
(declare-const x Int)
(assert (> x 10))
(assert (< x 5))
(check-sat)
"#;

fn arithmetic_ite_nonnegative_problem(
    extra_setup: &str,
    definition: &str,
    contradiction: &str,
) -> String {
    format!(
        r#"
(set-logic QF_LIA)
(declare-const A Int)
(declare-const B Int)
(declare-const C Int)
(declare-const D Int)
(declare-const E Int)
(declare-const F Int)
(declare-const G Int)
(declare-const H Int)
(declare-const I Int)
(declare-const J Int)
{extra_setup}
{definition}
(assert (= H (+ C F)))
(assert (= G (+ B 1)))
(assert (= F (+ A 1)))
(assert (= E (+ D G)))
(assert (>= D 0))
(assert (>= A 0))
(assert (>= B 0))
(assert (>= C 0))
{contradiction}
(check-sat)
"#
    )
}

const QF_UFLIA_UNSAT: &str = r#"
(set-logic QF_UFLIA)
(declare-const x Int)
(declare-const y Int)
(declare-fun f (Int) Int)
(assert (>= x 5))
(assert (<= x 5))
(assert (= y 5))
(assert (= (f x) 10))
(assert (= (f y) 20))
(check-sat)
"#;

const AUFLIA_EMATCHING_FORALL_EQUALITY_UNSAT: &str = r#"
(set-logic AUFLIA)
(declare-fun f (Int) Int)
(assert (forall ((x Int)) (! (> (f x) 0) :pattern ((f x)))))
(assert (= (f 7) (- 1)))
(check-sat)
"#;

const QF_ABV_PINNED_CONCAT_UNSAT: &str = r#"
(set-logic QF_ABV)
(declare-const tbl (Array (_ BitVec 24) (_ BitVec 32)))
(declare-const op (_ BitVec 8))
(declare-const lhs (_ BitVec 8))
(declare-const rhs (_ BitVec 8))
(declare-const out (_ BitVec 32))
(assert (= out (select tbl (concat op (concat lhs rhs)))))
(assert (= op #x01))
(assert (= (select tbl (concat #x01 (concat #x3f #x40))) #x40400000))
(assert (= lhs #x3f))
(assert (= rhs #x40))
(assert (distinct out #x40400000))
(check-sat)
"#;

fn workspace_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(|p| p.parent())
        .expect("workspace root")
        .to_path_buf()
}

fn keep_alethe_artifacts() -> bool {
    matches!(
        std::env::var("AY_KEEP_ALETHE_ARTIFACTS").as_deref(),
        Ok("1") | Ok("true") | Ok("TRUE")
    )
}

fn find_carcara() -> Option<PathBuf> {
    if let Ok(path) = std::env::var("CARCARA_PATH") {
        let path = PathBuf::from(path);
        if path.is_file() {
            return Some(path);
        }
    }

    let candidates = [
        workspace_root().join("bin/carcara"),
        workspace_root().join("reference/carcara/target/release/carcara"),
        workspace_root().join("reference/carcara/target/researcher_20/release/carcara"),
        PathBuf::from("/tmp/carcara/target/release/carcara"),
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

fn require_carcara_or_skip() -> Option<PathBuf> {
    if let Some(path) = find_carcara() {
        return Some(path);
    }

    assert!(
        std::env::var_os("CI").is_none(),
        "carcara not found. External Alethe verification is mandatory in CI.\n\
         Install: cargo install --git https://github.com/ufmg-smite/carcara.git"
    );

    eprintln!("carcara not found, skipping external Alethe verification");
    None
}

fn solve_unsat_and_get_proof(problem: &str, label: &str) -> String {
    let script = format!("(set-option :produce-proofs true)\n{problem}\n(get-proof)\n");
    let commands = parse(&script).expect("parse SMT-LIB script");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute SMT-LIB script");

    assert_eq!(
        outputs.first().map(String::as_str),
        Some("unsat"),
        "{label}: expected UNSAT result before proof output, got {outputs:?}"
    );
    assert!(
        outputs.len() >= 2,
        "{label}: expected proof output after UNSAT, got {outputs:?}"
    );

    let proof = outputs.last().cloned().expect("proof output");
    assert!(
        !proof.trim().is_empty(),
        "{label}: proof output must be non-empty"
    );
    assert!(
        proof.contains("(assume ") || proof.contains("(step "),
        "{label}: proof output must contain Alethe commands:\n{proof}"
    );

    proof
}

/// Return a proof only when the solver can publish UNSAT. Unsupported proof
/// shapes must fail closed as UNKNOWN; SAT is never valid for these fixtures.
fn solve_or_fail_closed_and_maybe_get_proof(problem: &str, label: &str) -> Option<String> {
    let script = format!("(set-option :produce-proofs true)\n{problem}\n");
    let commands = parse(&script).expect("parse SMT-LIB script");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute SMT-LIB script");

    match outputs.last().map(String::as_str) {
        Some("unknown") => {
            assert!(
                exec.last_proof().is_none(),
                "{label}: UNKNOWN must not retain a publishable proof"
            );
            None
        }
        Some("unsat") => {
            let get_proof = parse("(get-proof)").expect("parse get-proof");
            let proof_outputs = exec
                .execute_all(&get_proof)
                .expect("export proof after UNSAT");
            let proof = proof_outputs.last().cloned().expect("proof output");
            assert!(
                proof.contains("(assume ") || proof.contains("(step "),
                "{label}: proof output must contain Alethe commands:\n{proof}"
            );
            Some(proof)
        }
        status => panic!("{label}: expected UNSAT or fail-closed UNKNOWN, got {status:?}"),
    }
}

fn normalize_whitespace(text: &str) -> String {
    text.split_whitespace().collect::<Vec<_>>().join(" ")
}

fn extract_asserted_terms(problem: &str) -> BTreeSet<String> {
    let bytes = problem.as_bytes();
    let mut cursor = 0usize;
    let mut assertions = BTreeSet::new();

    while let Some(offset) = problem[cursor..].find("(assert") {
        let assert_start = cursor + offset;
        let mut idx = assert_start + "(assert".len();
        while idx < bytes.len() && bytes[idx].is_ascii_whitespace() {
            idx += 1;
        }
        let term_start = idx;
        let mut depth = 0i32;
        while idx < bytes.len() {
            match bytes[idx] {
                b'(' => depth += 1,
                b')' => {
                    if depth == 0 {
                        let term = normalize_whitespace(&problem[term_start..idx]);
                        assertions.insert(term);
                        idx += 1;
                        break;
                    }
                    depth -= 1;
                }
                _ => {}
            }
            idx += 1;
        }
        cursor = idx;
    }

    assertions
}

fn extract_assume_terms(proof: &str) -> Vec<String> {
    proof
        .lines()
        .filter_map(|line| {
            let line = line.trim();
            let rest = line.strip_prefix("(assume ")?;
            let split = rest.find(' ')?;
            let term = rest[split + 1..].strip_suffix(')')?;
            Some(normalize_whitespace(term))
        })
        .collect()
}

fn benchmark_content(relative_path: &str) -> String {
    let path = workspace_root().join(relative_path);
    std::fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("failed to read {}: {e}", path.display()))
}

fn write_problem_and_proof(label: &str, problem: &str, proof: &str) -> (PathBuf, PathBuf) {
    let run_id = TEMP_FILE_SEQ.fetch_add(1, Ordering::Relaxed);
    let problem_path = std::env::temp_dir().join(format!(
        "ay_carcara_problem_{label}_{}_{}.smt2",
        std::process::id(),
        run_id
    ));
    let proof_path = std::env::temp_dir().join(format!(
        "ay_carcara_proof_{label}_{}_{}.alethe",
        std::process::id(),
        run_id
    ));

    std::fs::write(&problem_path, problem).expect("write problem");
    std::fs::write(&proof_path, proof).expect("write proof");

    (problem_path, proof_path)
}

/// Run Carcara on an Alethe proof and assert it validates.
/// Panics with diagnostic info if Carcara rejects the proof.
fn verify_alethe_with_carcara(carcara: &Path, label: &str, problem: &str, proof: &str) {
    assert!(
        run_carcara(carcara, label, problem, proof),
        "carcara rejected Alethe proof ({label})"
    );
}

/// Run Carcara on an Alethe proof. Returns `true` if the proof validates,
/// `false` if Carcara rejects it (with diagnostic output to stderr).
fn run_carcara(carcara: &Path, label: &str, problem: &str, proof: &str) -> bool {
    let (problem_path, proof_path) = write_problem_and_proof(label, problem, proof);

    // --allowed-rules trust: AY uses `trust` for theory lemmas that haven't
    // been fully reconstructed (BV bit-blast, arrays, strings). Carcara treats
    // these as unchecked holes but still validates all other proof structure.
    let output = std::process::Command::new(carcara)
        .arg("check")
        .arg("--expand-let-bindings")
        .args(["--allowed-rules", "trust", "--"])
        .arg(&proof_path)
        .arg(&problem_path)
        .output()
        .expect("run carcara check");

    let _stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    let keep_artifacts = keep_alethe_artifacts() || !output.status.success();
    if keep_artifacts {
        eprintln!(
            "Preserving Alethe artifacts ({label}): smt2={} alethe={}",
            problem_path.display(),
            proof_path.display()
        );
    } else {
        let _ = std::fs::remove_file(&problem_path);
        let _ = std::fs::remove_file(&proof_path);
    }

    if !output.status.success() {
        eprintln!(
            "carcara REJECTED ({label}): status={:?} stderr={}",
            output.status.code(),
            stderr.trim()
        );
        return false;
    }

    true
}

#[test]
#[timeout(60_000)]
fn test_carcara_external_unsat_smoke_corpus() {
    let Some(carcara) = require_carcara_or_skip() else {
        return;
    };

    let cases = [
        ("qf_bool", QF_BOOL_UNSAT),
        ("qf_lra", QF_LRA_UNSAT),
        ("qf_uf", QF_UF_UNSAT),
        ("qf_lia", QF_LIA_UNSAT),
        ("qf_uflia", QF_UFLIA_UNSAT),
    ];

    for (label, problem) in cases {
        let proof = solve_unsat_and_get_proof(problem, label);
        verify_alethe_with_carcara(&carcara, label, problem, &proof);
    }
}

// ============================================================================
// Trust-free Alethe verification (no --allowed-rules trust)
// ============================================================================

/// Run Carcara WITHOUT `--allowed-rules trust`. Returns `true` if the proof
/// is fully verified with no trust holes.
fn run_carcara_trust_free(carcara: &Path, label: &str, problem: &str, proof: &str) -> bool {
    let (problem_path, proof_path) = write_problem_and_proof(label, problem, proof);

    let output = std::process::Command::new(carcara)
        .arg("check")
        .arg("--expand-let-bindings")
        .arg("--")
        .arg(&proof_path)
        .arg(&problem_path)
        .output()
        .expect("run carcara check (trust-free)");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    let valid = trust_free_carcara_verdict_is_valid(output.status.success(), &stdout);
    let keep_artifacts = keep_alethe_artifacts() || !valid;
    if keep_artifacts {
        eprintln!(
            "Preserving Alethe artifacts ({label} trust-free): smt2={} alethe={}",
            problem_path.display(),
            proof_path.display()
        );
    } else {
        let _ = std::fs::remove_file(&problem_path);
        let _ = std::fs::remove_file(&proof_path);
    }

    if !valid {
        eprintln!(
            "carcara REJECTED trust-free ({label}): status={:?} stdout={} stderr={}",
            output.status.code(),
            stdout.trim(),
            stderr.trim()
        );
        return false;
    }

    true
}

fn trust_free_carcara_verdict_is_valid(status_success: bool, stdout: &str) -> bool {
    status_success && stdout.trim() == "valid"
}

#[test]
fn trust_free_carcara_verdict_rejects_holey_success() {
    assert!(trust_free_carcara_verdict_is_valid(true, "valid\n"));
    assert!(!trust_free_carcara_verdict_is_valid(true, "holey\n"));
    assert!(!trust_free_carcara_verdict_is_valid(false, "valid\n"));
}

/// QF_BOOL proofs should be fully verifiable without trust steps.
#[test]
#[timeout(60_000)]
fn test_carcara_trust_free_qf_bool() {
    let Some(carcara) = require_carcara_or_skip() else {
        return;
    };
    let proof = solve_unsat_and_get_proof(QF_BOOL_UNSAT, "trust_free_qf_bool");
    assert!(
        run_carcara_trust_free(&carcara, "trust_free_qf_bool", QF_BOOL_UNSAT, &proof),
        "QF_BOOL proof must be trust-free verifiable by carcara"
    );
}

/// QF_LRA proofs should be fully verifiable without trust steps.
#[test]
#[timeout(60_000)]
fn test_carcara_trust_free_qf_lra() {
    let Some(carcara) = require_carcara_or_skip() else {
        return;
    };
    let proof = solve_unsat_and_get_proof(QF_LRA_UNSAT, "trust_free_qf_lra");
    assert!(
        run_carcara_trust_free(&carcara, "trust_free_qf_lra", QF_LRA_UNSAT, &proof),
        "QF_LRA proof must be trust-free verifiable by carcara"
    );
}

/// Both the post-lift formula-level ITE and its original RHS-ITE spelling
/// must export proofs accepted by an independent Alethe checker without
/// allowing trust. The two cases exercise the provenance repair and the
/// established `ite_intro` fallback respectively.
#[test]
#[timeout(60_000)]
fn test_carcara_trust_free_arithmetic_ite_lift_and_fallback() {
    let Some(carcara) = require_carcara_or_skip() else {
        return;
    };
    let cases = [
        (
            "trust_free_formula_arithmetic_ite",
            "",
            "(assert (ite (= J 1) (= I (+ E F)) (= I E)))",
            "(assert (< I 0))",
        ),
        (
            "trust_free_rhs_arithmetic_ite",
            "",
            "(assert (= I (ite (= J 1) (+ E F) E)))",
            "(assert (< I 0))",
        ),
        (
            "trust_free_formula_arithmetic_ite_irrelevant_bool_source",
            r#"
(declare-const K Bool)
(declare-const W Int)
(assert (= K true))
(assert (= W (ite K 0 1)))
"#,
            "(assert (ite (= J 1) (= I (+ E F)) (= I E)))",
            "(assert (< (+ I W (- W)) 0))",
        ),
        (
            "trust_free_arithmetic_ite_successor_failure_or",
            "",
            "(assert (ite (= J 1) (= I (+ E F)) (= I E)))",
            "(assert (or (< F 0) (< G 0) (< H 0) (< I 0)))",
        ),
    ];

    for (label, extra_setup, definition, contradiction) in cases {
        let problem = arithmetic_ite_nonnegative_problem(extra_setup, definition, contradiction);
        let proof = solve_unsat_and_get_proof(&problem, label);
        assert!(
            !proof.contains(":rule trust"),
            "{label}: proof contains trust:\n{proof}"
        );
        assert!(
            run_carcara_trust_free(&carcara, label, &problem, &proof),
            "{label}: Carcara must accept the proof without allowed trust"
        );
    }
}

/// A nested top-level OR may canonicalize to a flattened internal term. The
/// exporter must either derive the exact immediate surface disjunct structure
/// or decline the proof; emitting one flattened `or` step from the nested
/// authored premise is not externally valid.
#[test]
#[timeout(60_000)]
fn test_carcara_nested_provenance_or_is_valid_or_fails_closed() {
    let Some(carcara) = require_carcara_or_skip() else {
        return;
    };
    let problem = arithmetic_ite_nonnegative_problem(
        "",
        "(assert (ite (= J 1) (= I (+ E F)) (= I E)))",
        "(assert (or (< F 0) (or (< G 0) (< H 0) (< I 0))))",
    );
    let label = "nested_arithmetic_ite_successor_failure_or";
    let Some(proof) = solve_or_fail_closed_and_maybe_get_proof(&problem, label) else {
        return;
    };
    assert!(
        !proof.contains(":rule trust"),
        "{label}: proof contains trust:\n{proof}"
    );
    assert!(
        run_carcara_trust_free(&carcara, label, &problem, &proof),
        "{label}: Carcara must accept any published proof without allowed trust"
    );
}

/// A negated ITE condition canonicalizes by swapping branch order. Any proof
/// that is still published must honor the authored positional surface when
/// checked independently; declining the unsupported spelling is also sound.
#[test]
#[timeout(60_000)]
fn test_carcara_negated_condition_ite_is_valid_or_fails_closed() {
    let Some(carcara) = require_carcara_or_skip() else {
        return;
    };
    for (label, definition) in [
        (
            "negated_condition_formula_ite",
            "(assert (ite (not (= J 1)) (= I E) (= I (+ E F))))",
        ),
        (
            "negated_condition_rhs_ite",
            "(assert (= I (ite (not (= J 1)) E (+ E F))))",
        ),
    ] {
        let problem = arithmetic_ite_nonnegative_problem("", definition, "(assert (< I 0))");
        let Some(proof) = solve_or_fail_closed_and_maybe_get_proof(&problem, label) else {
            continue;
        };
        assert!(!proof.contains(":rule trust"), "{label}: {proof}");
        assert!(
            run_carcara_trust_free(&carcara, label, &problem, &proof),
            "{label}: Carcara must accept any published proof"
        );
    }
}

/// QF_UF proofs on simple benchmarks should be fully verifiable without trust steps.
#[test]
#[timeout(60_000)]
fn test_carcara_trust_free_qf_uf() {
    let Some(carcara) = require_carcara_or_skip() else {
        return;
    };
    let proof = solve_unsat_and_get_proof(QF_UF_UNSAT, "trust_free_qf_uf");
    assert!(
        run_carcara_trust_free(&carcara, "trust_free_qf_uf", QF_UF_UNSAT, &proof),
        "QF_UF proof must be trust-free verifiable by carcara"
    );
}

/// The direct E-matching proof lane must agree with the independent Alethe
/// checker, including authored-forall surface binding and Farkas literal order.
#[test]
#[timeout(60_000)]
fn test_carcara_trust_free_auflia_ematching_forall_equality() {
    let Some(carcara) = require_carcara_or_skip() else {
        return;
    };
    let label = "trust_free_auflia_ematching_forall_equality";
    let proof = solve_unsat_and_get_proof(AUFLIA_EMATCHING_FORALL_EQUALITY_UNSAT, label);
    assert!(!proof.contains(":rule trust"), "{proof}");
    assert!(proof.contains(":rule forall_inst"), "{proof}");
    assert!(proof.contains(":rule la_generic"), "{proof}");
    assert!(
        run_carcara_trust_free(
            &carcara,
            label,
            AUFLIA_EMATCHING_FORALL_EQUALITY_UNSAT,
            &proof,
        ),
        "AUFLIA E-matching proof must be verified without allowed trust"
    );
}

/// Exercise exact Clean composed roots and linear fold-to-false source roots
/// through the independent Alethe checker so a locally strict proof cannot
/// mask a surface mismatch.
#[test]
#[timeout(60_000)]
fn test_carcara_trust_free_composed_authored_roots() {
    let Some(carcara) = require_carcara_or_skip() else {
        return;
    };

    let cases = [
        (
            "trust_free_qf_uf_composed_authored_root",
            QF_UF_COMPOSED_AUTHORED_ROOT_UNSAT,
            QF_UF_COMPOSED_AUTHORED_ROOT_UNSAT,
        ),
        (
            "trust_free_qf_lia_composed_authored_root",
            QF_LIA_COMPOSED_AUTHORED_ROOT_UNSAT,
            QF_LIA_COMPOSED_AUTHORED_ROOT_UNSAT,
        ),
        (
            "trust_free_qf_auflia_composed_row2_root",
            QF_AUFLIA_COMPOSED_ROW2_ROOT_UNSAT,
            QF_AUFLIA_COMPOSED_ROW2_ROOT_UNSAT,
        ),
        (
            "trust_free_qf_lia_linear_and_fold",
            QF_LIA_LINEAR_AND_FOLD_UNSAT,
            QF_LIA_LINEAR_AND_FOLD_UNSAT,
        ),
        (
            "trust_free_qf_lia_literal_false",
            QF_LIA_LITERAL_FALSE_UNSAT,
            QF_LIA_LITERAL_FALSE_UNSAT,
        ),
        (
            "trust_free_qf_lia_mod_assuming",
            QF_LIA_MOD_ASSUMING_UNSAT,
            QF_LIA_MOD_ASSUMING_CARCARA_SCOPE,
        ),
        (
            "trust_free_qf_auflia_linear_assuming",
            QF_AUFLIA_LINEAR_ASSUMING_UNSAT,
            QF_AUFLIA_LINEAR_ASSUMING_CARCARA_SCOPE,
        ),
        (
            "trust_free_qf_lra_guarded_split",
            QF_LRA_GUARDED_SPLIT_UNSAT,
            QF_LRA_GUARDED_SPLIT_UNSAT,
        ),
        (
            "trust_free_qf_lia_let_linear_and_fold",
            QF_LIA_LET_LINEAR_AND_FOLD_UNSAT,
            QF_LIA_LET_LINEAR_AND_FOLD_UNSAT,
        ),
    ];

    for (label, solver_problem, carcara_problem) in cases {
        let proof = solve_unsat_and_get_proof(solver_problem, label);
        assert!(
            !proof.contains(":rule trust") && !proof.contains(":rule hole"),
            "{label}: composed-root proof must not contain unchecked rules:\n{proof}"
        );
        assert!(
            run_carcara_trust_free(&carcara, label, carcara_problem, &proof),
            "{label}: composed-root proof must be trust-free verifiable by carcara"
        );
    }
}

/// The exact QF_ABV regression must remain self-contained: the authored nested
/// concat and binary `distinct` are bridged explicitly, while the closed
/// constant folds use Carcara's checked `evaluate` rule.
#[test]
#[timeout(60_000)]
fn test_carcara_trust_free_qf_abv_pinned_concat_substitution() {
    let Some(carcara) = require_carcara_or_skip() else {
        return;
    };
    let label = "trust_free_qf_abv_pinned_concat_substitution";
    let proof = solve_unsat_and_get_proof(QF_ABV_PINNED_CONCAT_UNSAT, label);
    assert!(
        !proof.contains(":rule trust") && !proof.contains(":rule hole"),
        "QF_ABV regression proof must not contain unchecked rules:\n{proof}"
    );
    assert!(
        !proof.contains(":rule bv_bitblast"),
        "closed concat folding must use Carcara's evaluate rule, not AY's private bv_bitblast rule:\n{proof}"
    );
    assert!(
        proof.contains(":rule evaluate"),
        "closed concat folding must be certified by evaluate:\n{proof}"
    );
    assert!(
        proof.contains(":rule distinct_elim"),
        "surface distinct must be linked to its canonical disequality:\n{proof}"
    );
    assert!(
        run_carcara_trust_free(&carcara, label, QF_ABV_PINNED_CONCAT_UNSAT, &proof),
        "QF_ABV pinned-concat proof must be verified by Carcara without allowed trust"
    );
}

/// The `ay z3-audit` canonical QF_UF transitivity fixture must export a
/// genuine `eq_transitive` + `th_resolution` derivation that carcara accepts
/// WITHOUT `--allowed-rules trust`. This is the exact fixture used by the audit
/// (sorts declared as `Int`, contradiction is pure transitivity a=b, b=c, a≠c).
#[test]
#[timeout(60_000)]
fn test_carcara_trust_free_qf_uf_transitivity_fixture() {
    let Some(carcara) = require_carcara_or_skip() else {
        return;
    };
    let problem =
        benchmark_content("tests/fixtures/proof/smt_alethe_qf_uf_transitivity_not_eq.smt2");
    let proof = solve_unsat_and_get_proof(&problem, "trust_free_qf_uf_transitivity_fixture");
    assert!(
        proof.contains(":rule eq_transitive"),
        "fixture proof must use a genuine eq_transitive step:\n{proof}"
    );
    assert!(
        !proof.contains(":rule trust"),
        "fixture proof must not contain any trust step:\n{proof}"
    );
    assert!(
        run_carcara_trust_free(
            &carcara,
            "trust_free_qf_uf_transitivity_fixture",
            &problem,
            &proof
        ),
        "QF_UF transitivity fixture proof must be trust-free verifiable by carcara"
    );
}

/// A logically inert authored Boolean-equality wrapper installs the surface
/// spelling `(= (= a b) false)` for AY's canonical `not (= a b)` term. That
/// spelling is not a legal negated-equality hypothesis of `eq_transitive`.
/// Standalone generic-EUF promotion must therefore either leave publication
/// to a later fully audited repair or make the proof request fail closed; it
/// must never publish the native-only rendering.
#[test]
#[timeout(60_000)]
fn test_carcara_qf_uf_boolean_equality_surface_is_valid_or_fails_closed() {
    let Some(carcara) = require_carcara_or_skip() else {
        return;
    };
    const PROBLEM: &str = r#"
(set-logic QF_UF)
(declare-const a Int)
(declare-const b Int)
(declare-const c Int)
(assert (= a b))
(assert (= b c))
(assert (not (= a c)))
; Tautological, but its first child supplies the adversarial surface alias.
(assert (or (= (= a b) false) (= a b)))
(check-sat)
"#;
    let label = "qf_uf_boolean_equality_surface";
    let Some(proof) = solve_or_fail_closed_and_maybe_get_proof(PROBLEM, label) else {
        return;
    };
    assert!(
        !proof.contains(":rule trust") && !proof.contains(":rule hole"),
        "{label}: any published proof must be fully checkable:\n{proof}"
    );
    assert!(
        run_carcara_trust_free(&carcara, label, PROBLEM, &proof),
        "{label}: Carcara must accept any published proof"
    );
}

/// QF_LIA arithmetic proofs may still contain `trust`-backed theory steps when
/// coefficient annotations are unavailable. This test checks the current export
/// contract: the proof must remain structurally valid via carcara with AY's
/// supported allowlist.
#[test]
#[timeout(60_000)]
fn test_carcara_qf_lia_holey_valid() {
    let Some(carcara) = require_carcara_or_skip() else {
        return;
    };

    let proof = solve_unsat_and_get_proof(QF_LIA_UNSAT, "qf_lia_holey");
    verify_alethe_with_carcara(&carcara, "qf_lia_holey", QF_LIA_UNSAT, &proof);
}

/// AY strictly validates datatype exhaustiveness in its native proof IR, but
/// the pinned Alethe calculus has no corresponding inference. The exported
/// diagnostic must therefore be structurally accepted as `holey`, never claim
/// `valid`, and never invent an unsupported wire-rule name.
#[test]
#[timeout(60_000)]
fn test_carcara_finite_enum_pigeonhole_is_honestly_holey() {
    let Some(carcara) = require_carcara_or_skip() else {
        return;
    };
    let label = "finite_enum_pigeonhole_holey";
    let proof = solve_unsat_and_get_proof(QF_DT_FINITE_ENUM_PIGEONHOLE_UNSAT, label);
    assert_eq!(proof.matches(":rule hole").count(), 1, "{proof}");
    assert_eq!(
        proof
            .lines()
            .filter(|line| line.starts_with("(assume "))
            .count(),
        6,
        "{proof}"
    );
    assert_eq!(proof.matches(":rule resolution").count(), 1, "{proof}");
    assert!(!proof.contains(":rule dt_enum_pigeonhole"), "{proof}");
    let (problem_path, proof_path) =
        write_problem_and_proof(label, QF_DT_FINITE_ENUM_PIGEONHOLE_CARCARA_SCOPE, &proof);
    let output = std::process::Command::new(&carcara)
        .arg("check")
        .arg("--expand-let-bindings")
        .arg("--")
        .arg(&proof_path)
        .arg(&problem_path)
        .output()
        .expect("run carcara finite-enum holey check");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    let keep_artifacts = keep_alethe_artifacts() || !output.status.success();
    if !keep_artifacts {
        let _ = std::fs::remove_file(&problem_path);
        let _ = std::fs::remove_file(&proof_path);
    }
    assert!(
        output.status.success(),
        "Carcara rejected finite-enum skeleton: stdout={} stderr={}",
        stdout.trim(),
        stderr.trim()
    );
    assert_eq!(stdout.trim(), "holey");
}

/// The trust-FREE normalized-assume class: every step is checkable, but the
/// exported assumes are preprocessing-normalized (`(>= a 0)` -> `(<= 0 a)`,
/// `(> a 5)` -> `(< 5 a)`) and print unlike the problem premises. The
/// trust-surgery pass must fire without a trust anchor and bridge both the
/// normalized `and` conjunction and the plain normalized bound literal.
#[test]
#[timeout(60_000)]
fn test_carcara_qf_lia_normalized_assumes_no_trust_anchor_valid() {
    let Some(carcara) = require_carcara_or_skip() else {
        return;
    };

    const PROBLEM: &str = r#"
(set-logic QF_LIA)
(declare-const a Int)
(assert (and (>= a 0) (<= a 5)))
(assert (> a 5))
(check-sat)
"#;
    let proof = solve_unsat_and_get_proof(PROBLEM, "qf_lia_normalized_assumes_no_trust");
    assert!(
        !proof.contains(":rule trust"),
        "expected a trust-free proof, got:\n{proof}"
    );
    let assumes = extract_assume_terms(&proof);
    assert!(
        assumes.contains(&"(and (>= a 0) (<= a 5))".to_string()),
        "and-assume must print with the problem file's surface syntax:\n{proof}"
    );
    assert!(
        assumes.contains(&"(> a 5)".to_string()),
        "bound assume must print with the problem file's surface syntax:\n{proof}"
    );
    verify_alethe_with_carcara(
        &carcara,
        "qf_lia_normalized_assumes_no_trust",
        PROBLEM,
        &proof,
    );
}

#[test]
#[timeout(60_000)]
fn test_carcara_qf_lia_harder_binary_ilp_unsat_valid() {
    let Some(carcara) = require_carcara_or_skip() else {
        return;
    };

    let problem = benchmark_content("benchmarks/smt/QF_LIA/harder_binary_ilp_unsat.smt2");
    let proof = solve_unsat_and_get_proof(&problem, "QF_LIA_harder_binary_ilp_unsat");
    verify_alethe_with_carcara(&carcara, "QF_LIA_harder_binary_ilp_unsat", &problem, &proof);
}

#[test]
#[timeout(60_000)]
fn test_qf_lia_ring_exported_assumes_match_original_premises() {
    let problem = std::fs::read_to_string(
        workspace_root().join("benchmarks/smt/QF_LIA/ring_2exp4_3vars_0ite_unsat.smt2"),
    )
    .expect("read ring benchmark");
    let proof = solve_unsat_and_get_proof(&problem, "qf_lia_ring_assume_surface");

    let original_assertions = extract_asserted_terms(&problem);
    let assume_terms = extract_assume_terms(&proof);

    assert!(
        !assume_terms.is_empty(),
        "expected exported proof to contain assume steps:\n{proof}"
    );

    for term in &assume_terms {
        assert!(
            original_assertions.contains(term),
            "exported assume term is not an original SMT-LIB premise: {term}\n\
             original premises: {original_assertions:?}\nproof:\n{proof}"
        );
    }

    if let Some(carcara) = require_carcara_or_skip() {
        verify_alethe_with_carcara(
            &carcara,
            "qf_lia_ring_composed_divisibility",
            &problem,
            &proof,
        );
    }
}

#[test]
#[timeout(60_000)]
fn test_carcara_regression_parity_xor_unsat_valid() {
    let Some(carcara) = require_carcara_or_skip() else {
        return;
    };

    let problem = benchmark_content("benchmarks/smt/regression/parity_xor_unsat.smt2");
    let proof = solve_unsat_and_get_proof(&problem, "regression_parity_xor_unsat");
    verify_alethe_with_carcara(&carcara, "regression_parity_xor_unsat", &problem, &proof);
}

/// Multi-equality Farkas rebuild (the model-checker consumer `certify-all-n` initiation wall):
/// a conjunction of equalities substituted by preprocessing into a strict
/// inequality. The rebuilt proof — assume(and) + `and_pos` conjunct
/// extraction + ONE signed-coefficient `la_generic` lemma + resolution —
/// must be carcara-verifiable with NO trust allowance.
#[test]
#[timeout(60_000)]
fn test_carcara_trust_free_multi_equality_conjunction() {
    let Some(carcara) = require_carcara_or_skip() else {
        return;
    };
    const PROBLEM: &str = r#"
(set-logic QF_LIA)
(declare-const x Int)
(declare-const y Int)
(declare-const n Int)
(assert (and (= x n) (= y 0)))
(assert (< n (+ x y)))
(check-sat)
"#;
    let proof = solve_unsat_and_get_proof(PROBLEM, "trust_free_multi_equality_conjunction");
    assert!(
        !proof.contains(":rule trust"),
        "multi-equality conjunction proof must not contain trust steps:\n{proof}"
    );
    assert!(
        run_carcara_trust_free(
            &carcara,
            "trust_free_multi_equality_conjunction",
            PROBLEM,
            &proof
        ),
        "multi-equality conjunction proof must be trust-free verifiable by carcara"
    );
}

/// The disequality variant of the same wall: `x = n ∧ y = 0` against
/// `n ≠ x + y`. A single Farkas combination cannot orient the disequality
/// for printing, so the export must go through the `la_disequality` case
/// split (carcara validates that rule natively), with the equality units
/// extracted from the conjunction by `and_pos`.
#[test]
#[timeout(60_000)]
fn test_carcara_trust_free_multi_equality_diseq_split() {
    let Some(carcara) = require_carcara_or_skip() else {
        return;
    };
    const PROBLEM: &str = r#"
(set-logic QF_LIA)
(declare-const x Int)
(declare-const y Int)
(declare-const n Int)
(assert (and (= x n) (= y 0)))
(assert (not (= n (+ x y))))
(check-sat)
"#;
    let proof = solve_unsat_and_get_proof(PROBLEM, "trust_free_multi_equality_diseq_split");
    assert!(
        !proof.contains(":rule trust"),
        "multi-equality disequality proof must not contain trust steps:\n{proof}"
    );
    assert!(
        proof.contains(":rule la_disequality"),
        "expected the la_disequality case split:\n{proof}"
    );
    assert!(
        run_carcara_trust_free(
            &carcara,
            "trust_free_multi_equality_diseq_split",
            PROBLEM,
            &proof
        ),
        "multi-equality disequality proof must be trust-free verifiable by carcara"
    );
}

// ============================================================================
// Benchmark corpus Alethe external validation
// ============================================================================

/// Per-benchmark timeout for solving and independent oracle classification.
const PER_BENCHMARK_TIMEOUT_SECS: u64 = 10;

/// Files whose names contain `false_unsat` (plus the historical Hamiltonian
/// canary) are SAT regression inputs, not UNSAT proof obligations.  They were
/// previously counted as generic "skips", which blurred the denominator of
/// the external-proof gate.  Every row is checked against Z3 below.
const ORACLE_SAT_CORPUS_ROWS: &[&str] = &[
    "QF_LIA_false_unsat_20var_bb",
    "QF_LIA_false_unsat_disjunction_6205",
    "QF_LIA_false_unsat_implication_6206",
    "QF_LIA_false_unsat_step2_6207",
    "QF_LIA_mini_hamiltonian_unsat",
    "regression_false_unsat_cegqi_entailed_inner_forall",
    "regression_false_unsat_cegqi_entailed_inner_forall_nnf",
    "regression_false_unsat_cegqi_entailed_inner_forall_or_not",
    "regression_false_unsat_cegqi_entailed_inner_forall_witness",
];

/// Independently oracle-confirmed UNSAT rows whose exact proof surfaces are
/// not yet supported.  These are NOT counted as proof parity.  The gate below
/// requires AY to return fail-closed `unknown` for every one; SAT, timeout,
/// execution failure, or an unchecked proof is a hard failure.
const ORACLE_UNSAT_UNSUPPORTED_ROWS: &[&str] = &[
    "QF_ABV_csplit_repro_100selects_unsat",
    "QF_ABV_csplit_repro_indirect_store_unsat",
    "QF_ABV_csplit_repro_many_trivial_selects_unsat",
    "QF_ABV_csplit_repro_store_chain_unsat",
    "QF_ABV_csplit_repro_unsat",
    "QF_LIA_ring_2exp12_3vars_deep_unsat",
    "QF_LIA_ring_2exp16_5vars_cascade_unsat",
    "QF_LIA_ring_2exp16_5vars_cascade_v2_unsat",
    "QF_LIA_ring_2exp8_5vars_modular_unsat",
    "QF_NIA_simple_product_unsat",
    "QF_UFLIA_unsat_congruence_to_lia",
];

struct CorpusVerificationSummary {
    verified: usize,
    rejected_labels: Vec<String>,
    oracle_sat_labels: Vec<String>,
    unsupported_unsat_labels: Vec<String>,
}

enum CorpusSolve {
    CertifiedProof(String),
    Sat,
    Unknown,
}

/// Solve one corpus row under the mandatory strict proof boundary.
///
/// Timeout, parse/execution failure, malformed proof output, and any result
/// other than exact SAT/UNSAT/UNKNOWN fail loudly.  In particular there is no
/// generic "skip" bucket: callers must classify SAT and unsupported UNSAT rows
/// against the independent oracle and the explicit lists above.
fn solve_corpus_with_timeout(content: &str, label: &str) -> CorpusSolve {
    // Strip (exit) command if present — we need to append (get-proof) after (check-sat).
    let content = content
        .lines()
        .filter(|line| line.trim() != "(exit)")
        .collect::<Vec<_>>()
        .join("\n");

    let script = format!("(set-option :produce-proofs true)\n{content}\n(get-proof)\n");
    let commands = parse(&script).unwrap_or_else(|e| panic!("{label}: parse error: {e}"));

    let mut exec = Executor::new();
    let interrupt = Arc::new(AtomicBool::new(false));
    exec.set_interrupt(Arc::clone(&interrupt));

    let (cancel_tx, cancel_rx) = std::sync::mpsc::channel();
    let timer_interrupt = Arc::clone(&interrupt);
    let timer = std::thread::spawn(move || {
        if cancel_rx
            .recv_timeout(std::time::Duration::from_secs(PER_BENCHMARK_TIMEOUT_SECS))
            .is_err()
        {
            timer_interrupt.store(true, Ordering::Relaxed);
        }
    });

    let outputs = exec.execute_all(&commands);
    let timed_out = interrupt.load(Ordering::Relaxed);
    let _ = cancel_tx.send(());
    let _ = timer.join();

    assert!(
        !timed_out,
        "{label}: solving timed out ({PER_BENCHMARK_TIMEOUT_SECS}s limit)"
    );

    let outputs = outputs.unwrap_or_else(|e| panic!("{label}: execution error: {e}"));

    let first = outputs.first().map(String::as_str);
    match first {
        Some("sat") => return CorpusSolve::Sat,
        Some("unknown") => return CorpusSolve::Unknown,
        Some("unsat") => {}
        _ => panic!("{label}: unexpected result {first:?}"),
    }

    assert!(outputs.len() >= 2, "{label}: no proof output after UNSAT");

    let proof = outputs.last().cloned().expect("checked output length");
    assert!(!proof.trim().is_empty(), "{label}: empty proof output");
    assert!(
        proof.contains("(assume ") || proof.contains("(step "),
        "{label}: proof lacks Alethe commands"
    );

    CorpusSolve::CertifiedProof(proof)
}

fn z3_oracle_status(path: &Path, label: &str) -> String {
    let output = std::process::Command::new("z3")
        .arg(format!("-T:{PER_BENCHMARK_TIMEOUT_SECS}"))
        .arg(path)
        .output()
        .unwrap_or_else(|e| {
            panic!("{label}: Z3 is required to classify non-proof corpus rows independently: {e}")
        });
    assert!(
        output.status.success(),
        "{label}: Z3 oracle failed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    String::from_utf8_lossy(&output.stdout)
        .lines()
        .next()
        .unwrap_or_default()
        .trim()
        .to_ascii_lowercase()
}

/// Collect all `*unsat*.smt2` files from `benchmarks/smt/` subdirectories.
fn collect_unsat_smt2_benchmarks() -> Vec<PathBuf> {
    let smt_dir = workspace_root().join("benchmarks/smt");
    assert!(
        smt_dir.is_dir(),
        "benchmark directory does not exist: {}",
        smt_dir.display()
    );

    let mut files = Vec::new();
    for entry in std::fs::read_dir(&smt_dir).expect("read benchmarks/smt") {
        let subdir = entry.expect("read dir entry").path();
        if !subdir.is_dir() {
            continue;
        }
        for file_entry in std::fs::read_dir(&subdir).expect("read logic subdir") {
            let path = file_entry.expect("read file entry").path();
            if path.extension().is_some_and(|ext| ext == "smt2") {
                let name = path.file_name().unwrap().to_string_lossy().to_string();
                if name.contains("unsat") {
                    files.push(path);
                }
            }
        }
    }
    files.sort();
    files
}

/// Build a human-readable label from a benchmark path: `QF_LIA_unsat_00`.
fn benchmark_label(path: &Path) -> String {
    let logic_dir = path
        .parent()
        .and_then(|p| p.file_name())
        .and_then(|n| n.to_str())
        .unwrap_or("unknown");
    let stem = path.file_stem().and_then(|n| n.to_str()).unwrap_or("bench");
    format!("{logic_dir}_{stem}")
}

fn run_unsat_benchmark_corpus(carcara: &Path, smt2_files: &[PathBuf]) -> CorpusVerificationSummary {
    let mut summary = CorpusVerificationSummary {
        verified: 0,
        rejected_labels: Vec::new(),
        oracle_sat_labels: Vec::new(),
        unsupported_unsat_labels: Vec::new(),
    };

    for path in smt2_files {
        let label = benchmark_label(path);
        let content = std::fs::read_to_string(path)
            .unwrap_or_else(|e| panic!("failed to read {}: {e}", path.display()));

        match solve_corpus_with_timeout(&content, &label) {
            CorpusSolve::CertifiedProof(proof)
                if run_carcara(carcara, &label, &content, &proof) =>
            {
                summary.verified += 1;
            }
            CorpusSolve::CertifiedProof(_) => summary.rejected_labels.push(label),
            CorpusSolve::Sat => {
                assert!(
                    ORACLE_SAT_CORPUS_ROWS.contains(&label.as_str()),
                    "{label}: AY returned SAT for a corpus row not classified as oracle-SAT"
                );
                assert_eq!(
                    z3_oracle_status(path, &label),
                    "sat",
                    "{label}: independent oracle disagrees with SAT classification"
                );
                summary.oracle_sat_labels.push(label);
            }
            CorpusSolve::Unknown => {
                if ORACLE_SAT_CORPUS_ROWS.contains(&label.as_str()) {
                    assert_eq!(
                        z3_oracle_status(path, &label),
                        "sat",
                        "{label}: independent oracle disagrees with SAT classification"
                    );
                    summary.oracle_sat_labels.push(label);
                } else {
                    assert!(
                        ORACLE_UNSAT_UNSUPPORTED_ROWS.contains(&label.as_str()),
                        "{label}: unexpected fail-closed UNKNOWN; add proof support or an explicit oracle-backed classification"
                    );
                    assert_eq!(
                        z3_oracle_status(path, &label),
                        "unsat",
                        "{label}: independent oracle disagrees with unsupported-UNSAT classification"
                    );
                    summary.unsupported_unsat_labels.push(label);
                }
            }
        }
    }

    summary
}

fn assert_corpus_expectations(total: usize, summary: &CorpusVerificationSummary) {
    let rejected = summary.rejected_labels.len();
    let oracle_sat = summary.oracle_sat_labels.len();
    let unsupported = summary.unsupported_unsat_labels.len();
    let verified = summary.verified;

    eprintln!(
        "Carcara corpus: {verified} proofs verified, {rejected} rejected, \
         {unsupported} oracle-UNSAT fail-closed unsupported, {oracle_sat} oracle-SAT non-obligations"
    );
    for label in &summary.rejected_labels {
        eprintln!("  REJECTED: {label}");
    }
    for label in &summary.unsupported_unsat_labels {
        eprintln!("  UNSUPPORTED (oracle UNSAT, AY UNKNOWN): {label}");
    }
    for label in &summary.oracle_sat_labels {
        eprintln!("  NOT A PROOF OBLIGATION (oracle SAT): {label}");
    }

    assert_eq!(
        rejected, 0,
        "Carcara must not reject any UNSAT benchmark proof: {:?}",
        summary.rejected_labels
    );
    let actual_sat: BTreeSet<&str> = summary
        .oracle_sat_labels
        .iter()
        .map(String::as_str)
        .collect();
    let expected_sat: BTreeSet<&str> = ORACLE_SAT_CORPUS_ROWS.iter().copied().collect();
    assert_eq!(
        actual_sat, expected_sat,
        "oracle-SAT corpus classification drifted"
    );
    let actual_unsupported: BTreeSet<&str> = summary
        .unsupported_unsat_labels
        .iter()
        .map(String::as_str)
        .collect();
    let expected_unsupported: BTreeSet<&str> =
        ORACLE_UNSAT_UNSUPPORTED_ROWS.iter().copied().collect();
    assert_eq!(
        actual_unsupported, expected_unsupported,
        "oracle-UNSAT unsupported corpus classification drifted"
    );
    assert_eq!(
        verified + unsupported + oracle_sat,
        total,
        "every corpus row must be externally proof-verified or independently oracle-classified"
    );
}

/// Exhaustive Carcara validation for all UNSAT SMT benchmarks.
///
/// Solves each benchmark with proof generation, validates with Carcara.
/// Oracle-SAT filename matches are excluded from the proof denominator. Every
/// oracle-UNSAT row must either have a Carcara-verified proof or return exact
/// fail-closed UNKNOWN under the explicit unsupported list; there is no generic
/// skip path.
#[test]
#[cfg_attr(debug_assertions, timeout(300_000))]
#[cfg_attr(not(debug_assertions), timeout(120_000))]
fn test_carcara_external_unsat_benchmark_corpus() {
    let Some(carcara) = require_carcara_or_skip() else {
        return;
    };

    let smt2_files = collect_unsat_smt2_benchmarks();
    assert!(
        !smt2_files.is_empty(),
        "No unsat*.smt2 benchmark files found"
    );

    let total = smt2_files.len();
    let summary = run_unsat_benchmark_corpus(&carcara, &smt2_files);
    assert_corpus_expectations(total, &summary);
}

/// The eq_diamond family (SMT-COMP QF_UF): preprocessing derives per-segment
/// UF-transitivity tautologies `(or (= xi xj) (and (or (not ..) ..) ..))` and
/// a chain unit `(or (= x0 xn) (not (= x0 x1)) ..)`, which the raw export
/// leaks as mid-proof `assume`s / unit `trust` steps no checker can match to
/// the problem premises. The trust-surgery tautology planner must re-derive
/// every such leaf (eq_transitive + or_neg/and_neg + contraction), leaving a
/// trust-free proof whose assumes are all problem premises (#real-bench).
#[test]
#[cfg_attr(debug_assertions, timeout(300_000))]
#[cfg_attr(not(debug_assertions), timeout(120_000))]
fn test_carcara_external_eq_diamond_transitivity_tautologies() {
    let problem = r#"
(set-logic QF_UF)
(declare-sort U 0)
(declare-fun x0 () U)
(declare-fun y0 () U)
(declare-fun z0 () U)
(declare-fun x1 () U)
(declare-fun y1 () U)
(declare-fun z1 () U)
(declare-fun x2 () U)
(declare-fun y2 () U)
(declare-fun z2 () U)
(declare-fun x3 () U)
(assert (and (or (and (= x0 y0) (= y0 x1)) (and (= x0 z0) (= z0 x1))) (or (and (= x1 y1) (= y1 x2)) (and (= x1 z1) (= z1 x2))) (or (and (= x2 y2) (= y2 x3)) (and (= x2 z2) (= z2 x3))) (not (= x0 x3))))
(check-sat)
"#;

    let proof = solve_unsat_and_get_proof(problem, "eq_diamond_taut");
    assert!(
        !proof.contains(":rule trust"),
        "eq_diamond proof must be trust-free after the tautology surgery:\n{proof}"
    );
    // Every assume must be an asserted problem premise (no leaked
    // preprocessor-derived formulas).
    let asserted = extract_asserted_terms(problem);
    for assume in extract_assume_terms(&proof) {
        assert!(
            asserted.contains(&assume),
            "assume is not a problem premise: {assume}"
        );
    }
    let Some(carcara) = require_carcara_or_skip() else {
        return;
    };
    verify_alethe_with_carcara(&carcara, "eq_diamond_taut", problem, proof.as_str());
}

/// The NORMALIZED-ASSUME MISMATCH class (SMT-COMP QF_LIA CAV_2009 family):
/// the file spells linear atoms with explicit coefficients — `(* 1 x)`,
/// `(* 0 x)`, `(* (- 1) x)`, duplicated monomials — that arithmetic
/// elaboration canonicalizes (unit/zero elision, unary minus, folding,
/// reordering), so a canonical-print `assume` matches no problem premise.
/// The repair raw-interns the surface spelling for the assume and bridges
/// each extracted conjunct to its canonical atom with a certified `[1, 1]`
/// `la_generic` orientation lemma (#real-bench).
#[test]
#[cfg_attr(debug_assertions, timeout(300_000))]
#[cfg_attr(not(debug_assertions), timeout(120_000))]
fn test_carcara_external_normalized_linear_assume_bridge() {
    let problem = r#"
(set-logic QF_LIA)
(declare-fun x0 () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(assert (and (<= (+ (* 1 x0) (* 1 x0) (* 0 x1) (* (- 1) x1)) 0) (<= (+ (* 1 x1) (* (- 2) x0)) (- 1)) (<= (+ (* 0 x0) (* 1 x2)) 5)))
(check-sat)
"#;

    let proof = solve_unsat_and_get_proof(problem, "normalized_linear_assume");
    assert!(
        !proof.contains(":rule trust"),
        "normalized-assume proof must be trust-free:\n{proof}"
    );
    assert!(
        proof.contains(":rule la_generic"),
        "expected certified la_generic bridge lemmas:\n{proof}"
    );
    // Every assume must spell an asserted problem premise EXACTLY (the raw
    // surface print, not the canonicalized atom forms).
    let asserted = extract_asserted_terms(problem);
    for assume in extract_assume_terms(&proof) {
        assert!(
            asserted.contains(&assume),
            "assume is not a problem premise: {assume}"
        );
    }
    let Some(carcara) = require_carcara_or_skip() else {
        return;
    };
    verify_alethe_with_carcara(
        &carcara,
        "normalized_linear_assume",
        problem,
        proof.as_str(),
    );
}

/// The deduplicated-conjunct variant of the normalized-assume mismatch
/// (CAV_2009 problem__030): two surface conjuncts elaborate to the SAME
/// canonical atom, so the canonical conjunction has fewer conjuncts than the
/// file — positional pairing is impossible and the alignment-capable
/// `AndDistinct` classifier must carry the repair, dropping the exporter's
/// de-Morganized `and_pos` steps in favor of re-derived per-conjunct units
/// (#real-bench).
#[test]
#[cfg_attr(debug_assertions, timeout(300_000))]
#[cfg_attr(not(debug_assertions), timeout(120_000))]
fn test_carcara_external_normalized_assume_deduplicated_conjunct() {
    let problem = r#"
(set-logic QF_LIA)
(declare-fun x0 () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(assert (and (<= (+ (* 1 x0) (* (- 1) x1)) 0) (<= (+ (* 0 x2) (* 1 x0) (* (- 1) x1)) 0) (<= (+ (* 1 x1) (* (- 1) x0)) (- 1))))
(check-sat)
"#;

    let proof = solve_unsat_and_get_proof(problem, "normalized_assume_dedup");
    assert!(
        !proof.contains(":rule trust"),
        "deduplicated normalized-assume proof must be trust-free:\n{proof}"
    );
    let asserted = extract_asserted_terms(problem);
    for assume in extract_assume_terms(&proof) {
        assert!(
            asserted.contains(&assume),
            "assume is not a problem premise: {assume}"
        );
    }
    let Some(carcara) = require_carcara_or_skip() else {
        return;
    };
    verify_alethe_with_carcara(&carcara, "normalized_assume_dedup", problem, proof.as_str());
}
