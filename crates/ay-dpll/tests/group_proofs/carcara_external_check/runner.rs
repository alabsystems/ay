// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#[cfg(test)]
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
#[cfg(test)]
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

#[cfg(test)]
fn benchmark_content(relative_path: &str) -> String {
    let path = workspace_root().join(relative_path);
    std::fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("failed to read {}: {e}", path.display()))
}

#[cfg(test)]
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
#[cfg(test)]
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
#[cfg(test)]
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
