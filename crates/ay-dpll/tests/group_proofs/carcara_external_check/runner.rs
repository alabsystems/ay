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
        "{label}: expected UNSAT result before proof output, got {outputs:?}; unknown_reason={:?}",
        exec.unknown_reason()
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

/// Run Carcara on an Alethe proof and assert it is externally VERIFIED:
/// the trust-free runner's literal `valid`, never an exit-0 `holey`.
fn verify_alethe_with_carcara(carcara: &Path, label: &str, problem: &str, proof: &str) {
    assert!(
        run_carcara_trust_free(carcara, label, problem, proof),
        "carcara did not verify Alethe proof ({label}): only `valid` is verification"
    );
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
// Carcara verdicts — no allowance, ever
// ============================================================================
//
// There is deliberately NO runner here that passes `--allowed-rules trust` (or
// `-i`) or reads Carcara's exit status alone. Pinned Carcara exits 0 on a
// `holey` document: under `--allowed-rules trust` a `trust` step is a hole,
// and a `hole` step is one even without the flag. Measured with carcara 1.1.0
// [git 9a352ee]: a proof refuting the SATISFIABLE `(assert (> x 0))` through
// `(step t1 (cl (not (> x 0))) :rule trust)` exits 0 and prints `holey` under
// that flag, and the same proof with `:rule hole` does so with no flag at all.
// An exit-0 runner therefore "verified" a false refutation. Only the literal
// `valid` is external verification; `holey` must be asserted as exactly that.

/// Pinned Carcara's one-word verdict on stdout.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum CarcaraVerdict {
    /// Every step re-derived. The only verdict that is external verification.
    Valid,
    /// Every step re-derived EXCEPT disclosed `hole` steps. Never verification.
    /// With no allowance a `trust` step is an unknown rule, hence `Invalid`.
    Holey,
    /// Refused, or no exact verdict (a crash, a non-zero exit, extra output).
    /// Never a stand-in for "not evidence": a pair resting on an `evaluate`
    /// step pinned Carcara misjudges, or read with a rebound or captured
    /// variable, fails the test before the checker runs
    /// (`refuse_pinned_carcara_misjudgments`), so a refusal-direction
    /// assertion cannot pass on it.
    Invalid,
}

/// Run pinned Carcara with NO allowance and return its exact verdict. A pair
/// on which that verdict is not evidence (`ay_core::pinned_carcara`) fails the
/// test first, before the checker runs.
///
/// The verdict is the one in AY's canonical invocation,
/// `carcara check -- PROOF PROBLEM`, the same as `exact_carcara_verdict`'s.
/// This runner used to pass `--expand-let-bindings`, which only changes the
/// verdict when a document or its problem spells a `let`, and there it
/// contradicts the certificate: it refuses the `:rule let` step AY eliminates
/// a problem `let` with (`carcara_surface=without-let-expansion`), and it
/// accepts an `assume` that matches a `let` premise only after expansion,
/// which AY discloses as `foreign_assumes=yes`. Measured with carcara 1.1.0
/// (git 9a352ee) on `QF_BV_extract_concat/ext_con_004_001_0016`: plain
/// `valid`, under the flag `checking failed on step 't0.l' with rule 'let'`.
///
/// The old invocation stays as a second check: a `valid` document that prints
/// no `:rule let` step must be `valid` under `--expand-let-bindings` too, as
/// `carcara_surface=supported` promises. A failure is an invocation-dependent
/// step the certificate does not disclose.
#[cfg(test)]
fn carcara_verdict_without_allowances(
    carcara: &Path,
    label: &str,
    problem: &str,
    proof: &str,
) -> CarcaraVerdict {
    refuse_pinned_carcara_misjudgments(label, problem, proof);
    let (problem_path, proof_path) = write_problem_and_proof(label, problem, proof);

    let run = |flags: &[&str]| {
        std::process::Command::new(carcara)
            .arg("check")
            .args(flags)
            .arg("--")
            .arg(&proof_path)
            .arg(&problem_path)
            .output()
            .expect("run carcara check (no allowance)")
    };
    let output = run(&[]);

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    let verdict = carcara_stdout_verdict(output.status.success(), &stdout);
    if verdict == CarcaraVerdict::Valid && !proof.contains(":rule let") {
        let expanding = run(&["--expand-let-bindings"]);
        let expanding_stdout = String::from_utf8_lossy(&expanding.stdout);
        assert_eq!(
            carcara_stdout_verdict(expanding.status.success(), &expanding_stdout),
            CarcaraVerdict::Valid,
            "{label}: `valid` in `carcara check -- PROOF PROBLEM` but not under \
             `--expand-let-bindings`, and the document prints no `:rule let` step: \
             smt2={} alethe={} stdout={} stderr={}",
            problem_path.display(),
            proof_path.display(),
            expanding_stdout.trim(),
            String::from_utf8_lossy(&expanding.stderr).trim()
        );
    }
    if keep_alethe_artifacts() || verdict != CarcaraVerdict::Valid {
        eprintln!(
            "Preserving Alethe artifacts ({label}, carcara {verdict:?}): smt2={} alethe={}",
            problem_path.display(),
            proof_path.display()
        );
        eprintln!(
            "carcara {verdict:?} ({label}): status={:?} stdout={} stderr={}",
            output.status.code(),
            stdout.trim(),
            stderr.trim()
        );
    } else {
        let _ = std::fs::remove_file(&problem_path);
        let _ = std::fs::remove_file(&proof_path);
    }
    verdict
}

/// Run Carcara with NO allowance. Returns `true` only for the literal `valid`:
/// the proof is fully verified, with no `trust` and no `hole` step.
#[cfg(test)]
fn run_carcara_trust_free(carcara: &Path, label: &str, problem: &str, proof: &str) -> bool {
    carcara_verdict_without_allowances(carcara, label, problem, proof) == CarcaraVerdict::Valid
}

fn carcara_stdout_verdict(status_success: bool, stdout: &str) -> CarcaraVerdict {
    match (status_success, stdout.trim()) {
        (true, "valid") => CarcaraVerdict::Valid,
        (true, "holey") => CarcaraVerdict::Holey,
        _ => CarcaraVerdict::Invalid,
    }
}

fn trust_free_carcara_verdict_is_valid(status_success: bool, stdout: &str) -> bool {
    carcara_stdout_verdict(status_success, stdout) == CarcaraVerdict::Valid
}

#[test]
fn trust_free_carcara_verdict_rejects_holey_success() {
    assert!(trust_free_carcara_verdict_is_valid(true, "valid\n"));
    assert!(!trust_free_carcara_verdict_is_valid(true, "holey\n"));
    assert!(!trust_free_carcara_verdict_is_valid(false, "valid\n"));
    assert_eq!(
        carcara_stdout_verdict(true, "holey\n"),
        CarcaraVerdict::Holey
    );
    assert_eq!(
        carcara_stdout_verdict(false, "holey\n"),
        CarcaraVerdict::Invalid
    );
    assert_eq!(
        carcara_stdout_verdict(false, "invalid\n"),
        CarcaraVerdict::Invalid
    );
    assert_eq!(carcara_stdout_verdict(true, ""), CarcaraVerdict::Invalid);
    assert_eq!(
        carcara_stdout_verdict(true, "valid\nholey\n"),
        CarcaraVerdict::Invalid
    );
}

/// The defect the permissive runner had, pinned against the REAL checker: a
/// "refutation" of a SATISFIABLE problem through one unchecked step is never
/// verification. Pinned Carcara exits 0 on it (so an exit-code runner passed
/// it); the no-allowance verdict is `Invalid` for a `trust` step and `Holey`
/// for a `hole` step, and neither is `Valid`.
#[test]
#[timeout(60_000)]
fn carcara_unchecked_refutation_of_a_satisfiable_problem_is_never_verified() {
    let Some(carcara) = require_carcara_or_skip() else {
        return;
    };
    let problem = "(set-logic QF_LIA)\n(declare-const x Int)\n(assert (> x 0))\n(check-sat)\n";
    for (rule, expected) in [
        ("trust", CarcaraVerdict::Invalid),
        ("hole", CarcaraVerdict::Holey),
    ] {
        let label = format!("unchecked_{rule}_refutes_sat");
        let proof = format!(
            "(assume h1 (> x 0))\n(step t1 (cl (not (> x 0))) :rule {rule})\n\
             (step t2 (cl) :rule resolution :premises (h1 t1))\n"
        );
        assert_eq!(
            carcara_verdict_without_allowances(&carcara, &label, problem, &proof),
            expected,
            "{label}"
        );
        assert!(
            !run_carcara_trust_free(&carcara, &label, problem, &proof),
            "{label}"
        );
    }
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
