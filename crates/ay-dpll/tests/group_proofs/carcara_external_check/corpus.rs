// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

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
#[cfg(test)]
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

#[cfg(test)]
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
#[cfg(test)]
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

#[cfg(test)]
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

#[cfg(test)]
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
