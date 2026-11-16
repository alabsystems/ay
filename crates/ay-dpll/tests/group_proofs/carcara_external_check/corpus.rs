// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// ============================================================================
// Benchmark corpus Alethe external validation
// ============================================================================

/// Per-row wall budget for AY's solve. The independent Z3 oracle has its own
/// limit, `ORACLE_TIMEOUT_SECS`: it measures a row's status, not AY's speed.
const PER_BENCHMARK_TIMEOUT_SECS: u64 = 10;

// The row-classification lists live in `corpus_rows.rs`.

struct CorpusVerificationSummary {
    /// Carcara `valid` with no allowance: the only external verification.
    verified: usize,
    verified_labels: Vec<String>,
    rejected_labels: Vec<String>,
    oracle_sat_labels: Vec<String>,
    unsupported_unsat_labels: Vec<String>,
    export_refused_labels: Vec<String>,
    /// Carcara `holey` (label, unchecked steps): published, NOT verified.
    holey_labels: Vec<(String, usize)>,
}

enum CorpusSolve {
    CertifiedProof(String),
    /// `unsat`, but `get-proof` answered with an explicit refusal.
    ExportRefused,
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
    if !(proof.contains("(assume ") || proof.contains("(step ")) {
        // Only the exact refusal form is a classifiable outcome; any other
        // command-free output is a malformed proof.
        assert!(
            ORACLE_UNSAT_EXPORT_REFUSED_ROWS.contains(&label)
                && proof.contains("(error \"UNVERIFIABLE PROOF:"),
            "{label}: proof lacks Alethe commands: {}",
            proof
                .lines()
                .find(|line| line.starts_with("(error"))
                .unwrap_or("")
        );
        return CorpusSolve::ExportRefused;
    }

    CorpusSolve::CertifiedProof(proof)
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
        verified_labels: Vec::new(),
        rejected_labels: Vec::new(),
        oracle_sat_labels: Vec::new(),
        unsupported_unsat_labels: Vec::new(),
        export_refused_labels: Vec::new(),
        holey_labels: Vec::new(),
    };

    for path in smt2_files {
        let label = benchmark_label(path);
        let content = std::fs::read_to_string(path)
            .unwrap_or_else(|e| panic!("failed to read {}: {e}", path.display()));

        match solve_corpus_with_timeout(&content, &label) {
            CorpusSolve::CertifiedProof(proof) => {
                match carcara_verdict_without_allowances(carcara, &label, &content, &proof) {
                    CarcaraVerdict::Valid => {
                        summary.verified += 1;
                        summary.verified_labels.push(label);
                    }
                    // Every step re-derived except disclosed holes: published
                    // but NOT verified, so the refutation needs Z3's `unsat`.
                    CarcaraVerdict::Holey => {
                        let unchecked = unchecked_proof_steps(&proof);
                        for step in &unchecked {
                            eprintln!("  HOLEY {label}: {step}");
                        }
                        assert_eq!(
                            z3_oracle_status(path, &label),
                            "unsat",
                            "{label}: independent oracle disagrees with a holey UNSAT proof"
                        );
                        summary.holey_labels.push((label, unchecked.len()));
                    }
                    CarcaraVerdict::Invalid => summary.rejected_labels.push(label),
                }
            }
            CorpusSolve::ExportRefused => {
                assert_eq!(
                    z3_oracle_status(path, &label),
                    "unsat",
                    "{label}: independent oracle disagrees with export-refused UNSAT classification"
                );
                summary.export_refused_labels.push(label);
            }
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

    report_z3_oracle(&summary);
    summary
}

#[cfg(test)]
fn assert_corpus_expectations(total: usize, summary: &CorpusVerificationSummary) {
    let rejected = summary.rejected_labels.len();
    let oracle_sat = summary.oracle_sat_labels.len();
    let unsupported = summary.unsupported_unsat_labels.len();
    let export_refused = summary.export_refused_labels.len();
    let verified = summary.verified;
    let holey = summary.holey_labels.len();

    eprintln!(
        "Carcara corpus: {verified} proofs verified (`valid`), {holey} published holey \
         (NOT verified), {rejected} rejected, {unsupported} oracle-UNSAT fail-closed \
         unsupported, {export_refused} oracle-UNSAT export-refused, {oracle_sat} oracle-SAT \
         non-obligations"
    );
    for label in &summary.rejected_labels {
        eprintln!("  REJECTED: {label}");
    }
    for (label, holes) in &summary.holey_labels {
        eprintln!("  HOLEY (oracle UNSAT, {holes} unchecked step(s), NOT verified): {label}");
    }
    for label in &summary.unsupported_unsat_labels {
        eprintln!("  UNSUPPORTED (oracle UNSAT, AY UNKNOWN): {label}");
    }
    for label in &summary.export_refused_labels {
        eprintln!("  EXPORT REFUSED (oracle UNSAT, AY UNSAT, no document): {label}");
    }
    for label in &summary.oracle_sat_labels {
        eprintln!("  NOT A PROOF OBLIGATION (oracle SAT): {label}");
    }

    assert_published_rows(summary);
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
    let actual_export_refused: BTreeSet<&str> = summary
        .export_refused_labels
        .iter()
        .map(String::as_str)
        .collect();
    let expected_export_refused: BTreeSet<&str> =
        ORACLE_UNSAT_EXPORT_REFUSED_ROWS.iter().copied().collect();
    assert_eq!(
        actual_export_refused, expected_export_refused,
        "oracle-UNSAT export-refused corpus classification drifted"
    );
    assert_eq!(
        verified + holey + unsupported + export_refused + oracle_sat,
        total,
        "every corpus row must be externally proof-verified or independently oracle-classified"
    );
}

/// The published-row checks: the exact holey set (label and unchecked-step
/// count), and every required publication row verified or exactly holey.
#[cfg(test)]
fn assert_published_rows(summary: &CorpusVerificationSummary) {
    let actual_holey: BTreeSet<(&str, usize)> = summary
        .holey_labels
        .iter()
        .map(|(label, holes)| (label.as_str(), *holes))
        .collect();
    let expected_holey: BTreeSet<(&str, usize)> =
        ORACLE_UNSAT_HOLEY_PROOF_ROWS.iter().copied().collect();
    assert_eq!(
        actual_holey, expected_holey,
        "holey-proof corpus classification drifted (label, unchecked steps): a `valid` row \
         leaves ORACLE_UNSAT_HOLEY_PROOF_ROWS; a new or changed hole is recorded there with \
         its measured reason, never counted as verified"
    );
    let actual_published: BTreeSet<&str> = summary
        .verified_labels
        .iter()
        .map(String::as_str)
        .chain(actual_holey.iter().map(|(label, _)| *label))
        .collect();
    let required: BTreeSet<&str> = REQUIRED_DIVISIBILITY_PUBLICATION_ROWS
        .iter()
        .copied()
        .collect();
    assert!(
        required.is_subset(&actual_published),
        "required semantic-publication rows were neither Carcara-verified nor exactly listed \
         holey: {:?}",
        required
            .difference(&actual_published)
            .copied()
            .collect::<Vec<_>>()
    );
}

/// Exhaustive Carcara validation for all UNSAT SMT benchmarks.
///
/// Solves each benchmark with proof generation, validates with Carcara.
/// Oracle-SAT filename matches are excluded from the proof denominator. Every
/// oracle-UNSAT row must either have a Carcara-verified (`valid`, no allowance)
/// proof, publish exactly its listed `holey` proof (never counted verified),
/// have exactly its listed export refusal, or return exact fail-closed UNKNOWN
/// under the explicit unsupported list; there is no generic skip path. This is
/// the authoritative external publication gate and is deliberately
/// non-optional: unlike ancillary checker tests, a missing or misconfigured
/// Carcara executable fails the test instead of silently returning.
#[test]
#[cfg_attr(debug_assertions, timeout(300_000))]
#[cfg_attr(not(debug_assertions), timeout(120_000))]
fn test_carcara_external_unsat_benchmark_corpus() {
    let carcara = required_carcara_for_corpus();

    let smt2_files = collect_unsat_smt2_benchmarks();
    assert!(
        !smt2_files.is_empty(),
        "No unsat*.smt2 benchmark files found"
    );

    let total = smt2_files.len();
    let summary = run_unsat_benchmark_corpus(&carcara, &smt2_files);
    assert_corpus_expectations(total, &summary);
}

/// Focused real-checker gate for the four lattice-lowering corpus rows. This
/// is intentionally mandatory for the same reason as the canonical corpus gate.
///
/// CONTRACT CORRECTED 2026-09-23. It claimed all four documents were
/// completely discharged; that was only ever read through an exit-code runner
/// that accepted `holey`. Two are Carcara `valid` with no allowance; the other
/// two carry one multi-equality lattice `hole` each, measured at `b39a5c9c8`
/// (where this gate was written), `8d9e105fa` and `69efb137d`. Each row is now held to
/// its exact verdict, which is strictly more than the old gate checked.
///
/// 2026-09-26: the all-equality lattice lowering retired both holes, so all
/// four rows are held to Carcara `valid` (none is listed holey any more).
#[test]
#[cfg_attr(debug_assertions, timeout(120_000))]
#[cfg_attr(not(debug_assertions), timeout(60_000))]
fn test_carcara_checked_divisibility_wire_rows() {
    let carcara = required_carcara_for_corpus();
    let smt2_files: Vec<PathBuf> = collect_unsat_smt2_benchmarks()
        .into_iter()
        .filter(|path| {
            let label = benchmark_label(path);
            CHECKED_DIVISIBILITY_WIRE_ROWS.contains(&label.as_str())
        })
        .collect();
    let actual: BTreeSet<String> = smt2_files
        .iter()
        .map(|path| benchmark_label(path))
        .collect();
    let expected: BTreeSet<String> = CHECKED_DIVISIBILITY_WIRE_ROWS
        .iter()
        .map(|label| (*label).to_string())
        .collect();
    assert_eq!(actual, expected, "focused Carcara row set drifted");

    // A focused row is Carcara `valid` unless it is exactly listed holey.
    let (expected_holey, expected_valid): (BTreeSet<String>, BTreeSet<String>) = expected
        .iter()
        .cloned()
        .partition(|label| listed_holey_row(label).is_some());
    let summary = run_unsat_benchmark_corpus(&carcara, &smt2_files);
    assert!(
        summary.rejected_labels.is_empty(),
        "{:?}",
        summary.rejected_labels
    );
    assert_eq!(summary.unsupported_unsat_labels, [] as [String; 0]);
    assert_eq!(summary.oracle_sat_labels, [] as [String; 0]);
    assert_eq!(summary.verified, expected_valid.len());
    assert_eq!(
        summary.verified_labels.into_iter().collect::<BTreeSet<_>>(),
        expected_valid,
        "focused rows Carcara verified (`valid`, no allowance)"
    );
    for (label, holes) in &summary.holey_labels {
        assert_eq!(
            Some(*holes),
            listed_holey_row(label),
            "{label}: unchecked steps"
        );
    }
    assert_eq!(
        summary
            .holey_labels
            .into_iter()
            .map(|(label, _)| label)
            .collect::<BTreeSet<_>>(),
        expected_holey,
        "focused rows published holey (NOT verified)"
    );
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
