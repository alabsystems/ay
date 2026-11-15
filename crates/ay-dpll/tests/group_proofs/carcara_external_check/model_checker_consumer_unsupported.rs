// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// ============================================================================
// MODEL_CHECKER_CONSUMER rows of the oracle-UNSAT unsupported corpus bucket
// ============================================================================

/// MODEL_CHECKER_CONSUMER rows whose plain UNSAT the nested-array quarantine withholds, with
/// the `unknown.phase` each reports (#nested-array-quarantine-datatype-fields).
///
/// Each keeps an array inside a datatype field of an outer array's element
/// (`(Array _ PbTerm)` with `PbTerm{lits: Vec{data: Array}}` and the like),
/// which is nested array state, and each published its plain UNSAT only
/// because `StaticFeatures::has_nested_arrays` read a declared carrier as an
/// opaque sort. `array-combination-quarantine` means the solve reached UNSAT
/// and the quarantine withheld it.
///
/// Each published on `discharged-trust` alone -- a fresh executor re-deciding
/// the same nested combination. The ground-refutable `nested_query_false` row
/// reports `quantifier-instantiation`: its refutation is the
/// authored-ground-core probe (d14c2313e), whose own quarantine withholds the
/// core (pinned to the quarantine phase by `ground_core_corroboration::tests::
/// a_ground_refutable_nested_record_query_is_withheld_by_the_quarantine`).
///
/// `nested_premise_false` is nested too but absent on purpose: a checked
/// quarantine rung, the exact finite-expansion theorem (b79271632), admits its
/// plain verdict. `vec_ancestor_conflict` left with #nested-array-checked-rung:
/// the array-to-UF rung renames its record carriers, adds the checked instance
/// `fld_len (Vec_mk .. 65 ..) = 65`, and refutes that on a strict proof. The
/// rung refuses the rest, measured on their abstractions: `pbterm_same_key`
/// and `inner_miss_conflict` abstract to `a' = b'` plus a four-deep chain of
/// fresh functions into a bit-vector read, which the checked probe refutes
/// only without a strict proof (the one certificate this rung accepts); the
/// `pbterm_ancestor_default` abstraction with its five instances is not
/// refuted at all. `nested_query_false` is withheld before the rung, at
/// quantifier instantiation (see above).
/// A row that gains a checked authority fails here and must leave this list:
/// `pbterm_same_key` and `inner_miss_conflict` left with the raw ground
/// closure's strict refutation (`executor/proof/authored_ground_closure.rs`),
/// a checked certificate the quarantine admits.
const QUARANTINED_MODEL_CHECKER_CONSUMER_ROWS: &[(&str, &str)] = &[
    (
        "model_checker_consumer_nested_array_residual_pbterm_ancestor_default_unsat",
        "array-combination-quarantine",
    ),
    (
        "model_checker_consumer_quantified_counterexample_nested_query_false_unsat",
        "quantifier-instantiation",
    ),
];

/// AY's first verdict, and its `unknown.phase`, on one corpus row WITHOUT
/// `:produce-proofs`, under the same per-row limit as the strict corpus solve.
/// Under the strict boundary a withheld UNSAT and a solver that no longer
/// reaches UNSAT both print `unknown`; only this run tells them apart.
#[cfg(test)]
fn plain_corpus_verdict_with_timeout(content: &str, label: &str) -> (String, Option<String>) {
    let content = content
        .lines()
        .filter(|line| line.trim() != "(exit)")
        .collect::<Vec<_>>()
        .join("\n");
    let commands = parse(&content).unwrap_or_else(|e| panic!("{label}: parse error: {e}"));

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
        "{label}: plain solve timed out ({PER_BENCHMARK_TIMEOUT_SECS}s limit)"
    );
    let outputs = outputs.unwrap_or_else(|e| panic!("{label}: plain execution error: {e}"));
    let phase = exec
        .statistics()
        .get_string("unknown.phase")
        .map(str::to_string);
    (outputs.first().cloned().unwrap_or_default(), phase)
}

/// Focused gate for the MODEL_CHECKER_CONSUMER rows of `ORACLE_UNSAT_UNSUPPORTED_ROWS`.
///
/// The canonical corpus gate panics at its first failing row, so a failure on
/// an earlier row can mask these. This runs exactly them: each file must still
/// exist, AY must answer fail-closed `unknown` under `:produce-proofs` (never
/// `sat`, never a proof carcara rejects), and Z3 must independently answer
/// `unsat`. Without proofs AY must still answer `unsat`, so the `unknown` stays
/// a WITHHELD UNSAT: a solver that stops reaching UNSAT fails here instead of
/// hiding in the unsupported bucket. The exception is
/// `QUARANTINED_MODEL_CHECKER_CONSUMER_ROWS`, whose plain UNSAT is withheld too; for those
/// the exact withholding phase stands in for the verdict. A row that gains a
/// certified proof fails here and must leave the unsupported list.
#[test]
#[cfg_attr(debug_assertions, timeout(300_000))]
#[cfg_attr(not(debug_assertions), timeout(120_000))]
fn test_carcara_model_checker_consumer_unsupported_rows_fail_closed() {
    let carcara = required_carcara_for_corpus();
    let expected: BTreeSet<String> = ORACLE_UNSAT_UNSUPPORTED_ROWS
        .iter()
        .filter(|label| label.starts_with("model_checker_consumer_"))
        .map(|label| (*label).to_string())
        .collect();
    assert!(
        !expected.is_empty(),
        "no MODEL_CHECKER_CONSUMER row is classified"
    );
    let smt2_files: Vec<PathBuf> = collect_unsat_smt2_benchmarks()
        .into_iter()
        .filter(|path| expected.contains(&benchmark_label(path)))
        .collect();
    let actual: BTreeSet<String> = smt2_files
        .iter()
        .map(|path| benchmark_label(path))
        .collect();
    assert_eq!(
        actual, expected,
        "a classified MODEL_CHECKER_CONSUMER row is missing"
    );

    let summary = run_unsat_benchmark_corpus(&carcara, &smt2_files);
    assert!(
        summary.verified_labels.is_empty(),
        "now Carcara `valid` with no allowance: remove from ORACLE_UNSAT_UNSUPPORTED_ROWS: {:?}",
        summary.verified_labels
    );
    assert!(
        summary.holey_labels.is_empty(),
        "now published but only Carcara `holey` (NOT verified): move from \
         ORACLE_UNSAT_UNSUPPORTED_ROWS to ORACLE_UNSAT_HOLEY_PROOF_ROWS with its reason: {:?}",
        summary.holey_labels
    );
    assert!(
        summary.rejected_labels.is_empty(),
        "{:?}",
        summary.rejected_labels
    );
    assert!(
        summary.oracle_sat_labels.is_empty(),
        "{:?}",
        summary.oracle_sat_labels
    );
    assert_eq!(
        summary
            .unsupported_unsat_labels
            .into_iter()
            .collect::<BTreeSet<_>>(),
        expected
    );

    for (label, _) in QUARANTINED_MODEL_CHECKER_CONSUMER_ROWS {
        assert!(
            expected.contains(*label),
            "{label}: quarantined row is not classified"
        );
    }
    for path in &smt2_files {
        let label = benchmark_label(path);
        let content = std::fs::read_to_string(path)
            .unwrap_or_else(|e| panic!("failed to read {}: {e}", path.display()));
        let (verdict, phase) = plain_corpus_verdict_with_timeout(&content, &label);
        match QUARANTINED_MODEL_CHECKER_CONSUMER_ROWS
            .iter()
            .find(|(quarantined, _)| *quarantined == label)
        {
            Some((_, expected_phase)) => assert_eq!(
                (verdict.as_str(), phase.as_deref()),
                ("unknown", Some(*expected_phase)),
                "{label}: the nested-array quarantine must still be what withholds \
                 this plain UNSAT; a different outcome means the solver or the \
                 quarantine changed"
            ),
            None => assert_eq!(
                verdict, "unsat",
                "{label}: AY no longer reaches UNSAT without proofs, so its UNKNOWN is \
                 not a withheld UNSAT; fix the solver, do not keep it classified"
            ),
        }
    }
}

/// Rows that left `QUARANTINED_MODEL_CHECKER_CONSUMER_ROWS` when the raw ground closure
/// (`executor/proof/authored_ground_closure.rs`) gave them a strictly checked
/// refutation: the nested-array quarantine now admits their plain UNSAT on
/// that certificate. Counterfactual: with the lane disabled both answer
/// `unknown` in phase `array-combination-quarantine` again.
const RETIRED_QUARANTINE_ROWS: [&str; 2] = [
    "model_checker_consumer_nested_array_residual_pbterm_same_key_unsat",
    "model_checker_consumer_store_miss_residual_inner_miss_conflict_unsat",
];

#[test]
#[cfg_attr(debug_assertions, timeout(300_000))]
#[cfg_attr(not(debug_assertions), timeout(120_000))]
fn test_retired_quarantine_rows_publish_plain_unsat() {
    let rows: Vec<PathBuf> = collect_unsat_smt2_benchmarks()
        .into_iter()
        .filter(|path| RETIRED_QUARANTINE_ROWS.contains(&benchmark_label(path).as_str()))
        .collect();
    assert_eq!(
        rows.len(),
        RETIRED_QUARANTINE_ROWS.len(),
        "a retired row is missing"
    );
    for path in &rows {
        let label = benchmark_label(path);
        let content = std::fs::read_to_string(path)
            .unwrap_or_else(|e| panic!("failed to read {}: {e}", path.display()));
        let (verdict, phase) = plain_corpus_verdict_with_timeout(&content, &label);
        assert_eq!(
            (verdict.as_str(), phase.as_deref()),
            ("unsat", None),
            "{label}: the quarantine must admit this plain UNSAT on its checked certificate"
        );
    }
}
