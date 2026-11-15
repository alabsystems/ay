// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// ============================================================================
// The corpus's independent Z3 oracle: its own limit, its identity (which the
// gates report), its decision rule, and the oracle leg run alone
// ============================================================================

/// The `-T:` wall limit of ONE Z3 oracle query. It is deliberately NOT AY's
/// per-row solve budget ([`PER_BENCHMARK_TIMEOUT_SECS`], which it shared until
/// 2026-09-24): the oracle is independent evidence of a row's status, not a
/// measure of AY's speed, so a change to AY's budget must not move it.
///
/// Its value is measured, not inherited: on 2026-09-24 at `ad60a0707`, over
/// every corpus row under z3 4.8.12, 4.16.0 and 5.1.0 at -T:10, -T:30 and
/// -T:120 (load 16-40 on 20 cores), every whole-row query answers in at most
/// 0.04 s except `model_checker_consumer_quantified_counterexample_typed_vec_pins_cell64_unsat`,
/// which neither 4.16.0 nor 5.1.0 decides at any limit (see its row in
/// `ORACLE_UNSAT_UNSUPPORTED_ROWS`): `timeout` at 10 s, then `unknown` after
/// 26-35 s and 5.6 GB RSS even at -T:120. A longer limit would classify
/// nothing more and would spend that time and memory on every gate run under
/// those versions. Raise it only for a measured row that needs it.
const ORACLE_TIMEOUT_SECS: u64 = 10;

/// The row whose `set-logic` the oracle broadens (see [`z3_oracle_classify`]).
const ORACLE_ALL_PROFILE_ROW: &str = "regression_false_unsat_cegqi_entailed_inner_forall_witness";

/// The mandatory corpus oracle, reached by path and identity-checked by
/// `ay_test_support::z3` (`Z3_PATH`, else the first z3 on `PATH` that proves
/// it is z3, past reroute stubs), with its limit: the identity every gate
/// that consulted it reports. A program that does not identify as Z3 fails
/// the gate: its `sat`/`unsat` lines are not independent evidence.
#[cfg(test)]
fn z3_oracle_identity() -> &'static str {
    static IDENTITY: std::sync::OnceLock<String> = std::sync::OnceLock::new();
    IDENTITY.get_or_init(|| {
        let oracle = ay_test_support::z3::require_z3("ay-dpll carcara corpus oracle");
        format!("{}, -T:{ORACLE_TIMEOUT_SECS}", oracle.identity())
    })
}

/// One oracle query: the identified program with [`ORACLE_TIMEOUT_SECS`].
#[cfg(test)]
fn z3_oracle_command() -> std::process::Command {
    let mut command = ay_test_support::z3::require_z3("ay-dpll carcara corpus oracle").command();
    command.arg(format!("-T:{ORACLE_TIMEOUT_SECS}"));
    command
}

/// Z3's independent classification of one corpus row, `sat` or `unsat`, or
/// why it cannot confirm the row (see [`classify_oracle_answers`]).
#[cfg(test)]
fn z3_oracle_classify(path: &Path, label: &str) -> Result<&'static str, String> {
    let identity = z3_oracle_identity();
    let mut command = z3_oracle_command();
    let output = if label == ORACLE_ALL_PROFILE_ROW {
        // Z3 4.8.12 accepts constant arrays only under its `ALL` parser
        // profile. Keep AY's exact AUFLIA regression unchanged, but broaden
        // only the oracle's syntax profile in memory; `set-logic` does not
        // change the formula asserted below it. Exact-prefix matching makes a
        // fixture edit fail closed instead of silently transforming new input.
        let source = std::fs::read_to_string(path)
            .unwrap_or_else(|e| panic!("{label}: read oracle input: {e}"));
        let body = source
            .strip_prefix("(set-logic AUFLIA)\n")
            .unwrap_or_else(|| panic!("{label}: guarded Z3 logic-profile prefix changed"));
        let oracle_source = format!("(set-logic ALL)\n{body}");
        let mut child = command
            .arg("-in")
            .stdin(std::process::Stdio::piped())
            .stdout(std::process::Stdio::piped())
            .stderr(std::process::Stdio::piped())
            .spawn()
            .unwrap_or_else(|e| panic!("{label}: spawn the Z3 oracle ({identity}): {e}"));
        std::io::Write::write_all(
            child.stdin.as_mut().expect("piped Z3 stdin must exist"),
            oracle_source.as_bytes(),
        )
        .unwrap_or_else(|e| panic!("{label}: write guarded oracle input: {e}"));
        child
            .wait_with_output()
            .unwrap_or_else(|e| panic!("{label}: collect Z3 oracle result: {e}"))
    } else {
        command
            .arg(path)
            .output()
            .unwrap_or_else(|e| panic!("{label}: spawn the Z3 oracle ({identity}): {e}"))
    };
    classify_oracle_answers(
        label,
        identity,
        if output.status.success() {
            Ok(())
        } else {
            Err(output.status.code())
        },
        &String::from_utf8_lossy(&output.stdout),
        &String::from_utf8_lossy(&output.stderr),
        || z3_quantifier_free_subset_status(path, label),
    )
}

/// [`z3_oracle_classify`], failing the calling gate when Z3 cannot confirm.
#[cfg(test)]
fn z3_oracle_status(path: &Path, label: &str) -> String {
    z3_oracle_classify(path, label)
        .unwrap_or_else(|why| panic!("{why}"))
        .to_string()
}

/// The oracle's decision rule, apart from the spawns so it is testable
/// without Z3. `whole` is the whole-row run's exit (`Err` carries a failing
/// exit code) and output; `subset` queries the row's quantifier-free subset.
///
/// Exactly one `sat` or `unsat` line from a successful run classifies the
/// row. Only when that answer is `timeout` or `unknown` is the subset
/// consulted, and only its exact `unsat` is taken: unsatisfiability is
/// monotone, so a refuted subset of the row's own assertions refutes the row
/// exactly as independently as an `unsat` on the whole file. Everything else
/// is an oracle that cannot confirm, exception class (c) of
/// the development design notes section 5.7, reported
/// with the Z3 identity and never read as a verdict.
#[cfg(test)]
fn classify_oracle_answers(
    label: &str,
    identity: &str,
    whole: Result<(), Option<i32>>,
    stdout: &str,
    stderr: &str,
    subset: impl FnOnce() -> Option<String>,
) -> Result<&'static str, String> {
    if let Err(code) = whole {
        return Err(format!(
            "{label}: Z3 oracle ({identity}) failed: status={code:?}; stdout={}; stderr={}",
            stdout.trim(),
            stderr.trim(),
        ));
    }
    let output_lines: Vec<String> = stdout
        .lines()
        .map(str::trim)
        .filter(|line| !line.is_empty())
        .map(str::to_ascii_lowercase)
        .collect();
    match output_lines.as_slice() {
        [status] if status == "sat" => Ok("sat"),
        [status] if status == "unsat" => Ok("unsat"),
        [status] if status == "timeout" || status == "unknown" => match subset() {
            Some(answer) if answer == "unsat" => {
                eprintln!(
                    "  Z3 ORACLE {label}: whole row {output_lines:?}; its quantifier-free \
                     assertions are unsat ({identity})"
                );
                Ok("unsat")
            }
            answer => Err(format!(
                "{label}: the Z3 oracle ({identity}) cannot classify this row: whole row \
                 {output_lines:?}; quantifier-free subset {}. An oracle that cannot confirm is \
                 exception class (c) (the development design notes \
                 section 5.7): record the evidence with the Z3 version, never skip the row",
                answer.unwrap_or_else(|| "none (no quantified assertion to drop)".to_string()),
            )),
        },
        _ => Err(format!(
            "{label}: Z3 oracle ({identity}) must emit exactly one terminal status: \
             {output_lines:?}; stderr={}",
            stderr.trim(),
        )),
    }
}

/// Z3's answer on the row's [`quantifier_free_subset`], `None` when there is
/// no quantified assertion to drop (or the splitter declines). Only an exit-0
/// run whose whole stdout is `unsat` reads as `unsat`.
#[cfg(test)]
fn z3_quantifier_free_subset_status(path: &Path, label: &str) -> Option<String> {
    let source =
        std::fs::read_to_string(path).unwrap_or_else(|e| panic!("{label}: read oracle input: {e}"));
    let subset_script = quantifier_free_subset(&source)?;
    let directory = tempfile::tempdir().expect("temporary oracle directory");
    let subset = directory.path().join("quantifier_free_subset.smt2");
    std::fs::write(&subset, subset_script).expect("write oracle subset");
    let output = z3_oracle_command()
        .arg(&subset)
        .output()
        .unwrap_or_else(|e| panic!("{label}: run Z3 on the quantifier-free subset: {e}"));
    let stdout = String::from_utf8_lossy(&output.stdout);
    Some(if output.status.success() {
        stdout.trim().to_string()
    } else {
        format!(
            "status={:?}; stdout={}",
            output.status.code(),
            stdout.trim()
        )
    })
}

/// Name the oracle a corpus run consulted, when it consulted it: every row
/// outside Carcara `valid` is oracle-classified.
#[cfg(test)]
fn report_z3_oracle(summary: &CorpusVerificationSummary) {
    let consulted = summary.holey_labels.len()
        + summary.export_refused_labels.len()
        + summary.oracle_sat_labels.len()
        + summary.unsupported_unsat_labels.len();
    if consulted > 0 {
        eprintln!(
            "Z3 oracle: {} classified {consulted} row(s)",
            z3_oracle_identity()
        );
    }
}

#[test]
fn oracle_decision_rule_takes_only_a_decided_row_or_a_refuted_subset() {
    let classify = |whole: Result<(), Option<i32>>, stdout: &str, subset: Option<&str>| {
        classify_oracle_answers("row", "Z3 version test", whole, stdout, "", || {
            subset.map(str::to_string)
        })
    };
    assert_eq!(classify(Ok(()), "sat\n", None), Ok("sat"));
    assert_eq!(classify(Ok(()), "\nUNSAT\n", None), Ok("unsat"));
    // The whole row undecided, its quantifier-free assertions refuted.
    assert_eq!(classify(Ok(()), "timeout\n", Some("unsat")), Ok("unsat"));
    assert_eq!(classify(Ok(()), "unknown\n", Some("unsat")), Ok("unsat"));
    // Negative twins: the subset is consulted only for an undecided row, and
    // nothing but its exact `unsat` confirms anything.
    assert_eq!(classify(Ok(()), "sat\n", Some("unsat")), Ok("sat"));
    for subset in [
        None,
        Some("sat"),
        Some("timeout"),
        Some("status=Some(1); stdout=unsat"),
    ] {
        let why = classify(Ok(()), "timeout\n", subset).expect_err("undecided row");
        assert!(
            why.contains("exception class (c)") && why.contains("Z3 version test"),
            "{why}"
        );
    }
    let why = classify(Ok(()), "unknown\n", None).expect_err("undecided row");
    assert!(
        why.contains("none (no quantified assertion to drop)"),
        "{why}"
    );
    // A failing run, and anything but exactly one terminal status.
    assert!(classify(Err(Some(1)), "unsat\n", Some("unsat")).is_err());
    assert!(classify(Ok(()), "", Some("unsat")).is_err());
    assert!(classify(Ok(()), "unsat\nsat\n", None).is_err());
    assert!(classify(Ok(()), "(error \"x\")\nunsat\n", None).is_err());
}

/// The oracle leg ALONE, over every row a corpus gate hands to Z3: each
/// oracle-SAT row must classify `sat`, and each unsupported, export-refused
/// and holey row `unsat`. It needs neither AY nor Carcara, so a Z3 version
/// that cannot confirm a row is named here, every such row at once and with
/// the version, instead of surfacing as the first panic inside a gate.
#[test]
#[cfg_attr(debug_assertions, timeout(300_000))]
#[cfg_attr(not(debug_assertions), timeout(120_000))]
fn test_z3_oracle_classifies_every_oracle_backed_corpus_row() {
    let unsat_rows = ORACLE_UNSAT_UNSUPPORTED_ROWS
        .iter()
        .chain(ORACLE_UNSAT_EXPORT_REFUSED_ROWS)
        .chain(ORACLE_UNSAT_HOLEY_PROOF_ROWS.iter().map(|(label, _)| label));
    let expected: std::collections::BTreeMap<&str, &str> = ORACLE_SAT_CORPUS_ROWS
        .iter()
        .map(|label| (*label, "sat"))
        .chain(unsat_rows.map(|label| (*label, "unsat")))
        .collect();
    let mut found = BTreeSet::new();
    let mut unconfirmed = Vec::new();
    for path in collect_unsat_smt2_benchmarks() {
        let label = benchmark_label(&path);
        let Some(&listed) = expected.get(label.as_str()) else {
            continue;
        };
        match z3_oracle_classify(&path, &label) {
            Ok(status) if status == listed => {}
            Ok(status) => {
                unconfirmed.push(format!("{label}: Z3 answers {status}, listed {listed}"))
            }
            Err(why) => unconfirmed.push(why),
        }
        found.insert(label);
    }
    let listed: BTreeSet<String> = expected.keys().map(|label| (*label).to_string()).collect();
    assert_eq!(
        found, listed,
        "an oracle-backed row is missing from benchmarks/smt"
    );
    eprintln!(
        "Z3 oracle: {}; {} oracle-backed row(s)",
        z3_oracle_identity(),
        found.len()
    );
    assert!(
        unconfirmed.is_empty(),
        "the Z3 oracle ({}) does not confirm {} listed row(s): {unconfirmed:#?}",
        z3_oracle_identity(),
        unconfirmed.len()
    );
}
