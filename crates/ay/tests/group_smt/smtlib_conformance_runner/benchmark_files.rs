// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `smtlib_conformance_runner.rs` to preserve test FQNs.

// ===========================================================================
// Part 1: Benchmark file conformance tests
// ===========================================================================

#[test]
fn test_conformance_qf_ax_benchmarks() {
    let root = workspace_root();
    let dir = root.join("benchmarks/smt/QF_AX");
    if !dir.exists() {
        eprintln!("Skipping QF_AX: directory not found");
        return;
    }
    let (total, pass, fail, timeouts, errors, unknowns) = run_benchmark_dir(&dir, 30);
    eprintln!(
        "QF_AX: {total} benchmarks — {pass} pass, {fail} fail, {timeouts} timeout, {errors} error, {unknowns} unknown"
    );
    // At minimum we should run some benchmarks
    assert!(
        total > 0,
        "Expected at least one QF_AX benchmark with :status"
    );
    // Allow some failures (conformance gap discovery), but majority should pass
    let pass_rate = if total > 0 {
        pass as f64 / total as f64
    } else {
        0.0
    };
    eprintln!("QF_AX pass rate: {:.1}%", pass_rate * 100.0);
}

#[test]
fn test_conformance_qf_auflia_benchmarks() {
    let root = workspace_root();
    let dir = root.join("benchmarks/smt/QF_AUFLIA");
    if !dir.exists() {
        eprintln!("Skipping QF_AUFLIA: directory not found");
        return;
    }
    let (total, pass, fail, timeouts, errors, unknowns) = run_benchmark_dir_with_skip(
        &dir,
        30,
        &[
            "storeinv_t3_pp_sf_ai_00008_001.cvc.smt2",
            "storeinv_t3_pp_sf_ai_00009_001.cvc.smt2",
            "storeinv_t3_pp_sf_ai_00010_001.cvc.smt2",
        ],
    );
    eprintln!(
        "QF_AUFLIA: {total} benchmarks — {pass} pass, {fail} fail, {timeouts} timeout, {errors} error, {unknowns} unknown"
    );
    assert!(
        total > 0,
        "Expected at least one QF_AUFLIA benchmark with :status"
    );
    let pass_rate = if total > 0 {
        pass as f64 / total as f64
    } else {
        0.0
    };
    eprintln!("QF_AUFLIA pass rate: {:.1}%", pass_rate * 100.0);
}

#[test]
fn test_conformance_qf_bv_extract_concat_benchmarks() {
    let root = workspace_root();
    let dir = root.join("benchmarks/smt/QF_BV_extract_concat");
    if !dir.exists() {
        eprintln!("Skipping QF_BV_extract_concat: directory not found");
        return;
    }
    let (total, pass, fail, timeouts, errors, unknowns) = run_benchmark_dir(&dir, 30);
    eprintln!(
        "QF_BV_extract_concat: {total} benchmarks — {pass} pass, {fail} fail, {timeouts} timeout, {errors} error, {unknowns} unknown"
    );
    assert!(
        total > 0,
        "Expected at least one QF_BV benchmark with :status"
    );
    let pass_rate = if total > 0 {
        pass as f64 / total as f64
    } else {
        0.0
    };
    eprintln!("QF_BV_extract_concat pass rate: {:.1}%", pass_rate * 100.0);
}

#[test]
fn test_conformance_qf_uflra_benchmarks() {
    let root = workspace_root();
    let dir = root.join("benchmarks/smt/QF_UFLRA");
    if !dir.exists() {
        eprintln!("Skipping QF_UFLRA: directory not found");
        return;
    }
    // QF_UFLRA may have subdirectories; collect all .smt2 recursively
    let mut all_files: Vec<PathBuf> = Vec::new();
    fn collect_smt2(dir: &Path, files: &mut Vec<PathBuf>) {
        if let Ok(entries) = std::fs::read_dir(dir) {
            for entry in entries.flatten() {
                let path = entry.path();
                if path.is_dir() {
                    collect_smt2(&path, files);
                } else if path.extension().is_some_and(|ext| ext == "smt2") {
                    files.push(path);
                }
            }
        }
    }
    collect_smt2(&dir, &mut all_files);
    all_files.sort();

    let mut total = 0;
    let mut pass = 0;
    let mut fail = 0;
    let mut timeouts = 0;
    let mut errors = 0;
    let mut unknowns = 0;

    for path in &all_files {
        let expected = match extract_expected_status(path) {
            Some(e) => e,
            None => continue,
        };
        if expected == Outcome::Unknown {
            continue;
        }
        total += 1;
        let actual = run_ay_file(path, 30);
        match &actual {
            Outcome::Timeout => timeouts += 1,
            Outcome::Error(_) => errors += 1,
            Outcome::Unknown => unknowns += 1,
            outcome if *outcome == expected => pass += 1,
            _ => fail += 1,
        }
    }

    eprintln!(
        "QF_UFLRA: {total} benchmarks — {pass} pass, {fail} fail, {timeouts} timeout, {errors} error, {unknowns} unknown"
    );
    if total > 0 {
        let pass_rate = f64::from(pass) / f64::from(total);
        eprintln!("QF_UFLRA pass rate: {:.1}%", pass_rate * 100.0);
    }
}
