// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `group_soundness::soundness_comprehensive` to preserve test FQNs.

// ===========================================================================
// TEST: Benchmark files from benchmarks/sat/unsat/
// ===========================================================================

/// Verify all benchmarks/sat/unsat/*.cnf files return UNSAT or timeout.
/// This covers the full UNSAT corpus including graph coloring, pigeonhole,
/// Tseitin, mutex, parity, and random 3-SAT benchmarks.
#[test]
fn all_unsat_benchmarks() {
    let benchmarks = [
        "benchmarks/sat/unsat/at_most_1_of_5.cnf",
        "benchmarks/sat/unsat/blocked_chain_8.cnf",
        "benchmarks/sat/unsat/cardinality_8.cnf",
        "benchmarks/sat/unsat/double_parity_5.cnf",
        "benchmarks/sat/unsat/graph_coloring_k3_4clique.cnf",
        "benchmarks/sat/unsat/graph_coloring_k4_5clique.cnf",
        "benchmarks/sat/unsat/graph_coloring_k5_6clique.cnf",
        "benchmarks/sat/unsat/latin_square_2x2_conflict.cnf",
        "benchmarks/sat/unsat/mutex_4proc.cnf",
        "benchmarks/sat/unsat/mutex_6proc.cnf",
        "benchmarks/sat/unsat/mutilated_chessboard_2x2.cnf",
        "benchmarks/sat/unsat/ordering_cycle_5.cnf",
        "benchmarks/sat/unsat/parity_6.cnf",
        "benchmarks/sat/unsat/php_4_3.cnf",
        "benchmarks/sat/unsat/php_5_4.cnf",
        "benchmarks/sat/unsat/php_6_5.cnf",
        "benchmarks/sat/unsat/php_7_6.cnf",
        "benchmarks/sat/unsat/php_functional_5_4.cnf",
        "benchmarks/sat/unsat/ramsey_r3_3_6.cnf",
        "benchmarks/sat/unsat/random_3sat_50_213_s12345.cnf",
        "benchmarks/sat/unsat/random_3sat_50_213_s12349.cnf",
        "benchmarks/sat/unsat/resolution_chain_12.cnf",
        "benchmarks/sat/unsat/tseitin_cycle_11.cnf",
        "benchmarks/sat/unsat/tseitin_grid_3x3.cnf",
        "benchmarks/sat/unsat/tseitin_k5.cnf",
        "benchmarks/sat/unsat/tseitin_random_15.cnf",
        "benchmarks/sat/unsat/urquhart_3.cnf",
    ];

    let mut solved = 0usize;
    let mut timeouts = 0usize;

    for path in &benchmarks {
        let label = path.rsplit('/').next().unwrap_or(path);
        let cnf = super::common::load_repo_benchmark(path);
        let formula = ay_sat::parse_dimacs(&cnf).expect("parse");
        let original_clauses = formula.clauses.clone();

        let result = solve_and_verify_with_timeout(
            formula.num_vars,
            &original_clauses,
            label,
            Some(false), // known UNSAT
            15,
        );

        match classify(&result) {
            Verdict::Unsat => solved += 1,
            Verdict::Unknown => timeouts += 1,
            Verdict::Sat => {
                // solve_and_verify_with_timeout already panics on SAT for known-UNSAT
                unreachable!();
            }
        }
    }

    eprintln!(
        "UNSAT benchmarks: {solved} solved, {timeouts} timeouts (of {})",
        benchmarks.len()
    );
    // All of these are small enough to solve
    assert!(
        solved >= 20,
        "Expected at least 20 UNSAT benchmarks to solve, got {solved}"
    );
}

// ===========================================================================
// TEST: Known-SAT benchmark file tests with model verification
// ===========================================================================

/// Verify the canary SAT benchmark produces a valid model.
#[test]
fn canary_sat_model_verified() {
    let cnf = super::common::load_repo_benchmark("benchmarks/sat/canary/tiny_sat.cnf");
    let formula = ay_sat::parse_dimacs(&cnf).expect("parse");
    let original_clauses = formula.clauses.clone();
    solve_and_verify(
        formula.num_vars,
        &original_clauses,
        "canary-sat",
        Some(true),
    );
}

/// Verify the canary UNSAT benchmark.
#[test]
fn canary_unsat_verified() {
    let cnf = super::common::load_repo_benchmark("benchmarks/sat/canary/tiny_unsat.cnf");
    let formula = ay_sat::parse_dimacs(&cnf).expect("parse");
    let original_clauses = formula.clauses.clone();
    solve_and_verify(
        formula.num_vars,
        &original_clauses,
        "canary-unsat",
        Some(false),
    );
}

/// Known SAT benchmarks from must_solve.txt.
#[test]
fn must_solve_sat_benchmarks_model_verified() {
    let sat_benchmarks = [
        "benchmarks/sat/satcomp2024-sample/08ccc34df5d8eb9e9d45278af3dc093d-simon-r16-1.sanitized.cnf",
        "benchmarks/sat/satcomp2024-sample/7083b70c1976162e2693d7a493717ffd-battleship-14-26-sat.cnf",
    ];

    for path in &sat_benchmarks {
        let label = path.rsplit('/').next().unwrap_or(path);
        let Some(cnf) = super::common::load_optional_repo_benchmark(path) else {
            eprintln!("SKIP: must-solve SAT benchmark not available at {path}");
            continue;
        };
        let formula = ay_sat::parse_dimacs(&cnf).expect("parse");
        let original_clauses = formula.clauses.clone();

        let result = solve_and_verify_with_timeout(
            formula.num_vars,
            &original_clauses,
            label,
            Some(true), // known SAT
            30,
        );

        match classify(&result) {
            Verdict::Sat => {
                // Model already verified in solve_and_verify_with_timeout
            }
            Verdict::Unknown => {
                eprintln!("{label}: timeout (performance regression, not soundness bug)");
            }
            Verdict::Unsat => {
                // solve_and_verify_with_timeout already panics
                unreachable!();
            }
        }
    }
}

// ===========================================================================
// TEST: Cross-configuration differential on generated instances
// ===========================================================================

/// Run generated instances with both default and no-inprocessing configs.
/// Verify that they agree on SAT/UNSAT (when both resolve).
#[test]
fn differential_generated_formulas() {
    let mut rng = Rng::new(0x7904_D1FF_0001);
    let mut agreements = 0usize;
    let mut disagreements = Vec::new();

    for i in 0..40 {
        let num_vars = 15u32;
        let num_clauses = (f64::from(num_vars) * 4.267).round() as usize;
        let (nv, clauses) = generate_random_3sat(&mut rng, num_vars, num_clauses);
        let label = format!("diff-15v-{i}");

        let r1 = solve_and_verify(nv, &clauses, &format!("{label}-default"), None);
        let r2 = solve_no_inprocessing_and_verify(nv, &clauses, &format!("{label}-baseline"), None);

        let v1 = classify(&r1);
        let v2 = classify(&r2);

        if v1 != Verdict::Unknown && v2 != Verdict::Unknown {
            if v1 != v2 {
                disagreements.push(format!("{label}: default={v1:?}, baseline={v2:?}"));
            } else {
                agreements += 1;
            }
        }
    }

    eprintln!(
        "differential test: {agreements} agreements, {} disagreements (of 40)",
        disagreements.len()
    );
    assert!(
        disagreements.is_empty(),
        "SOUNDNESS BUG: configuration disagreements:\n{}",
        disagreements.join("\n")
    );
}

// ===========================================================================
// TEST: SATCOMP2024 sample benchmarks (mixed SAT/UNSAT)
// ===========================================================================

/// Run SATCOMP2024 sample benchmarks (.cnf and .cnf.xz) with a timeout.
/// Verify SAT models and ensure no false UNSAT on known-SAT instances.
#[test]
fn satcomp2024_sample_model_verification() {
    let root = super::common::workspace_root();
    let sample_dir = root.join("benchmarks/sat/satcomp2024-sample");
    if !sample_dir.is_dir() {
        eprintln!("SKIP: satcomp2024-sample directory not found");
        return;
    }

    let mut sat_verified = 0usize;
    let mut unsat_count = 0usize;
    let mut timeouts = 0usize;
    let mut failures = Vec::new();

    // Collect .cnf and .cnf.xz files. Benchmarks may be stored compressed
    // to save space (#8116).
    let entries: Vec<_> = std::fs::read_dir(&sample_dir)
        .expect("read sample dir")
        .filter_map(Result::ok)
        .filter(|e| {
            let p = e.path();
            p.extension().is_some_and(|ext| ext == "cnf")
                || (p.extension().is_some_and(|ext| ext == "xz")
                    && p.to_string_lossy().ends_with(".cnf.xz"))
        })
        .collect();

    // Limit to first 5 compressed benchmarks to keep test runtime reasonable.
    let max_xz = 5usize;
    let mut xz_count = 0usize;

    for entry in &entries {
        let path = entry.path();
        let is_xz = path.extension().is_some_and(|ext| ext == "xz");
        if is_xz {
            if xz_count >= max_xz {
                continue;
            }
            xz_count += 1;
        }
        let label = path.file_name().unwrap().to_string_lossy().to_string();

        let cnf = match super::common::load_optional_benchmark(&path) {
            Some(s) => s,
            None => continue,
        };

        let formula = match ay_sat::parse_dimacs(&cnf) {
            Ok(f) => f,
            Err(e) => {
                failures.push(format!("{label}: parse error: {e}"));
                continue;
            }
        };

        let original_clauses = formula.clauses.clone();

        // Use timeout since some benchmarks are hard
        let result = solve_and_verify_with_timeout(
            formula.num_vars,
            &original_clauses,
            &label,
            None, // we don't know the expected result for all
            15,
        );

        match classify(&result) {
            Verdict::Sat => sat_verified += 1,
            Verdict::Unsat => unsat_count += 1,
            Verdict::Unknown => timeouts += 1,
        }
    }

    eprintln!(
        "SATCOMP2024 sample: {} SAT (model verified), {} UNSAT, {} timeouts, {} failures (of {})",
        sat_verified,
        unsat_count,
        timeouts,
        failures.len(),
        entries.len()
    );

    assert!(
        failures.is_empty(),
        "SATCOMP2024 sample failures:\n{}",
        failures.join("\n")
    );

    if sat_verified + unsat_count == 0 {
        eprintln!(
            "SATCOMP2024 sample: all available benchmarks timed out; no wrong answer observed"
        );
    }
}

// ===========================================================================
// TEST: Inline known formulas
// ===========================================================================

/// PHP(3,2) from common module (cross-check against generated version).
#[test]
fn inline_php32_cross_check() {
    // Parse the DIMACS version from common
    let formula = ay_sat::parse_dimacs(super::common::PHP32_DIMACS).expect("parse PHP(3,2)");
    let result_dimacs = solve_and_verify(
        formula.num_vars,
        &formula.clauses,
        "PHP(3,2)-dimacs",
        Some(false),
    );

    // Compare with generated version
    let (nv, clauses) = generate_php(3, 2);
    let result_gen = solve_and_verify(nv, &clauses, "PHP(3,2)-gen", Some(false));

    assert_eq!(
        classify(&result_dimacs),
        classify(&result_gen),
        "PHP(3,2) DIMACS vs generated should agree"
    );
}

/// PHP(4,3) from common module.
#[test]
fn inline_php43_cross_check() {
    let formula = ay_sat::parse_dimacs(super::common::PHP43_DIMACS).expect("parse PHP(4,3)");
    solve_and_verify(
        formula.num_vars,
        &formula.clauses,
        "PHP(4,3)-dimacs",
        Some(false),
    );
}

// ===========================================================================
// TEST: Regression for the original P0 bug (any public .cnf returning wrong answer)
// ===========================================================================

/// Run all public .cnf files under benchmarks/sat/ (non-recursive, excluding
/// subdirectories already tested) to ensure no wrong answers. This catches
/// the case where a new benchmark is added and ay gives a wrong answer.
#[test]
fn all_benchmark_cnf_no_wrong_answer() {
    let root = super::common::workspace_root();

    // Collect all .cnf files under benchmarks/sat/ recursively.
    // Skip .xz files (decompression is slow).
    let mut all_cnf = Vec::new();
    collect_cnf_files(&root.join("benchmarks/sat"), &mut all_cnf);

    let mut sat_verified = 0usize;
    let mut unsat_count = 0usize;
    let mut timeouts = 0usize;
    let mut errors = Vec::new();

    for path in &all_cnf {
        let label = path
            .strip_prefix(&root)
            .unwrap_or(path)
            .display()
            .to_string();

        let cnf = match std::fs::read_to_string(path) {
            Ok(s) => s,
            Err(_) => continue, // skip unreadable files
        };

        let formula = match ay_sat::parse_dimacs(&cnf) {
            Ok(f) => f,
            Err(_) => continue, // skip unparseable files
        };

        let original_clauses = formula.clauses.clone();
        let proof_writer = ProofOutput::drat_text(Vec::<u8>::new());
        let mut solver = Solver::with_proof_output(formula.num_vars, proof_writer);
        for clause in &original_clauses {
            solver.add_clause(clause.clone());
        }

        let started = Instant::now();
        let timeout = std::time::Duration::from_secs(10);
        let result = solver
            .solve_interruptible(|| started.elapsed() >= timeout)
            .into_inner();

        match &result {
            SatResult::Sat(model) => {
                if let Some(ci) = find_violated_clause(&original_clauses, model) {
                    errors.push(format!(
                        "SOUNDNESS BUG: [{label}] SAT model violates clause {ci}"
                    ));
                } else {
                    sat_verified += 1;
                }
            }
            SatResult::Unsat(_) => {
                // Verify the DRAT proof for every UNSAT result.
                if let Some(writer) = solver.take_proof_writer() {
                    let proof_bytes = writer.into_vec().expect("proof writer flush");
                    let check_result =
                        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                            verify_drat_proof_native(
                                formula.num_vars,
                                &original_clauses,
                                &proof_bytes,
                                &label,
                            );
                        }));
                    if let Err(e) = check_result {
                        let msg = if let Some(s) = e.downcast_ref::<String>() {
                            s.clone()
                        } else {
                            format!("{label}: DRAT verification panicked")
                        };
                        errors.push(msg);
                    }
                }
                unsat_count += 1;
            }
            SatResult::Unknown => {
                timeouts += 1;
            }
            _ => unreachable!(),
        }
    }

    eprintln!(
        "All benchmark .cnf files: {} SAT verified, {} UNSAT, {} timeouts, {} errors (of {})",
        sat_verified,
        unsat_count,
        timeouts,
        errors.len(),
        all_cnf.len()
    );

    assert!(
        errors.is_empty(),
        "SOUNDNESS BUGS found in benchmark .cnf files:\n{}",
        errors.join("\n")
    );
}
