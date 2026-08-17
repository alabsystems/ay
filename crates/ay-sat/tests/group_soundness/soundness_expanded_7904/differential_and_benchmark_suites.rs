// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `group_soundness::soundness_expanded_7904` to preserve test FQNs.

// ===========================================================================
// TEST: Larger random 3-SAT (200 variables, phase transition)
// ===========================================================================

#[test]
fn random_3sat_200v_phase_transition() {
    let mut rng = Rng::new(0x7904_2001);
    let num_vars = 200u32;
    let num_clauses = (f64::from(num_vars) * 4.267).round() as usize;
    let mut sat_count = 0;
    let mut unsat_count = 0;

    for i in 0..10 {
        let (nv, clauses) = generate_random_3sat(&mut rng, num_vars, num_clauses);
        let r = solve_and_verify_with_timeout(nv, &clauses, &format!("random-200v-{i}"), None, 30);
        match classify(&r) {
            Verdict::Sat => sat_count += 1,
            Verdict::Unsat => unsat_count += 1,
            Verdict::Unknown => {}
        }
    }
    eprintln!("random 3-SAT (200v): {sat_count} SAT, {unsat_count} UNSAT");
    assert!(
        sat_count + unsat_count > 0,
        "expected at least one to resolve"
    );
}

#[test]
fn random_3sat_150v_below_transition() {
    let mut rng = Rng::new(0x7904_1500);
    let num_vars = 150u32;
    let num_clauses = (f64::from(num_vars) * 4.0).round() as usize;
    let mut sat_count = 0;

    for i in 0..10 {
        let (nv, clauses) = generate_random_3sat(&mut rng, num_vars, num_clauses);
        let r = solve_and_verify_with_timeout(
            nv,
            &clauses,
            &format!("random-150v-below-{i}"),
            None,
            15,
        );
        if matches!(r, SatResult::Sat(_)) {
            sat_count += 1;
        }
    }
    eprintln!("random 3-SAT (150v, ratio 4.0): {sat_count}/10 SAT");
}

#[test]
fn random_3sat_150v_above_transition() {
    let mut rng = Rng::new(0x7904_1501);
    let num_vars = 150u32;
    let num_clauses = (f64::from(num_vars) * 4.5).round() as usize;
    let mut unsat_count = 0;

    for i in 0..10 {
        let (nv, clauses) = generate_random_3sat(&mut rng, num_vars, num_clauses);
        let r = solve_and_verify_with_timeout(
            nv,
            &clauses,
            &format!("random-150v-above-{i}"),
            None,
            15,
        );
        if matches!(r, SatResult::Unsat(_)) {
            unsat_count += 1;
        }
    }
    eprintln!("random 3-SAT (150v, ratio 4.5): {unsat_count}/10 UNSAT");
}

// ===========================================================================
// TEST: Cross-configuration differential
// ===========================================================================

#[test]
fn differential_tseitin_configs() {
    let mut disagreements = Vec::new();
    let mut agreements = 0;

    for n in [3, 5, 7, 9, 11, 13, 4, 6, 8, 10, 12, 14] {
        let (nv, clauses) = generate_tseitin_cycle(n);
        let label = format!("tseitin-cycle-{n}");
        let expected = if n % 2 == 1 { Some(false) } else { Some(true) };

        let r1 = solve_and_verify(nv, &clauses, &format!("{label}-default"), expected);
        let r2 =
            solve_no_inprocessing_and_verify(nv, &clauses, &format!("{label}-no-inproc"), expected);

        let v1 = classify(&r1);
        let v2 = classify(&r2);
        if v1 != Verdict::Unknown && v2 != Verdict::Unknown {
            if v1 != v2 {
                disagreements.push(format!("{label}: default={v1:?}, no-inproc={v2:?}"));
            } else {
                agreements += 1;
            }
        }
    }

    eprintln!(
        "Tseitin differential: {agreements} agreements, {} disagreements",
        disagreements.len()
    );
    assert!(
        disagreements.is_empty(),
        "SOUNDNESS BUG: config disagreements:\n{}",
        disagreements.join("\n")
    );
}

#[test]
fn differential_xor_configs() {
    let mut disagreements = Vec::new();
    let mut agreements = 0;

    for n in [3, 5, 7, 9, 11, 15, 21] {
        let (nv, clauses) = generate_xor_unsat(n);
        let label = format!("xor-{n}");

        let r1 = solve_and_verify(nv, &clauses, &format!("{label}-default"), Some(false));
        let r2 = solve_no_inprocessing_and_verify(
            nv,
            &clauses,
            &format!("{label}-no-inproc"),
            Some(false),
        );

        let v1 = classify(&r1);
        let v2 = classify(&r2);
        if v1 != Verdict::Unknown && v2 != Verdict::Unknown {
            if v1 != v2 {
                disagreements.push(format!("{label}: default={v1:?}, no-inproc={v2:?}"));
            } else {
                agreements += 1;
            }
        }
    }

    eprintln!(
        "XOR differential: {agreements} agreements, {} disagreements",
        disagreements.len()
    );
    assert!(
        disagreements.is_empty(),
        "SOUNDNESS BUG: XOR config disagreements:\n{}",
        disagreements.join("\n")
    );
}

// ===========================================================================
// TEST: SATCOMP 2022/2023 benchmark coverage
// ===========================================================================

#[test]
fn satcomp_2022_soundness() {
    let benchmarks = [
        "benchmarks/sat/2022/6f956a3f95ccaf35a3de1fe72b9cf79e.cnf",
        "benchmarks/sat/2022/81b674a2aa6fbda9b06cf8ea334ddc44.cnf",
        "benchmarks/sat/2022/efc1b836380d0f84e7512f7b2ccdbb60.cnf",
    ];
    let mut sat_verified = 0;
    let mut unsat_count = 0;
    let mut timeout_count = 0;
    let mut skipped = 0;

    for path in &benchmarks {
        let label = path.rsplit('/').next().unwrap_or(path);
        let cnf = match super::common::load_optional_repo_benchmark(path) {
            Some(c) => c,
            None => {
                skipped += 1;
                continue;
            }
        };
        let formula = ay_sat::parse_dimacs(&cnf).expect("parse");

        let r = solve_and_verify_with_timeout(formula.num_vars, &formula.clauses, label, None, 30);
        match classify(&r) {
            Verdict::Sat => sat_verified += 1,
            Verdict::Unsat => unsat_count += 1,
            Verdict::Unknown => timeout_count += 1,
        }
    }
    eprintln!("SATCOMP 2022: {sat_verified} SAT, {unsat_count} UNSAT, {timeout_count} timeouts, {skipped} skipped");
}

#[test]
fn satcomp_2023_soundness() {
    let benchmarks = ["benchmarks/sat/2023/3663000b31a5c80922afc6e48322accb.cnf"];
    for path in &benchmarks {
        let label = path.rsplit('/').next().unwrap_or(path);
        let cnf = match super::common::load_optional_repo_benchmark(path) {
            Some(c) => c,
            None => continue,
        };
        let formula = ay_sat::parse_dimacs(&cnf).expect("parse");
        let r = solve_and_verify_with_timeout(formula.num_vars, &formula.clauses, label, None, 30);
        match classify(&r) {
            Verdict::Sat | Verdict::Unsat => {}
            Verdict::Unknown => eprintln!("{label}: timeout"),
        }
    }
}

// ===========================================================================
// TEST: DRAT proof batch for UNSAT benchmarks
// ===========================================================================

#[test]
fn benchmark_unsat_drat_proof_batch() {
    let small_unsat = [
        "benchmarks/sat/unsat/at_most_1_of_5.cnf",
        "benchmarks/sat/unsat/latin_square_2x2_conflict.cnf",
        "benchmarks/sat/unsat/ordering_cycle_5.cnf",
        "benchmarks/sat/unsat/blocked_chain_8.cnf",
        "benchmarks/sat/unsat/mutex_4proc.cnf",
        "benchmarks/sat/unsat/mutilated_chessboard_2x2.cnf",
        "benchmarks/sat/unsat/php_4_3.cnf",
        "benchmarks/sat/unsat/resolution_chain_12.cnf",
    ];
    let mut verified = 0;

    for path in &small_unsat {
        let label = path.rsplit('/').next().unwrap_or(path);
        let cnf = super::common::load_repo_benchmark(path);
        let formula = ay_sat::parse_dimacs(&cnf).expect("parse");

        let mut solver =
            Solver::with_proof_output(formula.num_vars, ProofOutput::drat_text(Vec::<u8>::new()));
        for clause in &formula.clauses {
            solver.add_clause(clause.clone());
        }

        let started = Instant::now();
        let timeout = std::time::Duration::from_secs(15);
        let result = solver
            .solve_interruptible(|| started.elapsed() >= timeout)
            .into_inner();

        match result {
            SatResult::Unsat(_) => {
                let proof_output = solver.take_proof_writer().expect("proof writer");
                let proof_bytes = proof_output.into_vec().expect("flush");
                let dimacs = super::common::clauses_to_dimacs(formula.num_vars, &formula.clauses);
                super::common::verify_drat_proof(&dimacs, &proof_bytes, label);
                verified += 1;
            }
            SatResult::Sat(_) => {
                panic!("SOUNDNESS BUG: {label} is known-UNSAT but returned SAT");
            }
            SatResult::Unknown => {
                eprintln!("{label}: timeout in DRAT proof verification test");
            }
            _ => unreachable!(),
        }
    }
    eprintln!(
        "DRAT proof batch: {verified}/{} verified",
        small_unsat.len()
    );
    assert!(
        verified >= 5,
        "expected at least 5 DRAT proofs to verify, got {verified}"
    );
}

// ===========================================================================
// TEST: eq.atree.braun differential
// ===========================================================================

#[test]
fn braun_differential_default_vs_baseline() {
    let braun_files = [
        (
            "benchmarks/sat/eq_atree_braun/eq.atree.braun.8.unsat.cnf",
            "braun-8",
        ),
        (
            "benchmarks/sat/eq_atree_braun/eq.atree.braun.10.unsat.cnf",
            "braun-10",
        ),
    ];
    let mut disagreements = Vec::new();

    for (path, name) in &braun_files {
        let cnf = match super::common::load_optional_repo_benchmark(path) {
            Some(c) => c,
            None => continue,
        };
        let formula = ay_sat::parse_dimacs(&cnf).expect("parse");

        let r1 = solve_and_verify_with_timeout(
            formula.num_vars,
            &formula.clauses,
            &format!("{name}-default"),
            Some(false),
            30,
        );
        let r2 = solve_no_inprocessing_and_verify(
            formula.num_vars,
            &formula.clauses,
            &format!("{name}-no-inproc"),
            Some(false),
        );

        let v1 = classify(&r1);
        let v2 = classify(&r2);
        if v1 != Verdict::Unknown && v2 != Verdict::Unknown && v1 != v2 {
            disagreements.push(format!("{name}: default={v1:?}, no-inproc={v2:?}"));
        }
    }
    assert!(
        disagreements.is_empty(),
        "SOUNDNESS BUG: braun differential disagreements:\n{}",
        disagreements.join("\n")
    );
}
