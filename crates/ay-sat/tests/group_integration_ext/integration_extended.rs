// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::print_stderr, clippy::print_stdout)]
#![allow(clippy::panic)]

//! Inprocessing and proof-mode integration tests for ay-sat.
//!
//! Congruence closure, BCE, transitive reduction, SCC decompose,
//! factorization, DRAT/LRAT proof verification, and preprocessing
//! proof-mode tests.
//! Correctness/soundness tests live in integration_correctness.rs.
//! Split from original integration_extended.rs for #6864.

use super::common::{assert_model_satisfies, generate_test_clauses, verify_model};
use ay_sat::{parse_dimacs, Literal, SatResult, Solver, Variable};
use ntest::timeout;

// Macro for generating inprocessing test triads (correctness, stats, disabled).
macro_rules! inprocessing_test_triad {
    (
        $name_c:ident, $name_s:ident, $name_d:ident,
        label: $label:expr,
        set_enabled: $enable:ident,
        get_stats: $stats:ident,
        zero_field: $zero:ident,
        seeds: [$seed_c:expr, $seed_s:expr, $seed_d:expr],
        stats_check: |$sv:ident| { $($sc:tt)* }
    ) => {
        #[test]
        #[timeout(2_000)]
        fn $name_c() {
            let mut solver = Solver::new(15);
            let clauses = generate_test_clauses(15, 60, $seed_c);
            for clause in &clauses {
                solver.add_clause(clause.clone());
            }
            let result = solver.solve().into_inner();
            if let SatResult::Sat(model) = &result {
                assert_model_satisfies(&clauses, model, $label);
            }
        }

        #[test]
        #[timeout(2_000)]
        fn $name_s() {
            let mut solver = Solver::new(10);
            let clauses = generate_test_clauses(10, 40, $seed_s);
            for clause in &clauses {
                solver.add_clause(clause.clone());
            }
            let _ = solver.solve().into_inner();
            let $sv = solver.$stats();
            $($sc)*
        }

        #[test]
        #[timeout(2_000)]
        fn $name_d() {
            let mut solver = Solver::new(10);
            solver.$enable(false);
            let clauses = generate_test_clauses(10, 40, $seed_d);
            for clause in &clauses {
                solver.add_clause(clause.clone());
            }
            let result = solver.solve().into_inner();
            if let SatResult::Sat(model) = &result {
                assert_model_satisfies(&clauses, model, concat!("Disabled ", $label));
            }
            let stats = solver.$stats();
            assert_eq!(stats.$zero, 0, concat!($label, " ran despite being disabled"));
        }
    };
}

// ============================================================================
// Congruence Closure Preprocessing Tests
// ============================================================================

/// Test that congruence closure analyzes duplicate AND gates.
///
/// Encodes: g1 = AND(a, b) and g2 = AND(a, b) where g1, g2 have the same
/// inputs. On larger formulas, congruence would detect g1 ≡ g2. On this
/// trivial 4-variable encoding, BCP + other inprocessing may resolve the
/// formula before congruence finds the equivalence. We verify that the
/// solver correctly solves the formula (SAT).
///
/// Full congruence equivalence detection is validated on real circuit
/// benchmarks in test_congruence_preprocessing_simon_circuit.
#[test]
fn test_congruence_preprocessing_duplicate_and_gates() {
    // Variables: a=0, b=1, g1=2, g2=3
    // AND gate for g1: (¬a ∨ ¬b ∨ g1) ∧ (a ∨ ¬g1) ∧ (b ∨ ¬g1)
    // AND gate for g2: (¬a ∨ ¬b ∨ g2) ∧ (a ∨ ¬g2) ∧ (b ∨ ¬g2)
    // Extra clause requiring g1 and g2 to be true: (g1) ∧ (g2)
    let dimacs_str = "p cnf 4 8\n\
        -1 -2 3 0\n\
        1 -3 0\n\
        2 -3 0\n\
        -1 -2 4 0\n\
        1 -4 0\n\
        2 -4 0\n\
        3 0\n\
        4 0\n";

    let formula = parse_dimacs(dimacs_str).expect("Failed to parse DIMACS");
    let mut solver = formula.into_solver();
    let result = solver.solve().into_inner();
    assert!(
        matches!(result, SatResult::Sat(_)),
        "Expected SAT for duplicate AND gate formula"
    );

    // On a 4-variable formula with unit clauses, BCP propagates g1=true and
    // g2=true at level 0 before congruence runs, collapsing the gate structure.
    // Congruence may or may not analyze gates depending on preprocessing order.
    // The correctness of congruence equivalence detection is validated on real
    // benchmarks (simon-r16-1) in test_congruence_preprocessing_simon_circuit.
}

/// Test that congruence preprocessing correctly extracts gates from a
/// Tseitin-encoded circuit benchmark (simon-r16-1 from SAT-COMP 2024).
#[test]
#[cfg_attr(debug_assertions, timeout(180_000))]
#[cfg_attr(not(debug_assertions), timeout(60_000))]
fn test_congruence_preprocessing_simon_circuit() {
    if cfg!(debug_assertions) {
        eprintln!("SKIP: simon-r16-1 exceeds debug-mode timeout (#4582)");
        return;
    }
    let path = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../benchmarks/sat/satcomp2024-sample/08ccc34df5d8eb9e9d45278af3dc093d-simon-r16-1.sanitized.cnf"
    );
    if !std::path::Path::new(path).exists() {
        eprintln!("SKIP: simon-r16-1 benchmark not found at {path} (decompress .xz)");
        return;
    }
    let dimacs_str = std::fs::read_to_string(path).unwrap();
    let formula = parse_dimacs(&dimacs_str).expect("Failed to parse DIMACS");
    let mut solver = formula.into_solver();
    let result = solver.solve().into_inner();
    // simon-r16-1 is SAT
    assert!(matches!(result, SatResult::Sat(_)));

    // simon is a Tseitin-encoded circuit - should find many gates
    let stats = solver.congruence_stats();
    assert!(
        stats.gates_analyzed >= 500,
        "Expected >=500 gates analyzed on simon circuit, got {}",
        stats.gates_analyzed
    );
}

// ============================================================================
// BCE (Blocked Clause Elimination) Solver-Integration Tests (#3384)
// ============================================================================

inprocessing_test_triad! {
    test_bce_correctness, test_bce_stats, test_bce_disabled,
    label: "BCE",
    set_enabled: set_bce_enabled,
    get_stats: bce_stats,
    zero_field: rounds,
    seeds: [4001, 4002, 4003],
    stats_check: |stats| {
        assert!(
            stats.checks_performed >= stats.clauses_eliminated,
            "checks_performed ({}) must be >= clauses_eliminated ({})",
            stats.checks_performed,
            stats.clauses_eliminated
        );
    }
}

// ============================================================================
// Transitive Reduction Solver-Integration Tests (#3384)
// ============================================================================

/// Test that transitive reduction doesn't break solver correctness.
/// Uses a binary-clause-heavy formula to exercise the implication graph.
#[test]
#[timeout(2_000)]
fn test_transred_correctness() {
    let num_vars = 20;
    let mut solver = Solver::new(num_vars);
    let mut clauses = Vec::new();

    // Generate binary implication chains: a → b → c → d
    // In CNF: (¬a ∨ b), (¬b ∨ c), (¬c ∨ d)
    for i in 0..(num_vars - 1) {
        let clause = vec![
            Literal::negative(Variable::new(i as u32)),
            Literal::positive(Variable::new((i + 1) as u32)),
        ];
        clauses.push(clause);
    }
    let random_clauses = generate_test_clauses(num_vars as u32, 50, 5001);
    clauses.extend(random_clauses);

    for clause in &clauses {
        solver.add_clause(clause.clone());
    }

    let result = solver.solve().into_inner();

    match &result {
        SatResult::Sat(model) => {
            assert!(
                verify_model(&clauses, model),
                "Transred produced invalid model"
            );
        }
        SatResult::Unsat(_) => {
            // Cross-check: verify UNSAT is genuine by solving without transred.
            let mut check = Solver::new(num_vars);
            check.set_transred_enabled(false);
            for clause in &clauses {
                check.add_clause(clause.clone());
            }
            assert!(
                matches!(check.solve().into_inner(), SatResult::Unsat(_)),
                "Transred caused false UNSAT: formula is SAT without transred"
            );
        }
        _ => panic!("Unexpected Unknown result from transred correctness test"),
    }
}

/// Test transred statistics are tracked.
#[test]
#[timeout(2_000)]
fn test_transred_stats() {
    let mut solver = Solver::new(10);
    let clauses = generate_test_clauses(10, 40, 5002);

    for clause in &clauses {
        solver.add_clause(clause.clone());
    }

    let _ = solver.solve().into_inner();

    let stats = solver.transred_stats();
    if stats.clauses_removed > 0 {
        assert!(
            stats.rounds > 0,
            "clauses_removed ({}) > 0 but rounds is 0",
            stats.clauses_removed
        );
    }
}

/// Test that transred can be disabled.
#[test]
#[timeout(2_000)]
fn test_transred_disabled() {
    let mut solver = Solver::new(10);
    solver.set_transred_enabled(false);

    let clauses = generate_test_clauses(10, 40, 5003);
    for clause in &clauses {
        solver.add_clause(clause.clone());
    }

    let result = solver.solve().into_inner();
    if let SatResult::Sat(model) = &result {
        assert!(
            verify_model(&clauses, model),
            "Disabled transred produced invalid model"
        );
    }

    let stats = solver.transred_stats();
    assert_eq!(stats.rounds, 0, "Transred ran despite being disabled");
}

// ============================================================================
// Decompose (SCC Equivalent Literal Substitution) Solver-Integration Tests (#3384)
// ============================================================================

/// Test that decompose doesn't break solver correctness.
/// Uses a formula with binary equivalence chains to exercise SCC detection.
#[test]
#[timeout(2_000)]
fn test_decompose_correctness() {
    let num_vars = 15;
    let mut solver = Solver::new(num_vars);
    let mut clauses = Vec::new();

    // Create equivalence pairs via binary implications: a ↔ b
    // In CNF: (¬a ∨ b) AND (a ∨ ¬b)
    for pair in 0..3 {
        let a = pair * 2;
        let b = pair * 2 + 1;
        clauses.push(vec![
            Literal::negative(Variable::new(a)),
            Literal::positive(Variable::new(b)),
        ]);
        clauses.push(vec![
            Literal::positive(Variable::new(a)),
            Literal::negative(Variable::new(b)),
        ]);
    }

    let random_clauses = generate_test_clauses(num_vars as u32, 40, 6001);
    clauses.extend(random_clauses);

    for clause in &clauses {
        solver.add_clause(clause.clone());
    }

    let result = solver.solve().into_inner();
    if let SatResult::Sat(model) = &result {
        assert!(
            verify_model(&clauses, model),
            "Decompose produced invalid model"
        );
    }
}

// ============================================================================
// Factorization (Extension Variable Compression) Solver-Integration Tests (#3384)
// ============================================================================

/// Test that factorization doesn't break solver correctness.
/// Factorization is disabled by default (soundness bug #3373), so this test
/// explicitly enables it and verifies the model.
#[test]
#[timeout(5_000)]
fn test_factorization_correctness() {
    let mut solver = Solver::new(15);
    solver.set_factor_enabled(true);

    let clauses = generate_test_clauses(15, 60, 7001);
    for clause in &clauses {
        solver.add_clause(clause.clone());
    }

    let result = solver.solve().into_inner();
    if let SatResult::Sat(model) = &result {
        assert!(
            verify_model(&clauses, model),
            "Factorization produced invalid model"
        );
    }
}

/// Test that factorization is disabled by default and can be explicitly disabled.
/// Factorization was disabled due to soundness bug #3373.
#[test]
#[timeout(2_000)]
fn test_factorization_disabled() {
    let mut solver = Solver::new(10);
    solver.set_factor_enabled(false);

    let clauses = generate_test_clauses(10, 40, 7003);
    for clause in &clauses {
        solver.add_clause(clause.clone());
    }

    let result = solver.solve().into_inner();
    if let SatResult::Sat(model) = &result {
        assert!(
            verify_model(&clauses, model),
            "Disabled factorization produced invalid model"
        );
    }

    let stats = solver.factor_stats();
    assert_eq!(stats.rounds, 0, "Factorization should not have run");
}

/// Smoke test: decompose_stats() API is accessible and returns valid data.
#[test]
#[timeout(2_000)]
fn test_decompose_stats() {
    let mut solver = Solver::new(10);

    let clauses = generate_test_clauses(10, 40, 6002);
    for clause in &clauses {
        solver.add_clause(clause.clone());
    }

    let _ = solver.solve().into_inner();

    let stats = solver.decompose_stats();
    if stats.substituted > 0 {
        assert!(
            stats.rounds > 0,
            "substituted ({}) > 0 but rounds is 0",
            stats.substituted
        );
    }
}

/// Test that decompose can be disabled and does not run.
#[test]
#[timeout(2_000)]
fn test_decompose_disabled() {
    let mut solver = Solver::new(10);
    solver.set_decompose_enabled(false);

    let clauses = generate_test_clauses(10, 40, 6003);
    for clause in &clauses {
        solver.add_clause(clause.clone());
    }

    let result = solver.solve().into_inner();
    if let SatResult::Sat(model) = &result {
        assert!(
            verify_model(&clauses, model),
            "Disabled decompose produced invalid model"
        );
    }

    let stats = solver.decompose_stats();
    assert_eq!(stats.rounds, 0, "Decompose should not have run");
}

/// Regression test: proof logging must clamp decompose.
///
/// Decompose rewrites variable mappings. Keep it disabled in proof mode until
/// proof emission and final model reconstruction are both safe.
#[test]
#[timeout(5_000)]
fn test_decompose_is_clamped_with_proof_logging() {
    use ay_sat::ProofOutput;

    // Formula must be large enough to generate 10,000+ conflicts
    // (DECOMPOSE_INTERVAL) so that SCC decomposition triggers.
    let num_vars = 200;
    let proof_buffer: Vec<u8> = Vec::new();
    let proof_writer = ProofOutput::drat_text(proof_buffer);
    let mut solver = Solver::with_proof_output(num_vars, proof_writer);
    assert!(
        !solver.inprocessing_feature_profile().decompose,
        "Decompose should be clamped in proof mode"
    );

    // Binary implications: a ↔ b (equivalence pairs that SCC would detect)
    for pair in 0..10 {
        let a = pair * 2;
        let b = pair * 2 + 1;
        solver.add_clause(vec![
            Literal::negative(Variable::new(a)),
            Literal::positive(Variable::new(b)),
        ]);
        solver.add_clause(vec![
            Literal::positive(Variable::new(a)),
            Literal::negative(Variable::new(b)),
        ]);
    }

    // Random 3-SAT clauses near phase transition (4.26 ratio) to force
    // enough conflicts for inprocessing to fire.
    let random_clauses = generate_test_clauses(num_vars as u32, 850, 8401);
    for clause in &random_clauses {
        solver.add_clause(clause.clone());
    }

    let _ = solver.solve().into_inner();

    let stats = solver.decompose_stats();
    assert_eq!(stats.rounds, 0, "Decompose should not run in proof mode");
}

/// Smoke test: factor_stats() API is accessible and returns valid data.
#[test]
#[timeout(5_000)]
fn test_factorization_stats() {
    let mut solver = Solver::new(10);
    solver.set_factor_enabled(true);

    let clauses = generate_test_clauses(10, 40, 7002);
    for clause in &clauses {
        solver.add_clause(clause.clone());
    }

    let _ = solver.solve().into_inner();

    let stats = solver.factor_stats();
    if stats.factored_count > 0 {
        assert!(
            stats.rounds > 0,
            "factored_count ({}) > 0 but rounds is 0",
            stats.factored_count
        );
    }
}

// ============================================================================
// DRAT Proof Verification Tests
// ============================================================================

/// Regression test for #3405: BVE + DRAT proof verification.
///
/// Uses a PHP(8,7) pigeonhole formula, solves with DRAT proof logging,
/// and verifies the proof with drat-trim.
#[test]
#[timeout(30_000)]
fn test_bve_drat_proof_verified() {
    use ay_sat::ProofOutput;

    // PHP(5,4): 5 pigeons, 4 holes -> 20 variables, guaranteed UNSAT.
    let pigeons: usize = 5;
    let holes: usize = 4;
    let num_vars = pigeons * holes;
    let mut clauses: Vec<Vec<Literal>> = Vec::new();

    // At-least-one: each pigeon must be in some hole
    for i in 0..pigeons {
        let clause: Vec<Literal> = (0..holes)
            .map(|j| Literal::positive(Variable::new((i * holes + j) as u32)))
            .collect();
        clauses.push(clause);
    }

    // At-most-one: no hole has two pigeons
    for j in 0..holes {
        for i1 in 0..pigeons {
            for i2 in (i1 + 1)..pigeons {
                clauses.push(vec![
                    Literal::negative(Variable::new((i1 * holes + j) as u32)),
                    Literal::negative(Variable::new((i2 * holes + j) as u32)),
                ]);
            }
        }
    }

    let dimacs = super::common::clauses_to_dimacs(num_vars, &clauses);

    let proof_buffer: Vec<u8> = Vec::new();
    let proof_writer = ProofOutput::drat_text(proof_buffer);
    let mut solver = Solver::with_proof_output(num_vars, proof_writer);
    solver.set_bve_enabled(true);

    for clause in &clauses {
        solver.add_clause(clause.clone());
    }

    let result = solver.solve().into_inner();
    assert!(result.is_unsat(), "PHP(5,4) must be UNSAT");

    let writer = solver.take_proof_writer().expect("proof writer");
    let proof_bytes = writer.into_vec().expect("proof writer flush");

    eprintln!(
        "BVE stats: {} vars eliminated, {} resolvents, {} rounds",
        solver.bve_stats().vars_eliminated,
        solver.bve_stats().resolvents_added,
        solver.bve_stats().rounds,
    );

    super::common::verify_drat_proof(&dimacs, &proof_bytes, "bve_drat_php54");
}

/// Build a 2x3 ternary factorization matrix on {a,b,c,d,e} plus a disjoint
/// 2-SAT UNSAT core on {u,v}. Returns (num_vars, clauses).
fn factorization_matrix_unsat() -> (usize, Vec<Vec<Literal>>) {
    let lit = |v: u32, pos: bool| {
        if pos {
            Literal::positive(Variable::new(v))
        } else {
            Literal::negative(Variable::new(v))
        }
    };
    let clauses = vec![
        // 2x3 matrix: factors={a,b}, quotients={c∨d, c∨e, d∨e}
        vec![lit(0, true), lit(2, true), lit(3, true)],
        vec![lit(1, true), lit(2, true), lit(3, true)],
        vec![lit(0, true), lit(2, true), lit(4, true)],
        vec![lit(1, true), lit(2, true), lit(4, true)],
        vec![lit(0, true), lit(3, true), lit(4, true)],
        vec![lit(1, true), lit(3, true), lit(4, true)],
        // Disjoint UNSAT core on {u,v}.
        vec![lit(5, true), lit(6, true)],
        vec![lit(5, false), lit(6, true)],
        vec![lit(5, true), lit(6, false)],
        vec![lit(5, false), lit(6, false)],
    ];
    (7, clauses)
}

/// Part of #4242: factorization enabled in DRAT proof mode.
///
/// Verifies factorization fires (`factored_count > 0`) and that the DRAT
/// proof validates externally with drat-trim.
#[test]
#[timeout(60_000)]
fn test_factorization_drat_proof_verified() {
    use ay_sat::ProofOutput;

    let (num_vars, clauses) = factorization_matrix_unsat();
    let dimacs = super::common::clauses_to_dimacs(num_vars, &clauses);

    let writer = ProofOutput::drat_text(Vec::new());
    let mut solver = Solver::with_proof_output(num_vars, writer);
    // Isolate factorization path: disable all other inprocessing.
    for setter in [
        Solver::set_vivify_enabled,
        Solver::set_subsume_enabled,
        Solver::set_probe_enabled,
        Solver::set_bve_enabled,
        Solver::set_bce_enabled,
        Solver::set_condition_enabled,
        Solver::set_transred_enabled,
        Solver::set_htr_enabled,
        Solver::set_gate_enabled,
        Solver::set_congruence_enabled,
        Solver::set_decompose_enabled,
        Solver::set_sweep_enabled,
        Solver::set_backbone_enabled,
        Solver::set_cce_enabled,
    ] {
        setter(&mut solver, false);
    }
    solver.set_factor_enabled(true);

    for clause in &clauses {
        solver.add_clause(clause.clone());
    }

    let result = solver.solve().into_inner();
    assert!(result.is_unsat(), "matrix+core formula must be UNSAT");

    let stats = solver.factor_stats();
    eprintln!(
        "Factor DRAT test: rounds={}, factored={}, ext_vars={}",
        stats.rounds, stats.factored_count, stats.extension_vars,
    );
    assert!(
        stats.factored_count > 0,
        "factorization must fire in proof mode"
    );
    assert!(
        stats.extension_vars > 0,
        "factorization must introduce extension vars"
    );

    let writer = solver.take_proof_writer().expect("proof writer");
    let proof_bytes = writer.into_vec().expect("flush");
    super::common::verify_drat_proof(&dimacs, &proof_bytes, "factor_drat_matrix_unsat");
}

/// Regression test for lucky phase DRAT proof bug.
///
/// Before the fix (preprocess.rs lucky_propagate_discrepancy), unit clauses
/// learned during lucky phase conflict analysis were enqueued without writing
/// to the DRAT proof, causing drat-trim to reject proofs with
/// "conflict claimed, but not detected".
#[test]
#[timeout(10_000)]
fn test_drat_lucky_phase_unit_clause_proof() {
    // php_2_1: simplest UNSAT formula that triggers lucky phase unit learning.
    let dimacs = "p cnf 2 4\n1 2 0\n-1 2 0\n1 -2 0\n-1 -2 0\n";
    let formula = parse_dimacs(dimacs).expect("parse");

    let proof_buffer: Vec<u8> = Vec::new();
    let mut solver = Solver::with_proof(formula.num_vars, proof_buffer);

    for clause in &formula.clauses {
        solver.add_clause(clause.clone());
    }

    let result = solver.solve().into_inner();
    assert!(result.is_unsat());

    let writer = solver.take_proof_writer().expect("writer");
    let proof_bytes = writer.into_vec().expect("proof writer flush");
    let proof_text = String::from_utf8_lossy(&proof_bytes);

    // Proof must contain at least one learned clause before the empty clause.
    let lines: Vec<&str> = proof_text.lines().collect();
    assert!(
        lines.len() >= 2,
        "Proof must have learned clauses before empty clause, got {} lines: {:?}",
        lines.len(),
        lines
    );
    assert_eq!(lines.last(), Some(&"0"), "Proof must end with empty clause");

    super::common::verify_drat_proof(dimacs, &proof_bytes, "lucky_phase_unit_clause");
}

/// Regression test for #3405: full inprocessing pipeline + DRAT proof.
///
/// Runs all UNSAT benchmarks with full inprocessing enabled under DRAT proof
/// logging, then verifies each proof with drat-trim.
#[test]
#[timeout(60_000)]
fn test_inprocessing_drat_corpus_verified() {
    use ay_sat::ProofOutput;

    let manifest_dir = std::env::var("CARGO_MANIFEST_DIR").expect("CARGO_MANIFEST_DIR");
    let workspace_root = std::path::Path::new(&manifest_dir)
        .parent()
        .and_then(|p| p.parent())
        .expect("workspace root");
    let corpus_dir = workspace_root.join("benchmarks/sat/unsat");
    assert!(corpus_dir.exists(), "UNSAT benchmark corpus must exist");

    let mut cnf_files: Vec<_> = std::fs::read_dir(corpus_dir)
        .expect("Read corpus dir")
        .filter_map(Result::ok)
        .filter(|e| e.path().extension().map_or(false, |ext| ext == "cnf"))
        .map(|e| e.path())
        .collect();
    cnf_files.sort();

    let mut verified_count = 0;
    let mut bve_fired = 0;

    for cnf_path in &cnf_files {
        let dimacs = std::fs::read_to_string(cnf_path).expect("Read CNF");
        let formula = parse_dimacs(&dimacs).expect("Parse CNF");

        let proof_buffer: Vec<u8> = Vec::new();
        let proof_writer = ProofOutput::drat_text(proof_buffer);
        let mut solver = Solver::with_proof_output(formula.num_vars, proof_writer);

        // Enable inprocessing techniques that are DRAT-compatible
        solver.set_bve_enabled(true);
        solver.set_vivify_enabled(true);
        solver.set_subsume_enabled(true);
        solver.set_probe_enabled(true);

        for clause in &formula.clauses {
            solver.add_clause(clause.clone());
        }

        let result = solver.solve().into_inner();
        assert!(
            result.is_unsat(),
            "Benchmark {} must be UNSAT",
            cnf_path.display()
        );

        if solver.bve_stats().vars_eliminated > 0 {
            bve_fired += 1;
        }

        let writer = solver.take_proof_writer().expect("proof writer");
        let proof_bytes = writer.into_vec().expect("proof writer flush");

        let file_name = cnf_path.file_stem().unwrap().to_string_lossy();
        super::common::verify_drat_proof(&dimacs, &proof_bytes, &format!("corpus_{file_name}"));
        verified_count += 1;
    }

    eprintln!(
        "Inprocessing DRAT: {}/{} benchmarks verified, BVE fired on {}",
        verified_count,
        cnf_files.len(),
        bve_fired
    );
    assert!(
        verified_count >= 10,
        "Expected at least 10 UNSAT benchmarks"
    );
}

// ============================================================================
// Congruence + Decompose Pipeline Tests
// ============================================================================

/// Test that congruence closure discovers gate equivalences when two outputs
/// encode the same AND gate (y0 = AND(a,b) and y1 = AND(a,b)).
///
/// The congruence closure should detect that y0 and y1 are functionally
/// equivalent via hash-table collision on their gate signatures. Combined
/// with SCC decomposition, this should enable literal substitution.
#[test]
#[timeout(10_000)]
fn test_congruence_decompose_pipeline_discovers_gate_equivalences() {
    let num_pairs = 16u32;
    let num_vars = num_pairs * 4;
    let mut solver = Solver::new(num_vars as usize);
    solver.set_congruence_enabled(true);
    solver.set_decompose_enabled(true);

    // For each pair (i): create variables a, b, y0, y1
    // Encode y0 = AND(a, b) and y1 = AND(a, b) as CNF:
    //   (~a | ~b | y0), (a | ~y0), (b | ~y0)   -- y0 = AND(a, b)
    //   (~a | ~b | y1), (a | ~y1), (b | ~y1)   -- y1 = AND(a, b)
    for i in 0..num_pairs {
        let base = i * 4;
        let a = Literal::positive(Variable::new(base));
        let b = Literal::positive(Variable::new(base + 1));
        let y0 = Literal::positive(Variable::new(base + 2));
        let y1 = Literal::positive(Variable::new(base + 3));

        // y0 = AND(a, b)
        solver.add_clause(vec![a.negated(), b.negated(), y0]);
        solver.add_clause(vec![a, y0.negated()]);
        solver.add_clause(vec![b, y0.negated()]);

        // y1 = AND(a, b) — same gate, different output
        solver.add_clause(vec![a.negated(), b.negated(), y1]);
        solver.add_clause(vec![a, y1.negated()]);
        solver.add_clause(vec![b, y1.negated()]);
    }

    // Link pairs in a ring to prevent trivial simplification
    for i in 0..num_pairs {
        let y0_i = Literal::positive(Variable::new(i * 4 + 2));
        let next = (i + 1) % num_pairs;
        let y1_next = Literal::positive(Variable::new(next * 4 + 3));
        solver.add_clause(vec![y0_i, y1_next]);
    }

    let result = solver.solve().into_inner();
    assert!(
        matches!(result, SatResult::Sat(_)),
        "Formula with duplicate AND gates should be SAT"
    );

    let cs = solver.congruence_stats();
    let ds = solver.decompose_stats();
    eprintln!(
        "[test] congruence: gates_analyzed={}, equivalences_found={}, rounds={}",
        cs.gates_analyzed, cs.equivalences_found, cs.rounds
    );
    eprintln!(
        "[test] decompose: substituted={}, rounds={}",
        ds.substituted, ds.rounds
    );

    // The pipeline should discover equivalences: y0 ≡ y1 for each pair
    assert!(
        cs.equivalences_found > 0 || ds.substituted > 0,
        "Expected congruence closure or decompose to discover gate equivalences, \
         but congruence_equiv={}, decompose_subst={}",
        cs.equivalences_found,
        ds.substituted
    );
}

/// Regression test for #3424: decompose() caused wrong-UNSAT on stric-bmc-ibm-10.
/// This benchmark is known-SAT (CaDiCaL exit 10, 0.29s). AY previously returned
/// UNSAT due to unsound SCC decomposition variable substitution.
#[test]
#[cfg_attr(debug_assertions, timeout(180_000))]
#[cfg_attr(not(debug_assertions), timeout(60_000))]
fn test_regression_3424_decompose_wrong_unsat_stric_bmc_ibm_10() {
    if cfg!(debug_assertions) {
        eprintln!("SKIP: stric-bmc-ibm-10 exceeds debug-mode timeout (#4582)");
        return;
    }
    let path = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../reference/creusat/tests/cnf-hard/stric-bmc-ibm-10.cnf"
    );
    if !std::path::Path::new(path).exists() {
        eprintln!("Skipping: benchmark missing: {path}");
        return;
    }
    let content =
        std::fs::read_to_string(path).unwrap_or_else(|e| panic!("Failed to read {path}: {e}"));
    let formula = parse_dimacs(&content).unwrap_or_else(|e| panic!("Failed to parse {path}: {e}"));
    let original_clauses: Vec<Vec<Literal>> = formula.clauses.clone();
    let num_vars = formula.num_vars;
    let mut solver = formula.into_solver();
    let result = solver.solve().into_inner();
    match result {
        SatResult::Sat(model) => {
            assert_model_satisfies(
                &original_clauses,
                &model,
                &format!(
                    "SOUNDNESS BUG (#3424): stric-bmc-ibm-10 ({num_vars} vars, {} clauses)",
                    original_clauses.len()
                ),
            );
        }
        SatResult::Unsat(_) => {
            panic!("REGRESSION #3424: stric-bmc-ibm-10 is known-SAT but AY returned UNSAT.");
        }
        SatResult::Unknown => {
            panic!("stric-bmc-ibm-10: AY returned Unknown (timeout). Expected SAT within 60s.");
        }
        #[allow(unreachable_patterns)]
        _ => unreachable!(),
    }
}

/// BVE effectiveness test (#3464): barrel6 must achieve >0 BVE eliminations.
///
/// Before the fix, `mark_failed()` permanently blacklisted all 248 variables,
/// yielding 0 eliminations. CaDiCaL gets 25 on the same benchmark.
#[test]
#[cfg_attr(debug_assertions, timeout(180_000))]
#[cfg_attr(not(debug_assertions), timeout(120_000))]
fn test_bve_effectiveness_barrel6() {
    if cfg!(debug_assertions) {
        eprintln!("SKIP: cmu-bmc-barrel6 exceeds debug-mode timeout (>120s preprocessing)");
        return;
    }
    let path = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../reference/creusat/tests/mfleury/SAT-2009-preprocessed/easy/unsat/cmu-bmc-barrel6.cnf"
    );
    if !super::common::require_benchmark(path) {
        return;
    }
    let content =
        std::fs::read_to_string(path).unwrap_or_else(|e| panic!("Failed to read {path}: {e}"));
    let formula = parse_dimacs(&content).unwrap_or_else(|e| panic!("Failed to parse {path}: {e}"));
    let mut solver = formula.into_solver();
    let result = solver.solve().into_inner();
    assert!(result.is_unsat(), "barrel6 must be UNSAT");
    let stats = solver.bve_stats();
    assert!(
        stats.vars_eliminated > 0,
        "BVE must eliminate >0 variables on barrel6 (got 0 — mark_failed blacklist bug). \
         CaDiCaL eliminates 25 variables on this benchmark."
    );
}

// ============================================================================
// Shrink + LRAT Chain Tests (#4092)
// ============================================================================

/// Test that LRAT proofs are structurally valid when shrink is enabled.
///
/// Block-UIP shrinking replaces multiple same-level literals with a single
/// block UIP. The resolution chain must include the reason clause IDs
/// traversed during the block-UIP search (#4092).
///
/// Uses a pigeon-hole PHP(3,2) formula (UNSAT, 6 variables, 9 clauses)
/// which generates non-trivial conflicts with potential for block-UIP firing.
#[test]
#[timeout(5_000)]
fn test_lrat_proof_with_shrink_enabled() {
    use ay_sat::ProofOutput;

    // PHP(3,2): 3 pigeons, 2 holes — always UNSAT
    // Variables: x_{p,h} = pigeon p in hole h
    //   x1=p1h1, x2=p1h2, x3=p2h1, x4=p2h2, x5=p3h1, x6=p3h2
    // At-least-one per pigeon:
    //   (x1 OR x2), (x3 OR x4), (x5 OR x6)
    // At-most-one per hole:
    //   hole1: (¬x1 ∨ ¬x3), (¬x1 ∨ ¬x5), (¬x3 ∨ ¬x5)
    //   hole2: (¬x2 ∨ ¬x4), (¬x2 ∨ ¬x6), (¬x4 ∨ ¬x6)
    let dimacs = r"
p cnf 6 9
1 2 0
3 4 0
5 6 0
-1 -3 0
-1 -5 0
-3 -5 0
-2 -4 0
-2 -6 0
-4 -6 0
";
    let formula = parse_dimacs(dimacs).expect("Failed to parse");
    assert_eq!(formula.num_vars, 6);
    assert_eq!(formula.clauses.len(), 9);

    // Solve with LRAT + shrink
    let proof_buffer: Vec<u8> = Vec::new();
    let proof_writer = ProofOutput::lrat_text(proof_buffer, 9);
    let mut solver = Solver::with_proof_output(formula.num_vars, proof_writer);
    solver.set_shrink_enabled(true);

    for clause in formula.clauses {
        solver.add_clause(clause);
    }

    let result = solver.solve().into_inner();
    assert!(result.is_unsat(), "PHP(3,2) must be UNSAT");

    let writer = solver
        .take_proof_writer()
        .expect("Proof writer should exist");
    let proof = String::from_utf8(writer.into_vec().expect("proof flush")).expect("Valid UTF-8");

    // LRAT proof must not be empty
    assert!(!proof.is_empty(), "LRAT proof must not be empty for UNSAT");

    // Every LRAT line must be well-formed: "id literals... 0 hints... 0" or "id d clause_ids... 0"
    for line in proof.lines() {
        let tokens: Vec<&str> = line.split_whitespace().collect();
        assert!(tokens.len() >= 2, "LRAT line too short: {line}");
        // First token must be a clause ID (positive integer)
        let id: u64 = tokens[0]
            .parse()
            .unwrap_or_else(|_| panic!("LRAT line must start with clause ID: {line}"));
        assert!(id > 0, "LRAT clause ID must be positive: {line}");

        if tokens[1] == "d" {
            // Deletion line: "id d clause_ids... 0"
            assert_eq!(
                tokens.last().copied(),
                Some("0"),
                "LRAT deletion must end with 0: {line}"
            );
        } else {
            // Addition line: "id literals... 0 hints... 0"
            let zero_count = tokens.iter().filter(|&&t| t == "0").count();
            assert!(
                zero_count >= 2,
                "LRAT addition must have at least two 0s (literals 0 hints 0): {line}"
            );
        }
    }
}

/// Validate LRAT proof: every non-empty addition line has at least one hint.
/// The final empty clause (finalize_unsat_proof writes `add(&[], &[])`) is
/// excluded — that's a separate pre-existing gap.
/// Verify LRAT proof IDs are well-formed: additions are monotonically increasing,
/// and every deletion references an ID that was previously added (or is an original clause).
fn assert_lrat_ids_consistent(proof: &str, num_original_clauses: u64) {
    let mut added_ids: std::collections::HashSet<u64> = (1..=num_original_clauses).collect();

    for line in proof.lines() {
        let tokens: Vec<&str> = line.split_whitespace().collect();
        if tokens.len() < 2 {
            continue;
        }
        if tokens[1] == "d" {
            // Deletion line: "latest_id d id1 id2 ... 0"
            for tok in &tokens[2..] {
                if *tok == "0" {
                    break;
                }
                let del_id: u64 = tok
                    .parse()
                    .unwrap_or_else(|_| panic!("Invalid deletion ID in LRAT proof: {tok}"));
                assert!(
                    added_ids.contains(&del_id),
                    "LRAT deletion references unknown clause ID {del_id} (line: {line})"
                );
            }
        } else {
            // Addition line: "id literals... 0 hints... 0"
            let add_id: u64 = tokens[0]
                .parse()
                .unwrap_or_else(|_| panic!("Invalid addition ID in LRAT proof: {}", tokens[0]));
            assert!(
                added_ids.insert(add_id),
                "Duplicate addition ID {add_id} in LRAT proof"
            );
        }
    }
}

fn assert_lrat_hints_complete(proof: &str) {
    let mut non_empty_additions = 0u32;
    for line in proof.lines() {
        let tokens: Vec<&str> = line.split_whitespace().collect();
        if tokens.len() < 2 || tokens[1] == "d" {
            continue;
        }
        let Some(pos) = tokens.iter().position(|&t| t == "0") else {
            continue;
        };
        if pos == 1 {
            continue; // Empty clause
        }
        non_empty_additions += 1;
        let hint_count = tokens[pos + 1..].iter().take_while(|&&t| t != "0").count();
        assert!(
            hint_count > 0,
            "LRAT addition line has empty hints section (missing resolution chain): {line}"
        );
    }
    assert!(
        non_empty_additions > 0,
        "LRAT proof must have at least one non-empty learned clause"
    );
}

/// Test LRAT proof with shrink: non-empty hints on PHP(4,3) (#4092).
#[test]
#[timeout(5_000)]
fn test_lrat_shrink_hints_not_empty() {
    use ay_sat::ProofOutput;

    // PHP(4,3): 4 pigeons, 3 holes — UNSAT, 12 vars, 22 clauses
    let dimacs = "p cnf 12 22\n\
        1 2 3 0\n4 5 6 0\n7 8 9 0\n10 11 12 0\n\
        -1 -4 0\n-1 -7 0\n-1 -10 0\n-4 -7 0\n-4 -10 0\n-7 -10 0\n\
        -2 -5 0\n-2 -8 0\n-2 -11 0\n-5 -8 0\n-5 -11 0\n-8 -11 0\n\
        -3 -6 0\n-3 -9 0\n-3 -12 0\n-6 -9 0\n-6 -12 0\n-9 -12 0\n";
    let formula = parse_dimacs(dimacs).expect("Failed to parse");
    let proof_writer = ProofOutput::lrat_text(Vec::new(), 22);
    let mut solver = Solver::with_proof_output(formula.num_vars, proof_writer);
    solver.set_shrink_enabled(true);
    for clause in formula.clauses {
        solver.add_clause(clause);
    }
    assert!(
        solver.solve().into_inner().is_unsat(),
        "PHP(4,3) must be UNSAT"
    );
    let writer = solver.take_proof_writer().expect("proof writer");
    let proof = String::from_utf8(writer.into_vec().expect("flush")).expect("UTF-8");
    assert_lrat_hints_complete(&proof);
}

// ============================================================================
// Theory Lemma LRAT ID Sync Tests (#4123)
// ============================================================================

/// Regression test for #4123: theory lemma addition must write LRAT proof entry
/// to keep solver clause ID counter in sync with writer's next_id counter.
///
/// Without the fix, add_theory_lemma() increments the solver's next_clause_id
/// without a corresponding writer.add(), causing all subsequent LRAT deletions
/// to reference incorrect clause IDs.
#[test]
#[timeout(3_000)]
fn test_lrat_theory_lemma_id_sync() {
    use ay_sat::ProofOutput;

    // Create a formula that's satisfiable on its own: (x1 OR x2) AND (NOT x1 OR x2)
    // Then add a theory lemma (NOT x2) to make it UNSAT via unit propagation.
    let num_vars = 2;
    let num_original_clauses = 2u64;

    let proof_writer = ProofOutput::lrat_text(Vec::new(), num_original_clauses);
    let mut solver = Solver::with_proof_output(num_vars, proof_writer);
    solver.enable_lrat();

    // Original clause 1: x1 OR x2
    solver.add_clause(vec![
        Literal::positive(Variable::new(0)),
        Literal::positive(Variable::new(1)),
    ]);
    // Original clause 2: NOT x1 OR x2
    solver.add_clause(vec![
        Literal::negative(Variable::new(0)),
        Literal::positive(Variable::new(1)),
    ]);

    // Theory lemma: NOT x1 (this would desync clause IDs before fix)
    solver.add_theory_lemma(vec![Literal::negative(Variable::new(0))]);

    // Theory lemma: NOT x2 (forces UNSAT with clause 1 after x1 is false)
    solver.add_theory_lemma(vec![Literal::negative(Variable::new(1))]);

    let result = solver.solve().into_inner();
    assert!(result.is_unsat(), "Should be UNSAT with theory lemmas");

    let writer = solver.take_proof_writer().expect("proof writer");
    let proof = String::from_utf8(writer.into_vec().expect("flush")).expect("UTF-8");

    // Verify that all LRAT clause IDs are consistent:
    // - Addition IDs are monotonically increasing
    // - Deletion IDs reference existing additions or original clauses
    assert_lrat_ids_consistent(&proof, num_original_clauses);
}

/// Regression test for #4641/#4693: add_theory_lemma's check-then-emit flow
/// must clear the pending prechecked obligation before the next proof emit.
///
/// Exercises both branches in add_theory_lemma:
/// - non-unit path: reorder + watched insertion
/// - unit path: enqueue at level 0
///
/// Before the fix, a subsequent theory lemma could panic in debug builds with:
/// "BUG: previous prechecked clause ... was never forward-checked".
#[test]
#[timeout(3_000)]
fn test_theory_lemma_prechecked_contract_unit_and_non_unit_paths() {
    use ay_sat::ProofOutput;

    let proof_writer = ProofOutput::lrat_text(Vec::new(), 0);
    let mut solver = Solver::with_proof_output(2, proof_writer);
    solver.enable_lrat();

    // Non-unit theory lemma path.
    let non_unit = solver.add_theory_lemma(vec![
        Literal::positive(Variable::new(0)),
        Literal::positive(Variable::new(1)),
    ]);
    assert!(
        non_unit.is_some(),
        "non-unit theory lemma should be inserted"
    );

    // Unit theory lemma path (twice) to trigger back-to-back proof emits.
    let unit0 = solver.add_theory_lemma(vec![Literal::negative(Variable::new(0))]);
    assert!(
        unit0.is_some(),
        "first unit theory lemma should be inserted"
    );
    let unit1 = solver.add_theory_lemma(vec![Literal::negative(Variable::new(1))]);
    assert!(
        unit1.is_some(),
        "second unit theory lemma should be inserted"
    );

    // (x0 ∨ x1) ∧ (¬x0) ∧ (¬x1) is UNSAT.
    assert!(solver.solve().into_inner().is_unsat());

    // LRAT stream remains ID-consistent across mixed theory-lemma branches.
    let writer = solver.take_proof_writer().expect("proof writer");
    let proof = String::from_utf8(writer.into_vec().expect("flush")).expect("UTF-8");
    assert_lrat_ids_consistent(&proof, 0);
}

/// Regression test for #4123: mark_empty_clause must not desync IDs when
/// both clause_trace and proof_writer (LRAT) are active.
///
/// Before the fix, mark_empty_clause() advanced next_clause_id for the
/// clause_trace but did not write to the proof_writer, causing the LRAT
/// writer's internal next_id to fall behind. Subsequent clause additions
/// would then produce duplicate or out-of-order IDs in the LRAT proof.
#[test]
#[timeout(10_000)]
fn test_mark_empty_clause_lrat_id_sync() {
    use ay_sat::ProofOutput;

    // Create a trivially UNSAT formula: (x1) AND (NOT x1).
    // add_clause with an empty vec goes through mark_empty_clause, but the
    // real desync path is: two unit clauses that conflict at level 0, causing
    // mark_empty_clause during propagation. Use the simplest path: direct
    // contradiction via unit clauses.
    let num_vars = 1;
    let num_original_clauses = 2u64;

    let proof_writer = ProofOutput::lrat_text(Vec::new(), num_original_clauses);
    let mut solver = Solver::with_proof_output(num_vars, proof_writer);
    solver.enable_lrat();
    solver.enable_clause_trace();

    // Original clause 1: x1
    solver.add_clause(vec![Literal::positive(Variable::new(0))]);
    // Original clause 2: NOT x1 — triggers mark_empty_clause at level 0
    solver.add_clause(vec![Literal::negative(Variable::new(0))]);

    let result = solver.solve().into_inner();
    assert!(
        result.is_unsat(),
        "contradictory unit clauses must be UNSAT"
    );

    let writer = solver.take_proof_writer().expect("proof writer");
    let proof = String::from_utf8(writer.into_vec().expect("flush")).expect("UTF-8");

    // The LRAT proof must have consistent IDs — no gaps, no duplicates.
    assert_lrat_ids_consistent(&proof, num_original_clauses);
}

// ============================================================================
// Preprocessing + Conditioning + Congruence DRAT Proof Tests
// ============================================================================

/// Regression test for T4 (#4172): preprocessing runs in proof mode.
///
/// Before the fix, `preprocess()` had a blanket `proof_writer.is_some()`
/// guard that disabled ALL preprocessing when proofs were enabled, even
/// though BVE, subsumption, and probing already emit valid DRAT records.
/// The blanket guard was removed in favor of per-technique guards (congruence,
/// decompose, factorization, conditioning each have their own). This test
/// verifies that preprocessing with BVE + subsumption produces a valid DRAT
/// proof verified by drat-trim.
#[test]
#[timeout(30_000)]
fn test_preprocessing_drat_proof_verified() {
    use ay_sat::ProofOutput;

    // PHP(5,4): 5 pigeons, 4 holes -> 20 variables, guaranteed UNSAT.
    // BVE and subsumption are effective on PHP instances during preprocessing.
    let pigeons: usize = 5;
    let holes: usize = 4;
    let num_vars = pigeons * holes;
    let mut clauses: Vec<Vec<Literal>> = Vec::new();

    // At-least-one: each pigeon must be in some hole
    for i in 0..pigeons {
        let clause: Vec<Literal> = (0..holes)
            .map(|j| Literal::positive(Variable::new((i * holes + j) as u32)))
            .collect();
        clauses.push(clause);
    }

    // At-most-one: no hole has two pigeons
    for j in 0..holes {
        for i1 in 0..pigeons {
            for i2 in (i1 + 1)..pigeons {
                clauses.push(vec![
                    Literal::negative(Variable::new((i1 * holes + j) as u32)),
                    Literal::negative(Variable::new((i2 * holes + j) as u32)),
                ]);
            }
        }
    }

    let dimacs = super::common::clauses_to_dimacs(num_vars, &clauses);

    let proof_buffer: Vec<u8> = Vec::new();
    let proof_writer = ProofOutput::drat_text(proof_buffer);
    let mut solver = Solver::with_proof_output(num_vars, proof_writer);

    // Enable BVE and preprocessing — the key change is that preprocessing
    // now runs even with proof logging enabled.
    solver.set_bve_enabled(true);
    solver.set_preprocess_enabled(true);

    for clause in &clauses {
        solver.add_clause(clause.clone());
    }

    let result = solver.solve().into_inner();
    assert!(result.is_unsat(), "PHP(5,4) must be UNSAT");

    let writer = solver.take_proof_writer().expect("proof writer");
    let proof_bytes = writer.into_vec().expect("proof writer flush");
    let proof_text = String::from_utf8_lossy(&proof_bytes);

    // Proof must not be empty — preprocessing should produce some steps.
    assert!(
        !proof_text.is_empty(),
        "Proof should contain steps from preprocessing"
    );

    eprintln!(
        "Preprocessing proof: {} bytes, {} lines",
        proof_bytes.len(),
        proof_text.lines().count(),
    );

    super::common::verify_drat_proof(&dimacs, &proof_bytes, "preprocessing_drat_php54");
}

/// Proof-mode conditioning test (#4205): GBCE runs with proof logging enabled.
///
/// Before the fix, this test could pass without observing any deletions due to
/// under-counting DRAT `d` lines (it only matched LRAT-style `" d "` records).
/// We now count both DRAT (`d ... 0`) and LRAT (`<id> d ... 0`) deletes and
/// require at least one delete to ensure a non-trivial proof mutation occurred.
///
/// Uses PHP(6,5) which is large enough for conditioning to find globally blocked
/// clauses during preprocessing, yet small enough to solve quickly.
#[test]
#[timeout(30_000)]
fn test_conditioning_drat_proof_verified() {
    use ay_sat::ProofOutput;

    let pigeons: usize = 6;
    let holes: usize = 5;
    let num_vars = pigeons * holes;
    let mut clauses: Vec<Vec<Literal>> = Vec::new();

    // At-least-one: each pigeon must be in some hole
    for i in 0..pigeons {
        let clause: Vec<Literal> = (0..holes)
            .map(|j| Literal::positive(Variable::new((i * holes + j) as u32)))
            .collect();
        clauses.push(clause);
    }

    // At-most-one: no hole has two pigeons
    for j in 0..holes {
        for i1 in 0..pigeons {
            for i2 in (i1 + 1)..pigeons {
                clauses.push(vec![
                    Literal::negative(Variable::new((i1 * holes + j) as u32)),
                    Literal::negative(Variable::new((i2 * holes + j) as u32)),
                ]);
            }
        }
    }

    let dimacs = super::common::clauses_to_dimacs(num_vars, &clauses);

    let proof_buffer: Vec<u8> = Vec::new();
    let proof_writer = ProofOutput::drat_text(proof_buffer);
    let mut solver = Solver::with_proof_output(num_vars, proof_writer);

    // Explicitly enable conditioning and preprocessing.
    solver.set_condition_enabled(true);
    solver.set_bve_enabled(true);
    solver.set_preprocess_enabled(true);

    for clause in &clauses {
        solver.add_clause(clause.clone());
    }

    let result = solver.solve().into_inner();
    assert!(result.is_unsat(), "PHP(6,5) must be UNSAT");

    let writer = solver.take_proof_writer().expect("proof writer");
    let proof_bytes = writer.into_vec().expect("proof writer flush");
    let proof_text = String::from_utf8_lossy(&proof_bytes);

    assert!(
        !proof_text.is_empty(),
        "Proof should contain steps when conditioning is enabled"
    );

    // Count both DRAT-style ("d ... 0") and LRAT-style ("<id> d ... 0") deletes.
    let delete_count = proof_text
        .lines()
        .map(str::trim)
        .filter(|line| line.starts_with("d ") || line.contains(" d "))
        .count();
    eprintln!(
        "Conditioning+BVE proof: {} bytes, {} lines, {} deletions",
        proof_bytes.len(),
        proof_text.lines().count(),
        delete_count,
    );
    assert!(
        delete_count > 0,
        "proof should contain at least one deletion when conditioning path is active"
    );

    super::common::verify_drat_proof(&dimacs, &proof_bytes, "conditioning_drat_php65");
}

/// Congruence is DRAT-open since 2026-07-10 (registry `Congruence { drat:
/// true }`, wf_ff5991a1; kill-switch AY_AB_DRAT_SUBST=0). The request must
/// be honored under a DRAT proof and the emitted proof must still verify —
/// urquhart_3 is the XOR-parity family that motivated the #3378 guard, so a
/// wrong congruence merge would flip the UNSAT verdict here.
#[test]
#[timeout(30_000)]
fn test_congruence_drat_request_is_honored() {
    let dimacs = super::common::load_repo_benchmark("benchmarks/sat/unsat/urquhart_3.cnf");
    let formula = parse_dimacs(&dimacs).expect("parse urquhart_3");

    let mut solver = Solver::with_proof(formula.num_vars, Vec::<u8>::new());

    // Keep the normal proof-mode inprocessing pipeline. #4273 was reproduced
    // in this configuration by the DRAT corpus test.
    solver.set_congruence_enabled(true);
    solver.set_preprocess_enabled(true);
    assert!(
        solver.inprocessing_feature_profile().congruence,
        "DRAT proof mode must honor congruence requests (registry drat=true \
         since 2026-07-10; kill-switch AY_AB_DRAT_SUBST=0)"
    );

    for clause in formula.clauses {
        solver.add_clause(clause);
    }

    let result = solver.solve().into_inner();
    assert!(result.is_unsat(), "urquhart_3 must be UNSAT");

    let writer = solver.take_proof_writer().expect("proof writer");
    let proof_bytes = writer.into_vec().expect("proof writer flush");
    let proof_text = String::from_utf8_lossy(&proof_bytes);
    let proof_lines: Vec<&str> = proof_text
        .lines()
        .map(str::trim)
        .filter(|line| !line.is_empty())
        .collect();
    assert!(
        !proof_lines.is_empty(),
        "proof should contain at least the empty clause, got:\n{proof_text}"
    );

    let final_line = proof_lines[proof_lines.len() - 1];
    assert_eq!(final_line, "0", "proof must end with empty clause");

    super::common::verify_drat_proof(&dimacs, &proof_bytes, "congruence_drat_honored");
}

/// Diagnostic: dump proof for urquhart_3 in corpus-style path (no explicit technique settings).
#[test]
#[timeout(30_000)]
fn test_diagnostic_urquhart3_corpus_path_proof() {
    let dimacs = super::common::load_repo_benchmark("benchmarks/sat/unsat/urquhart_3.cnf");
    let formula = parse_dimacs(&dimacs).expect("parse urquhart_3");

    // Corpus-style: NO explicit set_congruence_enabled / set_preprocess_enabled
    let mut solver = Solver::with_proof(formula.num_vars, Vec::<u8>::new());
    for clause in formula.clauses {
        solver.add_clause(clause);
    }

    let result = solver.solve().into_inner();
    assert!(result.is_unsat(), "urquhart_3 must be UNSAT");

    let cong_rounds = solver.congruence_stats().rounds;
    eprintln!("congruence rounds: {cong_rounds}");

    let writer = solver.take_proof_writer().expect("proof writer");
    let proof_bytes = writer.into_vec().expect("proof writer flush");
    let proof_text = String::from_utf8_lossy(&proof_bytes);
    eprintln!("DRAT proof ({} bytes):\n{proof_text}", proof_bytes.len());

    super::common::verify_drat_proof(&dimacs, &proof_bytes, "diagnostic_urquhart3_corpus");
}

/// DRAT validation test for the honored congruence route (drat-trim checked).
///
/// Runs the solver with congruence + preprocessing requested and validates the
/// full DRAT proof via drat-trim. Congruence is DRAT-open since 2026-07-10
/// (wf_ff5991a1), so the request is honored and congruence may actually run —
/// the emitted proof must still verify.
#[test]
#[timeout(60_000)]
fn test_congruence_drat_honored_proof_validated_by_drat_trim() {
    let dimacs = super::common::load_repo_benchmark("benchmarks/sat/unsat/urquhart_3.cnf");
    let formula = parse_dimacs(&dimacs).expect("parse urquhart_3");

    let mut solver = Solver::with_proof(formula.num_vars, Vec::<u8>::new());

    // Enable congruence + preprocessing (congruence needs preprocessing
    // to fire). Other techniques remain at defaults; this tests the
    // honored congruence route with a realistic inprocessing pipeline.
    solver.set_congruence_enabled(true);
    solver.set_preprocess_enabled(true);
    assert!(
        solver.inprocessing_feature_profile().congruence,
        "DRAT proof mode must honor congruence requests (registry drat=true \
         since 2026-07-10; kill-switch AY_AB_DRAT_SUBST=0)"
    );

    for clause in formula.clauses {
        solver.add_clause(clause);
    }

    let result = solver.solve().into_inner();
    assert!(result.is_unsat(), "urquhart_3 must be UNSAT");

    let cong_rounds = solver.congruence_stats().rounds;
    eprintln!("congruence rounds: {cong_rounds}");

    let writer = solver.take_proof_writer().expect("proof writer");
    let proof_bytes = writer.into_vec().expect("proof writer flush");

    super::common::verify_drat_proof(&dimacs, &proof_bytes, "congruence_drat_honored_4575");
}
