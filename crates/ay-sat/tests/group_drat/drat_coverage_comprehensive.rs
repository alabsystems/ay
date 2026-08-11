// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! DRAT proof coverage for programmatically generated UNSAT formulas.
//!
//! These tests close the DRAT proof gap for the deterministic UNSAT formulas
//! in `soundness_comprehensive.rs` and `integration_correctness.rs`:
//!
//! 1. **Pigeonhole Principle** PHP(n+1, n) for n in {2,3,4,5,6,7}
//! 2. **Graph Coloring** K_n with (n-1) colors for n in {4,5,6}
//! 3. **Ordering Cycles** with n in {3,5,10,20}
//! 4. **TLA+ Invariant UNSAT** formulas (unit contradictions, empty clause, PHP(2,1))
//! 5. **Watched-literals stress** formula (chain implications with conflict)
//! 6. **All benchmarks/sat/unsat/ corpus** with DRAT proof verification
//!
//! Every UNSAT result produces a DRAT proof and that proof is verified by the
//! native ay-drat-check forward checker (in-process, no external binaries).
//!
//! Part of #7913.

#![allow(clippy::panic)]

use ay_drat_check::checker::DratChecker;
use ay_drat_check::cnf_parser::parse_cnf;
use ay_drat_check::drat_parser::parse_drat;
use ay_sat::{Literal, ProofOutput, Solver, Variable};
use ntest::timeout;

// ===========================================================================
// Shared helpers
// ===========================================================================

/// Solve from (num_vars, clauses), assert UNSAT, extract DRAT proof, and verify
/// using the native ay-drat-check forward checker.
fn solve_clauses_and_verify_drat(num_vars: usize, clauses: &[Vec<Literal>], label: &str) {
    let dimacs = clauses_to_dimacs(num_vars, clauses);

    let proof_writer = ProofOutput::drat_text(Vec::<u8>::new());
    let mut solver = Solver::with_proof_output(num_vars, proof_writer);
    for clause in clauses {
        solver.add_clause(clause.clone());
    }

    let result = solver.solve().into_inner();
    assert!(result.is_unsat(), "{label}: expected UNSAT, got {result:?}");

    let writer = solver
        .take_proof_writer()
        .expect("proof writer must exist after UNSAT solve");
    let proof_bytes = writer.into_vec().expect("proof writer flush must succeed");

    assert!(
        !proof_bytes.is_empty(),
        "{label}: DRAT proof is empty (0 bytes)"
    );

    let cnf_for_check = parse_cnf(dimacs.as_bytes())
        .unwrap_or_else(|e| panic!("{label}: CNF re-parse for checker: {e}"));
    let steps =
        parse_drat(&proof_bytes).unwrap_or_else(|e| panic!("{label}: DRAT proof parse: {e}"));

    assert!(!steps.is_empty(), "{label}: DRAT proof parsed to 0 steps");

    let mut checker = DratChecker::new(cnf_for_check.num_vars, true);
    checker
        .verify(&cnf_for_check.clauses, &steps)
        .unwrap_or_else(|e| {
            panic!(
                "{label}: DRAT verification FAILED ({} proof bytes, {} steps): {e}",
                proof_bytes.len(),
                steps.len()
            )
        });

    eprintln!(
        "DRAT-comprehensive VERIFIED: {label} ({} bytes, {} steps)",
        proof_bytes.len(),
        steps.len()
    );
}

/// Solve a DIMACS string, assert UNSAT, extract DRAT proof, verify.
fn solve_dimacs_and_verify_drat(dimacs_text: &str, label: &str) {
    let formula = ay_sat::parse_dimacs(dimacs_text)
        .unwrap_or_else(|e| panic!("{label}: DIMACS parse error: {e}"));

    let proof_writer = ProofOutput::drat_text(Vec::<u8>::new());
    let mut solver = Solver::with_proof_output(formula.num_vars, proof_writer);
    for clause in &formula.clauses {
        solver.add_clause(clause.clone());
    }

    let result = solver.solve().into_inner();
    assert!(result.is_unsat(), "{label}: expected UNSAT, got {result:?}");

    let writer = solver
        .take_proof_writer()
        .expect("proof writer must exist after UNSAT solve");
    let proof_bytes = writer.into_vec().expect("proof writer flush must succeed");

    assert!(
        !proof_bytes.is_empty(),
        "{label}: DRAT proof is empty (0 bytes)"
    );

    let cnf_for_check = parse_cnf(dimacs_text.as_bytes())
        .unwrap_or_else(|e| panic!("{label}: CNF re-parse for checker: {e}"));
    let steps =
        parse_drat(&proof_bytes).unwrap_or_else(|e| panic!("{label}: DRAT proof parse: {e}"));

    assert!(!steps.is_empty(), "{label}: DRAT proof parsed to 0 steps");

    let mut checker = DratChecker::new(cnf_for_check.num_vars, true);
    checker
        .verify(&cnf_for_check.clauses, &steps)
        .unwrap_or_else(|e| {
            panic!(
                "{label}: DRAT verification FAILED ({} proof bytes, {} steps): {e}",
                proof_bytes.len(),
                steps.len()
            )
        });

    eprintln!(
        "DRAT-comprehensive VERIFIED: {label} ({} bytes, {} steps)",
        proof_bytes.len(),
        steps.len()
    );
}

/// Convert solver clauses to DIMACS CNF format.
fn clauses_to_dimacs(num_vars: usize, clauses: &[Vec<Literal>]) -> String {
    let mut dimacs = format!("p cnf {} {}\n", num_vars, clauses.len());
    for clause in clauses {
        for lit in clause {
            let var = lit.variable().index() as i64 + 1;
            let signed = if lit.is_positive() { var } else { -var };
            dimacs.push_str(&format!("{signed} "));
        }
        dimacs.push_str("0\n");
    }
    dimacs
}

// ===========================================================================
// Formula generators (same logic as soundness_comprehensive.rs)
// ===========================================================================

/// Generate pigeonhole principle PHP(pigeons, holes).
fn generate_php(pigeons: usize, holes: usize) -> (usize, Vec<Vec<Literal>>) {
    let num_vars = pigeons * holes;
    let mut clauses = Vec::new();

    let var = |p: usize, h: usize| -> Variable { Variable::new((p * holes + h) as u32) };

    // At-least-one: each pigeon must be in some hole
    for p in 0..pigeons {
        let clause: Vec<Literal> = (0..holes).map(|h| Literal::positive(var(p, h))).collect();
        clauses.push(clause);
    }

    // At-most-one: no two pigeons in the same hole
    for h in 0..holes {
        for p1 in 0..pigeons {
            for p2 in (p1 + 1)..pigeons {
                clauses.push(vec![
                    Literal::negative(var(p1, h)),
                    Literal::negative(var(p2, h)),
                ]);
            }
        }
    }

    (num_vars, clauses)
}

/// Generate a graph coloring instance: K_n with k colors. UNSAT when k < n.
fn generate_graph_coloring_complete(n: usize, k: usize) -> (usize, Vec<Vec<Literal>>) {
    let num_vars = n * k;
    let mut clauses = Vec::new();

    let var = |v: usize, c: usize| -> Variable { Variable::new((v * k + c) as u32) };

    // Each vertex has at least one color
    for v in 0..n {
        let clause: Vec<Literal> = (0..k).map(|c| Literal::positive(var(v, c))).collect();
        clauses.push(clause);
    }

    // Each vertex has at most one color (AMO)
    for v in 0..n {
        for c1 in 0..k {
            for c2 in (c1 + 1)..k {
                clauses.push(vec![
                    Literal::negative(var(v, c1)),
                    Literal::negative(var(v, c2)),
                ]);
            }
        }
    }

    // Adjacent vertices have different colors (complete graph: all pairs)
    for v1 in 0..n {
        for v2 in (v1 + 1)..n {
            for c in 0..k {
                clauses.push(vec![
                    Literal::negative(var(v1, c)),
                    Literal::negative(var(v2, c)),
                ]);
            }
        }
    }

    (num_vars, clauses)
}

/// Generate an ordering cycle that is UNSAT. All vars forced true by units,
/// but the last clause requires at least one false.
fn generate_ordering_cycle(n: usize) -> (usize, Vec<Vec<Literal>>) {
    let num_vars = n;
    let mut clauses = Vec::new();

    // Assert x_i for all i
    for i in 0..n {
        clauses.push(vec![Literal::positive(Variable::new(i as u32))]);
    }

    // At least one must be false
    let neg_all: Vec<Literal> = (0..n)
        .map(|i| Literal::negative(Variable::new(i as u32)))
        .collect();
    clauses.push(neg_all);

    (num_vars, clauses)
}

// ===========================================================================
// Section 1: Pigeonhole Principle with DRAT proof verification
// ===========================================================================

#[test]
#[timeout(30_000)]
fn drat_comprehensive_php_3_2() {
    let (nv, clauses) = generate_php(3, 2);
    solve_clauses_and_verify_drat(nv, &clauses, "php_3_2");
}

#[test]
#[timeout(30_000)]
fn drat_comprehensive_php_4_3() {
    let (nv, clauses) = generate_php(4, 3);
    solve_clauses_and_verify_drat(nv, &clauses, "php_4_3");
}

#[test]
#[timeout(30_000)]
fn drat_comprehensive_php_5_4() {
    let (nv, clauses) = generate_php(5, 4);
    solve_clauses_and_verify_drat(nv, &clauses, "php_5_4");
}

#[test]
#[timeout(30_000)]
fn drat_comprehensive_php_6_5() {
    let (nv, clauses) = generate_php(6, 5);
    solve_clauses_and_verify_drat(nv, &clauses, "php_6_5");
}

#[test]
#[timeout(60_000)]
fn drat_comprehensive_php_7_6() {
    let (nv, clauses) = generate_php(7, 6);
    solve_clauses_and_verify_drat(nv, &clauses, "php_7_6");
}

#[test]
#[timeout(120_000)]
fn drat_comprehensive_php_8_7() {
    let (nv, clauses) = generate_php(8, 7);
    solve_clauses_and_verify_drat(nv, &clauses, "php_8_7");
}

// ===========================================================================
// Section 2: Graph Coloring with DRAT proof verification
// ===========================================================================

/// K_4 with 3 colors: UNSAT (chromatic number of K_4 is 4)
#[test]
#[timeout(30_000)]
fn drat_comprehensive_graph_coloring_k4_3colors() {
    let (nv, clauses) = generate_graph_coloring_complete(4, 3);
    solve_clauses_and_verify_drat(nv, &clauses, "k4_3colors");
}

/// K_5 with 4 colors: UNSAT
#[test]
#[timeout(30_000)]
fn drat_comprehensive_graph_coloring_k5_4colors() {
    let (nv, clauses) = generate_graph_coloring_complete(5, 4);
    solve_clauses_and_verify_drat(nv, &clauses, "k5_4colors");
}

/// K_6 with 5 colors: UNSAT
#[test]
#[timeout(60_000)]
fn drat_comprehensive_graph_coloring_k6_5colors() {
    let (nv, clauses) = generate_graph_coloring_complete(6, 5);
    solve_clauses_and_verify_drat(nv, &clauses, "k6_5colors");
}

// ===========================================================================
// Section 3: Ordering Cycles with DRAT proof verification
// ===========================================================================

#[test]
#[timeout(10_000)]
fn drat_comprehensive_ordering_cycle_3() {
    let (nv, clauses) = generate_ordering_cycle(3);
    solve_clauses_and_verify_drat(nv, &clauses, "order_cycle_3");
}

#[test]
#[timeout(10_000)]
fn drat_comprehensive_ordering_cycle_5() {
    let (nv, clauses) = generate_ordering_cycle(5);
    solve_clauses_and_verify_drat(nv, &clauses, "order_cycle_5");
}

#[test]
#[timeout(10_000)]
fn drat_comprehensive_ordering_cycle_10() {
    let (nv, clauses) = generate_ordering_cycle(10);
    solve_clauses_and_verify_drat(nv, &clauses, "order_cycle_10");
}

#[test]
#[timeout(10_000)]
fn drat_comprehensive_ordering_cycle_20() {
    let (nv, clauses) = generate_ordering_cycle(20);
    solve_clauses_and_verify_drat(nv, &clauses, "order_cycle_20");
}

// ===========================================================================
// Section 4: TLA+ Invariant UNSAT formulas with DRAT proof verification
// ===========================================================================

/// Single variable contradiction: (x1) AND (NOT x1)
#[test]
#[timeout(10_000)]
fn drat_comprehensive_unit_contradiction() {
    solve_dimacs_and_verify_drat("p cnf 1 2\n1 0\n-1 0\n", "unit_contradiction");
}

/// Empty clause: trivially UNSAT
#[test]
#[timeout(10_000)]
fn drat_comprehensive_empty_clause() {
    solve_dimacs_and_verify_drat("p cnf 0 1\n0\n", "empty_clause");
}

/// PHP(2,1): 2 pigeons, 1 hole
#[test]
#[timeout(10_000)]
fn drat_comprehensive_php_2_1() {
    solve_dimacs_and_verify_drat("p cnf 2 3\n1 0\n2 0\n-1 -2 0\n", "php_2_1");
}

// ===========================================================================
// Section 5: Watched-literals stress formula (chain implication conflict)
// ===========================================================================

/// Chain of binary implications forming a contradiction at level 0.
/// x1 => x2 => ... => x20, with x1 forced true and NOT x10 forced true.
#[test]
#[timeout(10_000)]
fn drat_comprehensive_chain_implication_conflict() {
    let num_vars = 20;
    let mut clauses_str = String::new();
    let mut num_clauses = 0;

    // Chain: x1 -> x2 -> ... -> x20
    for i in 1..num_vars {
        clauses_str.push_str(&format!("-{} {} 0\n", i, i + 1));
        num_clauses += 1;
    }
    // Reverse chain: NOT x20 -> NOT x19 -> ... -> NOT x1
    for i in (1..num_vars).rev() {
        clauses_str.push_str(&format!("{} -{} 0\n", i, i + 1));
        num_clauses += 1;
    }
    // Seeds: x1 and NOT x10
    clauses_str.push_str("1 0\n-10 0\n");
    num_clauses += 2;

    let dimacs = format!("p cnf {num_vars} {num_clauses}\n{clauses_str}");
    solve_dimacs_and_verify_drat(&dimacs, "chain_implication_conflict");
}

// ===========================================================================
// Section 6: integration_correctness.rs UNSAT tests with DRAT proof
// ===========================================================================

/// CreuSAT minor032 benchmark with DRAT proof (complements the soundness-only
/// test in integration_correctness.rs).
#[test]
#[timeout(120_000)]
fn drat_comprehensive_minor032() {
    let path = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../reference/creusat/tests/mfleury/SAT-2009-preprocessed/easy/unsat/minor032.cnf"
    );
    if !std::path::Path::new(path).exists() {
        eprintln!("SKIP: minor032 not found: {path}");
        return;
    }
    let cnf_text = std::fs::read_to_string(path).unwrap_or_else(|e| panic!("read minor032: {e}"));
    solve_dimacs_and_verify_drat(&cnf_text, "minor032");
}

/// CreuSAT een-tip benchmark with DRAT proof.
#[test]
#[timeout(120_000)]
fn drat_comprehensive_een_tip() {
    let path = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../reference/creusat/tests/mfleury/SAT-2009-preprocessed/easy/unsat/een-tip-uns-nusmv-t5.B.cnf"
    );
    if !std::path::Path::new(path).exists() {
        eprintln!("SKIP: een-tip not found: {path}");
        return;
    }
    let cnf_text = std::fs::read_to_string(path).unwrap_or_else(|e| panic!("read een-tip: {e}"));
    solve_dimacs_and_verify_drat(&cnf_text, "een_tip");
}

/// CreuSAT hsat_vc11803 benchmark with DRAT proof.
/// This is a trivial benchmark (pre-preprocessed with empty clause) but the
/// DRAT proof path still needs exercising.
#[test]
#[timeout(10_000)]
fn drat_comprehensive_hsat_vc11803() {
    let path = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../reference/creusat/tests/mfleury/SAT-2009-preprocessed/easy/unsat/hsat_vc11803.cnf"
    );
    if !std::path::Path::new(path).exists() {
        eprintln!("SKIP: hsat_vc11803 not found: {path}");
        return;
    }
    let cnf_text =
        std::fs::read_to_string(path).unwrap_or_else(|e| panic!("read hsat_vc11803: {e}"));
    solve_dimacs_and_verify_drat(&cnf_text, "hsat_vc11803");
}

/// CreuSAT hsat_vc11813 benchmark with DRAT proof.
#[test]
#[timeout(10_000)]
fn drat_comprehensive_hsat_vc11813() {
    let path = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../reference/creusat/tests/mfleury/SAT-2009-preprocessed/easy/unsat/hsat_vc11813.cnf"
    );
    if !std::path::Path::new(path).exists() {
        eprintln!("SKIP: hsat_vc11813 not found: {path}");
        return;
    }
    let cnf_text =
        std::fs::read_to_string(path).unwrap_or_else(|e| panic!("read hsat_vc11813: {e}"));
    solve_dimacs_and_verify_drat(&cnf_text, "hsat_vc11813");
}

/// CreuSAT xinetd_vc56703 benchmark with DRAT proof.
#[test]
#[timeout(10_000)]
fn drat_comprehensive_xinetd_vc56703() {
    let path = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../reference/creusat/tests/mfleury/SAT-2009-preprocessed/easy/unsat/xinetd_vc56703.cnf"
    );
    if !std::path::Path::new(path).exists() {
        eprintln!("SKIP: xinetd_vc56703 not found: {path}");
        return;
    }
    let cnf_text =
        std::fs::read_to_string(path).unwrap_or_else(|e| panic!("read xinetd_vc56703: {e}"));
    solve_dimacs_and_verify_drat(&cnf_text, "xinetd_vc56703");
}

// ===========================================================================
// Section 7: SATCOMP2024 known-UNSAT benchmarks with DRAT proof
// ===========================================================================

/// crn_11_99_u (SATCOMP2024 known-UNSAT) with DRAT proof.
///
/// The uncompressed `.cnf` may be absent if only the `.cnf.xz` variant
/// is checked in. `load_optional_repo_benchmark` tries both.
#[test]
#[timeout(30_000)]
fn drat_comprehensive_satcomp_crn_11_99_u() {
    let Some(cnf_text) = super::common::load_optional_repo_benchmark(
        "benchmarks/sat/satcomp2024-sample/ef330d1b144055436a2d576601191ea5-crn_11_99_u.cnf",
    ) else {
        return;
    };
    solve_dimacs_and_verify_drat(&cnf_text, "crn_11_99_u");
}

/// spg_200_316 (SATCOMP2024 known-UNSAT) with DRAT proof.
///
/// `benchmarks/sat/satcomp2024-sample/*.cnf[.xz]` is a PROVISIONED corpus, not
/// a committed one (`benchmarks/.gitignore` excludes `*.cnf`/`*.cnf.xz` there;
/// `scripts/fetch_satcomp_sample.sh` downloads it from the GBD mirror). So the
/// instance is optional exactly like `crn_11_99_u` above — the DRAT assertion
/// is unchanged and still runs whenever the corpus has been fetched.
#[test]
#[cfg_attr(debug_assertions, timeout(300_000))]
#[cfg_attr(not(debug_assertions), timeout(120_000))]
fn drat_comprehensive_satcomp_spg_200_316() {
    if cfg!(debug_assertions) {
        eprintln!("SKIP: spg_200_316 DRAT exceeds debug-mode timeout");
        return;
    }
    let Some(cnf_text) = super::common::load_optional_repo_benchmark(
        "benchmarks/sat/satcomp2024-sample/b5028686db9bd1073fa09cbd8c805f47-spg_200_316.cnf",
    ) else {
        return;
    };
    solve_dimacs_and_verify_drat(&cnf_text, "spg_200_316");
}

/// FmlaEquivChain_4_6_6 (SATCOMP2024 known-UNSAT) with DRAT proof.
///
/// Provisioned-corpus instance; see `drat_comprehensive_satcomp_spg_200_316`.
#[test]
#[cfg_attr(debug_assertions, timeout(300_000))]
#[cfg_attr(not(debug_assertions), timeout(120_000))]
fn drat_comprehensive_satcomp_fmla_equiv_chain() {
    if cfg!(debug_assertions) {
        eprintln!("SKIP: FmlaEquivChain DRAT exceeds debug-mode timeout");
        return;
    }
    let Some(cnf_text) = super::common::load_optional_repo_benchmark(
        "benchmarks/sat/satcomp2024-sample/9cd3acdb765c15163bc239ae3a57f880-FmlaEquivChain_4_6_6.sanitized.cnf",
    ) else {
        return;
    };
    solve_dimacs_and_verify_drat(&cnf_text, "fmla_equiv_chain_4_6_6");
}

// ===========================================================================
// Section 8: Aggregate sweep — all benchmarks/sat/unsat/ with DRAT proof
// ===========================================================================

/// Dynamically discover all benchmarks/sat/unsat/*.cnf files, solve each
/// with DRAT proof enabled, and verify every proof with ay-drat-check.
/// This mirrors `drat_exhaustive_dynamic_sweep_all_unsat` but uses different
/// code paths (formula → Solver::with_proof_output) to exercise the proof
/// pipeline from a different entry point.
#[test]
#[cfg_attr(debug_assertions, timeout(300_000))]
#[cfg_attr(not(debug_assertions), timeout(180_000))]
fn drat_comprehensive_unsat_corpus_sweep() {
    let unsat_dir = super::common::workspace_root().join("benchmarks/sat/unsat");
    assert!(
        unsat_dir.is_dir(),
        "UNSAT benchmark directory not found: {}",
        unsat_dir.display()
    );

    let mut entries: Vec<_> = std::fs::read_dir(&unsat_dir)
        .expect("read benchmarks/sat/unsat")
        .filter_map(Result::ok)
        .filter(|e| e.path().extension().is_some_and(|ext| ext == "cnf"))
        .map(|e| e.path())
        .collect();

    entries.sort();

    assert!(
        !entries.is_empty(),
        "no .cnf files found in {}",
        unsat_dir.display()
    );

    let mut verified = 0u32;
    let mut failures: Vec<String> = Vec::new();

    for cnf_path in &entries {
        let file_name = cnf_path
            .file_name()
            .map(|n| n.to_string_lossy().to_string())
            .unwrap_or_default();
        let label = format!("corpus_sweep_{file_name}");

        let cnf_text = std::fs::read_to_string(cnf_path)
            .unwrap_or_else(|e| panic!("read {}: {e}", cnf_path.display()));

        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            solve_dimacs_and_verify_drat(&cnf_text, &label);
        }));

        match result {
            Ok(()) => verified += 1,
            Err(e) => {
                let msg = if let Some(s) = e.downcast_ref::<String>() {
                    s.clone()
                } else if let Some(s) = e.downcast_ref::<&str>() {
                    (*s).to_owned()
                } else {
                    format!("{file_name}: panicked")
                };
                failures.push(msg);
            }
        }
    }

    eprintln!(
        "DRAT-comprehensive corpus sweep: {} verified, {} failed (of {} total)",
        verified,
        failures.len(),
        entries.len()
    );

    assert!(
        failures.is_empty(),
        "DRAT-comprehensive corpus sweep failures ({} of {}):\n{}",
        failures.len(),
        entries.len(),
        failures.join("\n---\n")
    );
}
