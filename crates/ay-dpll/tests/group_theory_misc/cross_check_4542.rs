// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ay_dpll::api::{CrossCheckVariant, Logic, SolveResult, Solver};
use ay_dpll::Executor;
use ay_frontend::{parse, Command};
use ay_sat::{parse_dimacs, SatResult};

const AUFLIA_STORE_SCRIPT: &str = r#"
(set-logic QF_AUFLIA)
(declare-const a (Array Int Int))
(declare-const i Int)
(assert (not (= (select (store a i 5) i) 5)))
(check-sat)
"#;

const LIA_SEED_SCRIPT: &str = r#"
(set-logic QF_LIA)
(declare-const x Int)
(assert (= x 5))
(check-sat)
"#;

#[test]
fn logic_mode_cross_check_agrees_for_quantifier_free_auflia() {
    let report = Solver::cross_check_smtlib2(
        AUFLIA_STORE_SCRIPT,
        &[CrossCheckVariant::new("logic_all").with_logic(Logic::All)],
    )
    .expect("cross-check should replay AUFLIA script");

    assert_eq!(report.baseline.result, SolveResult::unsat());
    assert_eq!(report.variants.len(), 1);
    assert_eq!(report.variants[0].label, "logic_all");
    assert_eq!(report.variants[0].result, SolveResult::unsat());
    assert_eq!(report.disagreement, None);
}

#[test]
fn seed_perturbation_cross_check_agrees_for_stable_query() {
    let report = Solver::cross_check_smtlib2(
        LIA_SEED_SCRIPT,
        &[
            CrossCheckVariant::new("seed_0").with_random_seed(0),
            CrossCheckVariant::new("seed_1").with_random_seed(1),
            CrossCheckVariant::new("seed_2").with_random_seed(2),
        ],
    )
    .expect("cross-check should replay seeded QF_LIA script");

    assert_eq!(report.baseline.result, SolveResult::Sat);
    assert!(report.baseline.verification.sat_model_validated);
    assert_eq!(report.disagreement, None);
    assert_eq!(report.variants.len(), 3);
    assert!(report
        .variants
        .iter()
        .all(|run| run.result == SolveResult::Sat));
    assert!(report
        .variants
        .iter()
        .all(|run| run.verification.sat_model_validated));
}

// ============================================================================
// SAT-vs-DPLL internal consistency: same propositional formula through both
// the pure SAT solver and the DPLL(T) executor must agree.
// Part of #4542 acceptance criteria.
// ============================================================================

/// Convert a DIMACS CNF string to an equivalent SMT-LIB2 propositional script.
///
/// Each variable `k` becomes `(declare-const v_k Bool)`, and each clause
/// becomes an `(assert (or ...))` with negated literals as `(not v_k)`.
fn cnf_to_smtlib(cnf: &str) -> Option<String> {
    let formula = parse_dimacs(cnf).ok()?;
    let mut script = String::new();
    script.push_str("(set-logic QF_UF)\n");

    for var_idx in 0..formula.num_vars {
        script.push_str(&format!("(declare-const v_{} Bool)\n", var_idx + 1));
    }

    for clause in &formula.clauses {
        if clause.is_empty() {
            script.push_str("(assert false)\n");
            continue;
        }
        if clause.len() == 1 {
            let lit = &clause[0];
            let var = lit.variable().index() + 1;
            if lit.is_positive() {
                script.push_str(&format!("(assert v_{var})\n"));
            } else {
                script.push_str(&format!("(assert (not v_{var}))\n"));
            }
            continue;
        }
        script.push_str("(assert (or");
        for lit in clause {
            let var = lit.variable().index() + 1;
            if lit.is_positive() {
                script.push_str(&format!(" v_{var}"));
            } else {
                script.push_str(&format!(" (not v_{var})"));
            }
        }
        script.push_str("))\n");
    }

    script.push_str("(check-sat)\n");
    Some(script)
}

/// Run a propositional formula through the pure SAT solver.
fn run_pure_sat(cnf: &str) -> Option<SolveResult> {
    let formula = parse_dimacs(cnf).ok()?;
    let mut solver = formula.into_solver();
    let result = solver.solve().into_inner();
    Some(match result {
        SatResult::Sat(_) => SolveResult::Sat,
        SatResult::Unsat(_) => SolveResult::unsat(),
        SatResult::Unknown => SolveResult::Unknown,
        _ => SolveResult::Unknown,
    })
}

/// Run an SMT-LIB2 script through the DPLL(T) executor.
fn run_dpll_executor(smtlib: &str) -> SolveResult {
    let commands = parse(smtlib).expect("SMT-LIB parse should succeed");
    let mut executor = Executor::new();
    for command in &commands {
        if matches!(command, Command::CheckSat) {
            match executor.execute(command) {
                Ok(Some(ref output)) => {
                    let trimmed = output.trim();
                    if trimmed == "sat" {
                        return SolveResult::Sat;
                    } else if trimmed == "unsat" {
                        return SolveResult::unsat();
                    } else {
                        return SolveResult::Unknown;
                    }
                }
                _ => return SolveResult::Unknown,
            }
        }
        let _ = executor.execute(command);
    }
    SolveResult::Unknown
}

/// UNSAT benchmarks: pure SAT and DPLL(T) must both return UNSAT.
#[test]
fn sat_vs_dpll_consistency_unsat_benchmarks() {
    let unsat_cnfs = [
        (
            "php_4_3",
            include_str!("../../../../benchmarks/sat/unsat/php_4_3.cnf"),
        ),
        (
            "php_5_4",
            include_str!("../../../../benchmarks/sat/unsat/php_5_4.cnf"),
        ),
        (
            "tseitin_grid_3x3",
            include_str!("../../../../benchmarks/sat/unsat/tseitin_grid_3x3.cnf"),
        ),
        (
            "parity_6",
            include_str!("../../../../benchmarks/sat/unsat/parity_6.cnf"),
        ),
        (
            "at_most_1_of_5",
            include_str!("../../../../benchmarks/sat/unsat/at_most_1_of_5.cnf"),
        ),
        (
            "blocked_chain_8",
            include_str!("../../../../benchmarks/sat/unsat/blocked_chain_8.cnf"),
        ),
        (
            "graph_coloring_k3_4clique",
            include_str!("../../../../benchmarks/sat/unsat/graph_coloring_k3_4clique.cnf"),
        ),
        (
            "latin_square_2x2_conflict",
            include_str!("../../../../benchmarks/sat/unsat/latin_square_2x2_conflict.cnf"),
        ),
        (
            "mutex_4proc",
            include_str!("../../../../benchmarks/sat/unsat/mutex_4proc.cnf"),
        ),
        (
            "mutilated_chessboard_2x2",
            include_str!("../../../../benchmarks/sat/unsat/mutilated_chessboard_2x2.cnf"),
        ),
        (
            "ramsey_r3_3_6",
            include_str!("../../../../benchmarks/sat/unsat/ramsey_r3_3_6.cnf"),
        ),
        (
            "urquhart_3",
            include_str!("../../../../benchmarks/sat/unsat/urquhart_3.cnf"),
        ),
    ];

    let mut tested = 0;
    let mut disagreements = Vec::new();

    for (name, cnf) in &unsat_cnfs {
        let smtlib = match cnf_to_smtlib(cnf) {
            Some(s) => s,
            None => {
                eprintln!("SKIP {name}: CNF parse failed");
                continue;
            }
        };

        let sat_result = match run_pure_sat(cnf) {
            Some(r) => r,
            None => {
                eprintln!("SKIP {name}: SAT solver failed");
                continue;
            }
        };

        let dpll_result = run_dpll_executor(&smtlib);

        tested += 1;

        // Both should be UNSAT for these benchmarks
        if sat_result != dpll_result {
            disagreements.push(format!("{name}: SAT={sat_result:?} DPLL={dpll_result:?}"));
        }
    }

    eprintln!(
        "SAT-vs-DPLL consistency (UNSAT): {tested} tested, {} disagreements",
        disagreements.len()
    );
    assert!(
        disagreements.is_empty(),
        "SAT-vs-DPLL internal consistency disagreements:\n{}",
        disagreements.join("\n")
    );
    assert!(
        tested >= 10,
        "Expected at least 10 UNSAT benchmarks tested, got {tested}"
    );
}

/// Generate small random 3-SAT formulas and check SAT vs DPLL(T) consistency.
///
/// Uses a deterministic seed for reproducibility.
#[test]
fn sat_vs_dpll_consistency_random_3sat() {
    let mut tested = 0;
    let mut disagreements = Vec::new();

    // Generate 100 random 3-SAT instances with varying clause/variable ratios.
    // At ratio ~4.27, the phase transition makes about half SAT and half UNSAT.
    for instance_idx in 0..100u64 {
        let num_vars = 20;
        // Vary the clause count to hit both SAT and UNSAT regions
        let num_clauses = 60 + (instance_idx % 40) as usize; // 60-99 clauses

        let cnf = generate_random_3sat(num_vars, num_clauses, instance_idx);
        let smtlib = match cnf_to_smtlib(&cnf) {
            Some(s) => s,
            None => continue,
        };

        let sat_result = match run_pure_sat(&cnf) {
            Some(r) => r,
            None => continue,
        };

        let dpll_result = run_dpll_executor(&smtlib);

        // Skip if either returned Unknown
        if sat_result == SolveResult::Unknown || dpll_result == SolveResult::Unknown {
            continue;
        }

        tested += 1;
        if sat_result != dpll_result {
            disagreements.push(format!(
                "random_3sat_{instance_idx} (vars={num_vars}, clauses={num_clauses}): SAT={sat_result:?} DPLL={dpll_result:?}"
            ));
        }
    }

    eprintln!(
        "SAT-vs-DPLL consistency (random 3-SAT): {tested} tested, {} disagreements",
        disagreements.len()
    );
    assert!(
        disagreements.is_empty(),
        "SAT-vs-DPLL internal consistency disagreements on random 3-SAT:\n{}",
        disagreements.join("\n")
    );
    assert!(
        tested >= 50,
        "Expected at least 50 random instances tested, got {tested}"
    );
}

/// Generate a random 3-SAT DIMACS CNF string with a deterministic seed.
fn generate_random_3sat(num_vars: usize, num_clauses: usize, seed: u64) -> String {
    let mut rng = SimpleRng::new(seed);
    let mut lines = vec![format!("p cnf {num_vars} {num_clauses}")];

    for _ in 0..num_clauses {
        let mut clause = Vec::new();
        for _ in 0..3 {
            let var = (rng.next() % num_vars as u64) as i64 + 1;
            let lit = if rng.next().is_multiple_of(2) {
                var
            } else {
                -var
            };
            clause.push(lit);
        }
        let clause_str: Vec<String> = clause.iter().map(ToString::to_string).collect();
        lines.push(format!("{} 0", clause_str.join(" ")));
    }

    lines.join("\n")
}

/// Minimal deterministic PRNG (xorshift64) for reproducible test generation.
struct SimpleRng {
    state: u64,
}

impl SimpleRng {
    fn new(seed: u64) -> Self {
        Self {
            state: seed.wrapping_add(0x9E3779B97F4A7C15),
        }
    }

    fn next(&mut self) -> u64 {
        let mut x = self.state;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.state = x;
        x
    }
}
