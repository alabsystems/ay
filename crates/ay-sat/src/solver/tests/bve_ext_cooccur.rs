// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `--sat-bve-ext-cooccur`: after factoring, BVE refuses every original
//! variable that shares a clause with a live extension variable (the #8397
//! guard). The switch lifts the refusal; reconstruction restores each
//! eliminated variable from its own clauses in reverse order, so the model
//! stays a model of the input whatever the elimination order.

use super::*;
use crate::ProofOutput;

fn switched(value: Option<bool>) -> ay_core::sat_ab_test_override::Guard {
    ay_core::sat_ab_test_override::set(ay_core::SatAbSwitches {
        bve_ext_cooccur: value,
        ..Default::default()
    })
}

fn lit(v: i32) -> Literal {
    if v > 0 {
        Literal::positive(Variable((v - 1) as u32))
    } else {
        Literal::negative(Variable((-v - 1) as u32))
    }
}

/// A 6x6 grid of binaries `a_i | b_j` (variables 1..6 and 7..12) that
/// factoring compresses through one fresh variable, plus one clause per
/// `a_i` that gives it a negative occurrence, so it is an elimination
/// candidate with two occurrences.
fn grid_formula() -> (usize, Vec<Vec<i32>>) {
    let mut clauses = Vec::new();
    for i in 1..=6 {
        for j in 7..=12 {
            clauses.push(vec![i, j]);
        }
    }
    for i in 1..=6 {
        clauses.push(vec![-i, 12 + i]);
    }
    (18, clauses)
}

fn solver_for(num_vars: usize, clauses: &[Vec<i32>], proof: Option<ProofOutput>) -> Solver {
    let mut solver: Solver = match proof {
        Some(proof) => Solver::with_proof_output(num_vars, proof),
        None => Solver::new(num_vars),
    };
    for clause in clauses {
        let lits: Vec<Literal> = clause.iter().map(|&v| lit(v)).collect();
        solver.add_clause_db(&lits, false);
    }
    solver.initialize_watches();
    solver.set_factor_enabled(true);
    solver.set_bve_enabled(true);
    solver
}

fn satisfies(clauses: &[Vec<i32>], model: &[bool]) -> Option<Vec<i32>> {
    clauses
        .iter()
        .find(|clause| {
            !clause.iter().any(|&v| {
                let value = model
                    .get((v.unsigned_abs() - 1) as usize)
                    .copied()
                    .unwrap_or(false);
                (v > 0) == value
            })
        })
        .cloned()
}

fn brute_force_sat(num_vars: usize, clauses: &[Vec<i32>]) -> bool {
    (0..1u64 << num_vars).any(|bits| {
        let model: Vec<bool> = (0..num_vars).map(|v| bits >> v & 1 == 1).collect();
        satisfies(clauses, &model).is_none()
    })
}

#[test]
fn the_guard_refuses_originals_beside_a_live_extension_variable_unless_switched() {
    for (value, expect_eliminated) in [(None, false), (Some(false), false), (Some(true), true)] {
        let _switches = switched(value);
        let (num_vars, clauses) = grid_formula();
        let mut solver = solver_for(num_vars, &clauses, None);
        solver.factorize();
        let ext_start = solver.cold.first_extension_var_index;
        assert_ne!(
            ext_start,
            usize::MAX,
            "switch={value:?}: the grid must factor"
        );
        assert!(solver.cold.factor_factored_total > 0, "switch={value:?}");
        // Keep the fresh variable and the b side out, so the only candidates
        // are the six `a_i`, each beside the live extension variable.
        for v in 7..=12 {
            solver.freeze(Variable(v as u32 - 1));
        }
        for v in ext_start..solver.num_vars {
            solver.freeze(Variable(v as u32));
        }
        assert!(!solver.bve(), "switch={value:?}: the grid is satisfiable");
        let originals_removed = (0..6)
            .filter(|&i| solver.var_lifecycle.is_removed(i))
            .count();
        assert!(
            solver.cold.bve_ext_cooccur_skips > 0,
            "switch={value:?}: the guard must have seen the a_i"
        );
        if expect_eliminated {
            assert!(
                originals_removed > 0,
                "switch={value:?}: the switch admits the a_i to elimination"
            );
        } else {
            assert_eq!(
                originals_removed, 0,
                "switch={value:?}: the guard refuses the a_i"
            );
        }
    }
}

#[test]
fn the_switch_stays_closed_after_an_incremental_call() {
    let _switches = switched(Some(true));
    let (num_vars, clauses) = grid_formula();
    let mut solver = solver_for(num_vars, &clauses, None);
    assert!(solver.bve_ext_cooccur_allowed());
    solver.cold.has_been_incremental = true;
    assert!(!solver.bve_ext_cooccur_allowed());
}

/// A 64-bit LCG, the same on every platform.
fn next(state: &mut u64) -> u64 {
    *state = state
        .wrapping_mul(6364136223846793005)
        .wrapping_add(1442695040888963407);
    *state >> 33
}

/// A factorable 4x4 grid over variables 1..8 plus random clauses over all 14
/// variables: factoring fires on the grid, BVE then finds candidates beside
/// the extension variable, and the whole formula is small enough to decide by
/// enumeration.
fn random_formula(seed: u64) -> (usize, Vec<Vec<i32>>) {
    let num_vars = 14usize;
    let mut state = seed.wrapping_mul(0x9E37_79B9_7F4A_7C15) | 1;
    let mut clauses = Vec::new();
    for i in 1..=4 {
        for j in 5..=8 {
            clauses.push(vec![i, j]);
        }
    }
    let extra = 10 + (next(&mut state) % 12) as usize;
    for _ in 0..extra {
        let len = 2 + (next(&mut state) % 2) as usize;
        let mut clause: Vec<i32> = Vec::new();
        while clause.len() < len {
            let v = (next(&mut state) % num_vars as u64) as i32 + 1;
            if clause.iter().any(|l| l.abs() == v) {
                continue;
            }
            clause.push(if next(&mut state) & 1 == 0 { v } else { -v });
        }
        clauses.push(clause);
    }
    (num_vars, clauses)
}

#[test]
fn models_stay_models_of_the_input_under_the_switch_and_verdicts_agree_with_enumeration() {
    let _switches = switched(Some(true));
    let mut admitted_seeds = 0;
    let mut eliminated_beside_extension = 0;
    let mut sat_seeds = 0;
    for seed in 0..300u64 {
        let (num_vars, clauses) = random_formula(seed);
        let expected = brute_force_sat(num_vars, &clauses);
        let proof = ProofOutput::drat_text(Vec::<u8>::new());
        let mut solver = solver_for(num_vars, &clauses, Some(proof));
        let result = solver.solve().into_inner();
        if solver.cold.bve_ext_cooccur_skips > 0 {
            admitted_seeds += 1;
            let ext_start = solver.cold.first_extension_var_index;
            if ext_start != usize::MAX
                && (0..ext_start.min(num_vars)).any(|v| solver.var_lifecycle.is_removed(v))
            {
                eliminated_beside_extension += 1;
            }
        }
        match result {
            SatResult::Sat(model) => {
                sat_seeds += 1;
                assert!(expected, "seed {seed}: SAT on an unsatisfiable formula");
                if let Some(clause) = satisfies(&clauses, &model) {
                    panic!("seed {seed}: the model falsifies {clause:?} of the input");
                }
            }
            SatResult::Unsat(_) => {
                assert!(!expected, "seed {seed}: UNSAT on a satisfiable formula");
                let writer = solver.take_proof_writer().expect("DRAT writer");
                let text = writer.into_vec().expect("flush");
                let mut cnf = format!("p cnf {num_vars} {}\n", clauses.len());
                for clause in &clauses {
                    for v in clause {
                        cnf.push_str(&format!("{v} "));
                    }
                    cnf.push_str("0\n");
                }
                let parsed = ay_drat_check::cnf_parser::parse_cnf(cnf.as_bytes()).expect("cnf");
                let steps = ay_drat_check::drat_parser::parse_drat(&text).expect("drat");
                let mut checker = ay_drat_check::checker::DratChecker::new(parsed.num_vars, true);
                checker.verify(&parsed.clauses, &steps).unwrap_or_else(|e| {
                    panic!("seed {seed}: the DRAT checker rejects the proof: {e}")
                });
            }
            SatResult::Unknown => panic!("seed {seed}: no verdict"),
        }
    }
    assert!(sat_seeds > 0, "some seeds must be satisfiable");
    assert!(
        admitted_seeds > 0,
        "the guard must have been reached on some seed, or the test proves nothing"
    );
    assert!(
        eliminated_beside_extension > 0,
        "some seed must eliminate an original variable after factoring, or the test proves nothing"
    );
}

/// The two BVE reconstruction regressions on file (#8397, #8482), under the
/// switch: a wrong SAT would be the guard's fear come true; UNSAT (or, for
/// the harder braun members, a timeout) is the only acceptable answer.
#[test]
fn the_reconstruction_regressions_stay_unsat_under_the_switch() {
    let _switches = switched(Some(true));
    let base = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    let mut paths = vec![base.join("tests/data/crn_11_99_u.cnf")];
    for name in ["7", "9", "11"] {
        paths.push(base.join(format!(
            "../../benchmarks/sat/eq_atree_braun/eq.atree.braun.{name}.unsat.cnf"
        )));
    }
    let mut checked = 0;
    for path in paths {
        if !path.exists() {
            eprintln!("{} missing, skipped", path.display());
            continue;
        }
        let dimacs = std::fs::read_to_string(&path).expect("read");
        let formula = crate::parse_dimacs(&dimacs).expect("parse");
        let mut solver = formula.into_solver();
        let flag = Arc::new(AtomicBool::new(false));
        solver.set_interrupt(flag.clone());
        let timeout_flag = flag.clone();
        std::thread::spawn(move || {
            std::thread::sleep(std::time::Duration::from_secs(60));
            timeout_flag.store(true, Ordering::Relaxed);
        });
        let result = solver
            .solve_interruptible(move || flag.load(Ordering::Relaxed))
            .into_inner();
        assert!(
            !matches!(result, SatResult::Sat(_)),
            "{}: a model on a known-UNSAT formula under the switch",
            path.display()
        );
        checked += 1;
    }
    assert!(checked > 0, "no regression formula was found");
}

/// `--sat-bve-bound-progress`: x1 has two positive and three negative
/// occurrences over distinct variables, so eliminating it makes six
/// resolvents for five clauses removed: refused at bound 0, admitted at
/// bound 1. A complete phase that eliminates nothing moves the bound only
/// under the switch.
#[test]
fn an_unproductive_complete_phase_raises_the_bound_only_under_the_switch() {
    for (value, expect_progress) in [(None, false), (Some(false), false), (Some(true), true)] {
        let _switches = ay_core::sat_ab_test_override::set(ay_core::SatAbSwitches {
            bve_bound_progress: value,
            ..Default::default()
        });
        let clauses = vec![
            vec![1, 2],
            vec![1, 3],
            vec![-1, 4],
            vec![-1, 5],
            vec![-1, 6],
        ];
        let mut solver = solver_for(6, &clauses, None);
        for v in 2..=6 {
            solver.freeze(Variable(v as u32 - 1));
        }
        solver.inproc.bve.reset_growth_bound_for_inprocessing();
        solver.inproc.bve.mark_all_candidates_dirty();
        assert_eq!(solver.inproc.bve.growth_bound(), 0);
        assert!(!solver.bve(), "switch={value:?}");
        assert!(
            !solver.var_lifecycle.is_removed(0),
            "switch={value:?}: six resolvents for five clauses is refused at bound 0"
        );
        if expect_progress {
            assert_eq!(solver.inproc.bve.growth_bound(), 1, "switch={value:?}");
            assert!(solver.inproc.bve.has_dirty_candidates(), "switch={value:?}");
            assert!(!solver.bve(), "switch={value:?}");
            assert!(
                solver.var_lifecycle.is_removed(0),
                "switch={value:?}: at bound 1 the elimination is admitted"
            );
        } else {
            assert_eq!(solver.inproc.bve.growth_bound(), 0, "switch={value:?}");
            assert!(!solver.bve(), "switch={value:?}");
            assert!(!solver.var_lifecycle.is_removed(0), "switch={value:?}");
        }
    }
}
