// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A root-fixed variable whose unit clause has left the arena (a BVE unit
//! resolvent deleted as satisfied by the post-BVE dense propagation) is only
//! recorded on the trail. The startup walk reads the arena and the phases,
//! so it could set the variable the other way, the candidate satisfied every
//! arena clause, and the original-ledger check then failed: the solve ended
//! `unknown` on a SAT or an UNSAT formula (2026-09-17 audit, 6 of 40 seeds of
//! this generator). `get_model_from_phases` now keeps root-fixed values.

use super::*;
use crate::ProofOutput;

fn next(state: &mut u64) -> u64 {
    *state = state
        .wrapping_mul(6364136223846793005)
        .wrapping_add(1442695040888963407);
    *state >> 33
}

/// `gadgets` gadgets over fresh x, a, b, c — (x a b) (x ¬a b) (x ¬b c) (x ¬b ¬c),
/// which resolve on b to the unit x once subsumption has strengthened them —
/// plus nine clauses (¬x l1 l2) over random core literals, on top of a random
/// 3-SAT core of `core` variables at ratio 4.0.
fn gadget_formula(seed: u64, gadgets: usize, core: usize) -> (usize, Vec<Vec<i32>>) {
    let mut state = seed.wrapping_mul(0x9E37_79B9_7F4A_7C15) | 1;
    let mut clauses: Vec<Vec<i32>> = Vec::new();
    let mut lit = |state: &mut u64| {
        let v = (next(state) % core as u64) as i32 + 1;
        if next(state) & 1 == 0 {
            v
        } else {
            -v
        }
    };
    for _ in 0..(core * 4) {
        let mut clause: Vec<i32> = Vec::new();
        while clause.len() < 3 {
            let l = lit(&mut state);
            if clause.iter().any(|c| c.abs() == l.abs()) {
                continue;
            }
            clause.push(l);
        }
        clauses.push(clause);
    }
    let mut nv = core as i32;
    for _ in 0..gadgets {
        let (x, a, b, c) = (nv + 1, nv + 2, nv + 3, nv + 4);
        nv += 4;
        clauses.push(vec![x, a, b]);
        clauses.push(vec![x, -a, b]);
        clauses.push(vec![x, -b, c]);
        clauses.push(vec![x, -b, -c]);
        for _ in 0..9 {
            let (l1, l2) = (lit(&mut state), lit(&mut state));
            if l1.abs() == l2.abs() {
                continue;
            }
            clauses.push(vec![-x, l1, l2]);
        }
    }
    (nv as usize, clauses)
}

fn satisfies(clauses: &[Vec<i32>], model: &[bool]) -> bool {
    clauses.iter().all(|clause| {
        clause.iter().any(|&v| {
            let value = model
                .get((v.unsigned_abs() - 1) as usize)
                .copied()
                .unwrap_or(false);
            (v > 0) == value
        })
    })
}

#[test]
fn a_root_fixed_bve_unit_survives_the_startup_walk() {
    let mut answered = 0;
    for seed in 0..40u64 {
        let (num_vars, clauses) = gadget_formula(seed, 3, 120);
        let mut solver: Solver =
            Solver::with_proof_output(num_vars, ProofOutput::drat_text(Vec::<u8>::new()));
        for clause in &clauses {
            let lits: Vec<Literal> = clause
                .iter()
                .map(|&v| {
                    if v > 0 {
                        Literal::positive(Variable((v - 1) as u32))
                    } else {
                        Literal::negative(Variable((-v - 1) as u32))
                    }
                })
                .collect();
            solver.add_clause_db(&lits, false);
        }
        solver.initialize_watches();
        solver.set_bve_enabled(true);
        let result = solver.solve().into_inner();
        match result {
            SatResult::Sat(model) => {
                assert!(
                    satisfies(&clauses, &model),
                    "seed {seed}: the model falsifies the input"
                );
                answered += 1;
            }
            SatResult::Unsat(_) => {
                let writer = solver.take_proof_writer().expect("DRAT writer");
                let proof = writer.into_vec().expect("flush");
                let mut cnf = format!("p cnf {num_vars} {}\n", clauses.len());
                for clause in &clauses {
                    for v in clause {
                        cnf.push_str(&format!("{v} "));
                    }
                    cnf.push_str("0\n");
                }
                let parsed = ay_drat_check::cnf_parser::parse_cnf(cnf.as_bytes()).expect("cnf");
                let steps = ay_drat_check::drat_parser::parse_drat(&proof).expect("drat");
                let mut checker = ay_drat_check::checker::DratChecker::new(parsed.num_vars, true);
                checker.verify(&parsed.clauses, &steps).unwrap_or_else(|e| {
                    panic!("seed {seed}: the DRAT checker rejects the proof: {e}")
                });
                answered += 1;
            }
            SatResult::Unknown => panic!(
                "seed {seed}: no verdict on a small formula (finalize failures {})",
                solver.cold.finalize_sat_fail_count
            ),
        }
    }
    assert_eq!(answered, 40);
}

/// A random binary CSP (99.9 percent binary clauses, so binary propagations
/// are literal-tagged jump reasons): reduction deleted a hyper-binary
/// resolvent that still supported the trail, and the next learned clause's
/// proof step was not RUP for the checker (2026-09-17 audit; VeriPB rejected
/// the shipped posture's certificate at step 153,302). The fixture is the
/// auditor's trigger; the DRAT checker must accept the whole proof.
#[test]
fn a_hyper_binary_on_the_trail_survives_reduction_and_the_proof_checks() {
    let path =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/data/jump_reason_hbr.cnf");
    let text = std::fs::read_to_string(&path).expect("read jump_reason_hbr.cnf");
    let formula = crate::parse_dimacs(&text).expect("parse");
    let num_vars = crate::dimacs::max_variable_count(&formula.clauses);
    let mut solver = Solver::with_proof_output(num_vars, ProofOutput::drat_text(Vec::<u8>::new()));
    solver.set_symmetry_oneshot(true);
    let features = crate::features::SatFeatures::extract(num_vars, &formula.clauses);
    let config = crate::SolverVariant::Default.config(crate::variant::VariantInput::new(
        num_vars,
        formula.num_clauses,
        crate::variant::VariantProofMode::Drat,
    ));
    let plan = crate::variant::VariantProfilePlan::from_config_features_with_source(
        config,
        &features,
        crate::auto::DecisionSource::Default,
    );
    plan.apply_to_solver(&mut solver);
    for clause in formula.clauses {
        solver.add_clause(clause);
    }
    let result = solver.solve().into_inner();
    assert!(
        matches!(result, SatResult::Unsat(_)),
        "the CSP is UNSAT: got {result:?}"
    );
    assert!(
        solver.cold.jump_reasons_enabled,
        "the fixture must take the jump-reason path"
    );
    let writer = solver.take_proof_writer().expect("DRAT writer");
    let proof = writer.into_vec().expect("flush");
    let parsed = ay_drat_check::cnf_parser::parse_cnf(text.as_bytes()).expect("cnf");
    let steps = ay_drat_check::drat_parser::parse_drat(&proof).expect("drat");
    let mut checker = ay_drat_check::checker::DratChecker::new(parsed.num_vars, true);
    checker
        .verify(&parsed.clauses, &steps)
        .unwrap_or_else(|e| panic!("the DRAT checker rejects the proof: {e}"));
}
