// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

use ay_sat::{parse_dimacs, Literal, SatResult};

#[test]
fn test_soundness_manol_pipe_c9_with_bve_disabled() {
    let path = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../reference/creusat/tests/mfleury/SAT-2009-preprocessed/easy/unsat/manol-pipe-c9.cnf"
    );

    if !std::path::Path::new(path).exists() {
        eprintln!("Skipping: benchmark file missing: {path}");
        return;
    }

    let dimacs =
        std::fs::read_to_string(path).unwrap_or_else(|e| panic!("failed to read {path}: {e}"));
    let formula = parse_dimacs(&dimacs).unwrap_or_else(|e| panic!("failed to parse {path}: {e}"));

    // Keep original clauses for diagnostics if SAT is returned.
    let original_clauses = formula.clauses.clone();
    let mut solver = formula.into_solver();

    // #3309 reproduction setup: BVE off, other inprocessing passes enabled.
    solver.set_bve_enabled(false);

    match solver.solve().into_inner() {
        SatResult::Unsat(_) => {}
        SatResult::Unknown => panic!("expected UNSAT for {path}, got UNKNOWN"),
        SatResult::Sat(model) => {
            let first_violated = original_clauses
                .iter()
                .enumerate()
                .find_map(|(ci, clause)| {
                    let satisfied = clause.iter().any(|lit| lit_satisfied(*lit, &model));
                    if satisfied {
                        None
                    } else {
                        Some((ci, clause))
                    }
                });

            if let Some((ci, clause)) = first_violated {
                panic!(
                    "soundness bug: {path} returned SAT with violated clause #{ci}: {:?}",
                    clause_to_dimacs(clause)
                );
            }

            panic!("expected UNSAT for {path}, got SAT");
        }
        #[allow(unreachable_patterns)]
        _ => unreachable!(),
    }
}

fn lit_satisfied(lit: Literal, model: &[bool]) -> bool {
    let var_idx = lit.variable().index();
    if var_idx >= model.len() {
        return false;
    }
    if lit.is_positive() {
        model[var_idx]
    } else {
        !model[var_idx]
    }
}

fn clause_to_dimacs(clause: &[Literal]) -> Vec<i32> {
    clause
        .iter()
        .map(|lit| {
            let v = lit.variable().id() as i32 + 1;
            if lit.is_positive() {
                v
            } else {
                -v
            }
        })
        .collect()
}
