// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A checked native replay must carry a self-contained proof problem.

use std::time::Duration;

use crate::api::{Logic, NativeReplayMetadata, ProofAcceptanceMode, Solver, Sort, Term};

fn free_constant(solver: &mut Solver, name: &str, sort: Sort) -> Term {
    let term = solver.terms_mut().mk_fresh_var(name, sort);
    solver.wrap_term(term)
}

#[test]
fn native_replay_checked_transport_declares_its_free_array_and_scalar_constants() {
    for (length, right_value, unsat) in [(1, 2, true), (0, 2, false), (1, 1, false)] {
        let mut solver = Solver::try_new(Logic::QfAuflia).expect("solver");
        let len = free_constant(&mut solver, "len", Sort::Int);
        let array_sort = Sort::array(Sort::Int, Sort::Int);
        let left = free_constant(&mut solver, "left", array_sort.clone());
        let left_offset = free_constant(&mut solver, "left_offset", Sort::Int);
        let right = free_constant(&mut solver, "right", array_sort);
        let right_offset = free_constant(&mut solver, "right_offset", Sort::Int);
        let ext_eq = free_constant(&mut solver, "ext_eq", Sort::Bool);
        let zero = solver.int_const(0);
        let one = solver.int_const(1);
        let length_value = solver.int_const(length);
        let right_value = solver.int_const(right_value);
        let left_read = solver.select(left, left_offset);
        let right_read = solver.select(right, right_offset);
        let same_read = solver.eq(left_read, right_read);
        let in_bounds = solver.lt(zero, len);
        let not_ext_eq = solver.not(ext_eq);
        let not_in_bounds = solver.not(in_bounds);
        let equality_clause = solver.or(not_ext_eq, same_read);
        let equality_clause = solver.or(equality_clause, not_in_bounds);
        let length_pin = solver.eq(len, length_value);
        let left_pin = solver.eq(left_read, one);
        let right_pin = solver.eq(right_read, right_value);
        for root in [equality_clause, ext_eq, length_pin, left_pin, right_pin] {
            solver.assert_term(root);
        }
        let source = solver.export_native_replay_artifact(NativeReplayMetadata::default(), None);
        assert!(
            source.declarations.is_empty(),
            "fixture uses native free constants"
        );
        let (details, proof) = Solver::replay_native_replay_artifact_with_checked_proof(
            &source,
            Duration::from_secs(5),
        )
        .expect("checked native replay");
        if !unsat {
            assert!(
                details.result.is_sat() && details.result.was_model_validated(),
                "{details:#?}"
            );
            assert!(proof.is_none());
            continue;
        }
        assert!(details.result.is_unsat(), "{details:#?}");
        let proof = proof.expect("strict UNSAT has a retained proof");
        proof
            .accept_for_consumer(ProofAcceptanceMode::Strict)
            .expect("strict authority");
        let problem = proof
            .alethe_problem_smt2
            .expect("self-contained proof problem");
        let declarations: Vec<_> = problem
            .lines()
            .filter(|line| line.starts_with("(declare-const "))
            .collect();
        assert_eq!(declarations.len(), 6, "{problem}");
        assert!(
            declarations
                .iter()
                .all(|line| line.contains("__ay_native_replay_var_")),
            "{problem}"
        );
        assert_eq!(
            declarations
                .iter()
                .filter(|line| line.ends_with(" (Array Int Int))"))
                .count(),
            2,
            "{problem}"
        );
        assert_eq!(
            declarations
                .iter()
                .filter(|line| line.ends_with(" Bool)"))
                .count(),
            1,
            "{problem}"
        );
        ay_frontend::parse(&problem).expect("proof problem syntax");
    }
}
