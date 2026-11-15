// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The producer builds candidates; the unchanged strict checker judges them.

use super::*;
use crate::Executor;

fn candidate(text: &str) -> (Executor, Proof, Option<()>) {
    let mut executor = Executor::new();
    let commands = ay_frontend::parse(&format!(
        "(declare-const x Int)(declare-const y Int)(assert {text})"
    ))
    .expect("fixture parses");
    executor.execute_all(&commands).expect("fixture elaborates");
    let ay_frontend::Command::Assert(root) = &commands[2] else {
        panic!("assertion");
    };
    let raw = executor
        .raw_intern_surface(root)
        .expect("raw authored root");
    executor.record_rebuilt_authored_proof_premise(raw);
    let mut proof = Proof::new();
    let assume = proof.add_assume(raw, None);
    let result = refute_root(&mut executor.ctx.terms, &mut proof, assume, raw);
    (executor, proof, result)
}

#[test]
fn implication_branches_build_complete_strict_refutations() {
    for root in [
        "(and (= x 0) (=> (= x 0) (= y 32)) (not (= y 32)))",
        "(and (not (= y 32)) (=> (= x 0) (= y 32)) (= x 0))",
        "(not (=> (= x 0) (= x 0)))",
        "(and (= y 32) (not (=> (= x 0) (= y 32))))",
        "(and (not (= x 0)) (not (=> (= x 0) (= y 32))))",
        "(and (not (= x 0)) (=> (not (= x 0)) (= y 32)) (not (= y 32)))",
        "(or (not (=> (= x 0) (= x 0))) (and (= x 0) (not (= x 0))))",
    ] {
        let (executor, proof, result) = candidate(root);
        assert!(result.is_some(), "no refutation: {root}");
        assert!(Executor::proof_derives_empty_clause(&proof), "{root}");
        assert!(
            executor
                .check_proof_strict_with_datatypes(&proof)
                .is_ok_and(|quality| quality.is_complete()),
            "strict checker refused {root}"
        );
    }
}

#[test]
fn implication_branches_do_not_refute_satisfiable_controls() {
    for root in [
        "(and (not (= x 0)) (=> (= x 0) (= y 32)) (not (= y 32)))",
        "(and (= x 0) (=> (= x 0) (= y 32)) (= y 32))",
        "(not (=> (= x 0) (= y 32)))",
        "(or (not (=> (= x 0) (= x 0))) (= y 32))",
        "(and (not (= x 0)) (=> (not (= x 0)) (= y 32)) (= y 32))",
    ] {
        let (executor, proof, result) = candidate(root);
        assert!(result.is_none(), "false refutation: {root}");
        assert!(
            !Executor::proof_derives_empty_clause(&proof)
                || !executor
                    .check_proof_strict_with_datatypes(&proof)
                    .is_ok_and(|quality| quality.is_complete()),
            "strict checker accepted a false refutation: {root}"
        );
    }
}
