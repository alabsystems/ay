// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Adversarial differential audit for ground floating-point evaluation.

#[path = "fp_ground_adversarial_audit_tests/generator.rs"]
mod generator;
#[path = "fp_ground_adversarial_audit_tests/oracle.rs"]
mod oracle;

use generator::AcceptedClause;
use oracle::{ClauseVerdict, Oracle};

const ROUNDS_PER_LANE: u32 = 300;

fn audit(seed: u64, with_vars: bool, label: &str) {
    let Some(oracle) = Oracle::resolve() else {
        assert!(
            !oracle::differential_required(),
            "[{label}] Z3 is unavailable, but Z3_DIFFERENTIAL_REQUIRED is truthy; \
             set Z3_PATH to an existing Z3 executable or add z3 to PATH"
        );
        eprintln!(
            "[{label}] Z3 unavailable; skipping FP differential audit \
             (set Z3_DIFFERENTIAL_REQUIRED=1 to require it)"
        );
        return;
    };

    let clauses = generator::accepted_clauses(seed, ROUNDS_PER_LANE, with_vars);
    assert!(
        !clauses.is_empty(),
        "[{label}] generator produced no accepted clause -- vacuous audit"
    );

    let verdicts = oracle.check_clauses(&clauses).unwrap_or_else(|error| {
        panic!(
            "[{label}] Z3 oracle {} failed: {error}",
            oracle.path().display()
        )
    });
    let accepted = clauses.len();
    let oracle_checked = verdicts.len();
    assert_eq!(
        oracle_checked, accepted,
        "[{label}] oracle verdict count did not match accepted clauses"
    );

    let false_accepts = collect_false_accepts(label, &clauses, &verdicts);
    eprintln!(
        "[{label}] accepted={accepted} oracle-checked={oracle_checked} false_accepts={}",
        false_accepts.len()
    );
    assert!(
        false_accepts.is_empty(),
        "{}",
        false_accepts.join("\n----\n")
    );
}

fn collect_false_accepts(
    label: &str,
    clauses: &[AcceptedClause],
    verdicts: &[ClauseVerdict],
) -> Vec<String> {
    clauses
        .iter()
        .zip(verdicts)
        .filter(|(_, verdict)| **verdict == ClauseVerdict::Invalid)
        .map(|(clause, _)| {
            format!(
                "FALSE ACCEPT [{label}]: checker accepted a clause Z3 says is \
                 falsifiable\n  decls: {:?}\n  clause: {:?}",
                clause.declarations, clause.literals
            )
        })
        .collect()
}

#[test]
fn ground_fp_clauses_accepted_by_the_checker_are_valid_per_z3() {
    audit(0x1234_5678_9ABC_DEF0, false, "ground");
}

#[test]
fn near_ground_fp_clauses_accepted_by_the_checker_are_valid_per_z3() {
    audit(0x0FED_CBA9_8765_4321, true, "bindings+residual");
}
