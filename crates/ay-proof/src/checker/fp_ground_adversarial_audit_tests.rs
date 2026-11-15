// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Adversarial differential audit for ground floating-point evaluation.

#[path = "fp_ground_adversarial_audit_tests/generator.rs"]
mod generator;
#[path = "fp_ground_adversarial_audit_tests/integer_casts.rs"]
mod integer_casts;
#[path = "fp_ground_adversarial_audit_tests/oracle.rs"]
mod oracle;

use generator::AcceptedClause;
use oracle::{ClauseVerdict, Oracle};

const ROUNDS_PER_LANE: u32 = 300;

fn audit(seed: u64, with_vars: bool, label: &str) {
    // No usable z3: `Oracle::resolve` announced the skip (or failed the test
    // under Z3_DIFFERENTIAL_REQUIRED or a wrong Z3_PATH).
    let Some(oracle) = Oracle::resolve(label) else {
        return;
    };

    let clauses = generator::accepted_clauses(seed, ROUNDS_PER_LANE, with_vars);
    assert!(
        !clauses.is_empty(),
        "[{label}] generator produced no accepted clause -- vacuous audit"
    );

    let verdicts = oracle.check_clauses(&clauses).unwrap_or_else(|error| {
        panic!("[{label}] Z3 oracle {} failed: {error}", oracle.identity())
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

#[test]
fn integer_cast_clauses_accepted_by_the_checker_are_valid_per_z3() {
    let label = "integer-casts";
    let Some(oracle) = Oracle::resolve(label) else {
        return;
    };
    let clauses = integer_casts::accepted_clauses();
    assert!(clauses.len() > 1000, "nonvacuous conversion coverage");
    let verdicts = oracle
        .check_clauses(&clauses)
        .expect("integer cast oracle batch");
    assert_eq!(verdicts.len(), clauses.len());
    let false_accepts = collect_false_accepts(label, &clauses, &verdicts);
    eprintln!(
        "[{label}] accepted={} oracle-checked={} false_accepts={}",
        clauses.len(),
        verdicts.len(),
        false_accepts.len()
    );
    assert!(
        false_accepts.is_empty(),
        "{}",
        false_accepts.join("\n----\n")
    );
}
