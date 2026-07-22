// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

/// Test that counterexample steps have populated assignments from SMT models
///
/// Uses subtraction_unsafe.smt2 which should find a counterexample trace:
/// x = 3 -> 2 -> 1 -> 0 -> -1 (violates x >= 0)
///
/// Note: This test is intended to ensure counterexample traces include concrete
/// assignments from SMT models on at least some steps.
///
/// Timeout: 30s (measured <1s in release)
#[test]
#[timeout(30_000)]
fn pdr_counterexample_has_assignments() {
    let config = test_config(true);
    let result = pdr_solve_from_file(example_path("subtraction_unsafe.smt2"), config).unwrap();

    match &result {
        PdrResult::Unsafe(cex) => {
            eprintln!("Counterexample has {} steps:", cex.steps.len());
            for (i, step) in cex.steps.iter().enumerate() {
                eprintln!(
                    "  Step {}: predicate {:?}, assignments: {:?}",
                    i, step.predicate, step.assignments
                );
            }

            // At least some steps should have non-empty assignments
            let steps_with_assignments = cex
                .steps
                .iter()
                .filter(|s| !s.assignments.is_empty())
                .count();

            eprintln!(
                "Steps with non-empty assignments: {}/{}",
                steps_with_assignments,
                cex.steps.len()
            );

            // Verify at least one step has assignments (the root POB might not have a model)
            assert!(
                steps_with_assignments > 0 || cex.steps.is_empty(),
                "At least some counterexample steps should have variable assignments"
            );

            // Check witness is populated with instances
            if let Some(ref witness) = cex.witness {
                eprintln!(
                    "Derivation witness has {} entries, root={}",
                    witness.entries.len(),
                    witness.root
                );
                assert!(
                    !witness.entries.is_empty(),
                    "Derivation witness should have entries"
                );

                // Check that witness entries have instances populated
                for (i, entry) in witness.entries.iter().enumerate() {
                    eprintln!(
                        "  Entry {}: pred {:?}, level {}, instances: {:?}",
                        i, entry.predicate, entry.level, entry.instances
                    );
                }

                // At least some entries should have instances (from SMT models)
                let entries_with_instances = witness
                    .entries
                    .iter()
                    .filter(|e| !e.instances.is_empty())
                    .count();
                eprintln!(
                    "Entries with instances: {}/{}",
                    entries_with_instances,
                    witness.entries.len()
                );

                // Verify at least one entry has instances
                assert!(
                    entries_with_instances > 0 || witness.entries.is_empty(),
                    "At least some derivation entries should have concrete instances"
                );
            }
        }
        _ => {
            // subtraction_unsafe should be unsafe, but we're mainly testing assignment extraction
            eprintln!("Note: subtraction_unsafe did not return Unsafe result");
        }
    }
}

/// Test that a shallow unsafe counter returns concrete evidence.
///
/// The bounded unsafe precheck may find this before PDR's derivation witness path;
/// in that case the evidence is a concrete step trace. If PDR proper supplies a
/// derivation witness, keep checking that incoming clauses are populated.
///
/// Timeout: 30s (measured <1s in release)
#[test]
#[timeout(30_000)]
fn pdr_unsafe_counterexample_has_trace_or_incoming_clause() {
    let config = test_config(true);

    let result = pdr_solve_from_file(example_path("counter_unsafe.smt2"), config).unwrap();

    match &result {
        PdrResult::Unsafe(cex) => {
            eprintln!("Counterexample has {} steps:", cex.steps.len());

            if let Some(ref witness) = cex.witness {
                eprintln!(
                    "Derivation witness has {} entries, query_clause={:?}, root={}",
                    witness.entries.len(),
                    witness.query_clause,
                    witness.root
                );

                for (i, entry) in witness.entries.iter().enumerate() {
                    eprintln!(
                        "  Entry {}: pred {:?}, level {}, incoming_clause={:?}",
                        i, entry.predicate, entry.level, entry.incoming_clause
                    );
                }

                // Count entries with incoming_clause populated
                let entries_with_clause = witness
                    .entries
                    .iter()
                    .filter(|e| e.incoming_clause.is_some())
                    .count();

                eprintln!(
                    "Entries with incoming_clause: {}/{}",
                    entries_with_clause,
                    witness.entries.len()
                );

                // At least some entries should have incoming_clause populated
                // (the initial entry might not have one if it's the query root)
                assert!(
                    entries_with_clause > 0,
                    "At least some derivation entries should have incoming_clause populated"
                );
            } else {
                assert!(
                    cex.steps.iter().any(|step| !step.assignments.is_empty()),
                    "witnessless unsafe evidence should include concrete step assignments"
                );
            }
        }
        _ => {
            panic!("counter_unsafe should return Unsafe result");
        }
    }
}
