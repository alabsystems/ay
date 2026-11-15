// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
#![cfg(test)]

use super::*;

#[test]
fn distinct_bridge_replays_identical_complemented_and_preexisting_terms() {
    for case in 0..4 {
        cases::with_distinct(case, |native| native.require_valid());
    }
}

#[test]
fn native_checker_rejects_corrupt_distinct_premise_pivot_and_conclusion() {
    cases::with_distinct(0, |native| {
        native.require_valid();
        let index = native.bridge_steps[0].0 as usize;
        let mut premise = native.proof.clone();
        let ProofStep::Resolution { clause1, .. } = &mut premise.steps[index] else {
            panic!("bridge resolution");
        };
        *clause1 = native.assumptions[0];
        native.require_rejected(&premise);
        let mut pivot = native.proof.clone();
        let ProofStep::Resolution { pivot: wrong, .. } = &mut pivot.steps[index] else {
            panic!("bridge resolution");
        };
        *wrong = native.cnf.roots()[0];
        native.require_rejected(&pivot);
        let mut conclusion = native.proof.clone();
        let ProofStep::Resolution { clause, .. } = &mut conclusion.steps[index] else {
            panic!("bridge resolution");
        };
        let negated = native
            .cnf
            .source_literal_term(SourceLit {
                term: native.cnf.bridges()[0].source,
                positive: false,
            })
            .unwrap();
        assert_ne!(clause[0], negated);
        clause[0] = negated;
        native.require_rejected(&conclusion);
    });
}

#[test]
fn native_checker_refuses_theorem_assumption_and_missing_terminal_refutation() {
    cases::with_distinct(0, |native| {
        native.require_valid();
        let mut forged = native.proof.clone();
        let theorem = native.cnf.bridges()[0].equivalence;
        assert!(!native.cnf.roots().contains(&theorem));
        forged.steps.insert(0, ProofStep::Assume(theorem));
        // Keep references correctly shifted: rejection must concern the
        // unauthorized theorem assumption, not an accidental broken graph.
        for step in forged.steps.iter_mut().skip(1) {
            match step {
                ProofStep::Resolution {
                    clause1, clause2, ..
                } => {
                    clause1.0 += 1;
                    clause2.0 += 1;
                }
                ProofStep::Step { premises, .. } => {
                    for premise in premises {
                        premise.0 += 1;
                    }
                }
                _ => {}
            }
        }
        native.require_rejected(&forged);
        let mut incomplete = native.proof.clone();
        incomplete.steps.pop();
        native.require_rejected(&incomplete);
    });
}
