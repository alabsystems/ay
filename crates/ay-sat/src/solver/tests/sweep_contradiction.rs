// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Sweep equivalences that are each proved in their own COI environment can
//! be jointly contradictory (a ≡ b through one chain, a ≡ ¬b through
//! another): the formula is UNSAT. Before 2026-09-17 the union-find merged a
//! with ¬a, the rewrite mapped both polarities of the class to one literal,
//! and the satisfiable residue's model failed the original-ledger check, so
//! the run ended `unknown` (found by the audit on the generator below).

use super::*;
use crate::ProofOutput;

/// Two guarded equivalence chains of `links` links from `a` to `b` and from
/// `a` to `¬b`, plus `pad` random-free padding clauses over fresh variables
/// so preprocessing's sweep is the first pass that sees the chains (the
/// auditor's `gen_contra3.py`; the pad keeps the clause count above the
/// preprocessing backbone's 10,000-clause gate and the 4-literal clauses
/// defeat the uniform-k detection).
///
/// `links` is load-bearing. A sweep environment holds the gadgets within two
/// links of its seed (`COI_DEPTH_LIMIT` = 4), and the shipped posture cuts a
/// sweep at a 200 ms wall cap checked every 16 variables
/// (`sweep_with_kitten`), so the contradiction must close from the
/// environments of `a` and `b` alone: with 4 links `a`'s environment proves
/// `a ≡ c1 ≡ c2` on both chains and `b`'s proves `b ≡ c3 ≡ c2` and
/// `¬b ≡ c3' ≡ c2'`. Fewer than 3 links puts the whole cycle inside one
/// environment, which kitten refutes outright (`unsat_environments`, a
/// different path); 6 links needs environments seeded past variable 32,
/// which a debug build under load does not reach before the cap.
fn contradictory_chains(links: usize, pad: usize) -> String {
    struct Gen {
        nv: i32,
        clauses: Vec<Vec<i32>>,
    }
    impl Gen {
        fn newv(&mut self) -> i32 {
            self.nv += 1;
            self.nv
        }
        fn imp(&mut self, x: i32, y: i32) {
            let (g, h) = (self.newv(), self.newv());
            self.clauses.push(vec![-x, g, h]);
            self.clauses.push(vec![y, g, -h]);
            self.clauses.push(vec![y, -g, h]);
            self.clauses.push(vec![-x, -g, -h]);
        }
        fn chain(&mut self, links: usize, start: i32, end: i32) {
            let mut prev = start;
            for _ in 0..links - 1 {
                let c = self.newv();
                self.imp(prev, c);
                self.imp(c, prev);
                prev = c;
            }
            self.imp(prev, end);
            self.imp(end, prev);
        }
    }
    let mut builder = Gen {
        nv: 2,
        clauses: Vec::new(),
    };
    builder.chain(links, 1, 2);
    builder.chain(links, 1, -2);
    for i in 0..pad {
        let (p, q, r) = (builder.newv(), builder.newv(), builder.newv());
        if i % 7 == 0 {
            let s = builder.newv();
            builder.clauses.push(vec![p, q, r, s]);
        } else {
            builder.clauses.push(vec![p, q, r]);
        }
    }
    let (nv, clauses) = (builder.nv, builder.clauses);
    let mut text = format!("p cnf {nv} {}\n", clauses.len());
    for clause in &clauses {
        for v in clause {
            text.push_str(&format!("{v} "));
        }
        text.push_str("0\n");
    }
    text
}

#[test]
fn jointly_contradictory_sweep_equivalences_refute_the_formula_with_a_checked_proof() {
    let text = contradictory_chains(4, 10_100);
    let formula = crate::parse_dimacs(&text).expect("parse");
    let clauses: Vec<Vec<i32>> = text
        .lines()
        .skip(1)
        .map(|line| {
            line.split_whitespace()
                .map(|t| t.parse::<i32>().expect("literal"))
                .take_while(|&v| v != 0)
                .collect()
        })
        .collect();
    // The DIMACS default variant under the DRAT posture, as the CLI builds it
    // (`into_solver_with_variant_routed_source` with a proof writer).
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
    let stats = solver.inproc.sweeper.stats().clone();
    assert!(
        matches!(result, SatResult::Unsat(_)),
        "the chains contradict each other: expected UNSAT, got {result:?} \
         (sweep contradictory classes {})",
        stats.unsat_contradictory_equivalences
    );
    assert_eq!(
        stats.unsat_environments, 0,
        "no single environment may hold the whole cycle: that is kitten's own \
         refutation, not the contradictory-classes path this test guards"
    );
    assert!(
        stats.unsat_contradictory_equivalences >= 1,
        "the refutation must come from the contradictory sweep classes, not from search \
         (environments swept: {}, equivalences: {})",
        stats.kitten_environments,
        stats.kitten_equivalences
    );
    let writer = solver.take_proof_writer().expect("DRAT writer");
    let proof = writer.into_vec().expect("flush");
    let parsed = ay_drat_check::cnf_parser::parse_cnf(text.as_bytes()).expect("cnf");
    let steps = ay_drat_check::drat_parser::parse_drat(&proof).expect("drat");
    let mut checker = ay_drat_check::checker::DratChecker::new(parsed.num_vars, true);
    checker
        .verify(&parsed.clauses, &steps)
        .unwrap_or_else(|e| panic!("the DRAT checker rejects the proof: {e}"));
    assert_eq!(
        clauses.len(),
        2 * 4 * 2 * 4 + 10_100,
        "sanity: clause count (128 chain clauses keep the total above the \
         preprocessing backbone's 10,000-clause gate)"
    );
}
