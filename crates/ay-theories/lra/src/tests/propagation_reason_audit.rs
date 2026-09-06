// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Randomized audit: every DELIVERED theory propagation must carry a reason
//! that semantically entails it.
//!
//! `implied_propagation_entailment.rs` checks the five diagnosis probes
//! (tA..tE) by hand. This module checks the same property over random
//! tableaus driven through random assert/push/pop/check sequences, so the
//! explanation machinery is exercised on the shapes that actually occur in
//! search: stale slot bounds after pivots, pop-restored antecedents, chains
//! through equalities, and the strategy fallbacks.
//!
//! For every propagation the solver hands out, the reason is materialized
//! exactly as the DPLL layer would at conflict analysis
//! (`explain_propagation` for lazy ones, `prop.reason` for eager ones) and
//! then checked INDEPENDENTLY of the explanation machinery: a fresh
//! `LraSolver` that asserts the reason literals plus the NEGATED propagated
//! literal must be infeasible. That is exactly the soundness obligation the
//! SAT core relies on — the reason clause `(!r1 | ... | !rn | lit)` is valid
//! iff `reason /\ !lit` is unsatisfiable.
//!
//! The audit also requires that reasons are non-empty, non-circular, and
//! made only of currently-asserted literals; a false-premise or circular
//! reason corrupts conflict analysis even when it is "valid".

use super::*;
use ay_core::TheoryPropagation;

/// Deterministic xorshift PRNG (no dev-dependency needed).
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.0 = x;
        x
    }
    fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }
}

/// Independent semantic check: `reason /\ !lit` must be infeasible.
fn assert_entailed(terms: &TermStore, reason: &[TheoryLit], lit: TheoryLit, seed: u64) {
    let mut probe = LraSolver::new(terms);
    for r in reason {
        probe.assert_literal(r.term, r.value);
    }
    probe.assert_literal(lit.term, !lit.value);
    let verdict = probe.check();
    assert!(
        matches!(
            verdict,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ),
        "seed {seed}: reason {reason:?} does not entail {lit:?} (probe verdict {verdict:?})"
    );
}

/// Materialize and audit the reason of one delivered propagation.
fn audit_propagation(
    terms: &TermStore,
    solver: &mut LraSolver,
    prop: &TheoryPropagation,
    seed: u64,
) {
    let reason = if prop.is_lazy() {
        let reason_data = prop
            .reason_data
            .unwrap_or_else(|| panic!("seed {seed}: lazy propagation without reason_data"));
        solver
            .explain_propagation(prop.literal.term, reason_data)
            .unwrap_or_else(|| {
                panic!(
                    "seed {seed}: delivered lazy propagation {:?} has no materializable reason",
                    prop.literal
                )
            })
    } else {
        prop.reason.clone()
    };
    assert!(
        !reason.is_empty(),
        "seed {seed}: empty reason for {:?}",
        prop.literal
    );
    assert!(
        !reason.iter().any(|r| r.term == prop.literal.term),
        "seed {seed}: circular reason {reason:?} for {:?}",
        prop.literal
    );
    assert!(
        reason
            .iter()
            .all(|r| solver.asserted.get(&r.term) == Some(&r.value)),
        "seed {seed}: reason {reason:?} for {:?} cites a non-asserted literal",
        prop.literal
    );
    assert_entailed(terms, &reason, prop.literal, seed);
}

/// One random trial; returns how many propagations it audited.
fn run_trial(seed: u64) -> usize {
    let mut rng = Rng(seed | 1);
    let mut terms = TermStore::new();
    let n_vars = 6;
    let vars: Vec<TermId> = (0..n_vars)
        .map(|i| terms.mk_var(format!("x{i}"), Sort::Real))
        .collect();
    // Unit-coefficient expressions: singles, pair sums/differences, one
    // triple. Compound expressions are what key propagations on a SLACK
    // variable, the shape the freshness gate used to discard wholesale.
    let mut exprs: Vec<TermId> = vars.clone();
    for _ in 0..7 {
        let a = rng.below(n_vars);
        let mut b = rng.below(n_vars);
        while b == a {
            b = rng.below(n_vars);
        }
        let e = if rng.below(2) == 0 {
            terms.mk_add(vec![vars[a], vars[b]])
        } else {
            terms.mk_sub(vec![vars[a], vars[b]])
        };
        exprs.push(e);
    }
    exprs.push(terms.mk_add(vec![vars[0], vars[1], vars[2]]));
    // Bound atoms with small integer thresholds, both directions, plus a
    // strict pair so delta-rational bounds are exercised.
    let mut atoms: Vec<TermId> = Vec::new();
    for &e in &exprs {
        let c1 = terms.mk_rational(BigRational::from(BigInt::from(rng.below(7) as i64 - 3)));
        let c2 = terms.mk_rational(BigRational::from(BigInt::from(rng.below(7) as i64 - 3)));
        atoms.push(terms.mk_le(e, c1));
        atoms.push(terms.mk_ge(e, c2));
    }

    let mut solver = LraSolver::new(&terms);
    for &atom in &atoms {
        solver.register_atom(atom);
    }
    let mut depth = 0usize;
    let mut audited = 0usize;
    for _step in 0..60 {
        match rng.below(10) {
            0..=3 => {
                let atom = atoms[rng.below(atoms.len())];
                if solver.asserted.contains_key(&atom) {
                    continue;
                }
                solver.assert_literal(atom, rng.below(4) != 0);
            }
            4..=5 => {
                solver.push();
                depth += 1;
            }
            6 if depth > 0 => {
                solver.pop();
                depth -= 1;
            }
            _ => {
                let result = solver.check();
                let propagations = solver.propagate();
                // Propagations are only meaningful on a consistent state;
                // after Unsat the DPLL layer backtracks instead of taking
                // them.
                let unsat = matches!(
                    result,
                    TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
                );
                if !unsat {
                    for prop in &propagations {
                        audit_propagation(&terms, &mut solver, prop, seed);
                        audited += 1;
                    }
                }
                if unsat && depth > 0 {
                    solver.pop();
                    depth -= 1;
                }
            }
        }
    }
    audited
}

/// Every delivered propagation, over 60 random tableaus, carries a reason
/// that entails it under an independent re-solve.
#[test]
fn delivered_propagation_reasons_entail_their_literal() {
    let mut audited = 0usize;
    for seed in 1..=60u64 {
        audited += run_trial(seed.wrapping_mul(0x9E37_79B9_7F4A_7C15));
    }
    // Guard against the audit silently checking nothing (e.g. a future
    // change that stops delivering implied-bound propagations at all).
    assert!(
        audited >= 100,
        "audit checked only {audited} propagations; the corpus must exercise the explainer"
    );
}
