// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! #C6 differential test: the view-served `get_integer_bounds_for_term`
//! must produce EXACTLY the bounds of the historical O(asserted) trail
//! scan, over randomized assertion sets with push/pop
//! (the development design notes §C6).

use super::*;
use ay_core::term::{Symbol, TermData};
use ay_core::Sort;
use ay_core::TheorySolver;
use num_bigint::BigInt;
use num_traits::One;

/// Verbatim copy of the pre-#C6 `get_integer_bounds_for_term` trail scan
/// (bounds.rs at commit a3128a8). Kept as the reference oracle.
fn reference_bounds(solver: &LiaSolver<'_>, tid: TermId) -> (Option<BigInt>, Option<BigInt>) {
    let mut lower: Option<BigInt> = None;
    let mut upper: Option<BigInt> = None;

    for &(literal, value) in &solver.asserted {
        if !value {
            continue;
        }

        let TermData::App(Symbol::Named(name), args) = solver.terms.get(literal) else {
            continue;
        };

        if args.len() != 2 {
            continue;
        }

        // Pattern: tid OP constant or constant OP tid
        let (constant, is_target_on_left) = if args[0] == tid {
            (solver.extract_constant(args[1]), true)
        } else if args[1] == tid {
            (solver.extract_constant(args[0]), false)
        } else {
            continue;
        };

        let Some(c) = constant else {
            continue;
        };

        match (name.as_str(), is_target_on_left) {
            (">=", true) => {
                lower = Some(lower.map_or(c.clone(), |l| l.max(c.clone())));
            }
            (">=", false) => {
                upper = Some(upper.map_or(c.clone(), |u| u.min(c.clone())));
            }
            (">", true) => {
                let bound = &c + BigInt::one();
                lower = Some(lower.map_or(bound.clone(), |l| l.max(bound)));
            }
            (">", false) => {
                let bound = &c - BigInt::one();
                upper = Some(upper.map_or(bound.clone(), |u| u.min(bound)));
            }
            ("<=", true) => {
                upper = Some(upper.map_or(c.clone(), |u| u.min(c.clone())));
            }
            ("<=", false) => {
                lower = Some(lower.map_or(c.clone(), |l| l.max(c.clone())));
            }
            ("<", true) => {
                let bound = &c - BigInt::one();
                upper = Some(upper.map_or(bound.clone(), |u| u.min(bound)));
            }
            ("<", false) => {
                let bound = &c + BigInt::one();
                lower = Some(lower.map_or(bound.clone(), |l| l.max(bound)));
            }
            _ => {}
        }
    }

    (lower, upper)
}

/// Deterministic splitmix-style RNG (no dev-dependency needed).
struct Lcg(u64);

impl Lcg {
    fn next(&mut self, modulus: usize) -> usize {
        self.0 = self
            .0
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        ((self.0 >> 33) as usize) % modulus.max(1)
    }
}

struct Fixture {
    terms: TermStore,
    /// Atoms to assert (drawn at random with random polarity).
    atom_pool: Vec<TermId>,
    /// Terms to compare bounds for after every step.
    query_terms: Vec<TermId>,
}

fn build_fixture() -> Fixture {
    let mut terms = TermStore::new();

    let vars: Vec<TermId> = (0..8)
        .map(|i| terms.mk_var(format!("v{i}"), Sort::Int))
        .collect();
    let consts: Vec<TermId> = [-7i64, -3, 0, 2, 5, 11]
        .iter()
        .map(|&c| terms.mk_int(BigInt::from(c)))
        .collect();

    // Negation-app constants: (- 4) and (- (- 9)) exercise the recursive
    // constant extraction shared by both implementations.
    let four = terms.mk_int(BigInt::from(4));
    let neg4 = terms.mk_app(Symbol::Named("-".to_string()), [four], Sort::Int);
    let nine = terms.mk_int(BigInt::from(9));
    let neg9 = terms.mk_app(Symbol::Named("-".to_string()), [nine], Sort::Int);
    let negneg9 = terms.mk_app(Symbol::Named("-".to_string()), [neg9], Sort::Int);
    let weird_consts = [neg4, negneg9];

    // Linear expressions: opaque to BOTH implementations (no bound entries),
    // present to make sure they stay ignored.
    let sum01 = {
        let c = terms.mk_int(BigInt::from(3));
        terms.mk_add(vec![vars[0], vars[1], c])
    };
    let two_v2 = {
        let two = terms.mk_int(BigInt::from(2));
        terms.mk_mul(vec![two, vars[2]])
    };

    let mut atom_pool: Vec<TermId> = Vec::new();
    let ops: [fn(&mut TermStore, TermId, TermId) -> TermId; 4] = [
        TermStore::mk_ge,
        TermStore::mk_le,
        TermStore::mk_gt,
        TermStore::mk_lt,
    ];
    for (i, op) in ops.iter().enumerate() {
        for (j, &v) in vars.iter().enumerate() {
            // var OP const and const OP var, rotating constants.
            let c = consts[(i + j) % consts.len()];
            atom_pool.push(op(&mut terms, v, c));
            let c2 = consts[(i + j + 2) % consts.len()];
            atom_pool.push(op(&mut terms, c2, v));
            // var OP negation-app constant.
            let w = weird_consts[(i + j) % weird_consts.len()];
            atom_pool.push(op(&mut terms, v, w));
        }
        // var OP var (no constant side — ignored by both).
        atom_pool.push(op(&mut terms, vars[i], vars[(i + 3) % vars.len()]));
        // Same-term degenerate: v OP v.
        atom_pool.push(op(&mut terms, vars[i], vars[i]));
        // const OP const with distinct terms (both-sides-constant case).
        atom_pool.push(op(&mut terms, consts[i], consts[(i + 1) % consts.len()]));
        // const OP const with the SAME term.
        atom_pool.push(op(&mut terms, consts[i], consts[i]));
        // Negation-app constant on both sides.
        atom_pool.push(op(&mut terms, neg4, negneg9));
        // Linear-expression sides (ignored by both).
        atom_pool.push(op(&mut terms, sum01, consts[i]));
        atom_pool.push(op(&mut terms, two_v2, consts[(i + 4) % consts.len()]));
    }
    // Equalities: classified as equalities, never as bounds, by both.
    for (j, &v) in vars.iter().enumerate() {
        let eq = terms.mk_eq(v, consts[j % consts.len()]);
        atom_pool.push(eq);
    }

    let fresh_unused = terms.mk_var("unused".to_string(), Sort::Int);
    let mut query_terms = vars;
    query_terms.extend_from_slice(&consts);
    query_terms.extend_from_slice(&weird_consts);
    query_terms.push(sum01);
    query_terms.push(two_v2);
    query_terms.push(fresh_unused);

    Fixture {
        terms,
        atom_pool,
        query_terms,
    }
}

fn compare_all(solver: &LiaSolver<'_>, query_terms: &[TermId], step: usize, seed: u64) {
    for &t in query_terms {
        let expected = reference_bounds(solver, t);
        let actual = solver.get_integer_bounds_for_term(Some(t));
        assert_eq!(
            expected,
            actual,
            "view-served bounds diverge from reference scan for term {} \
             (seed {seed}, step {step}, trail len {})",
            t.0,
            solver.asserted.len()
        );
    }
    // None-term contract preserved.
    assert_eq!(solver.get_integer_bounds_for_term(None), (None, None));
}

fn run_randomized(seed: u64) {
    let fixture = build_fixture();
    let mut solver = LiaSolver::new(&fixture.terms);
    let mut rng = Lcg(seed);
    let mut depth = 0usize;

    for step in 0..240 {
        match rng.next(10) {
            7 => {
                solver.push();
                depth += 1;
            }
            8 if depth > 0 => {
                solver.pop();
                depth -= 1;
            }
            _ => {
                let atom = fixture.atom_pool[rng.next(fixture.atom_pool.len())];
                let polarity = rng.next(4) != 0; // bias towards positive
                solver.assert_literal(atom, polarity);
            }
        }
        compare_all(&solver, &fixture.query_terms, step, seed);
    }

    // Unwind all remaining scopes, re-checking at each level.
    while depth > 0 {
        solver.pop();
        depth -= 1;
        compare_all(&solver, &fixture.query_terms, usize::MAX - depth, seed);
    }
}

#[test]
fn view_served_bounds_match_reference_scan_randomized() {
    for seed in [1u64, 7, 42, 1234, 0xC6C6_C6C6] {
        run_randomized(seed);
    }
}
