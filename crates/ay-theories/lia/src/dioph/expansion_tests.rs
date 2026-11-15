// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! D3 (2026-09-23 hunt): substitution expansion must be exact or absent.
//!
//! The old expansion walked the substitution DAG as a tree and stopped after
//! 100 worklist pops, returning the PARTIAL sum as the expansion. These tests
//! pin the replacement: every expansion, every cached substitution and every
//! modular claim is an exact consequence of the equations, and a budget that
//! runs out yields no claim at all.

use super::expansion::{ExpansionPolicy, LinearForm, SubstitutionExpander};
use super::*;
// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::DetHashMap as HashMap;
use num_bigint::BigInt;
use num_integer::Integer;
use num_traits::{One, Zero};

fn big(s: &str) -> BigInt {
    s.parse().expect("test literal parses")
}

fn value_of(form: &LinearForm, point: &HashMap<usize, BigInt>) -> BigInt {
    let mut v = form.constant.clone();
    for (var, coeff) in &form.coeffs {
        v += coeff * &point[var];
    }
    v
}

/// `linear/wit/pbig_21_00085/min.smt2`, the D3 hunt witness (z3: sat, AY
/// base: unsat). Its equality system, with x0..x3 as variables 0..3, and the
/// model z3 5.1.0 prints for it.
fn pbig_21_00085_system() -> (DiophSolver, [BigInt; 4]) {
    let mut solver = DiophSolver::new(4);
    solver.add_equation_from(
        [
            (3, big("-4611686018427387903")),
            (1, big("-18446744073709551615")),
            (0, big("-9007199254740991")),
            (2, big("-4294967295")),
        ],
        big("5905686471349737029546786948242595643392"),
    );
    solver.add_equation_from(
        [
            (1, big("9007199254740993")),
            (3, big("-4611686018427387903")),
        ],
        big("461168601842719447477662793894202441730"),
    );
    let model = [
        big("20920221290197706900972355784227684355"),
        big("-10209966466665546402323682051478709"),
        big("-1267650600228229401496703205381"),
        big("-19941340755306147535296091138889"),
    ];
    (solver, model)
}

#[test]
fn d3_witness_model_satisfies_the_system() {
    // Guard for the test data itself: the model must satisfy both equations.
    let (solver, model) = pbig_21_00085_system();
    for eq in &solver.equations {
        let mut lhs = BigInt::zero();
        for (&var, coeff) in &eq.coeffs {
            lhs += coeff * &model[var];
        }
        assert_eq!(lhs, eq.constant, "z3's model must satisfy every equation");
    }
}

#[test]
fn d3_witness_modular_claims_hold_at_a_model() {
    let (mut solver, model) = pbig_21_00085_system();
    let result = solver.solve();
    assert!(
        !matches!(result, DiophResult::Infeasible { .. }),
        "the system has an integer solution"
    );

    // Every modulus the solver claims must hold at an actual solution. The
    // capped expansion claimed one from a partial sum and turned this
    // satisfiable file into `unsat`.
    for (var, gcd, residue) in solver.get_modular_constraints(4) {
        assert_eq!(
            model[var].mod_floor(&gcd),
            residue,
            "false modular claim: x{var} ≡ {residue} (mod {gcd}), but x{var} = {} in a model",
            model[var]
        );
    }

    // Every cached substitution must hold at the solution too.
    for (var, coeffs, constant) in solver.get_expanded_substitutions(4, true) {
        let mut rhs = constant.clone();
        for (dep, coeff) in &coeffs {
            rhs += coeff * &model[*dep];
        }
        assert_eq!(
            rhs, model[var],
            "expanded substitution for x{var} is not an identity of the system"
        );
    }
}

#[test]
fn d3_witness_expansions_are_exact_not_abandoned() {
    // Capability: the exact expansion of this system is cheap, so the
    // expander must produce it rather than decline. Each expansion over free
    // parameters must also agree with the substitution it expands at a point
    // built bottom-up from arbitrary leaf values.
    let (mut solver, _model) = pbig_21_00085_system();
    let _ = solver.solve();
    let mut expander =
        SubstitutionExpander::new(&solver.substitutions, ExpansionPolicy::FreeParams);
    let originals: Vec<usize> = solver
        .substitutions
        .keys()
        .copied()
        .filter(|&v| v < 4)
        .collect();
    assert!(
        !originals.is_empty(),
        "the witness eliminates original variables"
    );
    for var in originals {
        assert!(
            expander.expand(var).is_some(),
            "x{var}: exact expansion must be available within the default budget"
        );
    }
}

/// Original vars 0 and 1; fresh chain f_i = 2 + i for i in 0..=n; free
/// parameter `2 + n + 1`. `x0 = scale * f_0`, `f_i = f_{i+1} + f_{i+2}`,
/// `f_{n-1} = x1`, `f_n = p`. Walking it as a tree needs ~Fib(n) pops.
fn fibonacci_dag(n: usize, scale: i64) -> DiophSolver {
    let mut solver = DiophSolver::new(2);
    let f = |i: usize| 2 + i;
    let p = 2 + n + 1;
    let mut subs: HashMap<usize, (HashMap<usize, BigInt>, BigInt)> = HashMap::default();
    subs.insert(
        0,
        (
            [(f(0), BigInt::from(scale))].into_iter().collect(),
            BigInt::zero(),
        ),
    );
    for i in 0..n - 1 {
        subs.insert(
            f(i),
            (
                [(f(i + 1), BigInt::one()), (f(i + 2), BigInt::one())]
                    .into_iter()
                    .collect(),
                BigInt::from(1),
            ),
        );
    }
    subs.insert(
        f(n - 1),
        ([(1, BigInt::one())].into_iter().collect(), BigInt::zero()),
    );
    subs.insert(
        f(n),
        ([(p, BigInt::one())].into_iter().collect(), BigInt::zero()),
    );
    solver.substitutions = subs;
    solver
}

fn fib(k: usize) -> BigInt {
    let (mut a, mut b) = (BigInt::zero(), BigInt::one());
    for _ in 0..k {
        let next = &a + &b;
        a = b;
        b = next;
    }
    a
}

#[test]
fn d3_deep_dag_expands_exactly() {
    // n = 60: the tree walk would need ~Fib(60) ≈ 1.5e12 pops.
    let n = 60;
    let solver = fibonacci_dag(n, 1);
    let mut expander =
        SubstitutionExpander::new(&solver.substitutions, ExpansionPolicy::FreeParams);
    let form = expander
        .expand(0)
        .expect("memoized expansion is cheap")
        .clone();
    // f_i = Fib(n-i) * x1 + Fib(n-i-1) * p + (Fib(n-i+1) - 1): check the
    // coefficients against the closed form and the whole form at a point.
    let p = 2 + n + 1;
    assert_eq!(form.coeffs.len(), 2);
    assert_eq!(form.coeffs[&1], fib(n));
    assert_eq!(form.coeffs[&p], fib(n - 1));
    let mut point: HashMap<usize, BigInt> = HashMap::default();
    point.insert(1, BigInt::from(7));
    point.insert(p, BigInt::from(-3));
    // Evaluate the DAG bottom-up directly.
    let mut f_val = vec![BigInt::zero(); n + 1];
    f_val[n] = BigInt::from(-3);
    f_val[n - 1] = BigInt::from(7);
    for i in (0..n - 1).rev() {
        f_val[i] = &f_val[i + 1] + &f_val[i + 2] + BigInt::one();
    }
    assert_eq!(value_of(&form, &point), f_val[0]);
}

#[test]
fn d3_deep_dag_makes_no_false_modular_claim() {
    // gcd(Fib(60), Fib(59)) = 1: x0 has NO modulus. Any partial sum of this
    // DAG over a single leaf has a large GCD, which is the D3 false claim.
    let solver = fibonacci_dag(60, 1);
    assert!(
        solver.get_modular_constraints(2).is_empty(),
        "x0 = Fib(60)*x1 + Fib(59)*p + c has gcd 1 and no modulus"
    );
    // With x1 original and p a free fresh parameter, x0 has no expression over
    // original variables alone (#4830), so nothing may be cached for it.
    assert!(
        solver.get_expanded_substitutions(2, true).is_empty(),
        "an expression that needs a free parameter must not be cached"
    );
}

#[test]
fn d3_deep_dag_keeps_a_true_modulus() {
    // x0 = 6 * f_0: the exact expansion's GCD is 6 * gcd(Fib(60), Fib(59)) = 6.
    let n = 60;
    let solver = fibonacci_dag(n, 6);
    // The constant is 6 * c0 as well, so the residue is 0.
    let claims = solver.get_modular_constraints(2);
    assert_eq!(claims, vec![(0, BigInt::from(6), BigInt::zero())]);
}

/// The Fibonacci DAG closed over ORIGINAL leaves: original vars 0, 1, 2;
/// `x0 = f_0`, `f_i = f_{i+1} + f_{i+2} + 1`, `f_{n-1} = x1`, `f_n = x2`.
/// Every path ends at an original variable, so `x0` HAS an expression over
/// original variables alone — the case `get_expanded_substitutions` caches.
fn fibonacci_dag_over_originals(n: usize) -> DiophSolver {
    let f_n = 2 + n;
    // Renumber: the fresh chain starts at 3 so that 2 can be original.
    let shift = |v: usize| if v >= 2 { v + 1 } else { v };
    let mut subs: HashMap<usize, (HashMap<usize, BigInt>, BigInt)> = HashMap::default();
    for (&var, (coeffs, constant)) in &fibonacci_dag(n, 1).substitutions {
        let coeffs = if var == f_n {
            [(2, BigInt::one())].into_iter().collect()
        } else {
            coeffs.iter().map(|(&v, c)| (shift(v), c.clone())).collect()
        };
        subs.insert(shift(var), (coeffs, constant.clone()));
    }
    let mut solver = DiophSolver::new(3);
    solver.substitutions = subs;
    solver
}

#[test]
fn d3_cached_substitution_is_an_identity_not_a_partial_sum() {
    // StopAtOriginals (the cached substitutions that bound propagation, GCD
    // tightening and the composed-substitution check read): the tree walk
    // stopped after 100 pops and cached the partial sum as `x0 = ...`, an
    // equation the system does not imply. The exact expansion is cheap here
    // (n = 40: the tree has ~Fib(40) ≈ 1e8 paths, the DAG 40 nodes).
    let n = 40;
    let solver = fibonacci_dag_over_originals(n);
    let cached = solver.get_expanded_substitutions(3, true);
    let (x1, x2) = (BigInt::from(7), BigInt::from(-3));
    // Evaluate the DAG bottom-up at x1 = 7, x2 = -3.
    let mut f_val = vec![BigInt::zero(); n + 1];
    f_val[n] = x2.clone();
    f_val[n - 1] = x1.clone();
    for i in (0..n - 1).rev() {
        f_val[i] = &f_val[i + 1] + &f_val[i + 2] + BigInt::one();
    }
    let x0 = cached
        .iter()
        .find(|(var, _, _)| *var == 0)
        .expect("capability: x0's exact expression over x1, x2 is cheap and must be cached");
    let mut rhs = x0.2.clone();
    for (dep, coeff) in &x0.1 {
        let value = match *dep {
            1 => &x1,
            2 => &x2,
            other => panic!("x0's cached expression names x{other}, not an original leaf"),
        };
        rhs += coeff * value;
    }
    assert_eq!(
        rhs, f_val[0],
        "cached x0 = {:?} + {} is not an identity of the substitution DAG",
        x0.1, x0.2
    );
    assert_eq!(
        x0.1,
        vec![(1, fib(n)), (2, fib(n - 1))],
        "x0 = Fib(n)*x1 + Fib(n-1)*x2 + c"
    );
}

#[test]
fn d3_exhausted_budget_yields_no_expansion() {
    // Never a partial sum: with a budget too small to finish, the expansion
    // is absent.
    let solver = fibonacci_dag(60, 1);
    let mut expander =
        SubstitutionExpander::with_budget(&solver.substitutions, ExpansionPolicy::FreeParams, 10);
    assert!(expander.expand(0).is_none());
}

#[test]
fn d3_cyclic_substitutions_yield_no_expansion() {
    // Elimination never builds a cycle; if one existed the expansion must
    // terminate and claim nothing.
    let mut solver = DiophSolver::new(1);
    let mut subs: HashMap<usize, (HashMap<usize, BigInt>, BigInt)> = HashMap::default();
    subs.insert(
        0,
        ([(1, BigInt::from(2))].into_iter().collect(), BigInt::zero()),
    );
    subs.insert(
        1,
        ([(2, BigInt::from(2))].into_iter().collect(), BigInt::one()),
    );
    subs.insert(
        2,
        ([(1, BigInt::from(2))].into_iter().collect(), BigInt::one()),
    );
    solver.substitutions = subs;
    assert!(solver.get_modular_constraints(1).is_empty());
    assert!(solver.get_expanded_substitutions(1, true).is_empty());
}
