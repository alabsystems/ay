// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use ay_core::TheorySolver;
use num_rational::BigRational;

fn rat(n: i64) -> BigRational {
    BigRational::from_integer(n.into())
}

#[test]
fn test_flip_cmp() {
    assert_eq!(flip_cmp(">="), "<=");
    assert_eq!(flip_cmp(">"), "<");
    assert_eq!(flip_cmp("<="), ">=");
    assert_eq!(flip_cmp("<"), ">");
    assert_eq!(flip_cmp("="), "=");
}

#[test]
fn test_negate_cmp() {
    assert_eq!(negate_cmp(">="), "<");
    assert_eq!(negate_cmp(">"), "<=");
    assert_eq!(negate_cmp("<="), ">");
    assert_eq!(negate_cmp("<"), ">=");
    assert_eq!(negate_cmp("="), "distinct");
    assert_eq!(negate_cmp("distinct"), "=");
}

#[test]
fn test_eval_constant_cmp() {
    assert!(eval_constant_cmp(">=", &rat(5), &rat(3)));
    assert!(eval_constant_cmp(">=", &rat(3), &rat(3)));
    assert!(!eval_constant_cmp(">=", &rat(2), &rat(3)));
    assert!(eval_constant_cmp("=", &rat(3), &rat(3)));
    assert!(!eval_constant_cmp("=", &rat(2), &rat(3)));
}

#[test]
fn test_feasible_set_from_linear_ge() {
    // x >= 5 => [5, +inf)
    let terms = ay_core::term::TermStore::new();
    let solver = NraSolver::new(&terms);
    let fs = solver.feasible_set_from_linear(">=", true, &rat(1), &rat(5));
    assert!(fs.contains_point(&rat(5)));
    assert!(fs.contains_point(&rat(10)));
    assert!(!fs.contains_point(&rat(4)));
}

#[test]
fn test_feasible_set_from_linear_lt() {
    // x < 3 => (-inf, 3)
    let terms = ay_core::term::TermStore::new();
    let solver = NraSolver::new(&terms);
    let fs = solver.feasible_set_from_linear("<", true, &rat(1), &rat(3));
    assert!(fs.contains_point(&rat(2)));
    assert!(!fs.contains_point(&rat(3)));
    assert!(!fs.contains_point(&rat(4)));
}

#[test]
fn test_feasible_set_from_linear_negative_coeff() {
    // -2*x >= 6 => x <= -3 => (-inf, -3]
    let terms = ay_core::term::TermStore::new();
    let solver = NraSolver::new(&terms);
    let fs = solver.feasible_set_from_linear(">=", true, &rat(-2), &rat(6));
    assert!(fs.contains_point(&rat(-3)));
    assert!(fs.contains_point(&rat(-10)));
    assert!(!fs.contains_point(&rat(-2)));
}

#[test]
fn test_feasible_set_from_linear_negated() {
    // NOT(x >= 5) => x < 5 => (-inf, 5)
    let terms = ay_core::term::TermStore::new();
    let solver = NraSolver::new(&terms);
    let fs = solver.feasible_set_from_linear(">=", false, &rat(1), &rat(5));
    assert!(fs.contains_point(&rat(4)));
    assert!(!fs.contains_point(&rat(5)));
}

#[test]
fn test_feasible_set_from_linear_equality() {
    // x = 7 => {7}
    let terms = ay_core::term::TermStore::new();
    let solver = NraSolver::new(&terms);
    let fs = solver.feasible_set_from_linear("=", true, &rat(1), &rat(7));
    assert!(fs.contains_point(&rat(7)));
    assert!(!fs.contains_point(&rat(6)));
    assert_eq!(fs.is_singleton(), Some(rat(7)));
}

#[test]
fn test_feasible_set_from_linear_disequality() {
    // x != 3 => (-inf, 3) U (3, +inf)
    let terms = ay_core::term::TermStore::new();
    let solver = NraSolver::new(&terms);
    let fs = solver.feasible_set_from_linear("distinct", true, &rat(1), &rat(3));
    assert!(!fs.contains_point(&rat(3)));
    assert!(fs.contains_point(&rat(2)));
    assert!(fs.contains_point(&rat(4)));
}

// ====== Additional NLSAT tests (#8460) ======

/// Zero coefficient: 0*x >= 5 => 0 >= 5 is false => empty set.
#[test]
fn test_feasible_set_from_linear_zero_coeff_false() {
    let terms = ay_core::term::TermStore::new();
    let solver = NraSolver::new(&terms);
    let fs = solver.feasible_set_from_linear(">=", true, &rat(0), &rat(5));
    assert!(
        fs.is_empty(),
        "0 >= 5 is false, so feasible set should be empty"
    );
}

/// Zero coefficient: 0*x >= 0 => 0 >= 0 is true => full set.
#[test]
fn test_feasible_set_from_linear_zero_coeff_true() {
    let terms = ay_core::term::TermStore::new();
    let solver = NraSolver::new(&terms);
    let fs = solver.feasible_set_from_linear(">=", true, &rat(0), &rat(0));
    assert!(
        !fs.is_empty(),
        "0 >= 0 is true, so feasible set should be full"
    );
    assert!(fs.contains_point(&rat(42)));
    assert!(fs.contains_point(&rat(-42)));
}

/// Zero coefficient: 0*x > 0 => false => empty.
#[test]
fn test_feasible_set_from_linear_zero_coeff_strict_gt_false() {
    let terms = ay_core::term::TermStore::new();
    let solver = NraSolver::new(&terms);
    let fs = solver.feasible_set_from_linear(">", true, &rat(0), &rat(0));
    assert!(
        fs.is_empty(),
        "0 > 0 is false, so feasible set should be empty"
    );
}

/// Zero coefficient: 0*x = 0 => true => full.
#[test]
fn test_feasible_set_from_linear_zero_coeff_eq_true() {
    let terms = ay_core::term::TermStore::new();
    let solver = NraSolver::new(&terms);
    let fs = solver.feasible_set_from_linear("=", true, &rat(0), &rat(0));
    assert!(
        !fs.is_empty(),
        "0 = 0 is true, so feasible set should be full"
    );
}

/// Negated equality: NOT(x = 5) => x != 5 => (-inf,5) U (5,+inf).
#[test]
fn test_feasible_set_from_linear_negated_equality() {
    let terms = ay_core::term::TermStore::new();
    let solver = NraSolver::new(&terms);
    let fs = solver.feasible_set_from_linear("=", false, &rat(1), &rat(5));
    assert!(!fs.contains_point(&rat(5)));
    assert!(fs.contains_point(&rat(4)));
    assert!(fs.contains_point(&rat(6)));
}

/// Negated disequality: NOT(x != 3) => x = 3 => {3}.
#[test]
fn test_feasible_set_from_linear_negated_disequality() {
    let terms = ay_core::term::TermStore::new();
    let solver = NraSolver::new(&terms);
    let fs = solver.feasible_set_from_linear("distinct", false, &rat(1), &rat(3));
    assert!(fs.contains_point(&rat(3)));
    assert!(!fs.contains_point(&rat(2)));
    assert!(!fs.contains_point(&rat(4)));
    assert_eq!(fs.is_singleton(), Some(rat(3)));
}

/// Unknown comparator should conservatively return full set.
#[test]
fn test_feasible_set_from_linear_unknown_cmp() {
    let terms = ay_core::term::TermStore::new();
    let solver = NraSolver::new(&terms);
    let fs = solver.feasible_set_from_linear("???", true, &rat(1), &rat(5));
    assert!(!fs.is_empty(), "unknown comparator should produce full set");
    assert!(fs.contains_point(&rat(0)));
}

/// flip_cmp is its own inverse: flip(flip(x)) == x.
#[test]
fn test_flip_cmp_involution() {
    for cmp in &[">=", ">", "<=", "<", "=", "distinct"] {
        assert_eq!(
            flip_cmp(flip_cmp(cmp)),
            *cmp,
            "flip_cmp should be an involution for {cmp}"
        );
    }
}

/// negate_cmp is its own inverse: negate(negate(x)) == x.
#[test]
fn test_negate_cmp_involution() {
    for cmp in &[">=", ">", "<=", "<", "=", "distinct"] {
        assert_eq!(
            negate_cmp(negate_cmp(cmp)),
            *cmp,
            "negate_cmp should be an involution for {cmp}"
        );
    }
}

/// eval_constant_cmp covers all six operators.
#[test]
fn test_eval_constant_cmp_all_operators() {
    assert!(eval_constant_cmp(">", &rat(5), &rat(3)));
    assert!(!eval_constant_cmp(">", &rat(3), &rat(3)));
    assert!(eval_constant_cmp("<=", &rat(3), &rat(3)));
    assert!(eval_constant_cmp("<=", &rat(2), &rat(3)));
    assert!(!eval_constant_cmp("<=", &rat(4), &rat(3)));
    assert!(eval_constant_cmp("<", &rat(2), &rat(3)));
    assert!(!eval_constant_cmp("<", &rat(3), &rat(3)));
    assert!(eval_constant_cmp("distinct", &rat(1), &rat(2)));
    assert!(!eval_constant_cmp("distinct", &rat(2), &rat(2)));
    assert!(eval_constant_cmp("!=", &rat(1), &rat(2)));
}

/// Negative coefficient with negated literal:
/// NOT(-3*x >= 6) => NOT(x <= -2) => x > -2 => (-2, +inf).
#[test]
fn test_feasible_set_from_linear_negative_coeff_negated() {
    let terms = ay_core::term::TermStore::new();
    let solver = NraSolver::new(&terms);
    let fs = solver.feasible_set_from_linear(">=", false, &rat(-3), &rat(6));
    // -3*x >= 6 => x <= -2, negation => x > -2
    assert!(!fs.contains_point(&rat(-2)));
    assert!(fs.contains_point(&rat(-1)));
    assert!(fs.contains_point(&rat(0)));
}

/// Fractional coefficient: (1/2)*x >= 3 => x >= 6.
#[test]
fn test_feasible_set_from_linear_fractional_coeff() {
    let terms = ay_core::term::TermStore::new();
    let solver = NraSolver::new(&terms);
    let half = BigRational::new(1.into(), 2.into());
    let fs = solver.feasible_set_from_linear(">=", true, &half, &rat(3));
    assert!(fs.contains_point(&rat(6)));
    assert!(fs.contains_point(&rat(100)));
    assert!(!fs.contains_point(&rat(5)));
}

/// x <= -10 => (-inf, -10].
#[test]
fn test_feasible_set_from_linear_le_negative() {
    let terms = ay_core::term::TermStore::new();
    let solver = NraSolver::new(&terms);
    let fs = solver.feasible_set_from_linear("<=", true, &rat(1), &rat(-10));
    assert!(fs.contains_point(&rat(-10)));
    assert!(fs.contains_point(&rat(-100)));
    assert!(!fs.contains_point(&rat(-9)));
}

// ====== #nonlinear-phase-hints: the allocation-free phase decision ======

/// Deterministic LCG so the oracle sweep below is reproducible.
struct Lcg(u64);
impl Lcg {
    fn next(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        self.0 >> 33
    }
    /// A draw in `0..n`; `None` for the empty range `n == 0`.
    fn below(&mut self, n: u64) -> Option<u64> {
        self.next().checked_rem(n)
    }
}

/// Build a vocabulary of atoms over Real vars whose operands cover every arm
/// of `extract_linear_univariate` — bare vars, `c * x`, `x * y` (a factor the
/// model may send to zero), nested `(* (* a b) c)` with two args, `+`, binary
/// and unary `-`, numeric literals on either side, every comparator including
/// `distinct` and an uninterpreted predicate — with raw `mk_app` so the term
/// store's own normalisation does not fold the shapes away.
fn phase_oracle_vocabulary(terms: &mut ay_core::term::TermStore) -> (Vec<TermId>, Vec<TermId>) {
    use ay_core::Sort;
    let real = Sort::Real;
    let vars: Vec<TermId> = ["x", "y", "z", "w", "u"]
        .iter()
        .map(|n| terms.mk_var(*n, real.clone()))
        .collect();
    let c0 = terms.mk_rational(rat(0));
    let c2 = terms.mk_rational(rat(2));
    let cm3 = terms.mk_rational(rat(-3));
    let half = terms.mk_rational(BigRational::new(1.into(), 2.into()));
    fn app(t: &mut ay_core::term::TermStore, n: &str, a: &[TermId]) -> TermId {
        t.mk_app(Symbol::named(n), a, ay_core::Sort::Real)
    }
    let (x, y, z, w, u) = (vars[0], vars[1], vars[2], vars[3], vars[4]);
    let mut operands = vec![x, y, z, w, u, c0, c2, cm3, half];
    let xy = app(terms, "*", &[x, y]);
    let c2x = app(terms, "*", &[c2, x]);
    let ym3 = app(terms, "*", &[y, cm3]);
    let zw = app(terms, "*", &[z, w]);
    let xyz = app(terms, "*", &[xy, z]);
    let sum = app(terms, "+", &[x, c2]);
    let sum2 = app(terms, "+", &[zw, u]);
    let diff = app(terms, "-", &[y, x]);
    let diff2 = app(terms, "-", &[c2, zw]);
    let neg = app(terms, "-", &[x]);
    let negprod = app(terms, "-", &[xy]);
    let uf = terms.mk_app(Symbol::named("f"), [w], real.clone());
    let three = app(terms, "*", &[x, y, z]); // 3 args: no univariate form
    operands.extend([
        xy, c2x, ym3, zw, xyz, sum, sum2, diff, diff2, neg, negprod, uf, three,
    ]);
    let mut atoms = Vec::new();
    for (i, &a) in operands.iter().enumerate() {
        for (j, &b) in operands.iter().enumerate() {
            if i == j {
                continue;
            }
            // `(i * 7 + j) % 7` is `j % 7`; spelled directly so no product
            // or sum can overflow.
            let cmp = ["<", "<=", ">", ">=", "=", "distinct", "p"][j % 7];
            atoms.push(terms.mk_app(Symbol::named(cmp), [a, b], Sort::Bool));
        }
    }
    (vars, atoms)
}

fn is_uninterpreted_pred(terms: &ay_core::term::TermStore, atom: TermId) -> bool {
    matches!(terms.get(atom), TermData::App(Symbol::Named(n), _) if n.as_str() == "p")
}

/// Every reachable state of a scripted assert / check / push / pop
/// trajectory: the fast decision equals the reference on every atom, and
/// `value_sign` equals the sign of `get_value` on every operand. The
/// debug-build `debug_assert_eq!` in `suggest_phase` checks the same thing on
/// every real solve; this test pins it in release builds too.
#[test]
fn feasible_set_phase_matches_reference_across_trajectory() -> Result<(), Box<dyn std::error::Error>>
{
    let mut terms = ay_core::term::TermStore::new();
    let (vars, atoms) = phase_oracle_vocabulary(&mut terms);
    let mut solver = NraSolver::new(&terms);
    let mut rng = Lcg(0x5eed_2026_0921);
    let mut compared = 0usize;
    let mut decided = 0usize;
    let mut depth = 0usize;
    let check_state = |solver: &NraSolver<'_>, compared: &mut usize, decided: &mut usize| {
        for &atom in &atoms {
            let fast = solver.feasible_set_phase(atom);
            let reference = solver.feasible_set_phase_reference(atom);
            assert_eq!(
                fast, reference,
                "atom {atom:?}: fast {fast:?} vs reference {reference:?}"
            );
            *compared += 1;
            if fast.is_some() {
                *decided += 1;
            }
            // And the full suggestion, which appends the LRA fallback.
            let _ = solver.suggest_phase(atom);
        }
        for &v in &vars {
            let sign = solver.lra.value_sign(v);
            let value = solver.lra.get_value(v);
            assert_eq!(
                sign,
                value.as_ref().map(|q| q.cmp(&BigRational::zero())),
                "value_sign({v:?}) disagrees with get_value"
            );
        }
    };
    check_state(&solver, &mut compared, &mut decided);
    for step in 0..300 {
        match rng.below(10).ok_or("empty action range")? {
            0..=5 => {
                let draw = rng
                    .below(atoms.len() as u64)
                    .ok_or("the vocabulary has no atoms")?;
                let atom = atoms[draw as usize];
                // Only arithmetic comparators are assertable to the LRA.
                if !is_uninterpreted_pred(&terms, atom) {
                    let polarity = rng.below(2).ok_or("empty polarity range")?;
                    solver.assert_literal(atom, polarity == 0);
                }
            }
            6..=7 => {
                let _ = solver.check();
            }
            8 => {
                solver.push();
                depth += 1;
            }
            _ => {
                if depth > 0 {
                    solver.pop();
                    depth -= 1;
                }
            }
        }
        check_state(&solver, &mut compared, &mut decided);
        if step % 97 == 96 {
            solver.reset();
            depth = 0;
            check_state(&solver, &mut compared, &mut decided);
        }
    }
    assert!(
        compared > 100_000,
        "the sweep compared only {compared} atom states"
    );
    assert!(
        decided > 0,
        "the sweep never reached a state where the look-ahead has an opinion"
    );
    Ok(())
}

/// One `check()`'s feasible-set recomputation evaluates many asserted
/// atoms against one unchanged LRA model; the O(#vars) materialisation
/// delta must be shared across those evaluations instead of recomputed
/// per epsilon-carrying leaf (sampled as a top stack on QF_UFNRA
/// `cas/40f50` via `extract_linear_univariate` -> `get_value`).
#[test]
fn feasible_set_recompute_shares_one_materialization_delta() {
    use ay_core::Sort;
    let mut terms = ay_core::term::TermStore::new();
    let c0 = terms.mk_rational(rat(0));
    let c1 = terms.mk_rational(rat(1));
    let c3 = terms.mk_rational(rat(3));
    fn app(t: &mut ay_core::term::TermStore, n: &str, a: &[TermId], sort: Sort) -> TermId {
        t.mk_app(Symbol::named(n), a, sort)
    }
    // Six var pairs in the open unit box (vertex values carry epsilons
    // at the strict bounds) plus a product atom per pair, so the
    // feasible-set recomputation evaluates epsilon-carrying leaves for
    // every asserted product atom. All terms are built before the
    // solver borrows the store.
    let mut atoms = Vec::new();
    for i in 0..6 {
        let x = terms.mk_var(format!("x{i}"), Sort::Real);
        let y = terms.mk_var(format!("y{i}"), Sort::Real);
        let prod = app(&mut terms, "*", &[x, y], Sort::Real);
        for (v, cmp, c) in [(x, ">", c0), (x, "<", c1), (y, ">", c0), (y, "<", c1)] {
            atoms.push(app(&mut terms, cmp, &[v, c], Sort::Bool));
        }
        atoms.push(app(&mut terms, ">", &[prod, c0], Sort::Bool));
        atoms.push(app(&mut terms, "<", &[prod, c3], Sort::Bool));
    }
    let mut solver = NraSolver::new(&terms);
    for atom in atoms {
        solver.assert_literal(atom, true);
    }
    assert!(
        matches!(solver.check(), ay_core::TheoryResult::Sat),
        "unit-box products must be SAT"
    );
    let before = solver.lra.materialization_delta_computations();
    // A second check over the unchanged asserted set recomputes every
    // feasible set from scratch (update_feasible_sets); its delta must
    // be shared across the whole pass.
    assert!(matches!(solver.check(), ay_core::TheoryResult::Sat));
    let spent = solver.lra.materialization_delta_computations() - before;
    assert!(
        spent <= 2,
        "one check must share its materialisation delta, spent {spent}"
    );
}
