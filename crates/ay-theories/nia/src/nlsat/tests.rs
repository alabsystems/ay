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
    let solver = NiaSolver::new(&terms);
    let fs = solver.feasible_set_from_linear(">=", true, &rat(1), &rat(5));
    assert!(fs.contains_point(&rat(5)));
    assert!(fs.contains_point(&rat(10)));
    assert!(!fs.contains_point(&rat(4)));
}

#[test]
fn test_feasible_set_from_linear_lt() {
    // x < 3 => (-inf, 3)
    let terms = ay_core::term::TermStore::new();
    let solver = NiaSolver::new(&terms);
    let fs = solver.feasible_set_from_linear("<", true, &rat(1), &rat(3));
    assert!(fs.contains_point(&rat(2)));
    assert!(!fs.contains_point(&rat(3)));
    assert!(!fs.contains_point(&rat(4)));
}

#[test]
fn test_feasible_set_from_linear_negative_coeff() {
    // -2*x >= 6 => x <= -3 => (-inf, -3]
    let terms = ay_core::term::TermStore::new();
    let solver = NiaSolver::new(&terms);
    let fs = solver.feasible_set_from_linear(">=", true, &rat(-2), &rat(6));
    assert!(fs.contains_point(&rat(-3)));
    assert!(fs.contains_point(&rat(-10)));
    assert!(!fs.contains_point(&rat(-2)));
}

#[test]
fn test_feasible_set_from_linear_negated() {
    // NOT(x >= 5) => x < 5 => (-inf, 5)
    let terms = ay_core::term::TermStore::new();
    let solver = NiaSolver::new(&terms);
    let fs = solver.feasible_set_from_linear(">=", false, &rat(1), &rat(5));
    assert!(fs.contains_point(&rat(4)));
    assert!(!fs.contains_point(&rat(5)));
}

#[test]
fn test_feasible_set_from_linear_equality() {
    // x = 7 => {7}
    let terms = ay_core::term::TermStore::new();
    let solver = NiaSolver::new(&terms);
    let fs = solver.feasible_set_from_linear("=", true, &rat(1), &rat(7));
    assert!(fs.contains_point(&rat(7)));
    assert!(!fs.contains_point(&rat(6)));
    assert_eq!(fs.is_singleton(), Some(rat(7)));
}

#[test]
fn test_feasible_set_from_linear_disequality() {
    // x != 3 => (-inf, 3) U (3, +inf)
    let terms = ay_core::term::TermStore::new();
    let solver = NiaSolver::new(&terms);
    let fs = solver.feasible_set_from_linear("distinct", true, &rat(1), &rat(3));
    assert!(!fs.contains_point(&rat(3)));
    assert!(fs.contains_point(&rat(2)));
    assert!(fs.contains_point(&rat(4)));
}

#[test]
fn test_feasible_set_from_linear_zero_coeff_false() {
    let terms = ay_core::term::TermStore::new();
    let solver = NiaSolver::new(&terms);
    let fs = solver.feasible_set_from_linear(">=", true, &rat(0), &rat(5));
    assert!(
        fs.is_empty(),
        "0 >= 5 is false, so feasible set should be empty"
    );
}

#[test]
fn test_feasible_set_from_linear_zero_coeff_true() {
    let terms = ay_core::term::TermStore::new();
    let solver = NiaSolver::new(&terms);
    let fs = solver.feasible_set_from_linear(">=", true, &rat(0), &rat(0));
    assert!(
        !fs.is_empty(),
        "0 >= 0 is true, so feasible set should be full"
    );
    assert!(fs.contains_point(&rat(42)));
}

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
    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
}

/// Build a vocabulary of atoms over Int vars whose operands cover every arm
/// of `extract_linear_univariate` — bare vars, `c * x`, `x * y` (a factor the
/// model may send to zero), nested `(* (* a b) c)` with two args, `+`, binary
/// and unary `-`, numeric literals on either side, every comparator including
/// `distinct` and an uninterpreted predicate — with raw `mk_app` so the term
/// store's own normalisation does not fold the shapes away.
fn phase_oracle_vocabulary(terms: &mut ay_core::term::TermStore) -> (Vec<TermId>, Vec<TermId>) {
    use ay_core::Sort;
    let int = Sort::Int;
    let vars: Vec<TermId> = ["x", "y", "z", "w", "u"]
        .iter()
        .map(|n| terms.mk_var(*n, int.clone()))
        .collect();
    let c0 = terms.mk_int(0.into());
    let c2 = terms.mk_int(2.into());
    let cm3 = terms.mk_int((-3).into());
    let half = terms.mk_int(7.into());
    fn app(t: &mut ay_core::term::TermStore, n: &str, a: &[TermId]) -> TermId {
        t.mk_app(Symbol::named(n), a, ay_core::Sort::Int)
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
    let uf = terms.mk_app(Symbol::named("f"), [w], int.clone());
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
            let cmp = ["<", "<=", ">", ">=", "=", "distinct", "p"][(i * 7 + j) % 7];
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
fn feasible_set_phase_matches_reference_across_trajectory() {
    let mut terms = ay_core::term::TermStore::new();
    let (vars, atoms) = phase_oracle_vocabulary(&mut terms);
    let mut solver = NiaSolver::new(&terms);
    let mut rng = Lcg(0x5eed_2026_0921);
    let mut compared = 0usize;
    let mut decided = 0usize;
    let mut depth = 0usize;
    let check_state = |solver: &NiaSolver<'_>, compared: &mut usize, decided: &mut usize| {
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
            let sign = solver.lia.lra_solver().value_sign(v);
            let value = solver.lia.lra_solver().get_value(v);
            assert_eq!(
                sign,
                value.as_ref().map(|q| q.cmp(&BigRational::zero())),
                "value_sign({v:?}) disagrees with get_value"
            );
        }
    };
    check_state(&solver, &mut compared, &mut decided);
    for step in 0..300 {
        match rng.below(10) {
            0..=5 => {
                let atom = atoms[rng.below(atoms.len() as u64) as usize];
                // Only arithmetic comparators are assertable to the LRA.
                if !is_uninterpreted_pred(&terms, atom) {
                    solver.assert_literal(atom, rng.below(2) == 0);
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
}

/// The per-epoch `suggest_phase` memo must be transparent: identical
/// suggestions to direct computation, populated on first use, and
/// refreshed (not stale) after the LRA phase-state epoch advances.
#[test]
fn suggest_phase_memo_matches_direct_and_refreshes_on_epoch_change() {
    use ay_core::Sort;
    let mut terms = ay_core::term::TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let six = terms.mk_int(6.into());
    let xy = terms.mk_mul(vec![x, y]);
    let eq_atom = terms.mk_eq(xy, six);
    let two = terms.mk_int(2.into());
    let x_ge_two = terms.mk_ge(x, two);

    let mut solver = NiaSolver::new(&terms);
    solver.register_atom(eq_atom);
    solver.register_atom(x_ge_two);

    let direct = |s: &NiaSolver<'_>, atom| {
        s.feasible_set_phase(atom)
            .or_else(|| s.lia.suggest_phase(atom))
    };
    for atom in [eq_atom, x_ge_two] {
        assert_eq!(solver.suggest_phase(atom), direct(&solver, atom));
        assert_eq!(
            solver.suggest_phase(atom),
            direct(&solver, atom),
            "memoised second call must agree"
        );
    }
    {
        let memo = solver.phase_memo.borrow();
        assert_eq!(
            memo.0,
            Some(solver.lia.lra_solver().phase_state_epoch()),
            "memo must be keyed by the current phase-state epoch"
        );
        assert_eq!(memo.1.len(), 2, "both queried atoms are memoised");
    }

    // Advance the underlying LRA state; suggestions must be recomputed
    // (still equal to direct computation), never served stale.
    solver.assert_literal(x_ge_two, true);
    let _ = solver.check();
    for atom in [eq_atom, x_ge_two] {
        assert_eq!(solver.suggest_phase(atom), direct(&solver, atom));
    }
    let memo = solver.phase_memo.borrow();
    assert_eq!(
        memo.0,
        Some(solver.lia.lra_solver().phase_state_epoch()),
        "memo must re-key after the epoch advances"
    );
}

/// The per-epoch leaf-sign memo must be transparent: `term_has_value`
/// (now defined via the memoised sign) keeps its pre-memo meaning --
/// column existence or numeric literal -- and memoised signs agree with
/// direct `value_sign` reads, refreshed after the epoch advances.
#[test]
fn leaf_sign_memo_matches_direct_reads_across_epochs() {
    use ay_core::Sort;
    let mut terms = ay_core::term::TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let neg_three = terms.mk_int((-3).into());
    let two = terms.mk_int(2.into());
    let x_ge_two = terms.mk_ge(x, two);
    let xy = terms.mk_mul(vec![x, y]);

    let mut solver = NiaSolver::new(&terms);
    solver.register_atom(x_ge_two);

    let direct_has = |s: &NiaSolver<'_>, t| {
        s.lia.lra_solver().has_value(t)
            || matches!(
                s.terms.get(t),
                ay_core::term::TermData::Const(ay_core::term::Constant::Rational(_))
                    | ay_core::term::TermData::Const(ay_core::term::Constant::Int(_))
            )
    };
    let check_all = |s: &NiaSolver<'_>| {
        for t in [x, y, neg_three, two, xy] {
            assert_eq!(s.term_has_value(t), direct_has(s, t), "has_value({t:?})");
            assert_eq!(
                s.term_value_sign(t).is_some(),
                s.term_has_value(t),
                "sign existence must equal has_value for {t:?}"
            );
            // Second read serves the memo and must agree.
            assert_eq!(
                s.term_value_sign(t),
                s.lia
                    .lra_solver()
                    .value_sign(t)
                    .or_else(|| match s.terms.get(t) {
                        ay_core::term::TermData::Const(ay_core::term::Constant::Int(n)) => {
                            Some(n.sign().cmp(&num_bigint::Sign::NoSign))
                        }
                        _ => None,
                    }),
                "memoised sign for {t:?}"
            );
        }
    };
    check_all(&solver);
    {
        let memo = solver.leaf_sign_memo.borrow();
        assert_eq!(memo.0, Some(solver.lia.lra_solver().phase_state_epoch()));
        assert!(!memo.1.is_empty(), "leaf memo must be populated");
    }
    // Advance the LRA state so x gains a column/value; reads must refresh.
    solver.assert_literal(x_ge_two, true);
    let _ = solver.check();
    check_all(&solver);
    assert!(solver.term_has_value(x), "x has a column after assertion");
}
