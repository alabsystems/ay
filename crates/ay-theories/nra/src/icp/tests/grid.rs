// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `icp::tests` to preserve existing test FQNs.

#[test]
fn dyadic_grid_is_cumulative_and_capped() {
    // Level 0 is the integers in [-4, 4], zero first, positive before its
    // negation; each finer level ADDS only the new denominators.
    let l0 = dyadic_grid(0);
    assert_eq!(
        l0.iter().map(|q| q.to_string()).collect::<Vec<_>>(),
        ["0", "1", "-1", "2", "-2", "3", "-3", "4", "-4"]
    );
    for level in 0..GRID_MAX_LEVEL {
        let (a, b) = (dyadic_grid(level), dyadic_grid(level + 1));
        assert_eq!(
            &b[..a.len()],
            a,
            "level {level} must be a prefix of the next"
        );
        assert!(b.len() > a.len(), "level {level} must gain values");
    }
    let fine = dyadic_grid(GRID_MAX_LEVEL);
    let cap = BigRational::from_integer(BigInt::from(GRID_ABS_CAP as i64));
    assert!(
        fine.iter().all(|q| q.abs() <= cap),
        "values stay within the cap"
    );
    assert!(
        fine.iter()
            .all(|q| (q * BigRational::from_integer(BigInt::one() << GRID_MAX_LEVEL)).is_integer()),
        "every value is a dyadic with denominator dividing 2^GRID_MAX_LEVEL"
    );
    let mut seen = fine.to_vec();
    seen.sort();
    seen.dedup();
    assert_eq!(seen.len(), fine.len(), "no value repeats across levels");
}

#[test]
fn dyadic_grid_search_finds_a_mixed_coordinate_witness() {
    // `x*y = 2 ∧ x - y > 0 ∧ y > 0` has the witness (2, 1) — MIXED across
    // coordinates, so no single rung of the diagonal `pin_candidate` ladder
    // can name it. The grid must, and the model must verify exactly.
    use ay_core::term::TermStore;
    use ay_core::Sort;
    use ay_core::TheorySolver;
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let c0 = terms.mk_rational(rat(0));
    let c2 = terms.mk_rational(rat(2));
    let xy = terms.mk_mul(vec![x, y]);
    let a1 = terms.mk_eq(xy, c2);
    let diff = terms.mk_sub(vec![x, y]);
    let a2 = terms.mk_gt(diff, c0);
    let a3 = terms.mk_gt(y, c0);
    let mut solver = NraSolver::new(&terms);
    solver.assert_literal(a1, true);
    solver.assert_literal(a2, true);
    solver.assert_literal(a3, true);

    let mut constraints: Vec<MultiConstraint> = Vec::new();
    for &(atom, value) in &solver.asserted {
        if let Some(MultiAtom::Constraint(c)) = solver.atom_to_multi(atom, value) {
            constraints.push(c);
        }
    }
    let mut vars: Vec<TermId> = Vec::new();
    for c in &constraints {
        for v in c.poly.variables() {
            if !vars.contains(&v) {
                vars.push(v);
            }
        }
    }
    vars.sort_unstable_by_key(|t| t.0);
    let mut root: VarBox = collect_variable_bounds(&constraints);
    for &v in &vars {
        root.entry(v).or_insert_with(Interval::whole);
    }
    assert!(!matches!(
        contract_box(&constraints, &vars, &mut root),
        Contraction::Refuted
    ));
    let res = solver
        .dyadic_grid_search(&constraints, &vars, &root)
        .expect("the grid must find a mixed-coordinate rational witness");
    let UniResult::Sat(model) = res else {
        panic!("this system has a RATIONAL witness; the grid must report it as such");
    };
    assert!(
        solver.verify_model(&model),
        "the witness must pass the exact substitution gate"
    );
    assert_eq!(model.len(), 2);
}

/// Build the (constraints, vars, contracted-root) triple the grid takes,
/// exactly as `try_icp_branch_and_prune` does.
#[cfg(test)]
fn grid_inputs(solver: &NraSolver<'_>) -> (Vec<MultiConstraint>, Vec<TermId>, VarBox) {
    let mut constraints: Vec<MultiConstraint> = Vec::new();
    for &(atom, value) in &solver.asserted {
        if let Some(MultiAtom::Constraint(c)) = solver.atom_to_multi(atom, value) {
            constraints.push(c);
        }
    }
    let mut vars: Vec<TermId> = Vec::new();
    for c in &constraints {
        for v in c.poly.variables() {
            if !vars.contains(&v) {
                vars.push(v);
            }
        }
    }
    vars.sort_unstable_by_key(|t| t.0);
    let mut root: VarBox = collect_variable_bounds(&constraints);
    for &v in &vars {
        root.entry(v).or_insert_with(Interval::whole);
    }
    assert!(!matches!(
        contract_box(&constraints, &vars, &mut root),
        Contraction::Refuted
    ));
    (constraints, vars, root)
}

/// The grid's SECOND pass must SOLVE the last free coordinate, not guess it.
///
/// `x*y = 1 ∧ x - 100 > 0 ∧ y > 0` forces `y = 1/x` with `x > 100`, so
/// EVERY witness has `|y| < 1/100`. The grid alphabet is `{k/8, |k| <= 4}`,
/// whose smallest nonzero magnitude is `1/8`: no combination of alphabet
/// values can name a witness, and neither can any finer level of the same
/// bounded grid without an exponential blowup. Solving the residual
/// univariate system in the last coordinate names one immediately.
#[test]
fn grid_solves_a_last_coordinate_the_alphabet_cannot_name() {
    use ay_core::term::TermStore;
    use ay_core::Sort;
    use ay_core::TheorySolver;
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let c0 = terms.mk_rational(rat(0));
    let c1 = terms.mk_rational(rat(1));
    let c100 = terms.mk_rational(rat(100));
    let xy = terms.mk_mul(vec![x, y]);
    let a1 = terms.mk_eq(xy, c1);
    let xm = terms.mk_sub(vec![x, c100]);
    let a2 = terms.mk_gt(xm, c0);
    let a3 = terms.mk_gt(y, c0);
    let mut solver = NraSolver::new(&terms);
    solver.assert_literal(a1, true);
    solver.assert_literal(a2, true);
    solver.assert_literal(a3, true);
    let (constraints, vars, root) = grid_inputs(&solver);
    let res = solver
        .dyadic_grid_search(&constraints, &vars, &root)
        .expect("the exact last-coordinate pass must find a witness");
    let UniResult::Sat(model) = res else {
        panic!("both coordinates are rational here");
    };
    assert!(solver.verify_model(&model), "exact substitution gate");
    let yv = model
        .iter()
        .find(|(v, _)| *v == y)
        .map(|(_, q)| q.clone())
        .expect("y valued");
    assert!(
        yv > BigRational::zero() && yv < BigRational::new(BigInt::one(), BigInt::from(100)),
        "y must be a genuine off-alphabet value in (0, 1/100), got {yv}"
    );
}

/// When the last coordinate's feasible set contains NO rational, the grid
/// may report the exact algebraic point rather than declining. The rational
/// coordinates stay rational; only the solved one is algebraic.
#[test]
fn grid_reports_an_algebraic_last_coordinate() {
    use ay_core::term::TermStore;
    use ay_core::Sort;
    use ay_core::TheorySolver;
    // `x = 1 ∧ y*y = 2*x ∧ y > 0` ⇒ y = sqrt(2), which is irrational, so
    // no rational assignment satisfies the system at all.
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let c0 = terms.mk_rational(rat(0));
    let c1 = terms.mk_rational(rat(1));
    let c2 = terms.mk_rational(rat(2));
    let a1 = terms.mk_eq(x, c1);
    let yy = terms.mk_mul(vec![y, y]);
    let twox = terms.mk_mul(vec![c2, x]);
    let a2 = terms.mk_eq(yy, twox);
    let a3 = terms.mk_gt(y, c0);
    let mut solver = NraSolver::new(&terms);
    solver.assert_literal(a1, true);
    solver.assert_literal(a2, true);
    solver.assert_literal(a3, true);
    let (constraints, vars, root) = grid_inputs(&solver);
    let Some(UniResult::SatAlgebraic(witnesses)) =
        solver.dyadic_grid_search(&constraints, &vars, &root)
    else {
        panic!("the only witness is irrational; the grid must say SatAlgebraic");
    };
    let val = witnesses
        .iter()
        .find_map(|(v, w)| match w {
            UniWitness::Algebraic(a) if *v == y => Some(a.clone()),
            _ => None,
        })
        .expect("y must carry the exact algebraic witness");
    match val.try_mul(&val).expect("same algebraic point") {
        crate::algebraic::RealScalar::Rational(sq) => {
            assert_eq!(sq, BigRational::from_integer(BigInt::from(2)), "y^2 == 2");
        }
        other => panic!("y^2 must reduce to the rational 2, got {other:?}"),
    }
}

#[test]
fn dyadic_grid_search_declines_without_a_witness_and_never_refutes() {
    // `x*x + y*y = -1` has no real solution. The grid must return `None`
    // (it has no `Unsat` to return) and must not spend beyond its budget.
    use ay_core::term::TermStore;
    use ay_core::Sort;
    use ay_core::TheorySolver;
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let cm1 = terms.mk_rational(rat(-1));
    let xx = terms.mk_mul(vec![x, x]);
    let yy = terms.mk_mul(vec![y, y]);
    let sum = terms.mk_add(vec![xx, yy]);
    let a1 = terms.mk_eq(sum, cm1);
    let mut solver = NraSolver::new(&terms);
    solver.assert_literal(a1, true);
    let mut constraints: Vec<MultiConstraint> = Vec::new();
    for &(atom, value) in &solver.asserted {
        if let Some(MultiAtom::Constraint(c)) = solver.atom_to_multi(atom, value) {
            constraints.push(c);
        }
    }
    let vars: Vec<TermId> = vec![x, y];
    let mut root: VarBox = VarBox::default();
    for &v in &vars {
        root.insert(v, Interval::whole());
    }
    let before = solver.grid_budget.get();
    assert!(solver
        .dyadic_grid_search(&constraints, &vars, &root)
        .is_none());
    assert!(
        solver.grid_budget.get() < before,
        "the sweep must charge its solve-wide budget"
    );
    assert!(before - solver.grid_budget.get() <= GRID_MAX_NODES);
}

/// Pass 2 must NOT be billed to pass 1's counter.
///
/// `x*x + y*y = -1` is infeasible, so pass 1 sweeps every level, fails, and
/// pass 2 then re-sweeps and also fails — the exact shape that used to
/// double-charge `grid_budget` and starve a later `check()`. Pass 1's spend
/// must be bounded by its own per-call cap and the exact work must appear on
/// `grid_exact_budget` instead.
#[test]
fn the_exact_pass_is_billed_to_its_own_budget_not_the_grid_budget() {
    use ay_core::term::TermStore;
    use ay_core::Sort;
    use ay_core::TheorySolver;
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let cm1 = terms.mk_rational(rat(-1));
    let xx = terms.mk_mul(vec![x, x]);
    let yy = terms.mk_mul(vec![y, y]);
    let sum = terms.mk_add(vec![xx, yy]);
    let a1 = terms.mk_eq(sum, cm1);
    let mut solver = NraSolver::new(&terms);
    solver.assert_literal(a1, true);
    let mut constraints: Vec<MultiConstraint> = Vec::new();
    for &(atom, value) in &solver.asserted {
        if let Some(MultiAtom::Constraint(c)) = solver.atom_to_multi(atom, value) {
            constraints.push(c);
        }
    }
    let vars: Vec<TermId> = vec![x, y];
    let mut root: VarBox = VarBox::default();
    for &v in &vars {
        root.insert(v, Interval::whole());
    }
    let g_before = solver.grid_budget.get();
    let e_before = solver.grid_exact_budget.get();
    assert!(solver
        .dyadic_grid_search(&constraints, &vars, &root)
        .is_none());
    let g_spent = g_before - solver.grid_budget.get();
    let e_spent = e_before - solver.grid_exact_budget.get();
    assert!(
        g_spent <= GRID_MAX_NODES,
        "pass 1 may never exceed its own per-call cap, spent {g_spent}"
    );
    assert!(
        e_spent <= GRID_EXACT_MAX_NODES,
        "pass 2 may never exceed its own per-call cap, spent {e_spent}"
    );
    // The two counters are genuinely independent: draining pass 2's budget
    // must leave pass 1 with a full allowance on the next call.
    solver.grid_exact_budget.set(0);
    let g2_before = solver.grid_budget.get();
    assert!(solver
        .dyadic_grid_search(&constraints, &vars, &root)
        .is_none());
    assert!(
        g2_before - solver.grid_budget.get() > 0,
        "pass 1 must still run when the exact budget is exhausted"
    );
}

/// A long run of `Empty` exact decisions must switch the pass off rather
/// than pay for every surviving prefix.
#[test]
fn consecutive_empty_exact_decisions_disable_the_pass() {
    let st = ExactState::with(GRID_EXACT_SOLVES);
    for _ in 0..GRID_EXACT_EMPTY_STREAK - 1 {
        assert!(st.available(), "the cut must not fire early");
        st.charge(&ExactOutcome::Empty);
    }
    assert!(st.available());
    st.charge(&ExactOutcome::Empty);
    assert!(
        !st.available(),
        "GRID_EXACT_EMPTY_STREAK consecutive Empties must disable the pass"
    );
}

/// `Declined` is a bail BEFORE the expensive decision, so it must not reset
/// the streak — otherwise an alternating `Empty, Declined, …` run pays the
/// Sturm decision forever and the cut never fires.
#[test]
fn a_cheap_decline_does_not_reset_the_empty_streak() {
    let st = ExactState::with(GRID_EXACT_SOLVES);
    for _ in 0..GRID_EXACT_EMPTY_STREAK {
        st.charge(&ExactOutcome::Empty);
        if st.available() {
            st.charge(&ExactOutcome::Declined);
        }
    }
    assert!(
        !st.available(),
        "interleaved cheap declines must not keep an Empty run alive"
    );
}

/// Pass 1 must be able to run an unbounded number of decisions-free sweeps:
/// `ExactState::disabled` is what makes pass 1 bit-for-bit unchanged.
///
/// It must ALSO never be treated as spent, or the guard that stops pass 2
/// would stop pass 1 — which is the whole search.
#[test]
fn pass_one_never_makes_an_exact_decision_and_is_never_spent() {
    let st = ExactState::disabled();
    assert!(
        !st.available(),
        "pass 1 must never enter the exact last-coordinate solve"
    );
    assert!(
        !st.spent(),
        "pass 1 has no exact budget to spend and must never be cut short"
    );
}

/// The streak cut must STOP pass 2, not merely stop its Sturm calls.
///
/// Once the decisions are gone, pass 2's tree walk can only re-enumerate the
/// alphabet pass 1 already enumerated — on a second budget, for the same
/// nothing. `spent()` is what `grid_dfs` checks to unwind immediately.
#[test]
fn the_streak_cut_stops_pass_two_outright() {
    let st = ExactState::with(GRID_EXACT_SOLVES);
    assert!(!st.spent(), "pass 2 starts with work to do");
    for _ in 0..GRID_EXACT_EMPTY_STREAK {
        st.charge(&ExactOutcome::Empty);
    }
    assert!(
        st.spent(),
        "after the streak cut pass 2 must unwind rather than re-sweep"
    );
}

#[test]
fn dyadic_grid_search_declines_above_the_variable_cap() {
    use ay_core::term::TermStore;
    use ay_core::Sort;
    use ay_core::TheorySolver;
    let mut terms = TermStore::new();
    let vs: Vec<TermId> = (0..=GRID_MAX_VARS)
        .map(|i| terms.mk_var(format!("v{i}"), Sort::Real))
        .collect();
    let c1 = terms.mk_rational(rat(1));
    let prod = terms.mk_mul(vs.clone());
    let a1 = terms.mk_eq(prod, c1);
    let mut solver = NraSolver::new(&terms);
    solver.assert_literal(a1, true);
    let mut constraints: Vec<MultiConstraint> = Vec::new();
    for &(atom, value) in &solver.asserted {
        if let Some(MultiAtom::Constraint(c)) = solver.atom_to_multi(atom, value) {
            constraints.push(c);
        }
    }
    let mut root: VarBox = VarBox::default();
    for &v in &vs {
        root.insert(v, Interval::whole());
    }
    let before = solver.grid_budget.get();
    assert!(
        solver
            .dyadic_grid_search(&constraints, &vs, &root)
            .is_none(),
        "{}+ variables must be declined outright",
        GRID_MAX_VARS + 1
    );
    assert_eq!(
        solver.grid_budget.get(),
        before,
        "a declined call must cost nothing"
    );
}
