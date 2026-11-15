//! A weight with no negation in its width (`i64::MIN`, an ε-count of
//! `i64::MIN`) used to panic inside `Negate::negate`. Every caller now refuses
//! instead: the answer is "not decided", never a panic and never a wrong
//! (wrapped or saturated) weight.

use ay_diff_logic::{
    solve_int_atoms, AssertOutcome, BuildResult, DiffAtom, IStar, IncrementalDiffGraph, Op,
};

#[test]
fn an_unnegatable_int_constant_is_rejected_not_lowered() -> Result<(), String> {
    // `x >= i64::MIN` lowers to `0 - x <= -i64::MIN`, which has no i64.
    for op in [Op::Ge, Op::Gt, Op::Eq] {
        let atoms = [DiffAtom {
            lhs: 0,
            rhs: None,
            op,
            c: i64::MIN,
        }];
        match solve_int_atoms(&atoms) {
            BuildResult::Rejected => {}
            other => return Err(format!("{op:?} i64::MIN gave {other:?}; expected Rejected")),
        }
    }
    // The representable neighbour is still decided.
    let atoms = [DiffAtom {
        lhs: 0,
        rhs: None,
        op: Op::Ge,
        c: i64::MIN + 1,
    }];
    match solve_int_atoms(&atoms) {
        BuildResult::Sat { .. } => Ok(()),
        other => Err(format!("x >= i64::MIN + 1 gave {other:?}; expected Sat")),
    }
}

#[test]
fn an_unnegatable_potential_refuses_the_assert_and_keeps_the_graph() -> Result<(), String> {
    let mut g: IncrementalDiffGraph<IStar> = IncrementalDiffGraph::new(3);
    // 0 → 1 : (0, i64::MIN) would drive π(1) to an ε-count of i64::MIN, which
    // no later slack into vertex 1 could subtract.
    let deep = g.register_edge(0, 1, IStar::new(0, i64::MIN), 0);
    let got = g.assert_edge(deep);
    if got != AssertOutcome::Refused {
        return Err(format!(
            "π(1) = (0, i64::MIN) gave {got:?}; expected Refused"
        ));
    }
    if g.edge_is_active(deep) {
        return Err("a refused edge must stay inactive".into());
    }
    if g.model() != [IStar::new(0, 0); 3] {
        return Err(format!(
            "a refused edge moved the potentials: {:?}",
            g.model()
        ));
    }
    if !g.entailed_after_assert(deep, usize::MAX).is_empty() {
        return Err("an inactive edge entails nothing".into());
    }
    // The engine stays usable: the representable neighbour asserts, and an
    // edge into vertex 1 then subtracts its potential without trouble.
    let near = g.register_edge(0, 1, IStar::new(0, i64::MIN + 1), 1);
    let into = g.register_edge(2, 1, IStar::new(5, 0), 2);
    for (name, id) in [("near", near), ("into", into)] {
        match g.assert_edge(id) {
            AssertOutcome::Consistent => {}
            other => return Err(format!("{name} gave {other:?}; expected Consistent")),
        }
    }
    if !g.edge_is_satisfied(near) || !g.edge_is_satisfied(into) {
        return Err("asserted edges must be satisfied by the potential".into());
    }
    Ok(())
}
