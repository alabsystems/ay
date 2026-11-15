// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! LIA lazy propagations at the root, against the real `LiaSolver`.
//!
//! `LiaSolver::propagate` passes its inner LRA's lazy implied-bound
//! propagations through. A lazy reason is a theory-local handle, not a
//! clause, so a level-0 unit that keeps one gets no unit proof, and a level-0
//! conflict through it leaves the terminal chain incomplete
//! (`record_lrat_level0_conflict_chain`). With a proof consumer attached,
//! `resolve_lazy_propagation` therefore explains a decision-level-0 lazy
//! propagation at once through `TheorySolver::explain_level0_propagation`,
//! which `LiaSolver` forwards to its LRA, and delivers it eagerly with its
//! reason clause (`LazyResolution::Level0Explained`). These tests pin each
//! side of that branch:
//! * with proof tracking, a root-level lazy propagation is delivered eagerly
//!   with its reason clause, and nothing about it is left lazy;
//! * with proof tracking, a propagation above the root stays lazy (the proof
//!   tracker runs on every check-sat, so this is the ordinary search path);
//! * without proof tracking, a root-level propagation stays lazy.
//!
//! Ported from ce582849a (fix/replay-proof-budget), adapted to main's
//! `Level0Explained` path. Its first test also explained the proof-free lazy
//! token through `explain_lazy_reason`; that needs `LiaSolver` to forward
//! `explain_propagation`, the open item of the 2026-10-11 entry in
//! the development design notes, so only its lazy-delivery half is kept here.

use super::*;
use crate::proof_tracker::ProofTracker;
use ay_lia::LiaSolver;
use ay_sat::ExtPropagateResult;

type LiaSetup = (
    TermStore,
    HashMap<u32, TermId>,
    HashMap<TermId, u32>,
    Vec<TermId>,
    HashSet<TermId>,
);

/// Integer `x`, `y`; atoms `x + y <= 1` (var 1), `y >= 1` (var 2) and
/// `x <= 0` (var 3). With the first two asserted, the inner LRA derives
/// `x <= 0` through the row `x + y`: an implied bound, emitted lazily.
fn lia_setup() -> LiaSetup {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));
    let one = terms.mk_int(BigInt::from(1));
    let sum = terms.mk_add(vec![x, y]);
    let sum_le_1 = terms.mk_le(sum, one);
    let y_ge_1 = terms.mk_ge(y, one);
    let x_le_0 = terms.mk_le(x, zero);
    let var_to_term: HashMap<u32, TermId> = [(1, sum_le_1), (2, y_ge_1), (3, x_le_0)]
        .into_iter()
        .collect();
    let term_to_var: HashMap<TermId, u32> = [(sum_le_1, 1), (y_ge_1, 2), (x_le_0, 3)]
        .into_iter()
        .collect();
    let mut theory_atoms = vec![sum_le_1, y_ge_1, x_le_0];
    theory_atoms.sort_unstable_by_key(|term| term.0);
    let theory_atom_set: HashSet<TermId> = theory_atoms.iter().copied().collect();
    (
        terms,
        var_to_term,
        term_to_var,
        theory_atoms,
        theory_atom_set,
    )
}

fn premises() -> Vec<Literal> {
    vec![
        Literal::positive(Variable::new(1)),
        Literal::positive(Variable::new(2)),
    ]
}

fn x_le_0_literal() -> Literal {
    Literal::positive(Variable::new(3))
}

/// Run propagation rounds until the theory delivers something about `x <= 0`
/// (or the rounds run dry), returning the result of that round.
fn propagate_until_x_le_0<T: TheorySolver>(
    ext: &mut TheoryExtension<'_, T>,
    ctx: &MockContext,
) -> ExtPropagateResult {
    let target = x_le_0_literal();
    for _ in 0..8 {
        let r = ext.propagate(ctx);
        assert!(r.conflict.is_none(), "the premises are consistent: {r:?}");
        let delivered = r.propagations.iter().any(|(_, lit)| *lit == target)
            || r.lazy_propagations.iter().any(|(lit, _)| *lit == target);
        if delivered {
            return r;
        }
    }
    panic!("x <= 0 was never propagated from x + y <= 1, y >= 1");
}

fn is_lazy_x_le_0(r: &ExtPropagateResult) -> bool {
    r.lazy_propagations
        .iter()
        .any(|(lit, _)| *lit == x_le_0_literal())
}

/// Without a proof consumer the root-level propagation keeps the lazy path:
/// `Level0Explained` is a proof-tracking branch only.
#[test]
fn lia_lazy_root_propagation_stays_lazy_without_proofs() {
    let (terms, var_to_term, term_to_var, theory_atoms, theory_atom_set) = lia_setup();
    let mut theory = LiaSolver::new(&terms);
    let mut ext = TheoryExtension::new(
        &mut theory,
        &var_to_term,
        &term_to_var,
        &theory_atoms,
        &theory_atom_set,
        Some(&terms),
        None,
    );
    ext.init();
    let ctx = MockContext::new().with_level(0).with_trail(premises());
    let r = propagate_until_x_le_0(&mut ext, &ctx);
    assert!(
        is_lazy_x_le_0(&r),
        "without a proof consumer x <= 0 stays lazy, got {r:?}"
    );
    assert_eq!(ext.eager_stats.level0_lazy_explained, 0);
}

/// With a proof consumer, the same root-level propagation is explained while
/// the theory state still justifies it (`LiaSolver` forwards
/// `explain_level0_propagation` to its LRA) and delivered eagerly with its
/// explicit reason clause `x <= 0 ∨ ¬(x + y <= 1) ∨ ¬(y >= 1)`; nothing about
/// `x <= 0` is left lazy.
#[test]
fn lia_lazy_root_propagation_is_materialized_eagerly_with_proofs() {
    let (terms, var_to_term, term_to_var, theory_atoms, theory_atom_set) = lia_setup();
    let mut theory = LiaSolver::new(&terms);
    let mut tracker = ProofTracker::new();
    tracker.enable();
    tracker.set_theory("LIA");
    let negations = HashMap::default();
    let mut ext = TheoryExtension::new(
        &mut theory,
        &var_to_term,
        &term_to_var,
        &theory_atoms,
        &theory_atom_set,
        Some(&terms),
        None,
    )
    .with_proof_tracking(&mut tracker, &negations);
    ext.init();
    let ctx = MockContext::new().with_level(0).with_trail(premises());
    let r = propagate_until_x_le_0(&mut ext, &ctx);

    assert!(
        !is_lazy_x_le_0(&r),
        "a root-level lazy propagation must not reach the trail without a reason: {r:?}"
    );
    let (clause, _) = r
        .propagations
        .iter()
        .find(|(_, lit)| *lit == x_le_0_literal())
        .expect("x <= 0 is delivered eagerly");
    assert_eq!(clause[0], x_le_0_literal(), "propagated literal first");
    let mut reasons = clause[1..].to_vec();
    reasons.sort_by_key(|l| l.variable().id());
    assert_eq!(
        reasons,
        vec![
            Literal::negative(Variable::new(1)),
            Literal::negative(Variable::new(2))
        ],
        "the reason is the row bound and y's lower bound"
    );
    assert_eq!(ext.eager_stats.level0_lazy_explained, 1);
    assert_eq!(ext.eager_stats.level0_lazy_unexplained, 0);
}

/// Above the root nothing changes: a lazy propagation at decision level 1
/// stays lazy even with a proof consumer. Its reason is materialised on
/// demand, by conflict analysis.
#[test]
fn lia_lazy_propagation_above_root_stays_lazy_with_proofs() {
    let (terms, var_to_term, term_to_var, theory_atoms, theory_atom_set) = lia_setup();
    let mut theory = LiaSolver::new(&terms);
    let mut tracker = ProofTracker::new();
    tracker.enable();
    tracker.set_theory("LIA");
    let negations = HashMap::default();
    let mut ext = TheoryExtension::new(
        &mut theory,
        &var_to_term,
        &term_to_var,
        &theory_atoms,
        &theory_atom_set,
        Some(&terms),
        None,
    )
    .with_proof_tracking(&mut tracker, &negations);
    ext.init();
    // Settle an empty root first, then assert both premises at level 1.
    let root = MockContext::new().with_level(0);
    for _ in 0..8 {
        if ext.propagate(&root).clauses.is_empty() {
            break;
        }
    }
    let ctx = MockContext::new().with_level(1).with_trail(premises());
    let r = propagate_until_x_le_0(&mut ext, &ctx);
    assert!(
        is_lazy_x_le_0(&r),
        "above the root the lazy path is unchanged, got {r:?}"
    );
    assert!(
        r.propagations
            .iter()
            .all(|(_, lit)| *lit != x_le_0_literal()),
        "above the root x <= 0 is not delivered eagerly: {r:?}"
    );
    assert_eq!(ext.eager_stats.level0_lazy_explained, 0);
}
