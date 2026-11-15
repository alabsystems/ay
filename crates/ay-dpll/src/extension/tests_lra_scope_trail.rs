// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! #lra-scope-trail: the eager extension's BCP batching window against the
//! real `LraSolver`.
//!
//! `propagate_impl` aligns the theory scope BEFORE it feeds a round's atoms,
//! and BCP batching (`prepare_bcp_check`, armed after `PHASE1_STREAK`
//! zero-propagation rounds without a backtrack) can return a round WITHOUT
//! running `check_during_propagate`. The next round, at the next decision
//! level, pushes the theory first and then checks — so the deferred atoms of
//! level k had their bounds trailed at theory scope k+1. A backjump to level
//! k (a learned clause `¬a_k ∨ ¬d_{k+1}` asserting at level k) popped scope
//! k+1 and with it those bounds, while SAT kept `a_k` assigned and the LRA
//! kept it in `asserted`/`bound_atoms`; nothing re-applied it, and the final
//! `check()` accepted models violating `a_k`.
//!
//! The streak is set directly (as the batching tests in `tests.rs` do); the
//! rest is the production sequence: propagate (deferred) → propagate (push +
//! check) → backtrack → propagate → check.

use super::*;
use ay_lra::LraSolver;

type LraSetup = (
    TermStore,
    HashMap<u32, TermId>,
    HashMap<TermId, u32>,
    Vec<TermId>,
    HashSet<TermId>,
);

/// `a = x >= 0` (var 1), `d = x + y <= -1` (var 2), `b = y >= 0` (var 3),
/// `e = z >= 0` (var 4).
///
/// `a ∧ b ∧ d` is infeasible only through the row `s = x + y` — no
/// same-variable bound axiom (`bound_axioms.rs`) makes the contradiction
/// Boolean-visible, so the SAT trail can carry all three and only the
/// simplex can refute them. (A same-variable pair such as `x >= 0`, `x < 0`
/// is covered by the generated axiom clause and never reaches the theory
/// both-true.)
fn lra_setup() -> LraSetup {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let z = terms.mk_var("z", Sort::Real);
    let zero = terms.mk_rational(BigRational::from(BigInt::from(0)));
    let minus_one = terms.mk_rational(BigRational::from(BigInt::from(-1)));
    let a = terms.mk_ge(x, zero);
    let sum = terms.mk_add(vec![x, y]);
    let d = terms.mk_le(sum, minus_one);
    let b = terms.mk_ge(y, zero);
    let e = terms.mk_ge(z, zero);
    let var_to_term: HashMap<u32, TermId> = [(1, a), (2, d), (3, b), (4, e)].into_iter().collect();
    let term_to_var: HashMap<TermId, u32> = [(a, 1), (d, 2), (b, 3), (e, 4)].into_iter().collect();
    let mut theory_atoms = vec![a, d, b, e];
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

/// Drain the level-0 round: registration-time axiom clauses come back first
/// (`take_pending_axiom_result`), then the level-0 facts are fed and checked.
fn settle_level_zero<T: TheorySolver>(ext: &mut TheoryExtension<'_, T>, ctx: &MockContext) {
    for _ in 0..8 {
        let r = ext.propagate(ctx);
        assert!(r.conflict.is_none(), "level 0 is consistent");
        if r.clauses.is_empty() {
            return;
        }
    }
    panic!("level 0 did not settle");
}

/// Drive the production sequence once: level 1 asserts `a` (single-atom
/// round), level 2 asserts `e`, backjump to level 1, level 1 asserts `d`.
/// Returns whether the contradiction `a ∧ b ∧ d` was refuted (by the
/// BCP-time check or the final check).
fn run_backjump_sequence(streak: u32) -> (u64, bool) {
    let (terms, var_to_term, term_to_var, theory_atoms, theory_atom_set) = lra_setup();
    let mut theory = LraSolver::new(&terms);
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

    let lit_a = Literal::positive(Variable::new(1));
    let lit_d = Literal::positive(Variable::new(2));
    let lit_b = Literal::positive(Variable::new(3));
    let lit_e = Literal::positive(Variable::new(4));

    // Level 0: `b` (y >= 0) is a unit fact.
    let ctx0 = MockContext::new().with_level(0).with_trail(vec![lit_b]);
    settle_level_zero(&mut ext, &ctx0);
    assert_eq!(ext.theory_level, 0);

    // The long conflict-free descent that arms BCP batching.
    ext.has_checked = true;
    ext.zero_propagation_streak = streak;

    // Level 1 decides `a` (x >= 0): a single-atom round.
    let ctx1 = MockContext::new()
        .with_level(1)
        .with_trail(vec![lit_b, lit_a]);
    let r1 = ext.propagate(&ctx1);
    assert!(r1.conflict.is_none());
    assert_eq!(ext.theory_level, 1);
    let defers = ext.eager_stats().batch_defers;

    // Level 2 decides `e` (z >= 0): the theory is pushed to scope 2 first,
    // then the check applies what is pending.
    let ctx2 = MockContext::new()
        .with_level(2)
        .with_trail(vec![lit_b, lit_a, lit_e]);
    let r2 = ext.propagate(&ctx2);
    assert!(r2.conflict.is_none());
    assert_eq!(ext.theory_level, 2);

    // A conflict at level 2 whose learned clause asserts at level 1: SAT
    // keeps `a`, the theory pops scope 2.
    ext.backtrack(1);
    assert_eq!(ext.theory_level, 1);

    // Level 1 continues with `d` (x + y <= -1): with `a` and `b` this is
    // infeasible (x >= 0, y >= 0, x + y <= -1) — through the row only.
    let ctx3 = MockContext::new()
        .with_level(1)
        .with_trail(vec![lit_b, lit_a, lit_d]);
    let r3 = ext.propagate(&ctx3);
    let bcp_conflict = r3.conflict.is_some();
    let final_check = ext.check(&ctx3);
    let refuted = bcp_conflict || matches!(final_check, ExtCheckResult::Conflict(_));
    (defers, refuted)
}

#[test]
fn a_batching_deferred_level_survives_a_backjump_into_that_level() {
    // PHASE1_STREAK: single-atom rounds are deferred.
    let (defers, refuted) = run_backjump_sequence(512);
    assert_eq!(
        defers, 1,
        "the single-atom level-1 round must be batch-deferred for this test to exercise the window"
    );
    assert!(
        refuted,
        "x >= 0 (level 1, batch-deferred, applied by level 2's check) with y >= 0 (level 0) \
         and x + y <= -1 (level 1) must be refuted after the backjump popped the scope that \
         applied the deferred bound"
    );
}

/// The same sequence without batching (the streak below `PHASE1_STREAK`):
/// each round checks at its own level, the bound is trailed at scope 1 and
/// the contradiction is found. Documents that the window is the deferral.
#[test]
fn without_batching_each_level_is_checked_in_its_own_scope() {
    let (defers, refuted) = run_backjump_sequence(5);
    assert_eq!(defers, 0);
    assert!(refuted);
}
