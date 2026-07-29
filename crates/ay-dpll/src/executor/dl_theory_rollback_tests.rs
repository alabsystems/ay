// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Adversarial `push` / `pop` / `reset` conformance tests for
//! [`super::dl_theory::DiffLogicTheory`].
//!
//! `dl_theory_tests` pins the *lowering* (which half-plane each polarity means).
//! This module pins the *scope discipline* — the part of the trait contract
//! (`ay_core::TheorySolver::push`, crates/ay-core/src/theory/mod.rs) that is
//! invisible in a single-shot query and only shows up when the DPLL search
//! backtracks:
//!
//! * `pop()` logically retracts every `assert_literal` since the matching
//!   `push()` — checked against a FRESH solver given only the surviving
//!   assertions (the contract's "behavioral equivalence" property);
//! * no pending state (conflict, split request, propagation buffer, fail-closed
//!   mark) survives into a search branch that no longer entails it;
//! * conversely, no pending state is DISCARDED while the literal that caused it
//!   is still asserted. That direction is the dangerous one for this theory: a
//!   negated equality contributes NO edge to the graph, so the pending record is
//!   the solver's only memory of it, and the DPLL layer never re-notifies an
//!   assignment that survives a backjump (see `extension/mod.rs` `backtrack`).
//!   Losing the record turns the next `check()` into a `Sat` for a constraint
//!   set the solver never constrained;
//! * an unmatched or extra `pop()` is a no-op, not a panic and not a silent
//!   state wipe;
//! * `reset()` clears every assertion-derived buffer.

use ay_core::{Sort, TermId, TermStore, TheoryResult, TheorySolver};
use num_bigint::BigInt;
use num_rational::BigRational;

use ay_diff_logic::RStar;

/// See `dl_theory_tests`: these scope/rollback tests pin behaviour that is
/// independent of the weight representation, so they run on the exact-rational
/// lane only.
type DiffLogicTheory<'a> = super::dl_theory::DiffLogicTheory<'a, RStar>;

/// Three Real variables — enough for a cycle that is not just a two-atom pair.
struct Fx {
    terms: TermStore,
    x: TermId,
    y: TermId,
    z: TermId,
}

impl Fx {
    fn new() -> Self {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Real);
        let y = terms.mk_var("y", Sort::Real);
        let z = terms.mk_var("z", Sort::Real);
        Self { terms, x, y, z }
    }

    fn real(&mut self, n: i64) -> TermId {
        self.terms.mk_rational(BigRational::from(BigInt::from(n)))
    }

    /// `a − b <= c`
    fn diff_le(&mut self, a: TermId, b: TermId, c: i64) -> TermId {
        let d = self.terms.mk_sub(vec![a, b]);
        let k = self.real(c);
        self.terms.mk_le(d, k)
    }
}

fn is_sat(r: &TheoryResult) -> bool {
    matches!(r, TheoryResult::Sat)
}

fn is_unsat(r: &TheoryResult) -> bool {
    matches!(r, TheoryResult::Unsat(lits) if !lits.is_empty())
}

fn is_unknown(r: &TheoryResult) -> bool {
    matches!(r, TheoryResult::Unknown)
}

/// Short label for a verdict, so equivalence assertions report what differed.
fn label(r: &TheoryResult) -> String {
    match r {
        TheoryResult::Sat => "sat".to_string(),
        TheoryResult::Unsat(_) => "unsat".to_string(),
        TheoryResult::Unknown => "unknown".to_string(),
        TheoryResult::NeedExpressionSplit(s) => format!("split({:?})", s.disequality_term),
        other => format!("{other:?}"),
    }
}

/// The contract's behavioral-equivalence oracle: a fresh solver fed exactly the
/// assertions that survive, with no push/pop at all.
fn fresh_verdict(fx: &Fx, lits: &[(TermId, bool)]) -> TheoryResult {
    let mut th = DiffLogicTheory::new(&fx.terms);
    for &(t, v) in lits {
        th.assert_literal(t, v);
    }
    th.check()
}

// ---------------------------------------------------------------------------
// pop() retracts exactly the scope's assertions
// ---------------------------------------------------------------------------

#[test]
fn pop_matches_a_fresh_solver_over_the_surviving_assertions() {
    // x − y <= 0 at level 0, y − z <= 0 at level 1, z − x <= −1 at level 2.
    // The three together are a negative cycle; any prefix is satisfiable.
    let mut fx = Fx::new();
    let (x, y, z) = (fx.x, fx.y, fx.z);
    let a = fx.diff_le(x, y, 0);
    let b = fx.diff_le(y, z, 0);
    let c = fx.diff_le(z, x, -1);

    let mut th = DiffLogicTheory::new(&fx.terms);
    th.assert_literal(a, true);
    th.push();
    th.assert_literal(b, true);
    th.push();
    th.assert_literal(c, true);
    assert!(is_unsat(&th.check()), "the 3-cycle must conflict");

    th.pop();
    assert_eq!(
        label(&th.check()),
        label(&fresh_verdict(&fx, &[(a, true), (b, true)])),
        "after one pop the solver must behave as if only a,b were asserted"
    );

    th.pop();
    assert_eq!(
        label(&th.check()),
        label(&fresh_verdict(&fx, &[(a, true)])),
        "after two pops the solver must behave as if only a was asserted"
    );

    // The retracted literals can be re-asserted, re-deriving the conflict —
    // proving pop() really deactivated the edges rather than just hiding the
    // verdict.
    th.push();
    th.assert_literal(b, true);
    th.assert_literal(c, true);
    assert!(is_unsat(&th.check()));
}

#[test]
fn conflict_survives_a_pop_that_does_not_retract_its_literals() {
    // The other direction: a conflict whose literals all live at surviving
    // depths must NOT be forgotten by an unrelated pop.
    let mut fx = Fx::new();
    let (x, y) = (fx.x, fx.y);
    let a = fx.diff_le(x, y, 0);
    let b = fx.diff_le(y, x, -1);

    let mut th = DiffLogicTheory::new(&fx.terms);
    th.push(); // depth 1
    th.assert_literal(a, true);
    th.assert_literal(b, true);
    assert!(is_unsat(&th.check()));

    th.push(); // depth 2, asserts nothing
    assert!(is_unsat(&th.check()));
    th.pop(); // back to depth 1: both literals still asserted
    assert!(
        is_unsat(&th.check()),
        "popping a scope that asserted nothing must not clear the conflict"
    );

    th.pop(); // back to depth 0: both literals retracted
    assert!(is_sat(&th.check()));
}

#[test]
fn stale_conflict_cannot_leak_into_a_different_branch() {
    // assert, push, assert-to-conflict, pop, assert a DIFFERENT literal.
    // The second branch is satisfiable and must be reported as such.
    let mut fx = Fx::new();
    let (x, y) = (fx.x, fx.y);
    let a = fx.diff_le(x, y, 0);
    let bad = fx.diff_le(y, x, -1); // contradicts a
    let ok = fx.diff_le(y, x, 5); // consistent with a

    let mut th = DiffLogicTheory::new(&fx.terms);
    th.assert_literal(a, true);
    th.push();
    th.assert_literal(bad, true);
    assert!(is_unsat(&th.check()));
    th.pop();
    th.push();
    th.assert_literal(ok, true);
    assert_eq!(
        label(&th.check()),
        label(&fresh_verdict(&fx, &[(a, true), (ok, true)])),
        "the conflict from the abandoned branch leaked"
    );
}

#[test]
fn conflict_detected_without_check_is_still_retracted_by_pop() {
    // The DPLL layer may backjump on a conflict found by ANOTHER extension
    // before it ever calls check() here. The pending conflict must still be
    // scoped correctly.
    let mut fx = Fx::new();
    let (x, y) = (fx.x, fx.y);
    let a = fx.diff_le(x, y, 0);
    let b = fx.diff_le(y, x, -1);

    let mut th = DiffLogicTheory::new(&fx.terms);
    th.assert_literal(a, true);
    th.push();
    th.assert_literal(b, true); // conflict recorded, never observed
    th.pop();
    assert!(is_sat(&th.check()));
}

// ---------------------------------------------------------------------------
// Unmatched / extra pop
// ---------------------------------------------------------------------------

#[test]
fn extra_pop_is_a_no_op_and_keeps_level_zero_state() {
    let mut fx = Fx::new();
    let (x, y) = (fx.x, fx.y);
    let a = fx.diff_le(x, y, 0);
    let b = fx.diff_le(y, x, -1);

    let mut th = DiffLogicTheory::new(&fx.terms);
    th.assert_literal(a, true);
    th.assert_literal(b, true);
    assert!(is_unsat(&th.check()));

    // No matching push exists: these must not retract the level-0 assertions.
    th.pop();
    th.pop();
    th.pop();
    assert!(
        is_unsat(&th.check()),
        "an unmatched pop must be a no-op, not a retraction"
    );

    // ... and the solver is still usable afterwards.
    th.push();
    th.pop();
    assert!(is_unsat(&th.check()));
}

#[test]
fn pop_past_the_bottom_then_push_again_stays_in_sync() {
    let mut fx = Fx::new();
    let (x, y) = (fx.x, fx.y);
    let a = fx.diff_le(x, y, 0);
    let b = fx.diff_le(y, x, -1);

    let mut th = DiffLogicTheory::new(&fx.terms);
    th.push();
    th.assert_literal(a, true);
    th.pop();
    th.pop(); // one too many
    th.pop(); // and another
    th.push();
    th.assert_literal(b, true);
    assert_eq!(
        label(&th.check()),
        label(&fresh_verdict(&fx, &[(b, true)])),
        "extra pops desynchronised the graph scope from the theory scope"
    );
    th.pop();
    assert!(is_sat(&th.check()));
}

// ---------------------------------------------------------------------------
// Pending split request (negated equality) — the record IS the constraint
// ---------------------------------------------------------------------------

#[test]
fn negated_equality_is_refused() {
    let mut fx = Fx::new();
    let (x, y) = (fx.x, fx.y);
    let eq = fx.terms.mk_eq(x, y);
    let mut th = DiffLogicTheory::new(&fx.terms);
    th.assert_literal(eq, false);
    // Fail closed: the disjunction is refused outright, never approximated.
    assert!(is_unknown(&th.check()));
}

#[test]
fn pop_does_not_drop_a_refusal_from_a_surviving_scope() {
    // `not (x = y)` contributes NO edge; the pending record is the theory's only
    // memory of it. Asserted at depth 0, it must survive a pop of a deeper scope
    // — otherwise the constraint is lost forever (the DPLL layer does not
    // re-notify surviving assignments) and check() answers Sat for an assertion
    // set it never constrained.
    let mut fx = Fx::new();
    let (x, y) = (fx.x, fx.y);
    let eq = fx.terms.mk_eq(x, y);
    let filler = fx.diff_le(x, y, 3);

    let mut th = DiffLogicTheory::new(&fx.terms);
    th.assert_literal(eq, false); // depth 0
    th.push(); // depth 1
    th.assert_literal(filler, true);
    th.pop(); // retracts `filler` ONLY

    assert!(
        is_unknown(&th.check()),
        "the disequality asserted at depth 0 was silently dropped by the pop"
    );
}

#[test]
fn unmatched_pop_does_not_drop_a_refusal() {
    let mut fx = Fx::new();
    let (x, y) = (fx.x, fx.y);
    let eq = fx.terms.mk_eq(x, y);

    let mut th = DiffLogicTheory::new(&fx.terms);
    th.assert_literal(eq, false);
    th.pop(); // no matching push: a no-op per the trait contract
    assert!(
        is_unknown(&th.check()),
        "an unmatched pop discarded the refusal"
    );
}

#[test]
fn pop_does_drop_a_split_request_from_the_popped_scope() {
    // The other direction: a disequality asserted INSIDE the popped scope is
    // retracted with it, so the split must not be requested afterwards.
    let mut fx = Fx::new();
    let (x, y) = (fx.x, fx.y);
    let eq = fx.terms.mk_eq(x, y);

    let mut th = DiffLogicTheory::new(&fx.terms);
    th.push();
    th.assert_literal(eq, false);
    th.pop();
    assert!(
        is_sat(&th.check()),
        "a disequality retracted by pop must not still request a split"
    );
}

#[test]
fn conflict_outranks_a_refusal() {
    // A negative cycle and an unmodellable literal at the same time. `check()`
    // must report the CONFLICT: it is a cycle among ACTIVE edges only, hence a
    // subset of the genuinely asserted constraints, and a subset of an
    // infeasible set is still infeasible. Answering `Unknown` instead would
    // throw away a completed refutation and make simplex re-derive it.
    let mut fx = Fx::new();
    let (x, y, z) = (fx.x, fx.y, fx.z);
    let eq = fx.terms.mk_eq(y, z);
    let a = fx.diff_le(x, y, 0);
    let b = fx.diff_le(y, x, -1);

    let mut th = DiffLogicTheory::new(&fx.terms);
    th.assert_literal(eq, false); // refused: negated equality
    th.assert_literal(a, true);
    th.assert_literal(b, true); // negative cycle
    assert!(
        is_unsat(&th.check()),
        "a live conflict was masked by the pending split request"
    );
    // And the refutation survives an unmatched pop.
    th.pop(); // no-op at depth 0
    assert!(is_unsat(&th.check()));
}

// ---------------------------------------------------------------------------
// Fail-closed mark
// ---------------------------------------------------------------------------

#[test]
fn unsupported_mark_is_scoped_to_the_asserting_literal() {
    let mut fx = Fx::new();
    let (x, y) = (fx.x, fx.y);
    let sum = fx.terms.mk_add(vec![x, y]);
    let three = fx.real(3);
    let not_dl = fx.terms.mk_le(sum, three);

    let mut th = DiffLogicTheory::new(&fx.terms);
    th.push();
    th.push();
    th.assert_literal(not_dl, true);
    assert!(is_unknown(&th.check()));
    th.pop();
    assert!(
        is_sat(&th.check()),
        "the fail-closed mark outlived the literal that raised it"
    );
    th.pop();
    assert!(is_sat(&th.check()));
}

#[test]
fn unsupported_mark_raised_at_depth_zero_survives_an_unmatched_pop() {
    let mut fx = Fx::new();
    let (x, y) = (fx.x, fx.y);
    let sum = fx.terms.mk_add(vec![x, y]);
    let three = fx.real(3);
    let not_dl = fx.terms.mk_le(sum, three);

    let mut th = DiffLogicTheory::new(&fx.terms);
    th.assert_literal(not_dl, true);
    th.pop();
    assert!(
        is_unknown(&th.check()),
        "an unmatched pop cleared a fail-closed mark whose literal is still asserted"
    );
}

#[test]
fn unsupported_mark_raised_deep_does_not_hide_the_outer_one() {
    // Raised at depth 1 and again at depth 2; popping to depth 1 must keep the
    // mark (its literal is still asserted).
    let mut fx = Fx::new();
    let (x, y) = (fx.x, fx.y);
    let sum = fx.terms.mk_add(vec![x, y]);
    let three = fx.real(3);
    let four = fx.real(4);
    let bad1 = fx.terms.mk_le(sum, three);
    let bad2 = fx.terms.mk_le(sum, four);

    let mut th = DiffLogicTheory::new(&fx.terms);
    th.push();
    th.assert_literal(bad1, true);
    th.push();
    th.assert_literal(bad2, true);
    assert!(is_unknown(&th.check()));
    th.pop();
    assert!(is_unknown(&th.check()), "bad1 is still asserted at depth 1");
    th.pop();
    assert!(is_sat(&th.check()));
}

// ---------------------------------------------------------------------------
// reset()
// ---------------------------------------------------------------------------

#[test]
fn reset_clears_a_pending_split_request() {
    // `reset` is reached through `soft_reset` on every SAT restart. A split
    // request keyed to the pre-restart assertion set must not fire against the
    // new one — it would mask the real verdict of the first check after the
    // restart.
    let mut fx = Fx::new();
    let (x, y) = (fx.x, fx.y);
    let eq = fx.terms.mk_eq(x, y);

    let mut th = DiffLogicTheory::new(&fx.terms);
    th.assert_literal(eq, false);
    th.reset();
    assert!(
        is_sat(&th.check()),
        "a split request survived reset() and fired against an empty assertion set"
    );
}

#[test]
fn reset_clears_pending_propagations() {
    // Propagations are justified by the reasons that were asserted when they
    // were found. After a reset those reasons are retracted, so delivering the
    // propagation would assign a literal with an unassigned justification.
    let mut fx = Fx::new();
    let (x, y, z) = (fx.x, fx.y, fx.z);
    // x − y <= 0 and y − z <= 0 entail x − z <= 0 (registered, unasserted).
    let a = fx.diff_le(x, y, 0);
    let b = fx.diff_le(y, z, 0);
    let implied = fx.diff_le(x, z, 5);

    let mut th = DiffLogicTheory::new(&fx.terms);
    th.set_prop_budget_for_test(64);
    th.register_atom(a);
    th.register_atom(b);
    th.register_atom(implied);
    th.assert_literal(a, true);
    th.assert_literal(b, true);

    th.reset();
    assert!(
        th.propagate().is_empty(),
        "propagations from the pre-reset assertion set survived reset()"
    );
}

#[test]
fn pop_clears_pending_propagations() {
    let mut fx = Fx::new();
    let (x, y, z) = (fx.x, fx.y, fx.z);
    let a = fx.diff_le(x, y, 0);
    let b = fx.diff_le(y, z, 0);
    let implied = fx.diff_le(x, z, 5);

    let mut th = DiffLogicTheory::new(&fx.terms);
    th.set_prop_budget_for_test(64);
    th.register_atom(a);
    th.register_atom(b);
    th.register_atom(implied);
    th.assert_literal(a, true);
    th.push();
    th.assert_literal(b, true);
    th.pop();
    assert!(
        th.propagate().is_empty(),
        "propagations derived inside the popped scope leaked out of it"
    );
}

#[test]
fn reset_after_a_conflict_leaves_a_usable_solver() {
    let mut fx = Fx::new();
    let (x, y, z) = (fx.x, fx.y, fx.z);
    let a = fx.diff_le(x, y, 0);
    let b = fx.diff_le(y, x, -1);
    let c = fx.diff_le(y, z, 0);

    let mut th = DiffLogicTheory::new(&fx.terms);
    th.push();
    th.push();
    th.assert_literal(a, true);
    th.assert_literal(b, true);
    assert!(is_unsat(&th.check()));

    // reset() from inside two open scopes: depth, marks and the graph trail all
    // have to come back to zero together.
    th.reset();
    assert!(is_sat(&th.check()));
    th.assert_literal(a, true);
    th.assert_literal(c, true);
    assert_eq!(
        label(&th.check()),
        label(&fresh_verdict(&fx, &[(a, true), (c, true)])),
    );
    // A pop after reset must not underflow or resurrect anything.
    th.pop();
    assert!(is_sat(&th.check()));
}

// ---------------------------------------------------------------------------
// Repeated assertion of the same literal across scopes
// ---------------------------------------------------------------------------

#[test]
fn reasserting_a_surviving_literal_in_a_deeper_scope_is_idempotent() {
    // `extension/mod.rs` re-flushes atoms after a backjump, so the same literal
    // is asserted again in a deeper scope. Popping that scope must not
    // deactivate the ORIGINAL, still-live assertion.
    let mut fx = Fx::new();
    let (x, y) = (fx.x, fx.y);
    let a = fx.diff_le(x, y, 0);
    let b = fx.diff_le(y, x, -1);

    let mut th = DiffLogicTheory::new(&fx.terms);
    th.assert_literal(a, true); // depth 0
    th.push();
    th.assert_literal(a, true); // duplicate, depth 1
    th.assert_literal(a, true); // and again
    th.pop();

    // `a` is still asserted, so `b` must still conflict with it.
    th.assert_literal(b, true);
    assert!(
        is_unsat(&th.check()),
        "popping a duplicate assertion retracted the surviving original"
    );
}

#[test]
fn model_extraction_after_pop_ignores_retracted_edges() {
    use num_traits::Zero;
    // The slack scan that picks δ walks the adapter's own active-edge list; a
    // stale entry there would compute δ from a constraint that no longer holds.
    let mut fx = Fx::new();
    let (x, y, z) = (fx.x, fx.y, fx.z);
    let x_lt_y = fx.terms.mk_lt(x, y);
    let tight = fx.diff_le(z, x, -1000);

    let mut th = DiffLogicTheory::new(&fx.terms);
    th.assert_literal(x_lt_y, true);
    th.push();
    th.assert_literal(tight, true);
    th.pop();
    assert!(is_sat(&th.check()));

    let model = th.extract_model();
    let get = |t| {
        model
            .values
            .get(&t)
            .cloned()
            .unwrap_or_else(BigRational::zero)
    };
    assert!(get(x) < get(y), "the surviving strict constraint was lost");
}
