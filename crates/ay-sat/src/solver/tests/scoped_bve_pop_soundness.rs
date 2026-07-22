// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression tests: scoped-BVE resolvents must not leak across `pop()`
//! (the "push/pop clause-leak").
//!
//! Mechanism: scoped clauses are stored as `[C, +S]` where `S` is the scope
//! selector. The former #8579 fixup assigned `vals[+S] = false` around
//! scoped BVE (`run_incremental_inprocessing`), so BVE's root-false literal
//! pruning STRIPPED the `+S` guard from every resolvent whose parents were
//! scoped clauses. Those resolvents were stored as IRREDUNDANT, GUARDLESS
//! clauses derived from the scope's assertions:
//!
//! - `gc_scoped_clauses` (pop) only deletes clauses containing `+S`;
//! - `gc_leaked_learned_clauses` (pop, Z3 PR #9221) only deletes LEARNED
//!   clauses;
//! - `restore_scoped_bve_eliminations` (pop) only reactivates eliminated
//!   variables.
//!
//! So the resolvent survived `pop()` inside the live clause DB — a clause
//! derived from a POPPED scope's assertions, able to flip a later
//! satisfiable check-sat to a spurious UNSAT. (It was masked only by the
//! arena-vs-ledger rebuild in `reset_search_state`, #7987 — an accidental
//! rescue, not a contract.) This is the soundness hazard documented by
//! downstream consumers (model-checker consumer k-induction / IC3
//! isolated-process re-verification workarounds).
//!
//! The fix: scope selectors stay unassigned in `vals[]` during BVE, so
//! resolvents inherit `+S` from their parents (the selector algebra IS the
//! "max assertion level among derivation ancestors" tag) and pop()'s
//! `gc_scoped_clauses` reclaims them.

use crate::solver::Solver;
use crate::{Literal, Variable};

fn pos(v: u32) -> Literal {
    Literal::positive(Variable(v))
}

fn neg(v: u32) -> Literal {
    Literal::negative(Variable(v))
}

/// Force the incremental-inprocessing scheduling gates open so the next
/// `solve()` runs `run_incremental_inprocessing` (including scoped BVE),
/// exactly as a long-running incremental session would after accumulating
/// conflicts. Mirrors `ic3_scoped_bve_clause_reduction` (#8503).
fn open_inprocessing_gates(s: &mut Solver) {
    s.cold.lifetime_conflicts = 100;
    s.cold.next_inprobe_conflict = 0;
    s.cold.last_inprobe_reduction = 0;
    s.cold.num_reductions = 1;
    s.inproc_ctrl.bve.enabled = true;
    s.inproc_ctrl.bve.next_conflict = 0;
}

/// Returns true if any ACTIVE arena clause has exactly the given literal set.
fn arena_has_clause(s: &Solver, lits: &[Literal]) -> bool {
    s.arena.active_indices().any(|idx| {
        let clause = s.arena.literals(idx);
        clause.len() == lits.len() && lits.iter().all(|l| clause.contains(l))
    })
}

/// Two-scope incremental session (the downstream k-induction script shape):
///
///   push; assert scope-1 clauses; check-sat;  pop;
///   push; assert scope-2 clauses; check-sat;  pop;
///
/// Scope 1 introduces a local variable `t` with occurrences
/// `[t, !v0]` and `[!t, !v1]` (stored with the `+S1` guard). Scoped BVE
/// eliminates `t`. With the guard-stripping bug, the resolvent `[!v0, !v1]`
/// (no `+S1`!) survives the pop as an irredundant clause; scope 2 asserting
/// `v0 & v1` then sees state derived from popped assertions.
#[test]
fn scoped_bve_resolvent_must_not_leak_across_pop() {
    let num_base_vars = 8usize; // v0..v7
    let mut s = Solver::new(num_base_vars);

    // Small base formula (satisfiable with everything true or false).
    s.add_clause(vec![pos(2), pos(3)]);
    s.add_clause(vec![neg(4), pos(5)]);

    // ── Scope 1 ─────────────────────────────────────────────────────────
    s.push();
    assert!(s.has_scoped_bve(), "push must enable scoped BVE");

    // Scope-local variable t (index above the scope-var floor).
    let t = s.new_var_internal();
    let ti = t.index() as u32;

    // Scoped assertions: (t | !v0) and (!t | !v1).
    // Under scope-1 semantics these imply (!v0 | !v1) — but ONLY inside
    // scope 1. Stored as [t, !v0, +S1] and [!t, !v1, +S1].
    s.add_clause(vec![pos(ti), neg(0)]);
    s.add_clause(vec![neg(ti), neg(1)]);

    // Open the inprocessing gates so this solve runs scoped BVE.
    open_inprocessing_gates(&mut s);

    let r1 = s.solve();
    assert!(
        r1.is_sat(),
        "scope 1 must be SAT (e.g. v0=v1=false), got {:?}",
        r1.result()
    );

    assert!(s.pop(), "pop of scope 1 must succeed");

    // STRUCTURAL SOUNDNESS: after pop, NO trace of scope 1 may remain that
    // constrains base variables. The guardless resolvent [!v0, !v1] is
    // exactly such a trace (derived from scope-1 assertions, no +S1 guard,
    // irredundant — none of the pop()-time sweeps remove it).
    assert!(
        !arena_has_clause(&s, &[neg(0), neg(1)]),
        "push/pop clause-leak: the scoped-BVE resolvent [!v0, !v1] lost its \
         +S1 scope guard and survived pop() in the live clause DB"
    );

    // ── Scope 2 ─────────────────────────────────────────────────────────
    // Asserts v0 AND v1. Together with the base clauses this is clearly
    // satisfiable: v0=v1=true, v2=true, v5=true.
    s.push();
    s.add_clause(vec![pos(0)]);
    s.add_clause(vec![pos(1)]);

    let r2 = s.solve();
    assert!(
        r2.is_sat(),
        "SOUNDNESS: scope 2 (v0 & v1 over a satisfiable base) must be SAT. \
         UNSAT means a clause derived from scope 1's popped assertions \
         leaked across pop(). got {:?}",
        r2.result()
    );
    assert!(s.pop());
}

/// Same leak through the IC3 fast path (`solve_incremental_ic3`), which
/// reaches `run_incremental_inprocessing` via `solve/ic3.rs` (#8503) and is
/// the production configuration where BVE is enabled in incremental mode
/// (`set_ic3_mode`).
#[test]
fn scoped_bve_resolvent_must_not_leak_across_pop_ic3_path() {
    let num_base_vars = 8usize;
    let mut s = Solver::new(num_base_vars);
    s.set_ic3_mode();

    s.add_clause(vec![pos(2), pos(3)]);

    s.push();
    assert!(s.has_scoped_bve());

    let t = s.new_var_internal();
    let ti = t.index() as u32;
    s.add_clause(vec![pos(ti), neg(0)]);
    s.add_clause(vec![neg(ti), neg(1)]);

    open_inprocessing_gates(&mut s);

    let r1 = s.solve_incremental_ic3(&[]);
    assert!(r1.is_sat(), "scope 1 must be SAT");

    assert!(s.pop());

    assert!(
        !arena_has_clause(&s, &[neg(0), neg(1)]),
        "push/pop clause-leak (IC3 path): the scoped-BVE resolvent \
         [!v0, !v1] lost its +S1 scope guard and survived pop()"
    );

    s.push();
    s.add_clause(vec![pos(0)]);
    s.add_clause(vec![pos(1)]);

    let r2 = s.solve_incremental_ic3(&[]);
    assert!(
        r2.is_sat(),
        "SOUNDNESS (IC3 path): scope 2 must be SAT; UNSAT means the \
         scoped-BVE resolvent leaked across pop()"
    );
    assert!(s.pop());
}

/// Unit-resolvent variant: scope-1 clauses `[t, !v0]` and `[!t, !v0]`
/// resolve to `[!v0]` once the `+S1` guard is stripped — a UNIT clause that
/// fixes a BASE variable at level 0 permanently. With the guard retained,
/// the resolvent is the binary `[!v0, +S1]`, which pop() reclaims.
#[test]
fn scoped_bve_unit_resolvent_must_not_fix_base_var_across_pop() {
    let num_base_vars = 8usize;
    let mut s = Solver::new(num_base_vars);

    s.add_clause(vec![pos(2), pos(3)]);

    s.push();
    let t = s.new_var_internal();
    let ti = t.index() as u32;
    s.add_clause(vec![pos(ti), neg(0)]);
    s.add_clause(vec![neg(ti), neg(0)]);

    open_inprocessing_gates(&mut s);

    let r1 = s.solve();
    assert!(r1.is_sat(), "scope 1 must be SAT (v0=false)");

    assert!(s.pop());

    // STRUCTURAL SOUNDNESS: v0 must not be constrained by leftover scope-1
    // derivations — no guardless unit clause [!v0] in the live DB.
    assert!(
        !arena_has_clause(&s, &[neg(0)]),
        "push/pop clause-leak: guardless unit resolvent [!v0] survived pop()"
    );

    s.push();
    s.add_clause(vec![pos(0)]);

    let r2 = s.solve();
    assert!(
        r2.is_sat(),
        "SOUNDNESS: v0 was only falsified by popped scope-1 assertions; \
         asserting v0 in scope 2 must be SAT, got {:?}",
        r2.result()
    );
    assert!(s.pop());
}

/// Positive control for the fix: the scoped-BVE resolvent must carry the
/// `+S1` guard while scope 1 is active (this is what makes pop() able to
/// reclaim it), and in-scope semantics must be preserved (asserting v0 & v1
/// INSIDE scope 1 is UNSAT).
#[test]
fn scoped_bve_resolvent_keeps_scope_guard_and_in_scope_semantics() {
    let num_base_vars = 8usize;
    let mut s = Solver::new(num_base_vars);

    s.add_clause(vec![pos(2), pos(3)]);

    s.push();
    let selector = *s
        .cold
        .scope_selectors
        .last()
        .expect("push must register a scope selector");
    let t = s.new_var_internal();
    let ti = t.index() as u32;
    s.add_clause(vec![pos(ti), neg(0)]);
    s.add_clause(vec![neg(ti), neg(1)]);

    open_inprocessing_gates(&mut s);

    let r1 = s.solve();
    assert!(r1.is_sat(), "scope 1 alone must be SAT");

    // If BVE eliminated t (it should — 2 occurrences, 1 resolvent), the
    // resolvent must be the GUARDED [!v0, !v1, +S1], not the bare [!v0, !v1].
    let guarded = arena_has_clause(&s, &[neg(0), neg(1), Literal::positive(selector)]);
    let bare = arena_has_clause(&s, &[neg(0), neg(1)]);
    assert!(
        !bare,
        "scoped-BVE resolvent lost its +S1 guard while the scope is active"
    );
    assert!(
        guarded || arena_has_clause(&s, &[pos(ti), neg(0), Literal::positive(selector)]),
        "expected either the guarded resolvent [!v0, !v1, +S1] (t eliminated) \
         or the original scoped clauses (t not eliminated) to be present"
    );

    // In-scope semantics: v0 & v1 contradicts the scoped assertions.
    s.add_clause(vec![pos(0)]);
    s.add_clause(vec![pos(1)]);
    let r2 = s.solve();
    assert!(
        r2.is_unsat(),
        "asserting v0 & v1 inside scope 1 must be UNSAT, got {:?}",
        r2.result()
    );

    assert!(s.pop());

    // And after pop, the same assertions are SAT again.
    s.push();
    s.add_clause(vec![pos(0)]);
    s.add_clause(vec![pos(1)]);
    let r3 = s.solve();
    assert!(
        r3.is_sat(),
        "after pop, v0 & v1 must be SAT again, got {:?}",
        r3.result()
    );
    assert!(s.pop());
}
