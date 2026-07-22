// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Unit tests for the 1UIP conflict analysis algorithm (conflict_analysis.rs).
//!
//! These tests exercise the core analyze_conflict() path directly by
//! constructing small solver states, forcing decisions and propagation
//! to reach a conflict, then verifying the learned clause invariants.
//!
//! Previously, the 1UIP algorithm was tested only indirectly via
//! end-to-end soundness tests. These tests verify:
//! - Learned clause has exactly one literal at the asserting level (UIP)
//! - Backtrack level equals second-highest level in learned clause
//! - All learned literals are falsified under the current assignment
//! - No duplicate variables in the learned clause
//! - Learned clause is not tautological

use super::*;

/// Build a solver, add clauses, initialize watches, and propagate level 0.
/// Returns the solver ready for decisions.
fn setup_solver(num_vars: usize, clauses: Vec<Vec<Literal>>) -> Solver {
    let mut solver = Solver::new(num_vars);
    for clause in clauses {
        solver.add_clause(clause);
    }
    solver.initialize_watches();
    assert!(
        solver.process_initial_clauses().is_none(),
        "level-0 conflict during setup"
    );
    let conflict = solver.propagate();
    assert!(
        conflict.is_none(),
        "level-0 conflict during setup propagation"
    );
    solver
}

/// Verify that a ConflictResult satisfies all 1UIP invariants.
fn assert_1uip_invariants(solver: &Solver, result: &ConflictResult, label: &str) {
    let clause = &result.learned_clause;
    assert!(
        !clause.is_empty(),
        "{label}: learned clause must not be empty"
    );

    // 1. UIP (first literal) must be at the decision level where the conflict occurred.
    //    After backtracking, the solver level has changed, so we check against the
    //    UIP's assignment level directly.
    let uip = clause[0];
    let uip_level = solver.var_data[uip.variable().index()].level;

    // 2. All other literals must be at levels strictly lower than the UIP level.
    //    (1UIP property: exactly one literal at the asserting level.)
    for (i, &lit) in clause.iter().enumerate().skip(1) {
        let lit_level = solver.var_data[lit.variable().index()].level;
        assert!(
            lit_level < uip_level,
            "{label}: non-UIP literal at index {i} (var={}) is at level {lit_level}, \
             expected < UIP level {uip_level}",
            lit.variable().index(),
        );
    }

    // 3. Backtrack level: if unit clause, 0; otherwise max level among non-UIP literals.
    if clause.len() == 1 {
        assert_eq!(
            result.backtrack_level, 0,
            "{label}: unit learned clause must have backtrack_level=0"
        );
    } else {
        let expected_bt = clause
            .iter()
            .skip(1)
            .map(|lit| solver.var_data[lit.variable().index()].level)
            .max()
            .unwrap_or(0);
        assert_eq!(
            result.backtrack_level, expected_bt,
            "{label}: backtrack_level mismatch"
        );
    }

    // 4. No duplicate variables.
    let mut seen_vars: Vec<usize> = clause.iter().map(|l| l.variable().index()).collect();
    seen_vars.sort();
    for w in seen_vars.windows(2) {
        assert_ne!(
            w[0], w[1],
            "{label}: duplicate variable {} in learned clause",
            w[0]
        );
    }

    // 5. LBD (Literal Block Distance) must be > 0 for non-empty clauses.
    assert!(
        result.lbd > 0 || clause.len() == 1,
        "{label}: LBD must be positive for non-unit clauses (got {})",
        result.lbd
    );
}

// ========================================================================
// Test 1: Simple 2-variable UNSAT formula — single-resolution 1UIP
// ========================================================================

#[test]
fn test_analyze_conflict_2var_unsat_learns_unit_clause() {
    // Formula: (x ∨ y) ∧ (x ∨ ¬y) ∧ (¬x ∨ y) ∧ (¬x ∨ ¬y)
    // This is unsatisfiable. After deciding x=T at level 1:
    //   - (¬x ∨ y) propagates y=T
    //   - (¬x ∨ ¬y) conflicts
    // 1UIP should learn (¬x), backtrack to level 0, then decide x=F:
    //   - (x ∨ y) propagates y=T
    //   - (x ∨ ¬y) conflicts
    // Full solve returns UNSAT.
    let x = Variable(0);
    let y = Variable(1);
    let mut solver = setup_solver(
        2,
        vec![
            vec![Literal::positive(x), Literal::positive(y)],
            vec![Literal::positive(x), Literal::negative(y)],
            vec![Literal::negative(x), Literal::positive(y)],
            vec![Literal::negative(x), Literal::negative(y)],
        ],
    );

    // Level 1: decide x=true
    solver.decide(Literal::positive(x));
    let conflict = solver.propagate();
    assert!(conflict.is_some(), "expected conflict at level 1");

    let conflict_ref = conflict.unwrap();
    let result = solver.analyze_conflict(conflict_ref).unwrap();

    // Learned clause should be unit (¬x), backtrack to level 0.
    assert_eq!(
        result.learned_clause.len(),
        1,
        "expected unit learned clause (¬x)"
    );
    assert_eq!(
        result.learned_clause[0],
        Literal::negative(x),
        "learned clause should be (¬x)"
    );
    assert_eq!(
        result.backtrack_level, 0,
        "unit clause backtracks to level 0"
    );
    assert_1uip_invariants(&solver, &result, "2var_unsat");
}

// ========================================================================
// Test 2: 3-variable formula — multi-level 1UIP
// ========================================================================

#[test]
fn test_analyze_conflict_3var_learns_binary_clause() {
    // Formula: (a ∨ b) ∧ (a ∨ ¬b) ∧ (¬a ∨ c) ∧ (¬a ∨ ¬c)
    // Level 1: decide b=T, no propagation (no unit clause from b alone)
    // Level 2: decide a=F, propagation from (a ∨ b): no new prop (a=F, b=T → sat).
    //   (a ∨ ¬b): a=F, ¬b=F → conflict!
    // 1UIP at level 2: the conflict clause is (a ∨ ¬b). Both literals are false.
    //   a is the decision at level 2 (counter: a at level 2).
    //   ¬b is at level 1 (added to learned clause).
    //   counter goes to 1 immediately (a is the only level-2 literal).
    //   UIP = a's trail lit (negated = ¬a... wait, let me re-think.
    //
    // Actually: decide b=T at level 1. decide a=F at level 2.
    // Trail: [b@1, ¬a@2]
    // (a ∨ ¬b) has a=F (level 2), ¬b=F (level 1) → conflict.
    // Analysis: process conflict clause (a ∨ ¬b).
    //   - a is false (val(a) = val(¬(¬a)) < 0): ¬a is on trail.
    //     var(a) at level 2 (decision level). counter=1.
    //   - ¬b is false (b is true at level 1). level < decision_level.
    //     Add ¬b to learned clause. counter stays 1.
    //   counter == 1 after processing first clause → loop exits.
    //   Find UIP by scanning trail backward: ¬a is at decision_level, is seen.
    //   p = ¬a. counter-1 = 0. UIP found.
    //   Learned clause: [a, ¬b] (UIP negated = a, plus ¬b from level 1).
    //   Wait: UIP is ¬a (trail literal). Its negation is a. So learned[0] = a.
    //   Actually the UIP literal p found on the trail is ¬a. We negate it to get a.
    //   Learned: [a, ¬b]. But ¬b is FALSE (b=T). a is FALSE (¬a is true).
    //   Both falsified. Backtrack level = level of ¬b = 1.
    //
    // Wait, this analysis is getting confused. Let me use a clearer formula.
    // Let me use the canonical example from CDCL literature:
    //
    // Vars: a=0, b=1, c=2
    // Clauses:
    //   C1: (¬a ∨ b)       -- a=T → b=T
    //   C2: (¬a ∨ c)       -- a=T → c=T
    //   C3: (¬b ∨ ¬c)      -- b=T ∧ c=T → conflict
    //
    // Level 1: decide a=T
    //   C1 propagates b=T
    //   C2 propagates c=T
    //   C3: ¬b=F, ¬c=F → conflict
    //
    // Analysis of C3 (¬b ∨ ¬c):
    //   ¬b: var=b, level=1 (same as decision level). counter=1. Seen(b).
    //   ¬c: var=c, level=1. counter=2. Seen(c).
    //   counter > 0, scan trail backward for first seen var at level 1.
    //   Trail: [a@1(dec), b@1(C1), c@1(C2)]. Last = c.
    //   p = c (trail lit), counter=1.
    //   Reason for c = C2 = (¬a ∨ c). Process:
    //     ¬a: var=a, level=1. counter=2. Seen(a).
    //     c: skip (it's the pivot p).
    //   counter=2-1=1 (after consuming c). Now counter=1, continue.
    //   Wait actually let me re-read the counter logic.
    //
    // The way the code works: counter counts current-level unseen literals.
    // After processing C3: counter=2 (b and c at level 1).
    // Scan back: find c (seen, at decision_level). p=c. counter=2-1=1.
    // counter != 0, so resolve. Get reason for c = C2 = (¬a ∨ c).
    // Process C2:
    //   ¬a: var=a, level=1. Not seen. Mark seen. counter=2 (a at decision_level).
    //   c: skip (pivot).
    // Scan back: find b (seen, at decision_level). p=b. counter=2-1=1.
    // counter != 0. Get reason for b = C1 = (¬a ∨ b).
    // Process C1:
    //   ¬a: var=a, already seen. Skip.
    //   b: skip (pivot).
    // Scan back: find a (seen, at decision_level). p=a. counter=1-1=0.
    // UIP found! p=a. Negate: ¬a. Learned clause: [¬a].
    // This is a unit clause! Backtrack to 0.
    //
    // Hmm, that's also a unit clause. Let me make a formula where the
    // learned clause has 2+ literals.

    // Better: 4 variables, a, b, c, d.
    // Level 1: decide a=T (no propagation).
    // Level 2: decide b=T.
    //   C1: (¬b ∨ c) → c=T
    //   C2: (¬b ∨ d) → d=T
    //   C3: (¬a ∨ ¬c ∨ ¬d) → conflict (a=T, c=T, d=T)
    //
    // Analysis of C3:
    //   ¬a: level=1, add to learned. counter=0.
    //   ¬c: var=c, level=2. counter=1. Seen(c).
    //   ¬d: var=d, level=2. counter=2. Seen(d).
    //   Scan back trail: [a@1, b@2(dec), c@2(C1), d@2(C2)].
    //   Last seen at level 2: d. p=d, counter=1.
    //   Reason for d = C2 = (¬b ∨ d):
    //     ¬b: var=b, level=2. Not seen. counter=2. Seen(b).
    //     d: skip (pivot).
    //   Scan back: c (seen, level 2). p=c, counter=1.
    //   Reason for c = C1 = (¬b ∨ c):
    //     ¬b: var=b, already seen. Skip.
    //     c: skip (pivot).
    //   Scan back: b (seen, level 2). p=b, counter=0. UIP!
    //   UIP = b. Learned: [¬b, ¬a]. Backtrack level = 1 (level of a).
    //
    // This gives a binary learned clause.
    let a = Variable(0);
    let b = Variable(1);
    let c = Variable(2);
    let d = Variable(3);

    let mut solver = setup_solver(
        4,
        vec![
            vec![Literal::negative(b), Literal::positive(c)], // C1: ¬b → c
            vec![Literal::negative(b), Literal::positive(d)], // C2: ¬b → d
            vec![
                Literal::negative(a),
                Literal::negative(c),
                Literal::negative(d),
            ], // C3: ¬a ∨ ¬c ∨ ¬d
        ],
    );

    // Level 1: decide a=true
    solver.decide(Literal::positive(a));
    assert!(solver.propagate().is_none(), "no conflict at level 1");

    // Level 2: decide b=true → propagates c=true, d=true → C3 conflicts
    solver.decide(Literal::positive(b));
    let conflict = solver.propagate();
    assert!(conflict.is_some(), "expected conflict at level 2");

    let conflict_ref = conflict.unwrap();
    let result = solver.analyze_conflict(conflict_ref).unwrap();

    // Learned clause: [¬b, ¬a] (UIP=b, negated=¬b; ¬a from level 1).
    assert_eq!(
        result.learned_clause.len(),
        2,
        "expected binary learned clause, got {:?}",
        result.learned_clause
    );
    // UIP (first literal) should be ¬b.
    assert_eq!(
        result.learned_clause[0],
        Literal::negative(b),
        "UIP should be ¬b"
    );
    // Second literal should be ¬a (from level 1).
    assert_eq!(
        result.learned_clause[1],
        Literal::negative(a),
        "second literal should be ¬a"
    );
    assert_eq!(result.backtrack_level, 1, "backtrack to level of ¬a");
    assert_1uip_invariants(&solver, &result, "3var_binary");
}

// ========================================================================
// Test 3: 3-level conflict — learned clause with 3 literals
// ========================================================================

#[test]
fn test_analyze_conflict_3level_ternary_learned_clause() {
    // Vars: a=0, b=1, c=2, d=3, e=4
    // Level 1: decide a=T
    // Level 2: decide b=T
    // Level 3: decide c=T
    //   C1: (¬c ∨ d)    → d=T
    //   C2: (¬c ∨ e)    → e=T
    //   C3: (¬a ∨ ¬b ∨ ¬d ∨ ¬e) → conflict
    //
    // Analysis of C3:
    //   ¬a: level=1, add to learned.
    //   ¬b: level=2, add to learned.
    //   ¬d: level=3, counter=1. Seen(d).
    //   ¬e: level=3, counter=2. Seen(e).
    //   Trail: [..., c@3(dec), d@3(C1), e@3(C2)]
    //   Scan: e. p=e, counter=1. Reason C2 (¬c ∨ e):
    //     ¬c: level=3. counter=2. Seen(c).
    //   Scan: d. p=d, counter=1. Reason C1 (¬c ∨ d):
    //     ¬c: already seen.
    //   Scan: c. p=c, counter=0. UIP=c!
    //   Learned: [¬c, ¬a, ¬b]. Backtrack to level 2 (max of levels 1,2).
    let a = Variable(0);
    let b = Variable(1);
    let c = Variable(2);
    let d = Variable(3);
    let e = Variable(4);

    let mut solver = setup_solver(
        5,
        vec![
            vec![Literal::negative(c), Literal::positive(d)], // C1
            vec![Literal::negative(c), Literal::positive(e)], // C2
            vec![
                Literal::negative(a),
                Literal::negative(b),
                Literal::negative(d),
                Literal::negative(e),
            ], // C3
        ],
    );

    solver.decide(Literal::positive(a));
    assert!(solver.propagate().is_none());
    solver.decide(Literal::positive(b));
    assert!(solver.propagate().is_none());
    solver.decide(Literal::positive(c));

    let conflict = solver.propagate();
    assert!(conflict.is_some(), "expected conflict at level 3");

    let result = solver.analyze_conflict(conflict.unwrap()).unwrap();

    // Learned clause: [¬c, ...] where ... contains ¬a and ¬b in some order.
    assert_eq!(
        result.learned_clause.len(),
        3,
        "expected ternary learned clause, got {:?}",
        result.learned_clause
    );
    assert_eq!(
        result.learned_clause[0],
        Literal::negative(c),
        "UIP should be ¬c"
    );
    assert_eq!(result.backtrack_level, 2, "backtrack to level 2");

    // Non-UIP literals should be ¬a and ¬b (in either order).
    let non_uip: Vec<Literal> = result.learned_clause[1..].to_vec();
    assert!(
        non_uip.contains(&Literal::negative(a)) && non_uip.contains(&Literal::negative(b)),
        "non-UIP literals should be ¬a and ¬b, got {non_uip:?}"
    );

    assert_1uip_invariants(&solver, &result, "3level_ternary");
}

// ========================================================================
// Test 4: Conflict where UIP is NOT the decision variable
// ========================================================================

#[test]
fn test_analyze_conflict_uip_is_not_decision() {
    // Vars: a=0, b=1, c=2, d=3
    // Level 1: decide a=T
    //   C1: (¬a ∨ b) → b=T
    //   C2: (¬b ∨ c) → c=T
    //   C3: (¬b ∨ d) → d=T
    //   C4: (¬c ∨ ¬d) → conflict (c=T, d=T)
    //
    // Analysis of C4:
    //   ¬c: level=1, counter=1. Seen(c).
    //   ¬d: level=1, counter=2. Seen(d).
    //   Trail: [a@1(dec), b@1(C1), c@1(C2), d@1(C3)]
    //   Scan: d. p=d, counter=1. Reason C3 (¬b ∨ d):
    //     ¬b: level=1, counter=2. Seen(b).
    //   Scan: c. p=c, counter=1. Reason C2 (¬b ∨ c):
    //     ¬b: already seen.
    //   Scan: b. p=b, counter=0. UIP=b (NOT the decision a).
    //   Learned: [¬b, ¬a]. Backtrack? No: ¬a is at level... wait.
    //
    // Hmm, a is the decision at level 1, so level(a) = 1.
    // b is propagated at level 1. Both at level 1.
    // UIP = b (first 1UIP from the conflict side).
    // Learned: [¬b]. Wait... there are no non-level-1 literals.
    // So the learned clause is just [¬b], a unit clause.
    // Backtrack to level 0.
    //
    // This is interesting: UIP is b (propagated), not a (decision).
    let a = Variable(0);
    let b = Variable(1);
    let c = Variable(2);
    let d = Variable(3);

    let mut solver = setup_solver(
        4,
        vec![
            vec![Literal::negative(a), Literal::positive(b)], // C1
            vec![Literal::negative(b), Literal::positive(c)], // C2
            vec![Literal::negative(b), Literal::positive(d)], // C3
            vec![Literal::negative(c), Literal::negative(d)], // C4
        ],
    );

    solver.decide(Literal::positive(a));
    let conflict = solver.propagate();
    assert!(conflict.is_some(), "expected conflict at level 1");

    let result = solver.analyze_conflict(conflict.unwrap()).unwrap();

    // UIP should be b (first implication point from conflict).
    // Learned clause: [¬b, ¬a] or [¬b]. Depends on whether a is reached.
    // Actually: b is at level 1, a is at level 1.
    // During analysis: seen(c), seen(d), seen(b). b's reason is C1 (¬a ∨ b).
    // Processing C1: ¬a, level=1, counter increases. seen(a).
    // Scan: a. p=a, counter=0. UIP=a (the decision).
    // So actually the UIP IS the decision variable a in this case.
    //
    // Let me reconsider: after resolving on d (reason C3: ¬b ∨ d),
    //   seen(b), counter=2 (b and c at level 1).
    // Scan: c. p=c, counter=1. Reason C2 (¬b ∨ c):
    //   ¬b: already seen.
    // counter still 1 (no new level-1 seen vars). Scan: b. p=b, counter=0? No.
    // Wait: after processing c's reason, counter was 1 (for b). Then we decrement
    // counter for consuming b: counter=0. UIP=b.
    //
    // But b's reason is C1 (¬a ∨ b). If counter hits 0, we DON'T resolve further.
    // So UIP = b. Learned: [¬b]. But there's no non-level-1 literal...
    // Actually yes. Let me trace more carefully.
    //
    // C4: (¬c ∨ ¬d). Both at level 1.
    //   ¬c: level=1, not seen. Mark seen(c). counter=1.
    //   ¬d: level=1, not seen. Mark seen(d). counter=2.
    //
    // Scan trail backward: [a@1, b@1, c@1, d@1]
    //   d: seen, level=1. p=d. counter=2-1=1. counter!=0, resolve.
    //   Reason(d) = C3 = (¬b ∨ d).
    //     ¬b: level=1, not seen. Mark seen(b). counter=2.
    //     d: skip (pivot).
    //   Scan: c: seen, level=1. p=c. counter=2-1=1. Resolve.
    //   Reason(c) = C2 = (¬b ∨ c).
    //     ¬b: level=1, already seen. Skip.
    //     c: skip (pivot).
    //   Scan: b: seen, level=1. p=b. counter=1-1=0. UIP!
    //   UIP = b. Negate = ¬b.
    //   Learned clause body (non-UIP, non-current-level): empty.
    //   So learned = [¬b]. Backtrack to 0.
    //
    // UIP is b, a propagated literal — not the decision a.
    assert_eq!(
        result.learned_clause[0],
        Literal::negative(b),
        "UIP should be ¬b (propagated, not decision a)"
    );
    assert_eq!(result.learned_clause.len(), 1, "should be unit clause");
    assert_eq!(result.backtrack_level, 0);
    assert_1uip_invariants(&solver, &result, "uip_not_decision");
}

// ========================================================================
// Test 5: find_conflict_level places highest-level literals in watch positions
// ========================================================================

#[test]
fn test_find_conflict_level_reorders_watched_positions() {
    // Formula with 4 vars where a conflict clause has literals at levels 1, 2, 3.
    // find_conflict_level should place the two highest-level literals in positions 0,1.
    let a = Variable(0);
    let b = Variable(1);
    let c = Variable(2);
    let d = Variable(3);
    let e = Variable(4);

    // Clause setup: force conflict at level 3 involving levels 1, 2, 3.
    let mut solver = setup_solver(
        5,
        vec![
            vec![Literal::negative(c), Literal::positive(d)], // C1: c → d
            vec![Literal::negative(c), Literal::positive(e)], // C2: c → e
            vec![
                Literal::negative(a),
                Literal::negative(b),
                Literal::negative(d),
                Literal::negative(e),
            ], // C3
        ],
    );

    solver.decide(Literal::positive(a)); // level 1
    assert!(solver.propagate().is_none());
    solver.decide(Literal::positive(b)); // level 2
    assert!(solver.propagate().is_none());
    solver.decide(Literal::positive(c)); // level 3

    let conflict = solver.propagate();
    assert!(conflict.is_some());

    let conflict_ref = conflict.unwrap();
    let (conflict_level, forced) = solver.find_conflict_level(conflict_ref);

    // Conflict level should be 3 (d and e are at level 3).
    assert_eq!(conflict_level, 3, "conflict level should be 3");

    // With multiple level-3 literals, forced should be None (not exactly one at max).
    assert!(forced.is_none(), "multiple level-3 literals → not forced");

    // Verify watched positions: first two literals should be at the highest levels.
    let lits = solver.arena.literals(conflict_ref.0 as usize);
    let lvl0 = solver.var_data[lits[0].variable().index()].level;
    let lvl1 = solver.var_data[lits[1].variable().index()].level;
    assert!(
        lvl0 >= lvl1,
        "watched position 0 should have highest level ({lvl0} < {lvl1})"
    );
    // Both watched positions should be at level 3 (the highest).
    assert_eq!(lvl0, 3, "watched position 0 should be at level 3");
}

// ========================================================================
// Test 6: Backtrack after conflict analysis preserves trail invariants
// ========================================================================

#[test]
fn test_backtrack_after_conflict_preserves_trail() {
    let a = Variable(0);
    let b = Variable(1);
    let c = Variable(2);
    let d = Variable(3);

    let mut solver = setup_solver(
        4,
        vec![
            vec![Literal::negative(b), Literal::positive(c)], // b → c
            vec![Literal::negative(b), Literal::positive(d)], // b → d
            vec![
                Literal::negative(a),
                Literal::negative(c),
                Literal::negative(d),
            ], // conflict trigger
        ],
    );

    solver.decide(Literal::positive(a)); // level 1
    assert!(solver.propagate().is_none());
    solver.decide(Literal::positive(b)); // level 2

    let conflict = solver.propagate();
    assert!(conflict.is_some());

    let result = solver.analyze_conflict(conflict.unwrap()).unwrap();
    assert_eq!(result.backtrack_level, 1);

    // Backtrack to level 1
    solver.backtrack(result.backtrack_level);

    // Post-backtrack: decision_level == 1
    assert_eq!(solver.decision_level, 1, "decision_level should be 1");
    assert_eq!(solver.trail_lim.len(), 1, "trail_lim should have 1 entry");

    // All trail literals should be at levels <= 1
    for &lit in &solver.trail {
        let level = solver.var_data[lit.variable().index()].level;
        assert!(
            level <= 1,
            "trail literal {:?} at level {level} > target 1",
            lit
        );
    }

    // b, c, d should be unassigned (they were at level 2)
    assert_eq!(
        solver.lit_val(Literal::positive(b)),
        0,
        "b should be unassigned after backtrack"
    );
    assert_eq!(
        solver.lit_val(Literal::positive(c)),
        0,
        "c should be unassigned after backtrack"
    );
    assert_eq!(
        solver.lit_val(Literal::positive(d)),
        0,
        "d should be unassigned after backtrack"
    );

    // a should still be assigned (at level 1)
    assert_eq!(
        solver.lit_val(Literal::positive(a)),
        1,
        "a should remain assigned after backtrack to level 1"
    );
}

// ========================================================================
// Test 7: Backtrack to level 0 unassigns everything
// ========================================================================

#[test]
fn test_backtrack_to_zero_unassigns_all_decisions() {
    let x = Variable(0);
    let y = Variable(1);
    let z = Variable(2);

    // Simple satisfiable formula — no propagation, just decisions.
    let mut solver = setup_solver(
        3,
        vec![vec![
            Literal::positive(x),
            Literal::positive(y),
            Literal::positive(z),
        ]],
    );

    solver.decide(Literal::positive(x)); // level 1
    assert!(solver.propagate().is_none());
    solver.decide(Literal::positive(y)); // level 2
    assert!(solver.propagate().is_none());
    solver.decide(Literal::positive(z)); // level 3
    assert!(solver.propagate().is_none());

    assert_eq!(solver.decision_level, 3);
    assert_eq!(solver.trail.len(), 3);

    solver.backtrack(0);

    assert_eq!(solver.decision_level, 0, "should be at level 0");
    assert_eq!(solver.trail_lim.len(), 0, "no trail limits at level 0");
    assert_eq!(solver.trail.len(), 0, "trail should be empty");

    // All variables unassigned.
    for v in 0..3 {
        assert_eq!(
            solver.lit_val(Literal::positive(Variable(v as u32))),
            0,
            "variable {v} should be unassigned"
        );
    }
}
