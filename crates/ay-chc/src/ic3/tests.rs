// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Unit tests for clause-level IC3 (#8211).
//!
//! Tests cover basic IC3 functionality on small transition systems:
//! - Trivially safe (bad state unreachable from init)
//! - Trivially unsafe (bad state = initial state)
//! - Simple latch toggle (1-bit counter)
//! - 2-bit counter reaching a specific state

use super::solver::{Ic3Result, Ic3Solver};
use super::transition_system::BitLevelTransitionSystem;
use ay_sat::{Literal, Variable};

/// Helper: create variables for a small transition system.
/// Returns (state_vars, input_vars, next_vars, total_vars_count).
fn make_vars(
    num_state: usize,
    num_input: usize,
) -> (Vec<Variable>, Vec<Variable>, Vec<Variable>, usize) {
    let mut next_id = 0u32;
    let state_vars: Vec<Variable> = (0..num_state)
        .map(|_| {
            let v = Variable::new(next_id);
            next_id += 1;
            v
        })
        .collect();
    let input_vars: Vec<Variable> = (0..num_input)
        .map(|_| {
            let v = Variable::new(next_id);
            next_id += 1;
            v
        })
        .collect();
    let next_vars: Vec<Variable> = (0..num_state)
        .map(|_| {
            let v = Variable::new(next_id);
            next_id += 1;
            v
        })
        .collect();
    (state_vars, input_vars, next_vars, next_id as usize)
}

/// Test: trivially safe system.
///
/// Single state variable x. Init: x=0. Trans: x'=x (stays the same).
/// Bad: x=1. Since x starts at 0 and never changes, bad is unreachable.
#[test]
fn test_ic3_trivially_safe() {
    let (sv, iv, nv, total) = make_vars(1, 0);
    let x = sv[0];
    let x_next = nv[0];

    // Init: x = 0 (negated literal for x).
    let init_clauses = vec![vec![Literal::negative(x)]];

    // Trans: x' = x. Encoded as: (x => x') /\ (not-x => not-x')
    // CNF: (not-x OR x') /\ (x OR not-x')
    let trans_clauses = vec![
        vec![Literal::negative(x), Literal::positive(x_next)],
        vec![Literal::positive(x), Literal::negative(x_next)],
    ];

    // Bad: x = 1.
    let bad_literals = vec![Literal::positive(x)];

    let ts = BitLevelTransitionSystem::new(
        1,
        0,
        sv,
        nv,
        iv,
        init_clauses,
        trans_clauses,
        bad_literals,
        total,
    );

    let mut solver = Ic3Solver::new(ts, false);
    let result = solver.solve();

    match result {
        Ic3Result::Safe { .. } => {} // expected
        other => panic!("expected Safe, got {other:?}"),
    }
}

/// A past/immediate deadline preempts the search at a loop head and yields the
/// explicit `Unknown` — never a truncated `Safe`/`Unsafe`. A far-future deadline
/// is inert (the same TS still proves `Safe`), so the plumbing does not perturb
/// normal verdicts.
#[test]
fn test_ic3_deadline_yields_unknown_not_a_truncated_verdict() {
    // Same trivially-SAFE system as test_ic3_trivially_safe (x=0, x'=x, bad x=1).
    let build_ts = || {
        let (sv, iv, nv, total) = make_vars(1, 0);
        let x = sv[0];
        let x_next = nv[0];
        let init_clauses = vec![vec![Literal::negative(x)]];
        let trans_clauses = vec![
            vec![Literal::negative(x), Literal::positive(x_next)],
            vec![Literal::positive(x), Literal::negative(x_next)],
        ];
        let bad_literals = vec![Literal::positive(x)];
        BitLevelTransitionSystem::new(
            1,
            0,
            sv,
            nv,
            iv,
            init_clauses,
            trans_clauses,
            bad_literals,
            total,
        )
    };

    // Already-expired deadline: must return Unknown, not the Safe it would prove.
    let expired = ay_core::time::Instant::now();
    let mut solver = Ic3Solver::new(build_ts(), false).with_deadline(Some(expired));
    match solver.solve() {
        Ic3Result::Unknown => {}
        other => panic!("expired deadline must yield Unknown, got {other:?}"),
    }

    // Far-future deadline is inert: the same system still proves Safe.
    let far = ay_core::time::Instant::now() + std::time::Duration::from_hours(1);
    let mut solver = Ic3Solver::new(build_ts(), false).with_deadline(Some(far));
    match solver.solve() {
        Ic3Result::Safe { .. } => {}
        other => panic!("a far deadline must not perturb the Safe verdict, got {other:?}"),
    }
}

/// Test: trivially unsafe system.
///
/// Single state variable x. Init: x=1. Bad: x=1.
/// The initial state is already bad.
#[test]
fn test_ic3_trivially_unsafe() {
    let (sv, iv, nv, total) = make_vars(1, 0);
    let x = sv[0];
    let x_next = nv[0];

    // Init: x = 1.
    let init_clauses = vec![vec![Literal::positive(x)]];

    // Trans: x' = x (identity).
    let trans_clauses = vec![
        vec![Literal::negative(x), Literal::positive(x_next)],
        vec![Literal::positive(x), Literal::negative(x_next)],
    ];

    // Bad: x = 1.
    let bad_literals = vec![Literal::positive(x)];

    let ts = BitLevelTransitionSystem::new(
        1,
        0,
        sv,
        nv,
        iv,
        init_clauses,
        trans_clauses,
        bad_literals,
        total,
    );

    let mut solver = Ic3Solver::new(ts, false);
    let result = solver.solve();

    match result {
        Ic3Result::Unsafe { trace } => {
            assert!(
                !trace.is_empty(),
                "counterexample trace should be non-empty"
            );
        }
        other => panic!("expected Unsafe, got {other:?}"),
    }
}

/// Test: 1-step reachability (unsafe after one transition).
///
/// Single state variable x. Init: x=0. Trans: x'=1 (always sets x).
/// Bad: x=1. After one step, x becomes 1 (bad).
#[test]
fn test_ic3_one_step_unsafe() {
    let (sv, iv, nv, total) = make_vars(1, 0);
    let x = sv[0];
    let x_next = nv[0];

    // Init: x = 0.
    let init_clauses = vec![vec![Literal::negative(x)]];

    // Trans: x' = 1 (always). CNF: just (x').
    let trans_clauses = vec![vec![Literal::positive(x_next)]];

    // Bad: x = 1.
    let bad_literals = vec![Literal::positive(x)];

    let ts = BitLevelTransitionSystem::new(
        1,
        0,
        sv,
        nv,
        iv,
        init_clauses,
        trans_clauses,
        bad_literals,
        total,
    );

    let mut solver = Ic3Solver::new(ts, false);
    let result = solver.solve();

    match result {
        Ic3Result::Unsafe { trace } => {
            assert!(
                !trace.is_empty(),
                "counterexample trace should be non-empty"
            );
        }
        other => panic!("expected Unsafe, got {other:?}"),
    }
}

/// Test: safe system with nontrivial transition.
///
/// Two state variables x, y. Init: x=0, y=0.
/// Trans: x' = not-x, y' = y (x toggles, y stays 0).
/// Bad: y=1. Since y never changes from 0, bad is unreachable.
#[test]
fn test_ic3_toggle_safe() {
    let (sv, iv, nv, total) = make_vars(2, 0);
    let x = sv[0];
    let y = sv[1];
    let x_next = nv[0];
    let y_next = nv[1];

    // Init: x=0, y=0.
    let init_clauses = vec![vec![Literal::negative(x)], vec![Literal::negative(y)]];

    // Trans for x: x' = not-x. CNF: (x OR x') /\ (not-x OR not-x')
    // Trans for y: y' = y. CNF: (not-y OR y') /\ (y OR not-y')
    let trans_clauses = vec![
        vec![Literal::positive(x), Literal::positive(x_next)],
        vec![Literal::negative(x), Literal::negative(x_next)],
        vec![Literal::negative(y), Literal::positive(y_next)],
        vec![Literal::positive(y), Literal::negative(y_next)],
    ];

    // Bad: y=1.
    let bad_literals = vec![Literal::positive(y)];

    let ts = BitLevelTransitionSystem::new(
        2,
        0,
        sv,
        nv,
        iv,
        init_clauses,
        trans_clauses,
        bad_literals,
        total,
    );

    let mut solver = Ic3Solver::new(ts, false);
    let result = solver.solve();

    match result {
        Ic3Result::Safe { .. } => {} // expected
        other => panic!("expected Safe, got {other:?}"),
    }
}

/// Test: cube to_clause negation.
#[test]
fn test_cube_to_clause() {
    use super::cube::Cube;
    let v0 = Variable::new(0);
    let v1 = Variable::new(1);
    let cube = Cube::new(vec![Literal::positive(v0), Literal::negative(v1)]);
    let clause = cube.to_clause();
    assert_eq!(clause.len(), 2);
    assert_eq!(clause[0], Literal::negative(v0));
    assert_eq!(clause[1], Literal::positive(v1));
}

/// Test: transition system cube_to_next_state mapping.
#[test]
fn test_cube_to_next_state() {
    let (sv, iv, nv, total) = make_vars(2, 0);
    let ts = BitLevelTransitionSystem::new(
        2,
        0,
        sv.clone(),
        nv.clone(),
        iv,
        vec![],
        vec![],
        vec![],
        total,
    );

    let cube = vec![Literal::positive(sv[0]), Literal::negative(sv[1])];
    let next = ts.cube_to_next_state(&cube);

    assert_eq!(next.len(), 2);
    assert_eq!(next[0], Literal::positive(nv[0]));
    assert_eq!(next[1], Literal::negative(nv[1]));
}

/// Test: COI computation on a simple transition system (#8443).
///
/// Two state variables x, y with transition:
/// - x' = NOT x (toggle: clauses reference x and x')
/// - y' = y (identity: clauses reference only y and y')
///
/// COI from x' should include x and x' (and any auxiliary vars in those clauses).
/// COI from y' should include y and y' only.
#[test]
fn test_coi_computation_simple() {
    let (sv, iv, nv, total) = make_vars(2, 0);
    let x = sv[0];
    let y = sv[1];
    let x_next = nv[0];
    let y_next = nv[1];

    // x' = NOT x: (x OR x') /\ (NOT x OR NOT x')
    // y' = y: (NOT y OR y') /\ (y OR NOT y')
    let trans_clauses = vec![
        vec![Literal::positive(x), Literal::positive(x_next)],
        vec![Literal::negative(x), Literal::negative(x_next)],
        vec![Literal::negative(y), Literal::positive(y_next)],
        vec![Literal::positive(y), Literal::negative(y_next)],
    ];

    let ts = BitLevelTransitionSystem::new(2, 0, sv, nv, iv, vec![], trans_clauses, vec![], total);

    // COI from x' should include x and x' (from the first two clauses).
    let coi_x = ts.compute_coi(&[Literal::positive(x_next)]);
    assert!(coi_x.contains(&x), "COI from x' must include x");
    assert!(coi_x.contains(&x_next), "COI from x' must include x'");
    // Should NOT include y or y' since they are in separate clauses.
    assert!(!coi_x.contains(&y), "COI from x' should not include y");
    assert!(
        !coi_x.contains(&y_next),
        "COI from x' should not include y'"
    );

    // COI from y' should include y and y' only.
    let coi_y = ts.compute_coi(&[Literal::positive(y_next)]);
    assert!(coi_y.contains(&y), "COI from y' must include y");
    assert!(coi_y.contains(&y_next), "COI from y' must include y'");
    assert!(!coi_y.contains(&x), "COI from y' should not include x");
}

/// Test: COI with transitive dependencies (#8443).
///
/// Three state variables a, b, c. Trans:
/// - a' depends on b (clause containing a' and b)
/// - b' depends on c (clause containing b' and c)
///
/// COI from a' should transitively include a', b, then b', c.
#[test]
fn test_coi_computation_transitive() {
    let (sv, iv, nv, total) = make_vars(3, 0);
    let a = sv[0];
    let b = sv[1];
    let c = sv[2];
    let a_next = nv[0];
    let b_next = nv[1];
    let _c_next = nv[2];

    // a' depends on b: (NOT b OR a')
    // b' depends on c: (NOT c OR b')
    let trans_clauses = vec![
        vec![Literal::negative(b), Literal::positive(a_next)],
        vec![Literal::negative(c), Literal::positive(b_next)],
    ];

    let ts = BitLevelTransitionSystem::new(3, 0, sv, nv, iv, vec![], trans_clauses, vec![], total);

    // COI from a': starts with a', finds clause 0 (a' and b), adds b,
    // then finds clause 1 (b' and c, but b' is NOT b — different var).
    // Actually b is in clause 0 only. Clause 1 has b_next and c.
    // b_next != b, so clause 1 won't be expanded from a'.
    let coi = ts.compute_coi(&[Literal::positive(a_next)]);
    assert!(coi.contains(&a_next), "COI must include a_next");
    assert!(coi.contains(&b), "COI must include b (from clause 0)");
    // b_next is NOT in clause 0, so clause 1 should NOT be expanded.
    assert!(
        !coi.contains(&c),
        "COI should not transitively include c (separate clause)"
    );
}

/// Test: COI empty input (#8443).
#[test]
fn test_coi_computation_empty() {
    let (sv, iv, nv, total) = make_vars(1, 0);
    let ts = BitLevelTransitionSystem::new(1, 0, sv, nv, iv, vec![], vec![], vec![], total);

    let coi = ts.compute_coi(&[]);
    assert!(coi.is_empty(), "COI of empty input should be empty");
}

/// Test: query domain computation (#8443).
#[test]
fn test_query_domain_computation() {
    let (sv, iv, nv, total) = make_vars(2, 1);
    let x = sv[0];
    let y = sv[1];
    let inp = iv[0];
    let x_next = nv[0];
    let y_next = nv[1];

    let trans_clauses = vec![
        vec![
            Literal::positive(x),
            Literal::positive(inp),
            Literal::positive(x_next),
        ],
        vec![Literal::negative(y), Literal::positive(y_next)],
    ];

    let ts = BitLevelTransitionSystem::new(
        2,
        1,
        sv.clone(),
        nv.clone(),
        iv.clone(),
        vec![],
        trans_clauses,
        vec![],
        total,
    );

    // Query domain for cube = {x=1} and next_cube = {x'=1}
    let act_var = Variable::new(total as u32); // simulated activation var
    let domain = ts.compute_query_domain(
        Some(Literal::positive(act_var)),
        &[Literal::positive(x)],
        &[Literal::positive(x_next)],
    );

    // Should include: act_var, x, x_next, inp (from COI of x_next)
    assert!(
        domain.contains(&act_var),
        "domain must include activation var"
    );
    assert!(domain.contains(&x), "domain must include cube var x");
    assert!(
        domain.contains(&x_next),
        "domain must include next-cube var x_next"
    );
    assert!(domain.contains(&inp), "domain must include COI var inp");
    // y and y_next are in a separate clause; should NOT be in domain
    assert!(
        !domain.contains(&y),
        "domain should not include unrelated var y"
    );
    assert!(
        !domain.contains(&y_next),
        "domain should not include unrelated var y_next"
    );
}

/// Test: PdrER definition extraction recognizes canonical AND Tseitin gates (#8446).
#[test]
fn test_pdrer_definition_library_extracts_and_gate() {
    let (sv, iv, nv, total) = make_vars(2, 1);
    let a = sv[0];
    let b = sv[1];
    let z = iv[0];
    let z_next = nv[0];

    // z <-> a AND b:
    // (z OR !a OR !b) AND (!z OR a) AND (!z OR b)
    let trans_clauses = vec![
        vec![
            Literal::positive(z),
            Literal::negative(a),
            Literal::negative(b),
        ],
        vec![Literal::negative(z), Literal::positive(a)],
        vec![Literal::negative(z), Literal::positive(b)],
        // Noise: a next-state identity clause must not disturb extraction.
        vec![Literal::negative(z), Literal::positive(z_next)],
    ];

    let ts = BitLevelTransitionSystem::new(2, 1, sv, nv, iv, vec![], trans_clauses, vec![], total);

    assert_eq!(ts.definitions.len(), 1);
    assert!(ts.definitions.is_extension_variable(z));
    let definition = &ts.definitions.definitions()[0];
    assert_eq!(definition.output, Literal::positive(z));
    assert_eq!(
        definition.inputs,
        vec![Literal::positive(a), Literal::positive(b)]
    );
}

/// Test: PdrER cube/clause substitutions are deterministic and reversible (#8446).
#[test]
fn test_pdrer_definition_library_compacts_and_expands() {
    let (sv, iv, nv, total) = make_vars(2, 1);
    let a = sv[0];
    let b = sv[1];
    let z = iv[0];

    let trans_clauses = vec![
        vec![
            Literal::positive(z),
            Literal::negative(a),
            Literal::negative(b),
        ],
        vec![Literal::negative(z), Literal::positive(a)],
        vec![Literal::negative(z), Literal::positive(b)],
    ];

    let ts = BitLevelTransitionSystem::new(2, 1, sv, nv, iv, vec![], trans_clauses, vec![], total);

    let cube = vec![Literal::positive(a), Literal::positive(b)];
    let compact_cube = ts.definitions.compact_cube(&cube);
    assert_eq!(compact_cube, vec![Literal::positive(z)]);
    assert_eq!(ts.definitions.expand_cube(&compact_cube), cube);

    let clause = vec![Literal::negative(a), Literal::negative(b)];
    let compact_clause = ts.definitions.compact_clause(&clause);
    assert_eq!(compact_clause, vec![Literal::negative(z)]);
    assert_eq!(
        ts.definitions.expand_clause_fractions(&compact_clause),
        Some(vec![clause])
    );

    let positive_extension_clause = vec![Literal::positive(z)];
    assert_eq!(
        ts.definitions
            .expand_clause_fractions(&positive_extension_clause),
        Some(vec![vec![Literal::positive(a)], vec![Literal::positive(b)]])
    );
}

/// Test: IC3 with domain restriction still produces correct Safe result (#8443).
///
/// Same as test_ic3_trivially_safe but with domain restriction enabled.
/// Verifies that domain restriction doesn't break correctness.
#[test]
fn test_ic3_domain_restricted_safe() {
    let (sv, iv, nv, total) = make_vars(2, 0);
    let x = sv[0];
    let y = sv[1];
    let x_next = nv[0];
    let y_next = nv[1];

    // Init: x=0, y=0.
    let init_clauses = vec![vec![Literal::negative(x)], vec![Literal::negative(y)]];

    // Trans for x: x' = NOT x. Trans for y: y' = y.
    let trans_clauses = vec![
        vec![Literal::positive(x), Literal::positive(x_next)],
        vec![Literal::negative(x), Literal::negative(x_next)],
        vec![Literal::negative(y), Literal::positive(y_next)],
        vec![Literal::positive(y), Literal::negative(y_next)],
    ];

    // Bad: y=1. Since y stays 0 forever, this is safe.
    let bad_literals = vec![Literal::positive(y)];

    let ts = BitLevelTransitionSystem::new(
        2,
        0,
        sv,
        nv,
        iv,
        init_clauses,
        trans_clauses,
        bad_literals,
        total,
    );

    let mut solver = Ic3Solver::new(ts, false);
    let result = solver.solve();

    match result {
        Ic3Result::Safe { .. } => {} // expected
        other => panic!("expected Safe with domain restriction, got {other:?}"),
    }
}

/// Test: IC3 with domain restriction still detects Unsafe correctly (#8443).
#[test]
fn test_ic3_domain_restricted_unsafe() {
    let (sv, iv, nv, total) = make_vars(1, 0);
    let x = sv[0];
    let x_next = nv[0];

    // Init: x=0. Trans: x'=1. Bad: x=1.
    let init_clauses = vec![vec![Literal::negative(x)]];
    let trans_clauses = vec![vec![Literal::positive(x_next)]];
    let bad_literals = vec![Literal::positive(x)];

    let ts = BitLevelTransitionSystem::new(
        1,
        0,
        sv,
        nv,
        iv,
        init_clauses,
        trans_clauses,
        bad_literals,
        total,
    );

    let mut solver = Ic3Solver::new(ts, false);
    let result = solver.solve();

    match result {
        Ic3Result::Unsafe { trace } => {
            assert!(!trace.is_empty(), "trace should be non-empty");
        }
        other => panic!("expected Unsafe with domain restriction, got {other:?}"),
    }
}

/// Regression test: IC3 frame storage is bounded under delta encoding (#8672).
///
/// Constructs a safe counter-like system that forces IC3 to grow many
/// frames and block clauses at different levels. Verifies two invariants:
///
/// 1. **Single storage:** no clause appears in more than one frame's
///    `blocked_clauses`. Pre-#8672 the same clause was stored in every
///    frame 1..=level, giving O(lemmas * depth) memory. With delta
///    encoding each lemma lives in exactly one frame.
///
/// 2. **No unbounded duplication within a frame:** no frame holds the
///    same clause twice (defensive check against propagation loops).
///
/// Together these assertions enforce bounded memory growth. Before the
/// fix, a 64-step counter saw each blocking clause replicated into every
/// frame it had been propagated through.
#[test]
fn test_ic3_frame_storage_bounded_delta_encoding() {
    use super::cube::Ic3Frame;
    use ay_core::kani_compat::DetHashMap as FxHashMap;
    // 2-bit stuck counter: s0, s1. Bad: s1=1.
    // Safe because bad is never reached from s0=s1=0 when trans is stuck at 0.
    let (sv, iv, nv, total) = make_vars(2, 0);
    let s0 = sv[0];
    let s1 = sv[1];
    let s0n = nv[0];
    let s1n = nv[1];

    // Init: s0=s1=0.
    let init_clauses = vec![vec![Literal::negative(s0)], vec![Literal::negative(s1)]];

    // Trans: each bit stays 0 (x' = x). Forces IC3 to propagate many
    // blocking clauses through many frames before proving safe.
    let trans_clauses = vec![
        vec![Literal::negative(s0), Literal::positive(s0n)],
        vec![Literal::positive(s0), Literal::negative(s0n)],
        vec![Literal::negative(s1), Literal::positive(s1n)],
        vec![Literal::positive(s1), Literal::negative(s1n)],
    ];

    // Bad: s1=1.
    let bad_literals = vec![Literal::positive(s1)];

    let ts = BitLevelTransitionSystem::new(
        2,
        0,
        sv,
        nv,
        iv,
        init_clauses,
        trans_clauses,
        bad_literals,
        total,
    );

    let mut solver = Ic3Solver::new(ts, false);
    let result = solver.solve();

    match result {
        Ic3Result::Safe { .. } => {}
        other => panic!("expected Safe (counter stuck at 0), got {other:?}"),
    }

    // Post-solve invariants: delta encoding keeps each clause in at most
    // one frame. Count occurrences across all frames. `Ic3Solver::frames`
    // is `pub(super)` and this module is a child of `super`, so direct
    // access is allowed without any unsafe or extra accessor.
    let frames: &Vec<Ic3Frame> = &solver.frames;

    let mut occurrences: FxHashMap<Vec<Literal>, usize> = FxHashMap::default();
    for frame in frames {
        let mut seen_in_this_frame: ay_core::kani_compat::DetHashSet<&Vec<Literal>> =
            ay_core::kani_compat::DetHashSet::default();
        for clause in &frame.blocked_clauses {
            assert!(
                seen_in_this_frame.insert(clause),
                "delta encoding violation: clause {clause:?} appears twice in one frame"
            );
            *occurrences.entry(clause.clone()).or_insert(0) += 1;
        }
    }

    for (clause, count) in &occurrences {
        assert_eq!(
            *count, 1,
            "delta encoding violation: clause {clause:?} stored in {count} frames (expected 1)",
        );
    }

    // And a total-size sanity check: total stored clauses should be on the
    // order of distinct lemmas learned (via stats.cubes_blocked +
    // stats.clauses_propagated), not multiplied by frame depth. Under
    // delta encoding the sum of blocked_clauses lengths is bounded by the
    // number of distinct lemmas retained (propagated or blocked), which is
    // at most cubes_blocked. Before the fix this sum grew as
    // cubes_blocked * frame_depth.
    let total_stored: usize = frames.iter().map(|f| f.blocked_clauses.len()).sum();
    let cubes_blocked = solver.stats().cubes_blocked as usize;
    assert!(
        total_stored <= cubes_blocked.max(1) + solver.stats().clauses_propagated as usize,
        "total_stored={total_stored} exceeds cubes_blocked={cubes_blocked} + propagated \
         (delta encoding should not store more clauses than were ever blocked)",
    );
}

/// Holy-grail gate: IC3 must AUTO-SYNTHESIZE the parity invariant `acc <=> count[0]`.
///
/// Encodes the parity loop as a bit-level transition system with NO supplied
/// invariant. The system is a 4-bit ripple-carry counter (low bits c0..c3) plus
/// an accumulator `acc` that toggles in lock-step with c0:
///
/// - Init: acc = c0 = c1 = c2 = c3 = 0
/// - Trans (deterministic increment-by-1 + acc toggle):
///
///   ```text
///   acc' = ¬acc
///   c0'  = ¬c0
///   c1'  = c1 ⊕ c0
///   c2'  = c2 ⊕ (c1 ∧ c0)
///   c3'  = c3 ⊕ (c2 ∧ c1 ∧ c0)
///   ```
/// - Bad: acc ⊕ c0   (i.e. acc ≠ count[0])
///
/// Because acc and c0 both toggle every step from 0, the reachable states all
/// satisfy `acc = c0 = count mod 2`, so the bad set is unreachable: the system
/// is SAFE. The ONLY inductive strengthening that proves this is the parity
/// relation `acc <=> c0` (equivalently the two binary clauses
/// `¬acc ∨ c0` and `acc ∨ ¬c0`).
///
/// The bad property `acc ⊕ c0` is not a single cube, so it is encoded with a
/// fresh auxiliary variable `bad <=> (acc ⊕ c0)` (Tseitin XOR), present in both
/// `init_clauses` (so the depth-0 Init∧Bad check is constrained) and
/// `trans_clauses` (so `get_bad_cube` can find it). `bad_literals = [bad]`.
///
/// GAP (Step 0): plain literal-drop MIC (no CTG) cannot converge here. The bad
/// cube `get_bad_cube` extracts is a FULL per-bit assignment (acc + c0..c3); the
/// parity pair (acc, c0) is symmetric (dropping either alone breaks induction)
/// and the carry-chain bits are drop-order traps, so MIC fails to reduce to the
/// 2-literal parity cube and IC3 does not reach a fixpoint. This test therefore
/// currently FAILS (UNKNOWN / non-converging). CTG (Step 1) is required to break
/// the symmetry by recursively blocking the predecessor bad-class.
#[test]
fn test_ic3_parity_loop() {
    // 5 state vars: acc, c0, c1, c2, c3 (no primary inputs).
    let (sv, iv, nv, mut total) = make_vars(5, 0);
    let acc = sv[0];
    let c0 = sv[1];
    let c1 = sv[2];
    let c2 = sv[3];
    let c3 = sv[4];
    let acc_n = nv[0];
    let c0_n = nv[1];
    let c1_n = nv[2];
    let c2_n = nv[3];
    let c3_n = nv[4];

    // Auxiliary Tseitin variables (allocated past the state/next block).
    let g1 = Variable::new(total as u32); // g1 = c1 ∧ c0
    total += 1;
    let g2 = Variable::new(total as u32); // g2 = c2 ∧ g1  (= c2 ∧ c1 ∧ c0)
    total += 1;
    let bad = Variable::new(total as u32); // bad = acc ⊕ c0
    total += 1;

    let p = Literal::positive;
    let n = Literal::negative;

    // o <=> a ⊕ b  (XOR Tseitin, 4 clauses).
    let xor_def = |o: Variable, a: Variable, b: Variable| -> Vec<Vec<Literal>> {
        vec![
            vec![n(o), p(a), p(b)],
            vec![n(o), n(a), n(b)],
            vec![p(o), n(a), p(b)],
            vec![p(o), p(a), n(b)],
        ]
    };
    // o <=> a ∧ b  (AND Tseitin, 3 clauses).
    let and_def = |o: Variable, a: Variable, b: Variable| -> Vec<Vec<Literal>> {
        vec![vec![n(o), p(a)], vec![n(o), p(b)], vec![p(o), n(a), n(b)]]
    };

    let mut trans_clauses: Vec<Vec<Literal>> = Vec::new();
    // acc' = ¬acc : (acc ∨ acc') ∧ (¬acc ∨ ¬acc')
    trans_clauses.push(vec![p(acc), p(acc_n)]);
    trans_clauses.push(vec![n(acc), n(acc_n)]);
    // c0' = ¬c0
    trans_clauses.push(vec![p(c0), p(c0_n)]);
    trans_clauses.push(vec![n(c0), n(c0_n)]);
    // c1' = c1 ⊕ c0
    trans_clauses.extend(xor_def(c1_n, c1, c0));
    // g1 = c1 ∧ c0 ; c2' = c2 ⊕ g1
    trans_clauses.extend(and_def(g1, c1, c0));
    trans_clauses.extend(xor_def(c2_n, c2, g1));
    // g2 = c2 ∧ g1 ; c3' = c3 ⊕ g2
    trans_clauses.extend(and_def(g2, c2, g1));
    trans_clauses.extend(xor_def(c3_n, c3, g2));
    // bad = acc ⊕ c0
    trans_clauses.extend(xor_def(bad, acc, c0));

    // Init: all state bits 0, plus the bad definition so the Init∧Bad check is
    // properly constrained (bad is forced to 0 in the initial state).
    let mut init_clauses: Vec<Vec<Literal>> = vec![
        vec![n(acc)],
        vec![n(c0)],
        vec![n(c1)],
        vec![n(c2)],
        vec![n(c3)],
    ];
    init_clauses.extend(xor_def(bad, acc, c0));

    let bad_literals = vec![p(bad)];

    let ts = BitLevelTransitionSystem::new(
        5,
        0,
        sv,
        nv,
        iv,
        init_clauses,
        trans_clauses,
        bad_literals,
        total,
    );

    let mut solver = Ic3Solver::new(ts, false);
    let result = solver.solve();

    // The holy-grail assertion: the solver finds `acc <=> c0` with no supplied
    // invariant and proves the property SAFE. Pre-CTG this FAILS.
    match result {
        Ic3Result::Safe { .. } => {} // expected AFTER CTG (Step 1)
        other => panic!("expected Safe (parity invariant acc<=>c0), got {other:?}"),
    }
}

// ===========================================================================
// ADVERSARIAL REVIEW TESTS (added by reviewer; not part of the original port).
// ===========================================================================

/// Build the parity transition system. When `acc_toggles` is true this is the
/// genuine parity loop (SAFE, invariant `acc<=>c0`). When false, `acc' = acc`
/// (acc never toggles) so parity is BROKEN and the bad set `acc != c0` becomes
/// reachable in one step (UNSAFE) — used to confirm no false Safe.
fn adv_build_parity_ts(acc_toggles: bool) -> BitLevelTransitionSystem {
    let (sv, iv, nv, mut total) = make_vars(5, 0);
    let acc = sv[0];
    let c0 = sv[1];
    let c1 = sv[2];
    let c2 = sv[3];
    let c3 = sv[4];
    let acc_n = nv[0];
    let c0_n = nv[1];
    let c1_n = nv[2];
    let c2_n = nv[3];
    let c3_n = nv[4];
    let g1 = Variable::new(total as u32);
    total += 1;
    let g2 = Variable::new(total as u32);
    total += 1;
    let bad = Variable::new(total as u32);
    total += 1;
    let p = Literal::positive;
    let n = Literal::negative;
    let xor_def = |o: Variable, a: Variable, b: Variable| -> Vec<Vec<Literal>> {
        vec![
            vec![n(o), p(a), p(b)],
            vec![n(o), n(a), n(b)],
            vec![p(o), n(a), p(b)],
            vec![p(o), p(a), n(b)],
        ]
    };
    let and_def = |o: Variable, a: Variable, b: Variable| -> Vec<Vec<Literal>> {
        vec![vec![n(o), p(a)], vec![n(o), p(b)], vec![p(o), n(a), n(b)]]
    };
    let mut trans_clauses: Vec<Vec<Literal>> = Vec::new();
    if acc_toggles {
        trans_clauses.push(vec![p(acc), p(acc_n)]);
        trans_clauses.push(vec![n(acc), n(acc_n)]);
    } else {
        // acc' = acc : (¬acc ∨ acc') ∧ (acc ∨ ¬acc')
        trans_clauses.push(vec![n(acc), p(acc_n)]);
        trans_clauses.push(vec![p(acc), n(acc_n)]);
    }
    trans_clauses.push(vec![p(c0), p(c0_n)]);
    trans_clauses.push(vec![n(c0), n(c0_n)]);
    trans_clauses.extend(xor_def(c1_n, c1, c0));
    trans_clauses.extend(and_def(g1, c1, c0));
    trans_clauses.extend(xor_def(c2_n, c2, g1));
    trans_clauses.extend(and_def(g2, c2, g1));
    trans_clauses.extend(xor_def(c3_n, c3, g2));
    trans_clauses.extend(xor_def(bad, acc, c0));
    let mut init_clauses: Vec<Vec<Literal>> = vec![
        vec![n(acc)],
        vec![n(c0)],
        vec![n(c1)],
        vec![n(c2)],
        vec![n(c3)],
    ];
    init_clauses.extend(xor_def(bad, acc, c0));
    let bad_literals = vec![p(bad)];
    BitLevelTransitionSystem::new(
        5,
        0,
        sv,
        nv,
        iv,
        init_clauses,
        trans_clauses,
        bad_literals,
        total,
    )
}

/// ADVERSARIAL: confirm the SAFE result is backed by the GENUINE parity
/// relation `acc<=>c0` (the two binary clauses), not a vacuous over-approx,
/// AND that the independent-consecution cross-check actually ran.
#[test]
fn adv_parity_invariant_is_genuinely_parity() {
    use super::cube::Ic3Frame;
    let ts = adv_build_parity_ts(true);
    let mut solver = Ic3Solver::new(ts, false);
    let result = solver.solve();
    let level = match result {
        Ic3Result::Safe { invariant_level } => invariant_level,
        other => panic!("expected Safe, got {other:?}"),
    };

    let acc = Variable::new(0);
    let c0 = Variable::new(1);
    let p = Literal::positive;
    let n = Literal::negative;

    // F_level = Init ∧ ⋃_{j>=level} frames[j].blocked_clauses (delta encoding).
    let frames: &Vec<Ic3Frame> = &solver.frames;
    let mut inv: Vec<Vec<Literal>> = Vec::new();
    for frame in frames.iter().skip(level) {
        for clause in &frame.blocked_clauses {
            let mut c = clause.clone();
            c.sort();
            inv.push(c);
        }
    }
    eprintln!("ADV invariant (level {level}) clauses: {inv:?}");
    eprintln!("ADV stats: {}", solver.stats());

    let mut pc1 = vec![p(acc), n(c0)]; // acc ∨ ¬c0  ==  c0 -> acc
    pc1.sort();
    let mut pc2 = vec![n(acc), p(c0)]; // ¬acc ∨ c0  ==  acc -> c0
    pc2.sort();
    assert!(
        inv.contains(&pc1),
        "missing parity clause (acc ∨ ¬c0); invariant was {inv:?}"
    );
    assert!(
        inv.contains(&pc2),
        "missing parity clause (¬acc ∨ c0); invariant was {inv:?}"
    );

    // The independent-consecution cross-check MUST have run (soundness gate
    // active), and must NOT have rejected anything on this sound system.
    assert!(
        solver.stats().cross_check_calls > 0,
        "independent-consecution cross-check never ran (gate inactive)"
    );
    assert_eq!(
        solver.stats().cross_check_rejections,
        0,
        "cross-check rejected a cube on a sound system (incremental false-UNSAT?)"
    );
}

/// ADVERSARIAL no-false-Safe: break parity (`acc' = acc`). The bad set
/// `acc != c0` is now reachable in one step, so the property is UNSAFE. The
/// solver MUST NOT report Safe (a false proof = unsound).
#[test]
fn adv_false_parity_must_not_be_safe() {
    let ts = adv_build_parity_ts(false);
    let mut solver = Ic3Solver::new(ts, false);
    let result = solver.solve();
    if let Ic3Result::Safe { invariant_level } = result {
        panic!("UNSOUND: false-parity loop reported Safe at level {invariant_level}");
    }
    // Expect Unsafe specifically (counterexample reachable in 1 step).
    assert!(
        matches!(result, Ic3Result::Unsafe { .. }),
        "expected Unsafe for broken parity, got {result:?}"
    );
}

include!("tests/obligation_ordering.rs");
