// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Sampled decision-relevance counters: on a conflict-heavy UNSAT instance
//! the sampler must fire and stay within its arithmetic bounds (relevant
//! decisions are a subset of trail decisions, which cannot exceed sampled
//! conflicts times the variable count). The counters are read-only
//! measurement; this also pins that enabling them does not change the
//! verdict.

use super::*;

/// Pigeonhole PHP(pigeons, holes) as a Solver; UNSAT for pigeons > holes.
fn pigeonhole(pigeons: usize, holes: usize) -> Solver {
    let var = |p: usize, h: usize| Variable((p * holes + h) as u32);
    let mut solver = Solver::new(pigeons * holes);
    for p in 0..pigeons {
        solver.add_clause((0..holes).map(|h| Literal::positive(var(p, h))).collect());
    }
    for h in 0..holes {
        for p in 0..pigeons {
            for q in (p + 1)..pigeons {
                solver.add_clause(vec![
                    Literal::negative(var(p, h)),
                    Literal::negative(var(q, h)),
                ]);
            }
        }
    }
    solver
}

#[test]
fn sampled_decision_relevance_fires_and_is_bounded() {
    let mut solver = pigeonhole(9, 8);
    let result = solver.solve().into_inner();
    assert!(
        matches!(result, SatResult::Unsat(_)),
        "PHP(9,8) must be UNSAT, got {result:?}"
    );
    assert!(
        solver.num_conflicts() > 1024,
        "test needs >1024 conflicts to exercise the sampler, got {}",
        solver.num_conflicts()
    );
    let (focused, stable) = solver.sampled_decision_relevance();
    let sampled = focused.0 + stable.0;
    assert!(sampled > 0, "sampler never fired");
    for (conflicts, decisions, relevant) in [focused, stable] {
        assert!(
            relevant <= decisions,
            "relevant {relevant} exceeds decisions {decisions}"
        );
        assert!(
            decisions <= conflicts * 72,
            "decisions {decisions} exceeds conflicts*vars bound"
        );
    }
    assert!(
        focused.1 + stable.1 > 0,
        "sampled conflicts recorded no trail decisions"
    );
    let (focused_src, stable_src) = solver.sampled_decision_sources();
    assert_eq!(
        focused_src.0 + focused_src.2,
        focused.1,
        "focused source split must sum to sampled decisions"
    );
    assert_eq!(
        stable_src.0 + stable_src.2,
        stable.1,
        "stable source split must sum to sampled decisions"
    );
    assert_eq!(
        focused_src.1 + focused_src.3,
        focused.2,
        "focused relevant split must sum to sampled relevant"
    );
    assert_eq!(
        stable_src.1 + stable_src.3,
        stable.2,
        "stable relevant split must sum to sampled relevant"
    );
    let (analyzed_focused, analyzed_stable) = solver.sampled_analyzed();
    for ((conflicts, _, relevant), analyzed) in
        [(focused, analyzed_focused), (stable, analyzed_stable)]
    {
        assert!(
            analyzed >= relevant,
            "relevant {relevant} exceeds analyzed {analyzed}"
        );
        assert!(
            analyzed <= conflicts * 72,
            "analyzed {analyzed} exceeds conflicts*vars bound"
        );
    }
    assert!(
        analyzed_focused + analyzed_stable >= sampled,
        "each sampled conflict must analyze at least one variable"
    );
    let (trail_focused, trail_stable) = solver.sampled_trail_composition();
    for ((conflicts, decisions, _), (trail_len, target_set, target_agree)) in
        [(focused, trail_focused), (stable, trail_stable)]
    {
        assert!(
            trail_len >= decisions,
            "trail {trail_len} shorter than its decisions {decisions}"
        );
        assert!(
            trail_len <= conflicts * solver.num_vars as u64,
            "trail {trail_len} exceeds conflicts*vars bound"
        );
        assert!(
            target_agree <= target_set && target_set <= trail_len,
            "target agree {target_agree} / set {target_set} / trail {trail_len} out of order"
        );
    }
}

/// Deterministic over-constrained random 4-SAT: density (clauses/vars)
/// stays above the small-dense threshold through preprocessing because
/// random long clauses are rarely blocked or subsumed.
fn dense_random_4sat(vars: usize, clauses: usize) -> Solver {
    let mut solver = Solver::new(vars);
    let mut state = 0x9E37_79B9_7F4A_7C15u64;
    let mut next = move || {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        state
    };
    for _ in 0..clauses {
        let mut lits = Vec::new();
        while lits.len() < 4 {
            let v = (next() % vars as u64) as u32;
            let lit = if next() % 2 == 0 {
                Literal::positive(Variable(v))
            } else {
                Literal::negative(Variable(v))
            };
            if !lits
                .iter()
                .any(|l: &Literal| l.variable() == lit.variable())
            {
                lits.push(lit);
            }
        }
        solver.add_clause(lits);
    }
    solver
}

fn force_stable_ema_off() -> ay_core::debug_channel::sat_ab_test_override::Guard {
    ay_core::debug_channel::sat_ab_test_override::set(ay_core::SatAbSwitches {
        stable_ema: Some(false),
        ..Default::default()
    })
}

fn force_stable_ema_on() -> ay_core::debug_channel::sat_ab_test_override::Guard {
    ay_core::debug_channel::sat_ab_test_override::set(ay_core::SatAbSwitches {
        stable_ema: Some(true),
        ..Default::default()
    })
}

/// Band gate resolution lives in `solve_no_assumptions` after
/// preprocessing (not in `init_solve`). Run just far enough to pass it:
/// the entry/stop polls are consumed first, then the CDCL loop polls every
/// ~100 conflicts, so a generous poll budget stops well after resolution.
fn solve_until_gate_resolved(solver: &mut Solver) {
    let polls = std::cell::Cell::new(0usize);
    let _ = solver.solve_interruptible(|| {
        polls.set(polls.get() + 1);
        polls.get() > 200
    });
}

#[test]
fn stable_ema_force_wins_over_small_dense_override() {
    // 100 vars, 1600 clauses: density 16 trips the small-dense override
    // (active_vars < 1000 && density > 10) by default.
    let mut default_solver = dense_random_4sat(100, 1600);
    solve_until_gate_resolved(&mut default_solver);
    assert!(
        default_solver.num_conflicts > 0,
        "search never started: stop fired before band resolution"
    );
    assert_eq!(
        default_solver.cold.stable_ema_gate,
        u64::MAX,
        "default resolution must keep the small-dense EMA disable"
    );
    assert!(
        default_solver.cold.focused_restart_gate >= 10,
        "small-dense band must raise the focused restart floor"
    );

    assert_eq!(
        default_solver.cold.focused_restart_gate, 10,
        "the small-dense focused restart floor is independent of stable EMA"
    );

    let force_guard = force_stable_ema_on();
    let mut forced = dense_random_4sat(100, 1600);
    solve_until_gate_resolved(&mut forced);
    assert!(
        forced.num_conflicts > 0,
        "search never started: stop fired before band resolution"
    );
    assert_ne!(
        forced.cold.stable_ema_gate,
        u64::MAX,
        "explicit --sat-stable-ema true must win over the band override"
    );
    assert!(
        forced.cold.focused_restart_gate >= 10,
        "the force must not also move focused cadence (single-variable lever)"
    );
    assert_eq!(
        forced.cold.focused_restart_gate, default_solver.cold.focused_restart_gate,
        "forcing stable EMA must preserve the focused restart floor"
    );

    drop(force_guard);
    let _disabled = force_stable_ema_off();
    let mut disabled = dense_random_4sat(100, 1600);
    solve_until_gate_resolved(&mut disabled);
    assert!(
        disabled.num_conflicts > 0,
        "search never started: stop fired before band resolution"
    );
    assert_eq!(disabled.cold.stable_ema_gate, u64::MAX);
    assert_eq!(
        disabled.cold.focused_restart_gate, default_solver.cold.focused_restart_gate,
        "disabling stable EMA must preserve the focused restart floor"
    );
}

#[test]
fn stable_ema_force_wins_over_large_structured_override() {
    // >1M clauses after preprocessing trips the large-structured band
    // override (the band reads the post-preprocess active count). Fixture
    // constraints, each learned the hard way: width-3 clauses (units are
    // consumed at add time and binaries live in the binary watch store,
    // so neither reaches the arena count the band reads); global random
    // structure (single-polarity and chain-local spines are settled by
    // the lucky-phase sweeps before band resolution ever runs); 1.1M
    // clauses (margin over the 1M threshold after preprocessing).
    fn large_random_3sat() -> Solver {
        let vars = 250_000u32;
        let clauses = 1_100_000usize;
        let mut solver = Solver::new(vars as usize);
        let mut state = 0x2545_F491_4F6C_DD1Du64;
        let mut next = move || {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            state
        };
        for _ in 0..clauses {
            let mut lits = Vec::new();
            while lits.len() < 3 {
                let v = (next() % u64::from(vars)) as u32;
                let lit = if next() % 2 == 0 {
                    Literal::positive(Variable(v))
                } else {
                    Literal::negative(Variable(v))
                };
                if !lits
                    .iter()
                    .any(|l: &Literal| l.variable() == lit.variable())
                {
                    lits.push(lit);
                }
            }
            solver.add_clause(lits);
        }
        solver
    }

    // The poll budget must outlast preprocessing's own stop polls yet land
    // early in CDCL; the `num_conflicts > 0` asserts below fail loudly if
    // a future change makes the stop fire before band resolution, instead
    // of letting the forced arm pass vacuously.
    fn solve_past_band_resolution(solver: &mut Solver) {
        let polls = std::cell::Cell::new(0usize);
        let _ = solver.solve_interruptible(|| {
            polls.set(polls.get() + 1);
            polls.get() > 1_000
        });
    }

    let mut default_solver = large_random_3sat();
    solve_past_band_resolution(&mut default_solver);
    assert!(
        default_solver.num_conflicts > 0,
        "search never started: stop fired before band resolution"
    );
    assert!(
        default_solver.num_original_clauses > 1_000_000,
        "fixture must land in the >1M band, got num_original_clauses={}",
        default_solver.num_original_clauses
    );
    assert_eq!(
        default_solver.cold.stable_ema_gate,
        u64::MAX,
        "default resolution must keep the large-structured EMA disable"
    );

    let _guard = force_stable_ema_on();
    let mut forced = large_random_3sat();
    solve_past_band_resolution(&mut forced);
    assert!(
        forced.num_conflicts > 0,
        "search never started: stop fired before band resolution"
    );
    assert_ne!(
        forced.cold.stable_ema_gate,
        u64::MAX,
        "explicit --sat-stable-ema true must win over the >1M-clause override"
    );
}

#[test]
fn stable_ema_explicit_switches_on_non_band_instance() {
    // PHP(9,8): 72 vars, density ~4 — in neither band, so the gate is the
    // construction-time resolution alone. The switch is read when the
    // solver is built, so each guard precedes construction.
    let mut default_solver = pigeonhole(9, 8);
    let _ = default_solver.solve();
    let default_gate = default_solver.cold.stable_ema_gate;
    assert_ne!(default_gate, u64::MAX, "default gate must be finite");

    let off_gate = {
        let _guard = force_stable_ema_off();
        let mut off = pigeonhole(9, 8);
        let _ = off.solve();
        off.cold.stable_ema_gate
    };
    assert_eq!(
        off_gate,
        u64::MAX,
        "explicit --sat-stable-ema false must disable the stable EMA"
    );

    let _guard = force_stable_ema_on();
    let mut on = pigeonhole(9, 8);
    let _ = on.solve();
    assert_eq!(
        on.cold.stable_ema_gate, default_gate,
        "explicit true on a non-band instance must match the default gate"
    );
}

#[test]
fn descent_histogram_counts_restart_segments() {
    let mut solver = pigeonhole(9, 8);
    let result = solver.solve().into_inner();
    assert!(matches!(result, SatResult::Unsat(_)));
    let (focused, stable) = solver.descent_histograms();
    let segments: u64 = focused.iter().chain(stable.iter()).sum();
    assert!(segments > 0, "solve must restart at least once");
    assert!(
        segments <= solver.num_restarts(),
        "histogram segments {segments} exceed restarts {}",
        solver.num_restarts()
    );
}

#[test]
fn learned_composition_after_solve_within_retained_count() {
    // Live-composition semantics (incl. the empty case) are pinned in
    // solver::stats::tests; here only the end-to-end bound after a real
    // solve: live learned never exceeds retained (active) learned.
    let mut solver = pigeonhole(9, 8);
    let result = solver.solve().into_inner();
    assert!(matches!(result, SatResult::Unsat(_)));
    let (hyper, binary, short, long) = solver.learned_composition();
    assert!(
        hyper + binary + short + long <= solver.num_learned_clauses(),
        "live composition exceeds retained learned count"
    );
}
