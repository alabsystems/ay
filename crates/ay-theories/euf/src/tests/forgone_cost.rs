// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! P1.2 — THE RETRODICTION GATE for the forgone-cost detector.
//!
//! # The claim under test
//!
//! the development design notes §2 asserts that a
//! gate's own doc comment carries a falsifiable quantitative claim about the branch
//! it forces, and that instrumenting *that* claim separates the workloads a SIZE
//! proxy cannot — **from single ordinary runs, with no A/B, no arm, and no second
//! feature nominated with hindsight.**
//!
//! `CONG_UNDO_MIN_FUNC_APPS` states its claim outright (`solver.rs`): the
//! incremental path is *"a NET LOSS on merge-heavy / pop-light solves whose
//! func_apps set is small enough that the rebuild was already cheap"*, and *"a large
//! WIN only when func_apps is big enough that a single rebuild dominates"*. Both
//! factors are already at the call site: `func_apps.len()` and the pop count.
//!
//! the development design notes records the two real
//! workloads that pin the claim down:
//!
//! | file | func_apps | pops | what it wants |
//! |---|---|---|---|
//! | `QF_UF/NEQ` | 1,731 | 86,677 conflicts | incremental undo ON (1.79x) |
//! | `QF_UF_fischer.7` | ~1.5k asserts | pop-light | incremental undo OFF (+17% if on) |
//!
//! **Both sit far below the 16,384 size gate**, so the gate maps them to the same
//! decision, and it is wrong for one of them. That is the defect.
//!
//! # Scope, stated honestly
//!
//! Those two `.smt2` files are not in this repository and no SMT-LIB corpus is on
//! this machine, so this is **not** a run of the named files. It reproduces their
//! two REGIMES at the documented magnitudes — equal func_apps on both sides, far
//! below the gate, differing only in pop count — and drives the real engine and the
//! real counters. What it establishes is that the separator works on the shape; what
//! it does not establish is the 1.79x and the +17%, which were measured on the files.
//!
//! A run against the real corpus would strengthen this and cannot weaken it: the
//! prediction here is about the SIGN and the ORDER OF MAGNITUDE of the separation,
//! and those are properties of the regime, not of the file.

use super::*;

/// Build a solve with `n_apps` function applications and `n_pops` push/pop rounds,
/// then report `(func_apps, rebuild_work, undo_work, gate_says_incremental)`.
///
/// The size gate is a pure function of `func_apps`, so holding that equal across the
/// two regimes is what makes the comparison a test OF THE GATE rather than of the
/// models.
fn regime(n_apps: usize, n_pops: usize, frozen: bool) -> (usize, u64, u64, bool) {
    let mut store = TermStore::new();
    let u = Sort::Uninterpreted("U".to_string());

    let vars: Vec<TermId> = (0..n_apps)
        .map(|i| store.mk_var(format!("x{i}"), u.clone()))
        .collect();
    let apps: Vec<TermId> = vars
        .iter()
        .map(|&v| store.mk_app(Symbol::named("f"), vec![v], u.clone()))
        .collect();
    // A pool of equalities to assert and retract inside each scope.
    let eqs: Vec<TermId> = (0..n_apps.saturating_sub(1))
        .map(|i| store.mk_eq(vars[i], vars[i + 1]))
        .collect();

    // Relate the applications so `func_apps` is populated: build these BEFORE the
    // solver borrows the store.
    let app_eqs: Vec<TermId> = apps.windows(2).map(|w| store.mk_eq(w[0], w[1])).collect();

    let mut euf = EufSolver::new(&store);
    // FROZEN reproduces the PRE-FIX gate: with the incremental path unavailable,
    // `cong_undo_active()` is false at every pop, so every pop pays a rebuild and
    // the counter accumulates the cost the size gate was forcing. That is the state
    // the defect was found in, and therefore the state a retrodiction must measure.
    if frozen {
        euf.inc_cong_undo_enabled = false;
    }
    for &e in app_eqs.iter().take(2) {
        euf.assert_literal(e, true);
    }
    for &eq in eqs.iter().take(2) {
        euf.assert_literal(eq, true);
    }
    let _ = euf.check();

    // The backtracking regime. Each round asserts one equality inside a scope and
    // pops it — which is exactly what a conflict-heavy CDCL search does to a theory.
    for round in 0..n_pops {
        euf.push();
        if let Some(&eq) = eqs.get(round % eqs.len().max(1)) {
            euf.assert_literal(eq, true);
        }
        let _ = euf.check();
        euf.pop();
    }

    (
        euf.func_apps.len(),
        euf.rebuild_work,
        euf.undo_work,
        euf.cong_undo_active(),
    )
}

/// THE GATE. Under the gate as it stood when the defect was found, a size proxy
/// cannot tell these two workloads apart; the forgone-cost counter separates them by
/// orders of magnitude, from one ordinary run of each.
#[test]
#[serial]
fn forgone_cost_separates_pop_heavy_from_pop_light_at_equal_size() {
    // Both sides far below CONG_UNDO_MIN_FUNC_APPS (16,384), as both real files are.
    const APPS: usize = 120;
    const POP_LIGHT: usize = 4; // fischer.7's regime
    const POP_HEAVY: usize = 4_000; // NEQ's regime

    let (light_apps, light_rebuild, ..) = regime(APPS, POP_LIGHT, true);
    let (heavy_apps, heavy_rebuild, ..) = regime(APPS, POP_HEAVY, true);

    // 1. THE SIZE GATE IS BLIND. Same func_apps on both sides, both under the floor,
    //    so the gate's own input is identical and its decision cannot differ.
    assert_eq!(
        light_apps, heavy_apps,
        "the two regimes must be the same SIZE, or this tests the models and not the gate"
    );
    assert!(
        light_apps < crate::solver::CONG_UNDO_MIN_FUNC_APPS,
        "both regimes must sit below the size floor, as QF_UF/NEQ (1,731) and fischer.7 do"
    );

    // 2. THE FORGONE-COST COUNTER IS NOT BLIND. It charges the rebuild path what
    //    that path is about to cost, on exactly the branch the gate forces.
    assert!(
        heavy_rebuild > light_rebuild,
        "forgone cost must grow with backtracking: light={light_rebuild} heavy={heavy_rebuild}"
    );

    // 3. AND THE SEPARATION IS A REGIME DIFFERENCE, not a hair. The pop ratio here is
    //    1000x; the real pair differ by ~4 orders (86,677 conflicts vs pop-light).
    let ratio = heavy_rebuild as f64 / light_rebuild.max(1) as f64;
    assert!(
        ratio > 100.0,
        "separation must be orders of magnitude: light={light_rebuild} \
         heavy={heavy_rebuild} ratio={ratio:.1}x"
    );
}

/// THE FIX IS ALREADY IN, AND THIS IS WHAT IT LOOKS LIKE.
///
/// Running the same pop-heavy regime with the gate LIVE rather than frozen, the
/// counter stops at exactly one rebuild: `maybe_latch_undo` compares
/// `rebuild_work > undo_work`, that is true after the very first pop, and the solve
/// switches to the incremental path and never pays a second rebuild.
///
/// This is the mature form of the whole design — the gate instrumented its own claim
/// and then acted on it — and it is why the separation above has to be measured with
/// the gate frozen. There is no forgone cost left to measure once the engine stops
/// forgoing anything.
#[test]
#[serial]
fn the_live_gate_self_corrects_after_a_single_rebuild() {
    const APPS: usize = 120;
    let (_, frozen_cost, ..) = regime(APPS, 4_000, true);
    let (apps, live_cost, _, live_incremental) = regime(APPS, 4_000, false);

    assert_eq!(
        live_cost, apps as u64,
        "the live gate must pay exactly ONE rebuild ({apps}) and then latch"
    );
    assert!(
        live_incremental,
        "after latching, the solve must be on the incremental path"
    );
    assert!(
        frozen_cost > live_cost * 100,
        "the frozen gate pays what the live one avoids: frozen={frozen_cost} live={live_cost}"
    );
}

/// The counter measures the branch the gate FORCES, so it must accrue only while the
/// gate is sending work down the rebuild path. This is what makes it a *forgone*
/// cost rather than a plain activity counter: once the engine is on the incremental
/// path there is no rebuild to forgo and nothing accrues.
#[test]
#[serial]
fn nothing_accrues_once_the_expensive_branch_is_no_longer_taken() {
    let mut store = TermStore::new();
    let u = Sort::Uninterpreted("U".to_string());
    let a = store.mk_var("a".to_string(), u.clone());
    let b = store.mk_var("b".to_string(), u.clone());
    let eq = store.mk_eq(a, b);

    let mut euf = EufSolver::new(&store);
    euf.assert_literal(eq, true);
    let _ = euf.check();

    // Force the incremental path on directly: with it active, `pop` takes the
    // replay branch and charges nothing.
    euf.undo_latched = true;
    assert!(
        euf.cong_undo_active(),
        "fixture is wrong: the latch must put the solve on the incremental path"
    );
    let before = euf.rebuild_work;
    for _ in 0..50 {
        euf.push();
        let _ = euf.check();
        euf.pop();
    }
    assert_eq!(
        euf.rebuild_work, before,
        "the incremental path pays no rebuild, so there is no forgone cost to charge"
    );
}
