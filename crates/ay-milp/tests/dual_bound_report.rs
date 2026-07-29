// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! THE INTERRUPTED TREE'S DUAL BOUND MUST BE REPORTED, AND MUST BE VALID.
//!
//! A branch-and-bound solver that has explored nodes necessarily holds a valid
//! global dual bound — the minimum over the open frontier and the incumbent —
//! and `ay` was doing that work and then reporting nothing. Measured over 216
//! MIPLIB mid/large instances at 60s / 1 thread: 212 runs ended unproved, 166 of
//! those carried NO rigorous dual bound, and 165 of THOSE had explored nodes.
//! For the consumer this solver exists for, that is the difference between
//! "within 2% of optimal" and "no idea".
//!
//! Every optimum checked here is HAND-COMPUTED and argued in the model builder's
//! own doc comment, never taken from the solver, so a bug that moved both would
//! not hide. The direction is the whole point: on a minimisation the reported
//! bound must never EXCEED the true optimum, on a maximisation never fall below
//! it. Soundness here is asymmetric — an invalid "rigorous" bound is far worse
//! than no bound — so where a bound cannot be shown valid the engine must emit
//! nothing, and that too is pinned — in `session.rs`, by
//! `an_inexact_model_reports_no_dual_bound_on_any_arm`, which has to live there
//! because building a model with a non-`f64` coefficient goes through the
//! crate-private exact side store the MPS reader populates.
//!
//! The mechanism half of this suite lives in `bab.rs`'s own test module, where
//! `Node` and `push_children` are in scope: `a_child_inherits_the_bound_that_
//! covers_its_box` pins the inheritance itself on both arms of
//! `AY_MILP_NO_BOUND_COVER`, and `dedup_root_reduction_fires_and_preserves_the_
//! optimum` pins that the model below really does reduce.

use ay_milp::{BabSession, Col, Model, Outcome, Sense, SolveOpts};
use num_rational::BigRational;
use num_traits::ToPrimitive as _;
use std::sync::Mutex;
use std::time::Duration;

/// The engine's node cap, the fix's A/B arm and the node counter are all
/// PROCESS-global, so every test here holds this lock across its whole solve.
/// Cargo runs the tests in this binary on parallel threads; without it one
/// test's `AY_MILP_MAX_NODES` would silently cap another's tree and the suite
/// would be measuring nothing in particular.
static ENV: Mutex<()> = Mutex::new(());

/// One solve under a deterministic node cap. Returns `(outcome, nodes)`.
///
/// The node cap, not the clock, is what stops these trees: this box is contended
/// and a wall-clock interrupt would make the node count — and with it the bound —
/// depend on the load. The wall limit below is only a backstop against a hang.
fn solve_capped(model: &Model, cap: u64, cover_off: bool, opts: &SolveOpts) -> (Outcome, u64) {
    let _g = ENV
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    // SAFETY: the lock above makes this the only thread in this test binary
    // touching these names, and both are removed before it is released.
    unsafe {
        std::env::set_var("AY_MILP_MAX_NODES", cap.to_string());
        if cover_off {
            std::env::set_var("AY_MILP_NO_BOUND_COVER", "1");
        }
    }
    ay_milp::reset_nodes_explored();
    let out = BabSession::new(model.clone(), opts)
        .expect("valid model")
        .check()
        .expect("solve");
    let nodes = ay_milp::nodes_explored();
    unsafe {
        std::env::remove_var("AY_MILP_MAX_NODES");
        std::env::remove_var("AY_MILP_NO_BOUND_COVER");
    }
    (out, nodes)
}

fn opts() -> SolveOpts {
    SolveOpts::new().with_time_limit(Duration::from_secs(120))
}

/// The rigorous dual bound an outcome reports, in the CALLER's frame, or `None`
/// when it reports none. `Optimal` is excluded on purpose: this suite is about
/// what an INTERRUPTED tree says, and counting a proven optimum as "a bound"
/// would let every test pass by never being interrupted at all.
fn reported_bound(out: &Outcome) -> Option<BigRational> {
    match out {
        Outcome::Feasible { dual_bound, .. } => dual_bound.clone(),
        Outcome::Bound {
            dual_bound,
            rigorous,
        } => rigorous.then(|| dual_bound.clone()),
        _ => None,
    }
}

fn f(b: &BigRational) -> f64 {
    b.to_f64().expect("a reported bound is a finite rational")
}

fn rnd(s: &mut u64) -> u64 {
    *s = s
        .wrapping_mul(6_364_136_223_846_793_005)
        .wrapping_add(1_442_695_040_888_963_407);
    *s >> 33
}

// ---------------------------------------------------------------------------
// Models with HAND-PROVEN optima
// ---------------------------------------------------------------------------

/// MARKET SPLIT (`markshare`) with a PLANTED solution, and an objective offset.
///
/// `rows` equalities `Σ_j a_ij x_j + s_i⁻ − s_i⁺ = b_i` over `cols` binaries,
/// with `a_ij ∈ [0, 99]` and each `b_i` set to `Σ_j a_ij x*_j` for a randomly
/// drawn binary `x*`. The objective is `Σ_i (s_i⁺ + s_i⁻)` plus a constant.
///
/// THE OPTIMUM IS `offset`, PROVEN BY HAND AND NOT BY THE SOLVER, in two lines:
/// the slacks are bounded below by 0 so the objective is `>= offset` at every
/// feasible point; and `x = x*`, `s = 0` is feasible by construction and attains
/// `offset`. No search is involved in either direction.
///
/// This shape is here because it is the one small model that RELIABLY survives a
/// node cap. The obvious textbook candidates do not: `ay` closes a 51-cycle
/// vertex cover (`ceil(n/2)`, half-unit LP gap) and a spread-coefficient
/// equality knapsack at the ROOT, in one node, with cuts disabled — presolve and
/// probing get there first. Market split has no such structure to exploit, which
/// is exactly why it is the family this engine is measured on.
///
/// The offset is not decoration. It is the one term the caller-frame translation
/// adds (`Minimize => l + offset`, `Maximize => -l + offset`), and with an
/// optimum of a bare 0 a dropped offset would be invisible.
fn market_split(rows: usize, cols: usize, seed: u64, sense: Sense, offset: f64) -> Model {
    let mut s = seed;
    let a: Vec<Vec<f64>> = (0..rows)
        .map(|_| (0..cols).map(|_| (rnd(&mut s) % 100) as f64).collect())
        .collect();
    let xstar: Vec<f64> = (0..cols).map(|_| (rnd(&mut s) % 2) as f64).collect();
    let mut m = Model::new();
    let x: Vec<Col> = (0..cols).map(|_| m.add_binary_col()).collect();
    let mut obj: Vec<(Col, f64)> = Vec::new();
    // A Maximize model gets the NEGATED slack sum, so its optimum is the same
    // `offset` reached from the other side and the reported bound has to be an
    // UPPER bound. A sign error in the frame translation lands at `-offset` and
    // is caught; without this arm it would look like a merely weaker bound.
    let w = match sense {
        Sense::Minimize => 1.0,
        Sense::Maximize => -1.0,
    };
    for row in &a {
        let sp = m.add_col(0.0, f64::INFINITY);
        let sm = m.add_col(0.0, f64::INFINITY);
        obj.push((sp, w));
        obj.push((sm, w));
        let mut co: Vec<(Col, f64)> = (0..cols).map(|j| (x[j], row[j])).collect();
        co.push((sp, 1.0));
        co.push((sm, -1.0));
        let b: f64 = (0..cols).map(|j| row[j] * xstar[j]).sum();
        m.add_row(b, b, &co);
    }
    m.set_objective(&obj, sense);
    m.set_objective_offset(offset);
    m
}

/// A set-partitioning block with DUPLICATE COLUMNS — what the dedup root
/// reduction fires on — bolted onto a market-split core that keeps the tree from
/// closing.
///
/// Each of the `k` partition rows (`Σ x = 1`, unit coefficients, all binary —
/// the merge's licence, since two members of a group cannot both be 1) carries
/// one cheap column of cost `i + 1` and three IDENTICAL expensive ones of cost
/// `i + 10`. Two of every three duplicates merge away.
///
/// OPTIMUM, BY HAND: the partition rows are disjoint from each other and from
/// the market-split rows, so each contributes its own minimum independently —
/// `Σ_i (i + 1) = k(k+1)/2` — and the market-split part contributes 0 exactly as
/// argued in `market_split`. No offset here; the sum IS the optimum.
///
/// `bab.rs`'s `dedup_root_reduction_fires_and_preserves_the_optimum` pins that
/// this same construction really does reduce and that the reduction does not
/// move the optimum (that assertion needs crate-private access). The builder is
/// duplicated verbatim on both sides; the two must be kept in step.
fn duplicate_columns_over_market_split(k: usize, seed: u64) -> (Model, BigRational) {
    let mut s = seed;
    let (rows, cols) = (4usize, 30usize);
    let a: Vec<Vec<f64>> = (0..rows)
        .map(|_| (0..cols).map(|_| (rnd(&mut s) % 100) as f64).collect())
        .collect();
    let xstar: Vec<f64> = (0..cols).map(|_| (rnd(&mut s) % 2) as f64).collect();
    let mut m = Model::new();
    let x: Vec<Col> = (0..cols).map(|_| m.add_binary_col()).collect();
    let mut obj: Vec<(Col, f64)> = Vec::new();
    for row in &a {
        let sp = m.add_col(0.0, f64::INFINITY);
        let sm = m.add_col(0.0, f64::INFINITY);
        obj.push((sp, 1.0));
        obj.push((sm, 1.0));
        let mut co: Vec<(Col, f64)> = (0..cols).map(|j| (x[j], row[j])).collect();
        co.push((sp, 1.0));
        co.push((sm, -1.0));
        let b: f64 = (0..cols).map(|j| row[j] * xstar[j]).sum();
        m.add_row(b, b, &co);
    }
    let mut opt = 0i64;
    for i in 0..k {
        let mut prow: Vec<(Col, f64)> = Vec::new();
        let cheap = m.add_binary_col();
        obj.push((cheap, (i + 1) as f64));
        prow.push((cheap, 1.0));
        for _ in 0..3 {
            let dup = m.add_binary_col();
            obj.push((dup, (i + 10) as f64));
            prow.push((dup, 1.0));
        }
        m.add_row(1.0, 1.0, &prow);
        opt += (i + 1) as i64;
    }
    m.set_objective(&obj, Sense::Minimize);
    (m, BigRational::from_integer(opt.into()))
}

// ---------------------------------------------------------------------------
// The tests
// ---------------------------------------------------------------------------

#[test]
fn an_interrupted_minimisation_never_reports_a_bound_above_the_optimum() {
    let model = market_split(5, 40, 0xABCD, Sense::Minimize, 1000.0);
    let opt = BigRational::from_integer(1000.into());
    let (out, nodes) = solve_capped(&model, 400, false, &opts());
    assert!(
        nodes > 1,
        "the tree must actually explore nodes, or this proves nothing (nodes={nodes})"
    );
    let bound = reported_bound(&out)
        .unwrap_or_else(|| panic!("an interrupt after {nodes} nodes must report a bound: {out:?}"));
    assert!(
        bound <= opt,
        "MINIMIZE: reported dual bound {} EXCEEDS the true optimum {} — an invalid \
         'rigorous' bound is worse than no bound at all",
        f(&bound),
        f(&opt)
    );
    // NON-VACUITY. The inequality above is also satisfied by a bound that has
    // silently collapsed to -inf-ish dust, or by one that lost the +1000 offset.
    // The real claim this tree holds is 1000 (the slack sum's LP bound is 0), so
    // require the report to be within a unit of it.
    assert!(
        f(&bound) > 999.0,
        "the bound must be the tree's REAL claim near 1000, got {} — a collapsed \
         or offset-less bound satisfies the validity test while saying nothing",
        f(&bound)
    );
}

#[test]
fn an_interrupted_maximisation_never_reports_a_bound_below_the_optimum() {
    // The Maximize frame flips the bound's DIRECTION, and the sign lives in one
    // line of `solve_milp_in`. A Minimize-only suite would let a flipped sign
    // through: `validate_witnesses` fails it closed to `WitnessRejected`, so it
    // would look like "no bound" rather than like a bug.
    let model = market_split(5, 40, 0xABCD, Sense::Maximize, 1000.0);
    let opt = BigRational::from_integer(1000.into());
    let (out, nodes) = solve_capped(&model, 400, false, &opts());
    assert!(
        nodes > 1,
        "the tree must actually explore nodes (nodes={nodes})"
    );
    let bound = reported_bound(&out)
        .unwrap_or_else(|| panic!("an interrupt after {nodes} nodes must report a bound: {out:?}"));
    assert!(
        bound >= opt,
        "MAXIMIZE: reported dual bound {} falls BELOW the true optimum {} — for a \
         maximisation the dual bound is an UPPER bound, and this one excludes the optimum",
        f(&bound),
        f(&opt)
    );
    assert!(
        f(&bound) < 1001.0,
        "the bound must be the tree's REAL claim near 1000, got {}",
        f(&bound)
    );
}

#[test]
fn a_root_reduction_lifts_a_bound_that_is_valid_for_the_caller() {
    // Dedup is the root reduction whose `Outcome::Bound` arm passes the number
    // through UNSHIFTED — the one that would be wrong if the reduction ever
    // moved the achievable objective. It only runs with tree-certificate capture
    // disarmed, which is why `tree_cert_leaves(0)` is set here rather than left
    // at the default 256; without it this test exercises the ordinary path and
    // says nothing about dedup at all.
    let (model, opt) = duplicate_columns_over_market_split(24, 0x5EED);
    let o = opts().with_tree_cert_leaves(0);
    let (out, nodes) = solve_capped(&model, 200, false, &o);
    assert!(
        nodes > 1,
        "the tree must actually explore nodes (nodes={nodes})"
    );
    let bound = reported_bound(&out)
        .unwrap_or_else(|| panic!("an interrupt after {nodes} nodes must report a bound: {out:?}"));
    assert!(
        bound <= opt,
        "a bound lifted out of the dedup-reduced frame reports {} against a caller \
         optimum of {} — the reduced model's optimum must EQUAL the caller's, or \
         the pass-through is an invalid, too-optimistic bound",
        f(&bound),
        f(&opt)
    );
    assert!(
        f(&bound) > 0.0,
        "the lifted bound must carry the partition block's content, got {}",
        f(&bound)
    );
}

#[test]
fn reporting_the_bound_does_not_move_the_search() {
    // THE CLAIM THAT MAKES THE A/B A MEASUREMENT: `Node::cover` is read only by
    // the dual-bound claim, never by the heap `Ord`, the pop-time cutoff prune,
    // the plateau tracker or the pseudocosts — so the two arms must run the
    // BYTE-IDENTICAL tree. Node count is the repo's own load-invariant signal
    // for "same search"; if it ever moves here, the fix has stopped being a
    // reporting change and every measurement taken across the arms is void.
    let model = market_split(5, 40, 0xABCD, Sense::Minimize, 1000.0);
    let (_, with) = solve_capped(&model, 400, false, &opts());
    let (_, without) = solve_capped(&model, 400, true, &opts());
    assert_eq!(
        with, without,
        "the bound-cover arm moved the tree ({with} vs {without} nodes) — it must not"
    );
}
