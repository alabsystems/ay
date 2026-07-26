// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! M5 demand-lane PRODUCTION-vs-FORCED-EAGER differential
//! (`demand-driven-instantiation-campaign` memory).
//!
//! Since the M5 flip the frontier-gated family demand lane is the PRODUCTION path
//! for M1-classified self-chaining / bridge-cycle families (always-on). The
//! forced-eager override (`Executor::set_demand_force_eager`) is
//! `#[cfg(debug_assertions)]`, so this whole differential module is gated the same
//! way — it is entirely absent from release builds (where the lane is
//! unconditionally the production path with no way to force eager).
//!
//! It is the DUAL-SOLVE differential (the A2 pattern,
//! `smt/array_persistent_combiner_shadow.rs`): every pinned demand probe is solved
//! TWICE — once by a PRODUCTION-DEMAND executor (the flip default, `shadow==true`)
//! and once by a FORCED-EAGER executor (`shadow==false`, the pre-flip path). The
//! gates:
//!
//! - GREENS STAY GREEN: every pinned green reaches `unsat` under PRODUCTION-DEMAND
//!   (the F<=1 frontier + fence must never regress the ground / depth-1
//!   refutations). This includes `parking_fixpoint_core` (LAW #1's red/green: a
//!   demand engine that parked every locally-model-consistent bridge would miss
//!   the joint contradiction — the flush must be unconditional).
//! - BOUNDED FRONTIER: the self-chaining and bridge-cycle reductions both
//!   finish at F<=2 with real demand accounting.  This pins the mechanism that
//!   produced the original `freevar_takesome` flip without putting its slow
//!   ground DT+LIA campaign in the unit-test lane.
//! - DISAGREE=0 (verdict-class) between the demand and eager arms over the GREEN
//!   corpus: the production-demand path must not turn a forced-eager `unsat` into
//!   anything else.
//!
//! Every test here is bounded and runs by default.  Long corpus campaigns
//! belong in the benchmark harness, not behind ignored unit tests.
#![cfg(debug_assertions)]

use crate::Executor;
use crate::Statistics;
use ay_frontend::parse;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;
use std::time::Duration;

/// Diagnostic counters read off a shadow solve.
#[derive(Debug, Default, Clone)]
struct ShadowDiag {
    frontier: u64,
    frontier_parked: u64,
    flushed: u64,
    flushes: u64,
    fence_drains: u64,
    parked_remaining: u64,
    gated_families: u64,
    // M4 (A0 no-drop conservation oracle) counters.
    gated_bindings: u64,
    gated_passed: u64,
    fence_seen_resets: u64,
    /// Whether the solve emitted real demand stats (vs. a timeout-wall default).
    stats_present: bool,
}

impl ShadowDiag {
    fn from_stats(s: &Statistics) -> Self {
        let g = |k: &str| s.get_int(k).unwrap_or(0);
        Self {
            frontier: g("quantifier.demand.frontier"),
            frontier_parked: g("quantifier.demand.frontier_parked"),
            flushed: g("quantifier.demand.flushed"),
            flushes: g("quantifier.demand.flushes"),
            fence_drains: g("quantifier.demand.fence_drains"),
            parked_remaining: g("quantifier.demand.parked_remaining"),
            gated_families: g("quantifier.demand.gated_families"),
            gated_bindings: g("quantifier.demand.gated_bindings"),
            gated_passed: g("quantifier.demand.gated_passed"),
            fence_seen_resets: g("quantifier.demand.fence_seen_resets"),
            // `gated_families` is emitted (as a real value, possibly 0) only when
            // the demand lane armed AND the solve wrote statistics; a timeout-wall
            // default `Statistics` has no demand keys at all.
            stats_present: s.get_int("quantifier.demand.frontier").is_some(),
        }
    }
}

/// Solve `input` with the demand shadow set to `shadow`, bounded by a HARD wall
/// cap of `timeout`. Mirrors `demand_probes::solve` (detached worker + fail-closed
/// Unknown on overrun) so a slow ground combiner never blocks the suite.
fn solve(input: &str, shadow: bool, timeout: Duration) -> (String, Statistics) {
    let src = input.to_string();
    let interrupt = Arc::new(AtomicBool::new(false));
    let interrupt_worker = Arc::clone(&interrupt);
    let (tx, rx) = std::sync::mpsc::channel();
    let _worker = std::thread::spawn(move || {
        let commands = parse(&src).expect("parse demand-lane shadow probe");
        let mut exec = Executor::new();
        exec.set_interrupt(interrupt_worker);
        exec.set_timeout(Some(timeout));
        // M5 FLIP: the demand lane is the production default; the differential's
        // eager arm (`shadow == false`) forces the pre-flip eager path via the
        // debug-only override. `shadow == true` leaves the production-demand default.
        exec.set_demand_force_eager(!shadow);
        let (verdict, stats) = match exec.execute_all(&commands) {
            Ok(outputs) => (
                outputs.last().cloned().unwrap_or_default(),
                exec.statistics().clone(),
            ),
            Err(_) => ("unknown".to_string(), Statistics::default()),
        };
        let _ = tx.send((verdict, stats));
    });
    match rx.recv_timeout(timeout + Duration::from_secs(3)) {
        Ok(result) => result,
        Err(_) => {
            interrupt.store(true, Ordering::Relaxed);
            ("unknown".to_string(), Statistics::default())
        }
    }
}

// The pinned probe corpus, re-embedded here (the `demand_probes` consts are
// private to that module). Kept verbatim so the two suites cannot drift.

const GREEN_SUM_DATATYPE_FORALL: &str = r#"
(set-logic ALL)
(declare-datatypes ((Lst 0)) (((Nil) (Cons (hd Int) (tl Lst)))))
(declare-fun sum (Lst) Int)
(assert (forall ((l Lst)) (! (= (sum l) (ite ((_ is Cons) l) (+ (hd l) (sum (tl l))) 0))
   :pattern ((sum l)))))
(assert (forall ((l Lst)) (! (>= (sum l) 0) :pattern ((sum l)))))
(declare-const a Int)
(declare-const rest Lst)
(declare-const k Int)
(assert (>= a 0)) (assert (>= k 0))
(assert (not (= (- (sum (Cons (+ a k) rest)) (sum (Cons a rest))) k)))
(check-sat)
"#;

const GREEN_PARKING_FIXPOINT_CORE: &str = r#"
(set-logic ALL)
(declare-datatypes ((Lst 0)) (((Nil) (Cons (hd Int) (tl Lst)))))
(declare-fun payload_hd (Lst) Int)
(declare-const a Lst)(declare-const b Lst)(declare-const c Lst)
(assert ((_ is Cons) a))
(assert ((_ is Cons) b))
(assert ((_ is Cons) c))
(assert (=> ((_ is Cons) a) (= (payload_hd a) (hd a))))
(assert (=> ((_ is Cons) b) (= (payload_hd b) (hd b))))
(assert (=> ((_ is Cons) c) (= (payload_hd c) (hd c))))
(assert (= (payload_hd a) (+ (hd b) 1)))
(assert (= (payload_hd b) (+ (hd c) 1)))
(assert (= (payload_hd c) (+ (hd a) 1)))
(check-sat)
"#;

const GREEN_FREEVAR_BRIDGE_REPRO: &str = r#"
(set-logic ALL)
(declare-datatypes ((Lst 0)) (((Nil) (Cons (hd Int) (tl Lst)))))
(declare-fun sum (Lst) Int)
(declare-fun payload_get (Lst) Lst)
(assert (forall ((l Lst)) (! (=> ((_ is Cons) l) (= (payload_get l) (tl l))) :pattern ((payload_get l)))))
(assert (forall ((l Lst)) (! (= (sum l) (ite ((_ is Cons) l) (+ (hd l) (sum (tl l))) 0)) :pattern ((sum l)))))
(declare-const self Lst)
(assert ((_ is Cons) self))
(assert (not (= (sum self) (+ (hd self) (sum (payload_get self))))))
(check-sat)
"#;

/// The tree analog RED (doubled recursive frontier). Its residual may stay the
/// ground combiner; the test reports its shadow verdict + counters, not a flip.
const RED_SUM_TREE_FORALL: &str = r#"
(set-logic ALL)
(declare-datatypes ((Tree 0)) (((Leaf) (Node (left Tree) (val Int) (right Tree)))))
(declare-fun tsum (Tree) Int)
(assert (forall ((t Tree)) (! (= (tsum t) (ite ((_ is Node) t) (+ (val t) (+ (tsum (left t)) (tsum (right t)))) 0)) :pattern ((tsum t)))))
(assert (forall ((t Tree)) (! (>= (tsum t) 0) :pattern ((tsum t)))))
(declare-const a Int)(declare-const k Int)
(declare-const l Tree)(declare-const r Tree)
(assert (>= a 0))(assert (>= k 0))
(assert (not (= (- (tsum (Node l (+ a k) r)) (tsum (Node l a r))) k)))
(check-sat)
"#;

const GREENS: &[(&str, &str)] = &[
    ("sum_datatype_forall", GREEN_SUM_DATATYPE_FORALL),
    ("parking_fixpoint_core", GREEN_PARKING_FIXPOINT_CORE),
    ("freevar_bridge_repro", GREEN_FREEVAR_BRIDGE_REPRO),
];

/// Fast per-green cap: ground / depth-1, solve well under a second.
const GREEN_TIMEOUT: Duration = Duration::from_secs(20);

/// GATE 2 (GREENS STAY GREEN in shadow) + GATE 3 (DISAGREE=0 over the greens):
/// every pinned green reaches `unsat` under the demand shadow AND agrees with the
/// production verdict. `parking_fixpoint_core` is LAW #1's gate — the
/// unconditional under-frontier flush must never suppress the joint refutation.
#[test]
fn demand_shadow_greens_stay_unsat_and_agree() {
    for (name, smt2) in GREENS {
        let (prod, _ps) = solve(smt2, false, GREEN_TIMEOUT);
        let (shadow, ss) = solve(smt2, true, GREEN_TIMEOUT);
        let diag = ShadowDiag::from_stats(&ss);
        eprintln!("[demand-shadow] green `{name}`: prod={prod} shadow={shadow} diag={diag:?}");
        assert_eq!(
            prod, "unsat",
            "green `{name}` must be unsat on the PRODUCTION (eager) path; got {prod}"
        );
        assert_eq!(
            shadow, "unsat",
            "GATE 2: green `{name}` regressed under the demand SHADOW (F<=1 frontier / \
             fence dropped the ground/depth-1 refutation). Got {shadow}"
        );
        assert_eq!(
            prod, shadow,
            "GATE 3 DISAGREE: green `{name}` production={prod} shadow={shadow}"
        );
    }
}

/// Shadow must not turn a production non-unsat into a wrong unsat on the tree
/// analog either (fail-closed): whatever the shadow decides on `sum_tree_forall`,
/// it must not be a SAT (all reds are z3-UNSAT) — reported, not gated on a flip.
#[test]
fn demand_shadow_tree_is_not_wrong_sat() {
    let (shadow, ss) = solve(RED_SUM_TREE_FORALL, true, Duration::from_secs(8));
    let diag = ShadowDiag::from_stats(&ss);
    eprintln!("[demand-shadow] sum_tree_forall shadow={shadow} diag={diag:?}");
    assert_ne!(
        shadow, "sat",
        "sum_tree_forall shadow returned sat but is z3-UNSAT — soundness regression"
    );
}

/// The production demand lane must arm and account for every binding on the
/// bounded self-chaining reduction.  This replaces the old env-only diagnostic
/// with assertions over emitted statistics.
#[test]
fn demand_shadow_self_chaining_arms_and_accounts() {
    let (verdict, stats) = solve(GREEN_SUM_DATATYPE_FORALL, true, GREEN_TIMEOUT);
    let diag = ShadowDiag::from_stats(&stats);
    assert_eq!(verdict, "unsat", "bounded self-chaining probe regressed");
    assert!(
        diag.stats_present && diag.gated_families >= 1,
        "demand lane did not emit real gated-family accounting: {diag:?}"
    );
    assert_eq!(
        diag.gated_bindings,
        diag.frontier_parked + diag.gated_passed,
        "every gated binding must be parked or passed"
    );
}

/// The bridge-cycle mechanism behind the original takesome flip must converge
/// within the bounded frontier and agree with the forced-eager reference arm.
#[test]
fn demand_shadow_bridge_cycle_converges_within_bounded_frontier() {
    let (prod, _ps) = solve(GREEN_FREEVAR_BRIDGE_REPRO, false, GREEN_TIMEOUT);
    let (shadow, ss) = solve(GREEN_FREEVAR_BRIDGE_REPRO, true, GREEN_TIMEOUT);
    let diag = ShadowDiag::from_stats(&ss);
    assert_eq!(prod, "unsat", "forced-eager bridge reduction regressed");
    assert_eq!(
        shadow, "unsat",
        "production-demand bridge reduction regressed"
    );
    assert!(
        diag.stats_present,
        "bridge reduction must finish with real demand statistics"
    );
    assert!(
        diag.frontier <= 2,
        "bridge reduction must converge at F<=2; frontier reached {}",
        diag.frontier
    );
    assert!(
        diag.gated_families >= 1,
        "expected at least one bridge/self-chaining family to be gated"
    );
}

/// The ground DT+LIA combiner-gap probe (no foralls at all — so the demand lane
/// arms nothing and gates no family). Currently-decided obligation: it must stay
/// NOT-unsat (z3-UNSAT but ay's ground DT+LIA combiner is documented-incomplete
/// here), and above all never a wrong SAT. Pinned in the tripwire below.
const RED_GROUND_DTLIA: &str = r#"
(set-logic ALL)
(declare-datatypes ((Lst 0)) (((Nil) (Cons (hd Int) (tl Lst)))))
(declare-fun sum (Lst) Int)
(declare-const a Int)(declare-const rest Lst)(declare-const k Int)
(declare-const c1 Lst)(declare-const c2 Lst)
(assert (= c1 (Cons (+ a k) rest)))
(assert (= c2 (Cons a rest)))
(assert (not (= k (- (sum c1) (sum c2)))))
(assert (= (sum c1) (+ (hd c1) (sum (tl c1)))))
(assert (= (sum c2) (+ (hd c2) (sum (tl c2)))))
(assert (<= 0 (sum c1)))
(check-sat)
"#;

/// M4 (item 3) — A0 NO-RELEVANT-INSTANCE-DROPPED / FENCE-SUPERSET oracle, enforced
/// over the corpus. For every probe whose shadow solve produced real demand stats,
/// the demand lane's per-family accounting must be internally conservative — the
/// exact witness that "every instance the eager path asserted is either asserted or
/// parked-then-flushed by the demand lane, never silently dropped":
///
///   (A) CONSERVATION: `gated_bindings == frontier_parked + gated_passed` — every
///       gated-family binding the cost gate SAW is either parked (LAW #7) or passed
///       to the normal assert/defer path. No gated binding vanishes.
///   (B) FLUSH ⊆ PARK: `flushed <= frontier_parked` — the flush/fence only ever
///       re-asserts instances that were first parked (a parked-THEN-flushed set),
///       never conjures a new one, and `flushed > 0 ⇒ flushes>0 || fence_drains>0`.
///   (C) PARKED-THEN-FLUSHED AT A NON-UNSAT CONCLUSION: if the shadow did NOT refute
///       (Sat/Unknown with real stats), the fence must have drained the queue
///       (`parked_remaining == 0`) — no Sat/Unknown is concluded while a parked
///       instance is withheld (LAW #2). An UNSAT may legitimately refute early with
///       instances still parked (dropping nothing needed).
///
/// Runs over the GREENS (ground / depth-1, fast + real stats) — the corpus where
/// the eager path terminates so the superset claim is meaningful.
#[test]
fn demand_shadow_conservation_no_relevant_instance_dropped() {
    for (name, smt2) in GREENS {
        let (verdict, ss) = solve(smt2, true, GREEN_TIMEOUT);
        let d = ShadowDiag::from_stats(&ss);
        eprintln!("[demand-shadow] A0-oracle `{name}`: verdict={verdict} diag={d:?}");
        if !d.stats_present {
            // A timeout-wall default carries no counters; nothing to assert.
            continue;
        }
        // (A) conservation — no gated binding silently dropped.
        assert_eq!(
            d.gated_bindings,
            d.frontier_parked + d.gated_passed,
            "A0 (A) conservation on `{name}`: gated_bindings={} != frontier_parked={} + \
             gated_passed={} (a gated binding was dropped)",
            d.gated_bindings,
            d.frontier_parked,
            d.gated_passed
        );
        // (B) flush ⊆ park.
        assert!(
            d.flushed <= d.frontier_parked,
            "A0 (B) on `{name}`: flushed={} exceeds frontier_parked={} (flushed a \
             non-parked instance)",
            d.flushed,
            d.frontier_parked
        );
        assert!(
            d.flushed == 0 || d.flushes > 0 || d.fence_drains > 0,
            "A0 (B) on `{name}`: flushed={} without any flush/fence event",
            d.flushed
        );
        // Every fence drain resets the seen frame exactly once (M4 discipline #3).
        assert_eq!(
            d.fence_seen_resets, d.fence_drains,
            "A0 on `{name}`: each fence drain must reset the seen frame once \
             (fence_drains={} fence_seen_resets={})",
            d.fence_drains, d.fence_seen_resets
        );
        // (C) parked-then-flushed at a non-UNSAT conclusion.
        if verdict != "unsat" {
            assert_eq!(
                d.parked_remaining, 0,
                "A0 (C) on `{name}`: a non-UNSAT conclusion ({verdict}) left \
                 parked_remaining={} — the fence did not achieve a full flush",
                d.parked_remaining
            );
        }
    }
}

/// M4 (item 5) — TRIPWIRES over every currently-decided demand-probe obligation, IN
/// SHADOW (production is untouched — the differential's production arm never sets
/// the demand flag). If any of these flips, a human must look:
///   - GREENS: stay `unsat` under the demand shadow (the F<=1 frontier + fence must
///     never regress a ground / depth-1 refutation) AND agree with production.
///   - `red_ground_dtlia` (a currently-decided RED, no foralls): stays NOT `unsat`
///     in shadow — the demand lane arms nothing here, so it must be byte-inert.
///   - SOUNDNESS FENCE: NO probe (green or red) may return a wrong `sat` in shadow;
///     every probe is z3-UNSAT.
#[test]
fn demand_shadow_tripwire_currently_decided_obligations() {
    // Greens: unsat in shadow, agree with production, never wrong-sat.
    for (name, smt2) in GREENS {
        let (prod, _ps) = solve(smt2, false, GREEN_TIMEOUT);
        let (shadow, _ss) = solve(smt2, true, GREEN_TIMEOUT);
        eprintln!("[demand-shadow] tripwire green `{name}`: prod={prod} shadow={shadow}");
        assert_eq!(
            prod, "unsat",
            "tripwire: green `{name}` must be unsat on production; got {prod}"
        );
        assert_eq!(
            shadow, "unsat",
            "tripwire: green `{name}` regressed under the demand shadow; got {shadow}"
        );
        assert_ne!(
            shadow, "sat",
            "tripwire SOUNDNESS: green `{name}` returned a wrong sat in shadow"
        );
    }
    // `red_ground_dtlia`: the demand lane arms nothing (no foralls), so the shadow
    // verdict must match production's currently-decided NOT-unsat, and never sat.
    let (prod_g, _pg) = solve(RED_GROUND_DTLIA, false, Duration::from_secs(3));
    let (shadow_g, sg) = solve(RED_GROUND_DTLIA, true, Duration::from_secs(3));
    let dg = ShadowDiag::from_stats(&sg);
    eprintln!(
        "[demand-shadow] tripwire red_ground_dtlia: prod={prod_g} shadow={shadow_g} diag={dg:?}"
    );
    // The lazy-DT-AUFLIA route (AY_DT_LAZY_AUFLIA — the orthogonal combined-theory
    // L1a lever, NOT the demand lane) legitimately closes this documented ground
    // DT+LIA gap to its z3-UNSAT verdict when armed. Reclassify the not-unsat pin
    // accordingly; the never-wrong-`sat` soundness fence and the prod==shadow
    // DISAGREE fence below both hold unconditionally.
    let lazy_auflia = std::env::var("AY_DT_LAZY_AUFLIA")
        .map(|v| v != "0" && !v.is_empty())
        .unwrap_or(false);
    assert_ne!(
        shadow_g, "sat",
        "tripwire SOUNDNESS: red_ground_dtlia returned a wrong sat in shadow \
         (it is z3-UNSAT); got {shadow_g}"
    );
    if lazy_auflia {
        assert_eq!(
            shadow_g, "unsat",
            "red_ground_dtlia under AY_DT_LAZY_AUFLIA must close to its z3-UNSAT \
             verdict (the lazy-DT ground combiner win); got {shadow_g}"
        );
    } else {
        assert_ne!(
            shadow_g, "unsat",
            "tripwire: red_ground_dtlia FLIPPED to unsat in shadow with no lazy-DT \
             route — a human must look (the demand lane gates no family here, so \
             this would be an unexpected ground DT+LIA change, not a demand-lane win)"
        );
    }
    // Byte-inert: with no foralls the lane arms nothing, so it gates no family.
    if dg.stats_present {
        assert_eq!(
            dg.gated_families, 0,
            "red_ground_dtlia has no foralls — the demand lane must gate no family"
        );
    }
    // The shadow must not disagree with production's decided class here.
    assert_eq!(
        prod_g, shadow_g,
        "tripwire DISAGREE: red_ground_dtlia production={prod_g} shadow={shadow_g}"
    );
}
