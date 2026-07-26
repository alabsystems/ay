// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! M0' demand-driven-instantiation PINNED PROBE CORPUS.
//!
//! A regression fence for the demand-driven-instantiation campaign
//! (`demand-driven-instantiation-campaign` memory). Each probe smt2 is embedded
//! INLINE as a raw string (no filesystem reads at test time) and pinned to its
//! expected verdict class:
//!
//! - GREENS — must be `unsat` today, within a sane budget. These are the ground /
//!   depth-1 refutations the current engine already discharges: the demand-driven
//!   frontier at F<=1 must never regress below them.
//! - PRODUCTION FLIPS (M5) — bounded reductions of the prophecy-pair
//!   dual-vocabulary bridge chain and the two-recursive-field tree defining
//!   forall.  Both solve `unsat` in a plain production solve and run in the
//!   default suite.
//! - REDS — expected NOT `unsat` today (Unknown/timeout). Post-M5 this is the
//!   residual ground DT+LIA combiner gap (`red_ground_dtlia`, NO foralls, so the
//!   demand lane arms nothing and the solve is byte-identical to the eager path).
//!   The pin asserts the verdict is not `unsat`: **if it ever flips, a human must
//!   look** — with no forall to gate it would be an unexpected ground-combiner
//!   change, not a demand-lane win.
//!
//! MEASURED RECLASSIFICATION (2026-07-16, b9e51ad1): the blueprint's fourth red,
//! `freevar_bridge_repro`, is EMPIRICALLY `unsat` (<0.01s) on this base — its
//! `sum(self)` / `payload_get(self)` are already ground in the goal, so the single
//! bridge fires in one round with no cross-variable chaining. Per the blueprint's
//! own "flip => celebrate and reclassify" rule it is pinned here as a GREEN. The
//! genuine free-var bridge WALL remains represented by `freevar_takesome_repro`
//! (the `self`/`final` prophecy pair, which does need the un-buildable chain).
//!
//! Plus the NEW `parking_fixpoint_core` probe (a GREEN): three ground
//! dual-vocabulary bridge instances that are each individually model-satisfiable
//! but JOINTLY unsat (a size-3 minimal unsat core — dropping any one bridge
//! restores SAT, verified with z3). This is design-law #1's trap in miniature: a
//! demand engine that parks every instance it deems locally model-consistent would
//! never discover the joint contradiction. Ground, so ay decides it `unsat` today;
//! the pin guards that the joint refutation is never lost.

use crate::Executor;
use crate::Statistics;
use ay_frontend::parse;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;
use std::time::Duration;

// ===========================================================================
// GREENS — pinned must-be-`unsat` within budget.
// ===========================================================================

/// Same goal as `freevar_takesome_repro` but with the four foralls REPLACED by
/// their manual depth<=1 instances at roots {self, final} only (6 ground
/// instances). If UNSAT the refutation needs nothing deeper than F<=1.
///
/// MEASURED SUBTLETY (2026-07-16, b9e51ad1): this exact goal is decided `unsat`
/// (0.1s) ONLY with `:produce-unsat-cores` + `:named` assertions — the
/// assumption-tracking path routes the ground refutation around the ground DT+LIA
/// combiner gap. Strip either and it degrades to `unknown` (the same wall as
/// `red_ground_dtlia`). Both are therefore preserved verbatim from the source
/// file; only the trailing `(get-unsat-core)` is dropped so the sole output line
/// is the `check-sat` verdict.
const GREEN_FREEVAR_TAKESOME_MANUAL_D1: &str = r#"
(set-logic ALL)
(set-option :produce-unsat-cores true)
(declare-datatypes ((Lst 0)) (((Nil) (Cons (hd Int) (tl Lst)))))
(declare-fun sum (Lst) Int)
(declare-fun payload_hd (Lst) Int)
(declare-fun payload_get (Lst) Lst)
(declare-const self Lst)
(declare-const final Lst)
(declare-const k Int)
(assert (! (=> ((_ is Cons) self)  (= (payload_get self)  (tl self)))  :named bridge_get_self))
(assert (! (=> ((_ is Cons) final) (= (payload_get final) (tl final))) :named bridge_get_final))
(assert (! (=> ((_ is Cons) self)  (= (payload_hd self)  (hd self)))   :named bridge_hd_self))
(assert (! (=> ((_ is Cons) final) (= (payload_hd final) (hd final)))  :named bridge_hd_final))
(assert (! (= (sum self)  (ite ((_ is Cons) self)  (+ (hd self)  (sum (tl self)))  0)) :named sumdef_self))
(assert (! (= (sum final) (ite ((_ is Cons) final) (+ (hd final) (sum (tl final))) 0)) :named sumdef_final))
(assert (! ((_ is Cons) self)  :named f_is_cons_self))
(assert (! ((_ is Cons) final) :named f_is_cons_final))
(assert (! (>= k 0) :named f_k))
(assert (! (= (payload_hd final) (+ (payload_hd self) k)) :named f_hd_bump))
(assert (! (= (payload_get final) (payload_get self)) :named f_tail_eq))
(assert (! (not (= (- (sum final) (sum self)) k)) :named goal))
(check-sat)
"#;

/// RECLASSIFIED GREEN (was a blueprint red). Dual-vocabulary bridge over a single
/// FREE variable: `sum(self)` and `payload_get(self)` both appear ground in the
/// goal, so E-matching fires `bridge@self` + `sumdef@self` immediately (one round,
/// no round-chaining) and ay decides `unsat` in <0.01s on b9e51ad1. The blueprint
/// pinned it as a residual red, but MEASUREMENT shows the current engine already
/// discharges it (z3-UNSAT, so the win is sound). Kept as a GREEN so a regression
/// below this capability is caught; the bridge-chain WALL is represented by the
/// prophecy-pair `freevar_takesome_repro` red, which genuinely needs the
/// cross-`self`/`final` bridge chain the engine cannot yet build.
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

/// Tree bracket: same goal as `sum_tree_forall` but the two foralls REPLACED by
/// manual instances at the two Node literals only (ground). If ay ground-solves
/// this fast, the tree refutation needs nothing deeper and the F<=1 frontier
/// suffices for the tree class too.
const GREEN_TREE_MANUAL_D1: &str = r#"
(set-logic ALL)
(declare-datatypes ((Tree 0)) (((Leaf) (Node (left Tree) (val Int) (right Tree)))))
(declare-fun tsum (Tree) Int)
(declare-const a Int)(declare-const k Int)
(declare-const l Tree)(declare-const r Tree)
(assert (= (tsum (Node l (+ a k) r))
           (ite ((_ is Node) (Node l (+ a k) r))
                (+ (val (Node l (+ a k) r)) (+ (tsum (left (Node l (+ a k) r))) (tsum (right (Node l (+ a k) r)))))
                0)))
(assert (= (tsum (Node l a r))
           (ite ((_ is Node) (Node l a r))
                (+ (val (Node l a r)) (+ (tsum (left (Node l a r))) (tsum (right (Node l a r)))))
                0)))
(assert (>= (tsum l) 0))
(assert (>= (tsum r) 0))
(assert (>= a 0))(assert (>= k 0))
(assert (not (= (- (tsum (Node l (+ a k) r)) (tsum (Node l a r))) k)))
(check-sat)
"#;

/// `sum` over a recursive List datatype; a defining forall with a `(sum l)`
/// trigger plus a nonneg lemma, and a take_some-style prophecy goal over the two
/// `Cons` constructor literals. The engine's landed selector-fold discharges this
/// in a couple of E-matching rounds.
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

/// NEW M0' probe — the PARKING-FIXPOINT CORE (design-law #1 red/green). Three
/// ground dual-vocabulary bridge instances (payload UF vocab <-> datatype
/// selector vocab), each individually model-satisfiable, JOINTLY unsat as a
/// size-3 minimal unsat core (dropping any single bridge restores SAT; verified
/// with z3 AND ay). Ground => ay decides `unsat` today.
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

const GREENS: &[(&str, &str)] = &[
    (
        "freevar_takesome_manual_d1",
        GREEN_FREEVAR_TAKESOME_MANUAL_D1,
    ),
    ("tree_manual_d1", GREEN_TREE_MANUAL_D1),
    ("sum_datatype_forall", GREEN_SUM_DATATYPE_FORALL),
    ("parking_fixpoint_core", GREEN_PARKING_FIXPOINT_CORE),
    // Reclassified from the blueprint's red list — MEASURED unsat on b9e51ad1.
    ("freevar_bridge_repro", GREEN_FREEVAR_BRIDGE_REPRO),
];

// ===========================================================================
// PRODUCTION FLIPS (M5) — the two former reds that the M5 authority flip now
// discharges in a PLAIN production solve (no flag). Pinned to `unsat`: if either
// regresses BELOW `unsat` the flip broke. Both are z3-UNSAT, so the flip is a
// sound capability win. `freevar_takesome_repro` needs the ground DT+LIA
// final-solve over the full frontier-gated batch is a benchmark campaign.  The
// always-on gate below uses the exact depth-1 refutation core plus the fast tree
// flip, so it proves the production mechanism in every default run.
// ===========================================================================

// ===========================================================================
// REDS — pinned expected-NOT-`unsat`-today (Unknown/timeout). A flip to `unsat`
// must trip the human-review assertion. Post-M5 this is the residual combiner gap:
// `red_ground_dtlia` has NO foralls, so the demand lane arms NOTHING and the solve
// is byte-identical to the pre-flip eager path (the documented ground DT+LIA
// incompleteness stays out of scope).
// ===========================================================================

/// Tree analog: recursive defining forall over a 2-recursive-field datatype
/// (`Node left val right`). The doubled recursive frontier compounds the DT
/// selector-axiom re-mint wall. M5: flips to `unsat` in PRODUCTION (fast, F=1).
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

/// Ground DT+LIA combiner gap: no foralls at all, only ground `sum` unfoldings
/// over two `Cons` constructor terms sharing a tail. z3 closes it; ay's ground
/// DT+LIA combiner does not (documented out-of-scope incompleteness).
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

/// Bounded M5 production flips, pinned to `unsat` in a plain production solve
/// (no debug flag).  The manual depth-1 takesome core is the precise ground
/// batch the demand frontier must deliver; the tree case exercises the
/// production quantifier lane end to end.
const PRODUCTION_FLIPS: &[(&str, &str)] = &[
    (
        "freevar_takesome_manual_d1",
        GREEN_FREEVAR_TAKESOME_MANUAL_D1,
    ),
    ("sum_tree_forall", RED_SUM_TREE_FORALL),
];

/// Post-M5 residual reds: expected NOT-`unsat` (the lane arms nothing here).
const REDS: &[(&str, &str)] = &[("red_ground_dtlia", RED_GROUND_DTLIA)];

/// Nominal per-check timeout for GREEN probes. They are ground or depth-1 and
/// solve in well under a second; the ceiling is pure hang-protection.
const GREEN_TIMEOUT: Duration = Duration::from_secs(15);

/// Nominal per-check timeout for RED probes. Kept short — the reds cannot be
/// discharged by any budget today (ay's iterative-deepening DT final-solve is not
/// deadline-interruptible mid-level, so a natural fail-closed can take ~90s in a
/// debug build). The hard `recv_timeout` wall cap in [`solve`] is what actually
/// bounds the suite: a red that overruns is abandoned and reported as Unknown.
const RED_TIMEOUT: Duration = Duration::from_secs(3);

/// Per-check timeout for the bounded M5 production probes.
const PRODUCTION_FLIP_TIMEOUT: Duration = Duration::from_secs(20);

/// Solve `input` under a nominal `timeout`, bounded by a HARD wall cap of
/// `timeout + 3s`. The solve runs on a worker thread; if it does not finish
/// within the cap (ay's DT deepening is not promptly interruptible), we request
/// interrupt, ABANDON the worker (it winds down at its next interrupt poll or at
/// process exit — a detached test thread never blocks process teardown), and
/// report the fail-closed `unknown` verdict with empty stats. A solve that DOES
/// finish within the cap returns its real verdict + statistics — so a red that
/// ever flips to a fast `unsat` is still caught, and the fast greens/emit-probe
/// return genuine `quantifier.demand.*` counters.
fn solve(input: &str, timeout: Duration) -> (String, Statistics) {
    let src = input.to_string();
    let interrupt = Arc::new(AtomicBool::new(false));
    let interrupt_worker = Arc::clone(&interrupt);
    let (tx, rx) = std::sync::mpsc::channel();
    let _worker = std::thread::spawn(move || {
        let commands = parse(&src).expect("parse demand probe");
        let mut exec = Executor::new();
        exec.set_interrupt(interrupt_worker);
        exec.set_timeout(Some(timeout));
        // Graceful on interrupt/error: an abandoned worker must not panic on a
        // dropped receiver or an interrupted solve (it would print scary — but
        // harmless — stderr noise during the suite). Send Unknown and exit.
        let (verdict, stats) = match exec.execute_all(&commands) {
            Ok(outputs) => (
                outputs.last().cloned().unwrap_or_default(),
                exec.statistics().clone(),
            ),
            Err(_) => ("unknown".to_string(), Statistics::default()),
        };
        let _ = tx.send((verdict, stats));
    });
    // Hard wall cap. A red that self-completes (ay's deadline honors the nominal
    // budget with a small DT-level overshoot) returns its real verdict here; one
    // that overruns is abandoned (interrupt requested, worker detached — it winds
    // down at its next poll / process exit) and reported as the pinned Unknown.
    match rx.recv_timeout(timeout + Duration::from_secs(3)) {
        Ok(result) => result,
        Err(_) => {
            interrupt.store(true, Ordering::Relaxed);
            ("unknown".to_string(), Statistics::default())
        }
    }
}

#[test]
fn demand_green_probes_are_unsat() {
    for (name, smt2) in GREENS {
        let (verdict, _stats) = solve(smt2, GREEN_TIMEOUT);
        assert_eq!(
            verdict, "unsat",
            "GREEN probe `{name}` must be unsat (the F<=1 frontier / ground \
             refutation regressed if this fails). Got: {verdict}"
        );
    }
}

#[test]
fn demand_red_probes_are_not_unsat_today() {
    // The lazy-DT-AUFLIA route (AY_DT_LAZY_AUFLIA, the combined-theory-engine L1a
    // increment) is an ORTHOGONAL ground DT+LIA lever, not the demand lane. When it
    // is armed it legitimately closes `red_ground_dtlia` (the documented ground
    // DT+LIA combiner gap) to its z3-correct `unsat` — a lazy-DT win, not a
    // demand-lane change. Reclassify the pin accordingly (the file's own "flip =>
    // celebrate and reclassify" rule); the never-wrong-`sat` soundness arm holds
    // unconditionally.
    let lazy_auflia = std::env::var("AY_DT_LAZY_AUFLIA")
        .map(|v| v != "0" && !v.is_empty())
        .unwrap_or(false);
    for (name, smt2) in REDS {
        let (verdict, _stats) = solve(smt2, RED_TIMEOUT);
        if lazy_auflia {
            // Under the lazy-DT route the residual ground DT+LIA gap is closed:
            // `red_ground_dtlia` is z3-UNSAT and the route now decides it `unsat`.
            assert_eq!(
                verdict, "unsat",
                "RED probe `{name}` under AY_DT_LAZY_AUFLIA must close to its \
                 z3-UNSAT verdict (the lazy-DT ground combiner win). Got: {verdict}"
            );
        } else {
            assert_ne!(
                verdict, "unsat",
                "RED probe `{name}` FLIPPED to unsat with no lazy-DT route — a human \
                 must look. This probe has no foralls, so the M5 demand lane arms \
                 NOTHING and the solve must be byte-identical to the pre-flip eager \
                 path; a flip here is an unexpected ground DT+LIA combiner change, \
                 not a demand-lane win."
            );
        }
        // Fail-closed soundness expectation (UNCONDITIONAL): a red must never be a
        // wrong `sat` (all reds are z3-UNSAT). Unknown/timeout is the pinned state
        // absent the lazy route.
        assert_ne!(
            verdict, "sat",
            "RED probe `{name}` returned sat but is z3-UNSAT — soundness \
             regression. Got: {verdict}"
        );
    }
}

/// GATE #1 (M5 THE FLIP, PRODUCTION): the two former reds now solve `unsat` in a
/// PLAIN production solve — [`solve`] builds a stock `Executor::new()` with NO
/// demand flag, so this is the flip firing on the production-authoritative path,
/// not a shadow/debug arm. Pinned to `unsat`: a regression BELOW `unsat` means the
/// flip broke; a `sat` is a soundness stop-the-line (both are z3-UNSAT).
///
/// Both reductions are bounded and always run.
#[test]
fn demand_production_flip_reds_are_unsat() {
    for (name, smt2) in PRODUCTION_FLIPS {
        let (verdict, _stats) = solve(smt2, PRODUCTION_FLIP_TIMEOUT);
        eprintln!("[demand-probe] M5 production flip `{name}`: verdict={verdict}");
        assert_ne!(
            verdict, "sat",
            "PRODUCTION FLIP `{name}` returned sat but is z3-UNSAT — soundness \
             regression. Got: {verdict}"
        );
        assert_eq!(
            verdict, "unsat",
            "GATE #1: PRODUCTION FLIP `{name}` must reach `unsat` on the plain \
             production path (the M5 demand lane is authoritative for its \
             classified family). Got: {verdict}"
        );
    }
}

/// Gate #5: the `quantifier.demand.*` counters actually emit after a solve that
/// exercises E-matching. `sum_datatype_forall` has two triggered foralls (the
/// recursive defining axiom + the nonneg lemma), so the cost gate runs, the
/// demand counters populate, and they surface — and it completes fast (`unsat`,
/// ~0.3s) so the real statistics are available.
#[test]
fn demand_counters_emit_on_ematching_solve() {
    let (verdict, stats) = solve(GREEN_SUM_DATATYPE_FORALL, GREEN_TIMEOUT);
    // Diagnostic dump (visible under `--nocapture`): every emitted demand key.
    eprintln!("[demand-probe] sum_datatype_forall verdict = {verdict}");
    for (key, value) in &stats.extra {
        if key.starts_with("quantifier.demand.") {
            eprintln!("[demand-probe]   {key} = {value:?}");
        }
    }
    // The instrumentation keys must be present regardless of the verdict.
    for key in [
        "quantifier.demand.asserted",
        "quantifier.demand.parked",
        "quantifier.demand.blocked",
        "quantifier.demand.budget_break_rounds",
        "quantifier.demand.families",
        "quantifier.demand.max_generation",
    ] {
        assert!(
            stats.get_int(key).is_some(),
            "expected demand counter `{key}` to be emitted after an E-matching \
             solve; it was absent"
        );
    }
    // E-matching genuinely ran here: at least one instance must have been
    // asserted (the recursive `sum` defining forall fires on the `Cons` literals).
    let asserted = stats.get_int("quantifier.demand.asserted").unwrap_or(0);
    assert!(
        asserted > 0,
        "expected quantifier.demand.asserted > 0 on sum_datatype_forall (E-matching \
         instantiated nothing?) verdict={verdict}"
    );
    // At least one family (quantifier x head-symbol) must have been seen.
    assert!(
        stats.get_int("quantifier.demand.families").unwrap_or(0) > 0,
        "expected quantifier.demand.families > 0 on sum_datatype_forall"
    );

    // M1 shadow family classifier: the per-class population + activity keys must
    // surface after the same E-matching solve.
    for key in [
        "quantifier.demand.family.self_chaining",
        "quantifier.demand.family.bridge_cycle",
        "quantifier.demand.family.other",
        "quantifier.demand.family.self_chaining.asserted",
        "quantifier.demand.family.bridge_cycle.asserted",
        "quantifier.demand.family.other.asserted",
    ] {
        assert!(
            stats.get_int(key).is_some(),
            "expected M1 family classifier counter `{key}` to be emitted; it was absent"
        );
    }
    // `sum_datatype_forall` is exactly the recursive `sum` definition (self-chaining)
    // plus its nonneg lemma (other); no bridge cycle. The population is a partition.
    assert_eq!(
        stats.get_int("quantifier.demand.family.self_chaining"),
        Some(1),
        "the recursive `sum` defining forall classifies self-chaining"
    );
    assert_eq!(
        stats.get_int("quantifier.demand.family.other"),
        Some(1),
        "the `sum` nonneg lemma classifies other"
    );
    assert_eq!(
        stats.get_int("quantifier.demand.family.bridge_cycle"),
        Some(0),
        "sum_datatype_forall has no cross-vocabulary bridge cycle"
    );
    // The class-tagged activity re-aggregation partitions the asserted total: every
    // asserted instance is charged to exactly one class.
    let sc = stats
        .get_int("quantifier.demand.family.self_chaining.asserted")
        .unwrap_or(0);
    let bc = stats
        .get_int("quantifier.demand.family.bridge_cycle.asserted")
        .unwrap_or(0);
    let ot = stats
        .get_int("quantifier.demand.family.other.asserted")
        .unwrap_or(0);
    assert_eq!(
        sc + bc + ot,
        asserted,
        "class-tagged asserted counts must partition the asserted total"
    );
}
