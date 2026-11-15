// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Kill-switch coverage for guarded instance clauses
//! (#quantifier-guarded-instances, #quantifier-guarded-enumerative).
//!
//! Its own binary, following `quantifier_proxy_abstraction_kill_switch.rs`:
//! it installs a thread-local `MiscCliFlags` override, which must never race a
//! sibling test that could run interleaved on the same thread.
//!
//! Five positions are covered, because the two lanes are nested under the
//! stage-2 abstraction and each switch must restore its predecessor exactly:
//!
//! | position                               | matcher | enumerative |
//! |----------------------------------------|---------|-------------|
//! | default                                | on      | on IFF the matcher produced no instance |
//! | `--quantifier-guarded-enumerative`     | on      | on everywhere (override) |
//! | `--no-quantifier-guarded-enumerative`  | on      | off |
//! | `--no-quantifier-guarded-instances`    | off     | off (nested)|
//! | `--no-quantifier-proxy-abstraction`    | off     | off — no proxy |
//!
//! The enumerative lane's default is a STRUCTURAL trigger rather than a flag,
//! and the structure was measured: see
//! `quantifier_guarded_enumerative_enabled` and
//! `guarded_enumerative_fires_only_when_the_matcher_produced_nothing` below.
//!
//! What must hold in EVERY position is the soundness direction: a guarded
//! clause may not refute a satisfiable problem, and an abstracted solve may not
//! publish `sat`.

#![allow(clippy::panic)]

mod common;

/// GROUND TRUTH: **SATISFIABLE** (`c := true`, `f(1) := -1`, universal false).
/// Conjoining the E-matched instance `f(1) > 0` would refute it; the guarded
/// clause cannot, because `qproxy := false` satisfies the clause.
const GUARD_SATISFIABLE_SAT: &str = r#"
(set-logic UFLIA)
(declare-fun f (Int) Int)
(declare-const c Bool)
(assert (or c (forall ((x Int)) (> (f x) 0))))
(assert c)
(assert (< (f 1) 0))
(check-sat)
"#;

/// GROUND TRUTH: **UNSATISFIABLE**, and the refutation needs the instance:
/// `(not d)` forces `(not c)`, which forces the universal, which forces
/// `f(1) > 0` against `f(1) < 0`. Every switch position must answer `unsat` or
/// `unknown`, never `sat`.
const GUARD_FORCED_UNSAT: &str = r#"
(set-logic UFLIA)
(declare-fun f (Int) Int)
(declare-const c Bool)
(declare-const d Bool)
(assert (or c (forall ((x Int)) (> (f x) 0))))
(assert (or (not c) d))
(assert (not d))
(assert (< (f 1) 0))
(check-sat)
"#;

/// A TRIGGERLESS universal in disjunct position: no E-matching pattern exists,
/// so the matcher lane cannot reach it at all and it must stay unrefuted in
/// every position. GROUND TRUTH: **SATISFIABLE** (`c := true`).
const TRIGGERLESS_GUARD_SATISFIABLE_SAT: &str = r#"
(set-logic UFLIA)
(declare-fun g () Int)
(declare-const c Bool)
(assert (or c (forall ((x Int)) (> (+ x g) 100))))
(assert c)
(assert (< g 0))
(check-sat)
"#;

/// An entailed top-level universal: no proxy is minted, so every switch
/// position runs the identical code path and must return the identical verdict.
const CONJUNCTIVE_ONLY_UNSAT: &str = r#"
(set-logic UFLIA)
(declare-fun c () Int)
(declare-fun p (Int) Bool)
(assert (forall ((x Int)) (p x)))
(assert (not (p c)))
(check-sat)
"#;

fn assert_sound(position: &str, sat_fixture: &[String], unsat_fixture: &[String]) {
    assert!(
        !sat_fixture.iter().any(|r| r == "unsat"),
        "{position}: the problem is SATISFIABLE — a guarded instance clause is \
         satisfied by `qproxy := false` and may never refute it; got \
         {sat_fixture:?}"
    );
    assert!(
        !unsat_fixture.iter().any(|r| r == "sat"),
        "{position}: the problem is UNSATISFIABLE, and the abstraction is live, \
         so `sat` is forbidden twice over; got {unsat_fixture:?}"
    );
}

#[test]
fn guarded_instances_are_fully_covered_by_their_kill_switches() {
    // Position 1: matcher lane off (enumerative is nested under it, so also
    // off). This is exactly the stage-2 tree.
    let guard = ay_core::misc_test_override::set(ay_core::MiscCliFlags {
        no_quantifier_guarded_instances: true,
        ..Default::default()
    });
    let off_sat = common::solve_vec(GUARD_SATISFIABLE_SAT);
    let off_unsat = common::solve_vec(GUARD_FORCED_UNSAT);
    let off_enum_sat = common::solve_vec(TRIGGERLESS_GUARD_SATISFIABLE_SAT);
    let off_conjunctive = common::solve_vec(CONJUNCTIVE_ONLY_UNSAT);
    drop(guard);

    // Position 2: the parent abstraction switch starves both lanes — no proxy
    // is minted, so no guarded clause can be built even with both own switches
    // in their default ON position.
    let guard = ay_core::misc_test_override::set(ay_core::MiscCliFlags {
        no_quantifier_proxy_abstraction: true,
        ..Default::default()
    });
    let starved_sat = common::solve_vec(GUARD_SATISFIABLE_SAT);
    let starved_unsat = common::solve_vec(GUARD_FORCED_UNSAT);
    let starved_conjunctive = common::solve_vec(CONJUNCTIVE_ONLY_UNSAT);
    drop(guard);

    // Position 3: the enumerative lane FORCED ON for every solve, overriding
    // the structural trigger. The triggerless fixture can produce a guarded
    // clause here whatever its shape, so this position's soundness assertion on
    // it is never vacuous.
    let guard = ay_core::misc_test_override::set(ay_core::MiscCliFlags {
        quantifier_guarded_enumerative: true,
        ..Default::default()
    });
    let enum_on_sat = common::solve_vec(GUARD_SATISFIABLE_SAT);
    let enum_on_unsat = common::solve_vec(GUARD_FORCED_UNSAT);
    let enum_on_triggerless = common::solve_vec(TRIGGERLESS_GUARD_SATISFIABLE_SAT);
    let enum_on_conjunctive = common::solve_vec(CONJUNCTIVE_ONLY_UNSAT);
    drop(guard);

    // Position 4: the enumerative lane explicitly KILLED. Nothing it could
    // build is built, whatever the structural trigger says.
    let guard = ay_core::misc_test_override::set(ay_core::MiscCliFlags {
        no_quantifier_guarded_enumerative: true,
        ..Default::default()
    });
    let enum_off_sat = common::solve_vec(GUARD_SATISFIABLE_SAT);
    let enum_off_unsat = common::solve_vec(GUARD_FORCED_UNSAT);
    let enum_off_triggerless = common::solve_vec(TRIGGERLESS_GUARD_SATISFIABLE_SAT);
    let enum_off_conjunctive = common::solve_vec(CONJUNCTIVE_ONLY_UNSAT);
    drop(guard);

    // Position 5: default (matcher on; enumerative on exactly when the
    // E-matcher produced no instance in the solve).
    let on_sat = common::solve_vec(GUARD_SATISFIABLE_SAT);
    let on_unsat = common::solve_vec(GUARD_FORCED_UNSAT);
    let on_enum_sat = common::solve_vec(TRIGGERLESS_GUARD_SATISFIABLE_SAT);
    let on_conjunctive = common::solve_vec(CONJUNCTIVE_ONLY_UNSAT);

    assert_sound("matcher lane OFF", &off_sat, &off_unsat);
    assert_sound("abstraction OFF", &starved_sat, &starved_unsat);
    assert_sound("enumerative lane FORCED ON", &enum_on_sat, &enum_on_unsat);
    assert_sound("enumerative lane KILLED", &enum_off_sat, &enum_off_unsat);
    assert_sound("default (structural trigger)", &on_sat, &on_unsat);
    for (position, results) in [
        ("matcher lane OFF", &off_enum_sat),
        ("enumerative lane FORCED ON", &enum_on_triggerless),
        ("enumerative lane KILLED", &enum_off_triggerless),
        ("default (structural trigger)", &on_enum_sat),
    ] {
        assert!(
            !results.iter().any(|r| r == "unsat"),
            "{position}: the triggerless fixture is SATISFIABLE; got {results:?}"
        );
    }

    // The no-proxy family runs the identical code path in every position, so
    // its verdict must be identical — not merely sound.
    assert_eq!(
        off_conjunctive, on_conjunctive,
        "no proxy is minted for an all-entailed assertion set, so the guarded \
         lanes are inert and both switch positions must produce the same output"
    );
    assert_eq!(
        starved_conjunctive, on_conjunctive,
        "same, with the parent abstraction switch flipped"
    );
    assert_eq!(
        enum_on_conjunctive, on_conjunctive,
        "same, with the enumerative lane forced on"
    );
    assert_eq!(
        enum_off_conjunctive, on_conjunctive,
        "same, with the enumerative lane killed"
    );
    assert!(
        on_conjunctive.iter().any(|r| r == "unsat"),
        "the entailed top-level universal must still be instantiated and \
         refuted; got {on_conjunctive:?}"
    );
}

/// A proxy is internal scaffolding. It must not reach published output in any
/// switch position — including through a guarded clause, which is the first
/// mechanism that puts a proxy into an assertion the solver can report on.
#[test]
fn guarded_clauses_never_leak_a_proxy_into_published_output() {
    let with_get_model = format!(
        "{}\n(get-model)\n",
        GUARD_SATISFIABLE_SAT
            .trim_end()
            .trim_end_matches("(check-sat)")
    );
    let with_get_model = format!("{with_get_model}(check-sat)\n(get-model)\n");
    for line in common::solve_vec(&with_get_model) {
        assert!(
            !line.contains("qproxy"),
            "a guarded clause leaked an abstraction proxy into published \
             output: {line:?}"
        );
    }
}

/// The ONLY-ROUTE half of the structural trigger. A triggerless interpreted
/// universal reachable only under a two-step Boolean chain: the E-matcher has
/// no pattern to fire on and creates NOTHING, so the guarded enumerative lane
/// is the only route to any instance at all and must fire by default.
///
/// GROUND TRUTH: **UNSATISFIABLE**. `(not d)` forces `(not c)`, which forces
/// the universal, and the universal is false at `x := 0`
/// (`(div 0 2) = 0`, not `> 100`).
const ONLY_ROUTE_TRIGGERLESS_UNSAT: &str = r#"
(set-logic UFLIA)
(declare-const c Bool)
(declare-const d Bool)
(assert (or c (forall ((x Int)) (> (div x 2) 100))))
(assert (or (not c) d))
(assert (not d))
(check-sat)
"#;

/// The MATCHER-PRODUCED half. Byte-for-byte the problem above plus a second,
/// trigger-carrying universal whose pattern DOES match a ground term the
/// problem contains, so the E-matcher creates an instance before the
/// enumerative lane is reached. The added conjunct is satisfiable on its own
/// and shares no symbol with the refutation, so the problem is still
/// **UNSATISFIABLE** for exactly the same reason — only the structural trigger
/// differs.
const MATCHER_PRODUCED_TRIGGERLESS_UNSAT: &str = r#"
(set-logic UFLIA)
(declare-const c Bool)
(declare-const d Bool)
(declare-fun f (Int) Int)
(assert (forall ((y Int)) (! (>= (f y) 0) :pattern ((f y)))))
(assert (>= (f 3) 0))
(assert (or c (forall ((x Int)) (> (div x 2) 100))))
(assert (or (not c) d))
(assert (not d))
(check-sat)
"#;

/// What one solve says about the guarded enumerative lane, read from the
/// executor's own statistics rather than inferred from its verdict.
#[derive(Debug)]
struct LaneObservation {
    lines: Vec<String>,
    /// Eligible universals whose structural gate this executor consulted.
    consulted: u64,
    /// Of those, the universals the gate admitted to enumeration.
    admitted: u64,
    /// Guarded instance clauses asserted. Both fixtures above give the
    /// matcher lane nothing to guard (their one unentailed universal is
    /// triggerless), and every arm below whose gate declines asserts this is
    /// zero, so on these fixtures every clause counted here is the
    /// enumerative lane's.
    guarded_asserted: u64,
}

fn solve_observing_lane(smt: &str) -> LaneObservation {
    let commands =
        ay_frontend::parse(smt).unwrap_or_else(|err| panic!("parse failed: {err}\nSMT2:\n{smt}"));
    let mut exec = ay_dpll::Executor::new();
    let lines = exec
        .execute_all(&commands)
        .unwrap_or_else(|err| panic!("execution failed: {err}\nSMT2:\n{smt}"));
    let stats = exec.statistics();
    let int = |key: &str| stats.get_int(key).unwrap_or(0);
    LaneObservation {
        consulted: int("quantifier.guarded_enumerative.consulted"),
        admitted: int("quantifier.guarded_enumerative.admitted"),
        guarded_asserted: stats.quantifier_guarded_instances_asserted,
        lines,
    }
}

/// The structural trigger, pinned in BOTH directions.
///
/// This is the test the `#quantifier-guarded-enumerative` gate exists for. A
/// global default for this lane was measured **net -1 corpus-wide** while being
/// worth **+65 of 200** on one bit-vector family; the separator between the two
/// populations is whether the E-matcher produced any instance before the lane
/// ran (measured: 0 on every sampled `2018-Preiner-cav18` file that reaches the
/// quantifier pipeline, 423-1 295 on every AUFDTLIRA `spark2014bench` file the
/// lane costs a refutation).
///
/// The gate is observed DIRECTLY, through its census
/// (`quantifier.guarded_enumerative.{consulted,admitted}`) and the guarded
/// clauses the lane asserted, not through the final verdict. The verdict was
/// the original observable and stopped being one: the ground-first fallback
/// (#qe-ground-first, d5bfab7d5) decides the matcher-produced fixture WITHOUT
/// its trigger-carrying axiom on a disposable probe, where the E-matcher
/// produces nothing and the lane is correctly the only route, so the fixture
/// is now (correctly) refuted by default while THIS executor's gate declined.
/// The decline is therefore pinned twice: with the fallback (the census must
/// not count the probe's firing) and with it stood down (the gate alone). The
/// matcher-produced verdict is asserted for soundness only: pinning `unknown`
/// would pin an incompleteness, and which route refutes it is not this test's
/// business.
///
/// A MUTATION must make this fail: forcing the lane on everywhere (the
/// `--quantifier-guarded-enumerative` arm, or the structural condition
/// dropped) makes the matcher-produced census admit, and the pre-gate opt-in
/// default (07212780a reverted) makes the only-route census decline. Both are
/// asserted, so neither an always-on nor an always-off implementation passes.
#[test]
fn guarded_enumerative_fires_only_when_the_matcher_produced_nothing() {
    let default_only_route = solve_observing_lane(ONLY_ROUTE_TRIGGERLESS_UNSAT);
    let default_matcher_produced = solve_observing_lane(MATCHER_PRODUCED_TRIGGERLESS_UNSAT);

    let guard = ay_core::misc_test_override::set(ay_core::MiscCliFlags {
        no_ground_first: true,
        ..Default::default()
    });
    let no_fallback_matcher_produced = solve_observing_lane(MATCHER_PRODUCED_TRIGGERLESS_UNSAT);
    drop(guard);

    let guard = ay_core::misc_test_override::set(ay_core::MiscCliFlags {
        quantifier_guarded_enumerative: true,
        ..Default::default()
    });
    let forced_matcher_produced = solve_observing_lane(MATCHER_PRODUCED_TRIGGERLESS_UNSAT);
    drop(guard);

    let guard = ay_core::misc_test_override::set(ay_core::MiscCliFlags {
        no_quantifier_guarded_enumerative: true,
        ..Default::default()
    });
    let killed_only_route = solve_observing_lane(ONLY_ROUTE_TRIGGERLESS_UNSAT);
    drop(guard);

    let positions = [
        ("default / only-route", &default_only_route),
        ("default / matcher-produced", &default_matcher_produced),
        (
            "ground-first off / matcher-produced",
            &no_fallback_matcher_produced,
        ),
        ("forced on / matcher-produced", &forced_matcher_produced),
        ("killed / only-route", &killed_only_route),
    ];
    for (position, observed) in positions {
        // Soundness first, in every position: both fixtures are UNSATISFIABLE
        // and the abstraction is live, so `sat` is forbidden twice over.
        assert!(
            !observed.lines.iter().any(|r| r == "sat"),
            "{position}: the fixture is UNSATISFIABLE; got {observed:?}"
        );
        // Every position reaches the gate, so no census below is vacuous: a
        // zero `admitted` is the gate saying no, not a universal that never
        // got there.
        assert!(
            observed.consulted >= 1,
            "{position}: the triggerless unentailed universal is eligible, so \
             the gate must be consulted; got {observed:?}"
        );
    }

    // The trigger admits the only-route fixture by default and the lane builds
    // its guarded clauses...
    assert!(
        default_only_route.admitted >= 1 && default_only_route.guarded_asserted >= 1,
        "the E-matcher creates no instance here, so the enumerative lane is the \
         only route and must fire by default; got {default_only_route:?}"
    );
    assert!(
        default_only_route.lines.iter().any(|r| r == "unsat"),
        "the only-route fixture is refuted by default; got {default_only_route:?}"
    );
    // ...and the kill switch takes the lane away, at the gate.
    assert!(
        killed_only_route.admitted == 0 && killed_only_route.guarded_asserted == 0,
        "the kill switch outranks the structural trigger; got {killed_only_route:?}"
    );
    // The trigger declines the matcher-produced fixture by default, whether or
    // not the ground-first probe then decides it on its own executor...
    for (position, observed) in [
        ("default / matcher-produced", &default_matcher_produced),
        (
            "ground-first off / matcher-produced",
            &no_fallback_matcher_produced,
        ),
    ] {
        assert!(
            observed.admitted == 0 && observed.guarded_asserted == 0,
            "{position}: the E-matcher already produced an instance here, so \
             the enumerative lane must decline, whatever a probe decided; got \
             {observed:?}"
        );
    }
    // ...and the override restores it, so the decline is the trigger's doing
    // and not an ineligible fixture.
    assert!(
        forced_matcher_produced.admitted >= 1 && forced_matcher_produced.guarded_asserted >= 1,
        "`--quantifier-guarded-enumerative` removes the structural condition, \
         so the lane must fire on the same fixture; got {forced_matcher_produced:?}"
    );
    assert!(
        forced_matcher_produced.lines.iter().any(|r| r == "unsat"),
        "the same fixture is refuted with the lane forced on; got \
         {forced_matcher_produced:?}"
    );
}
