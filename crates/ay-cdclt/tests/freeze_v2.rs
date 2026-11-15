// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Interface freeze v2, the engine side: KC1 (one search per check, per
//! engine), KC2 (no borrowed store, assumptions with their failed core,
//! level-0 units, `Send`), KC25 (the default and the lane-parity profiles).

use ay_cdclt::{Engine, EngineConfig, Guard, SearchProfile, Verdict};
use ay_core::{Sort, TermId, TermStore, TheoryLit};
use num_bigint::BigInt;
use num_rational::BigRational;

fn q(n: i64) -> BigRational {
    BigRational::from_integer(BigInt::from(n))
}

/// `x ≤ 0` asserted, with the atoms `x ≥ 1`, `y ≥ 0`, `x - y ≤ 3` and a
/// Boolean `p` for assumptions.
struct Fixture {
    terms: TermStore,
    x_le_0: TermId,
    x_ge_1: TermId,
    y_ge_0: TermId,
    diff: TermId,
    p: TermId,
}

fn fixture() -> Fixture {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let p = terms.mk_var("p", Sort::Bool);
    let zero = terms.mk_rational(q(0));
    let one = terms.mk_rational(q(1));
    let three = terms.mk_rational(q(3));
    let x_le_0 = terms.mk_le(x, zero);
    let x_ge_1 = terms.mk_ge(x, one);
    let y_ge_0 = terms.mk_ge(y, zero);
    let x_minus_y = terms.mk_sub(vec![x, y]);
    let diff = terms.mk_le(x_minus_y, three);
    Fixture {
        terms,
        x_le_0,
        x_ge_1,
        y_ge_0,
        diff,
        p,
    }
}

/// KC2: the failed core names exactly the assumptions the refutation used;
/// the same engine then answers other assumption sets, each in one search
/// (KC1).
#[test]
fn assumptions_answer_with_their_failed_core_in_one_search_each() {
    let Fixture {
        mut terms,
        x_le_0,
        x_ge_1,
        y_ge_0,
        diff,
        p,
    } = fixture();
    let mut engine = Engine::new(EngineConfig::default());
    engine.assert(x_le_0);
    engine.assert(diff);
    let guard = Guard::new();

    let outcome = engine.check(&mut terms, &[p, x_ge_1, y_ge_0], &guard);
    assert_eq!(outcome.verdict, Verdict::Unsat, "{:?}", outcome.reason);
    assert!(outcome.failed.contains(&x_ge_1), "{:?}", outcome.failed);
    assert!(!outcome.failed.contains(&p), "{:?}", outcome.failed);
    assert_eq!(outcome.stats.solve_calls, 1);

    let outcome = engine.check(&mut terms, &[p, y_ge_0], &guard);
    assert_eq!(outcome.verdict, Verdict::Sat, "{:?}", outcome.reason);
    assert!(outcome.failed.is_empty());
    assert_eq!(engine.atom_value(p), Some(true));
    assert_eq!(outcome.stats.solve_calls, 1);

    let not_x_ge_1 = terms.mk_not(x_ge_1);
    let outcome = engine.check(&mut terms, &[not_x_ge_1], &guard);
    assert_eq!(outcome.verdict, Verdict::Sat, "{:?}", outcome.reason);

    let outcome = engine.check(&mut terms, &[], &guard);
    assert_eq!(outcome.verdict, Verdict::Sat, "{:?}", outcome.reason);
    assert_eq!(outcome.stats.solve_calls, 1);
}

/// KC1: K1 holds per engine (per worker) across every check it runs:
/// assertions added between checks, with and without recording.
#[test]
fn every_check_of_an_engine_is_exactly_one_search() {
    let Fixture {
        mut terms,
        x_le_0,
        x_ge_1,
        y_ge_0,
        diff,
        ..
    } = fixture();
    for record_proofs in [false, true] {
        let mut engine = Engine::new(EngineConfig {
            record_proofs,
            ..EngineConfig::default()
        });
        let guard = Guard::new();
        let mut verdicts = Vec::new();
        for atom in [x_le_0, diff, y_ge_0, x_ge_1] {
            engine.assert(atom);
            let outcome = engine.check(&mut terms, &[], &guard);
            assert_eq!(outcome.stats.solve_calls, 1, "{:?}", outcome.stats);
            assert_eq!(engine.stats().solve_calls, 1);
            assert_eq!(outcome.proof.is_some(), record_proofs);
            verdicts.push(outcome.verdict);
        }
        assert_eq!(
            verdicts,
            [Verdict::Sat, Verdict::Sat, Verdict::Sat, Verdict::Unsat]
        );
    }
}

/// KC2: an asserted bound is a level-0 unit of the check.
#[test]
fn level_zero_units_are_reported() {
    let Fixture {
        mut terms,
        x_le_0,
        diff,
        ..
    } = fixture();
    let mut engine = Engine::new(EngineConfig::default());
    engine.assert(x_le_0);
    engine.assert(diff);
    let outcome = engine.check(&mut terms, &[], &Guard::new());
    assert_eq!(outcome.verdict, Verdict::Sat);
    assert!(
        outcome.level0_units.contains(&TheoryLit::new(x_le_0, true)),
        "{:?}",
        outcome.level0_units
    );
    assert!(outcome.sigma.is_empty());
}

/// KC2 / KC7: the engine owns no borrow, so it is built before the store
/// exists and runs its check on another thread.
#[test]
fn an_engine_moves_to_another_thread() {
    let mut engine = Engine::new(EngineConfig::default());
    let Fixture {
        mut terms,
        x_le_0,
        x_ge_1,
        ..
    } = fixture();
    engine.assert(x_le_0);
    engine.assert(x_ge_1);
    let verdict = std::thread::spawn(move || engine.check(&mut terms, &[], &Guard::new()).verdict)
        .join()
        .expect("the worker thread finishes");
    assert_eq!(verdict, Verdict::Unsat);
}

/// KC25: the kernel's default profile is ay-sat's own; the lane-parity
/// profile is a named configuration, and both decide the same way.
#[test]
fn both_search_profiles_decide_alike() {
    assert_eq!(EngineConfig::default().search, SearchProfile::SatDefault);
    assert_eq!(
        EngineConfig::lane_parity().search,
        SearchProfile::LaneParity
    );
    let Fixture {
        mut terms,
        x_le_0,
        x_ge_1,
        y_ge_0,
        diff,
        p,
    } = fixture();
    for cfg in [EngineConfig::default(), EngineConfig::lane_parity()] {
        let mut engine = Engine::new(cfg);
        for atom in [x_le_0, diff, y_ge_0] {
            engine.assert(atom);
        }
        let outcome = engine.check(&mut terms, &[p], &Guard::new());
        assert_eq!(outcome.verdict, Verdict::Sat);
        let outcome = engine.check(&mut terms, &[x_ge_1], &Guard::new());
        assert_eq!(outcome.verdict, Verdict::Unsat);
        assert_eq!(outcome.failed, [x_ge_1]);
    }
}
