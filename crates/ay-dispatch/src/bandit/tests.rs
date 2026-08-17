// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum Arm {
    A,
    B,
    C,
}

impl EngineId for Arm {}

fn approx(a: f64, b: f64, tol: f64) -> bool {
    (a - b).abs() <= tol
}

#[test]
fn rng_is_deterministic() {
    let mut a = Rng::new(42);
    let mut b = Rng::new(42);
    for _ in 0..1_000 {
        assert!(approx(a.next_f64(), b.next_f64(), 0.0));
    }
}

#[test]
fn rng_output_in_unit_interval() {
    let mut r = Rng::new(7);
    for _ in 0..10_000 {
        let x = r.next_f64();
        assert!((0.0..1.0).contains(&x));
    }
}

#[test]
fn mw_rewards_winning_arm() {
    let mut mw = MultiplicativeWeights::new([Arm::A, Arm::B, Arm::C], 0.3, 12345);
    // Arm A always wins, B/C never do.
    for _ in 0..200 {
        mw.update(Arm::A, 1.0);
        mw.update(Arm::B, 0.0);
        mw.update(Arm::C, 0.0);
    }
    let dist = mw.distribution();
    let pa = dist[&Arm::A];
    assert!(pa > 0.95, "expected A-prob > 0.95, got {pa}");
}

#[test]
fn mw_regret_bounded_on_three_arm_trace() {
    // Construct a synthetic trace: arm A has mean reward 0.8,
    // B has 0.5, C has 0.2. MW should concentrate mass on A.
    let mut mw = MultiplicativeWeights::new([Arm::A, Arm::B, Arm::C], 0.2, 99);
    let trace = [
        (Arm::A, 0.8),
        (Arm::B, 0.5),
        (Arm::C, 0.2),
        (Arm::A, 0.9),
        (Arm::B, 0.4),
        (Arm::C, 0.1),
        (Arm::A, 0.85),
        (Arm::B, 0.55),
        (Arm::C, 0.25),
    ];
    for _ in 0..100 {
        for (arm, r) in trace {
            mw.update(arm, r);
        }
    }
    let dist = mw.distribution();
    // Best arm must dominate.
    assert!(dist[&Arm::A] > dist[&Arm::B]);
    assert!(dist[&Arm::B] > dist[&Arm::C]);
}

#[test]
fn mw_sample_respects_distribution() {
    let mut mw = MultiplicativeWeights::new([Arm::A, Arm::B], 0.5, 1);
    for _ in 0..500 {
        mw.update(Arm::A, 1.0);
    }
    // A-prob should be overwhelming.
    let mut counts = [0usize; 2];
    for _ in 0..5_000 {
        match mw.sample().expect("non-empty bandit") {
            Arm::A => counts[0] += 1,
            Arm::B => counts[1] += 1,
            Arm::C => unreachable!(),
        }
    }
    assert!(
        counts[0] > counts[1] * 10,
        "A should vastly outnumber B: {counts:?}"
    );
}

#[test]
fn mw_large_learning_rate_does_not_reset_to_uniform() {
    let mut mw = MultiplicativeWeights::new([Arm::A, Arm::B], 1_000.0, 1);
    mw.update(Arm::A, 1.0);
    let dist = mw.distribution();
    assert!(dist[&Arm::A] > 0.999, "large update was lost: {dist:?}");
}

#[test]
fn mw_arm_recovers_after_extreme_underflow_pressure() {
    let mut mw = MultiplicativeWeights::new([Arm::A, Arm::B], 1_000.0, 1);
    mw.update(Arm::A, 1.0);
    assert!(mw.distribution()[&Arm::A] > 0.999);

    // Equal and then surpass A's cumulative reward. Although B's projected
    // weight underflowed to zero, its cumulative score was not discarded.
    mw.update(Arm::B, 1.0);
    let tied = mw.distribution();
    assert!(approx(tied[&Arm::A], 0.5, 1e-12), "not tied: {tied:?}");
    assert!(approx(tied[&Arm::B], 0.5, 1e-12), "not tied: {tied:?}");

    mw.update(Arm::B, 1.0);
    let dist = mw.distribution();
    assert!(dist[&Arm::B] > 0.999, "B did not recover: {dist:?}");
}

#[test]
fn nan_reward_is_a_no_op() {
    let mut mw = MultiplicativeWeights::new([Arm::A, Arm::B], 0.5, 1);
    mw.update(Arm::A, f64::NAN);
    assert!(approx(mw.distribution()[&Arm::A], 0.5, 1e-12));

    let mut exp3 = Exp3::new([Arm::A, Arm::B], 0.5, 0.05, 1);
    exp3.update(Arm::A, f64::NAN);
    assert!(approx(exp3.distribution()[&Arm::A], 0.5, 1e-12));
}

#[test]
fn exp3_arm_recovers_after_log_weight_underflow_pressure() {
    let mut exp3 = Exp3::new([Arm::A, Arm::B], 1_000.0, 0.05, 1);
    exp3.update(Arm::A, 1.0);
    assert_eq!(exp3.log_weights[&Arm::A], 0.0);
    assert_eq!(exp3.log_weights[&Arm::B], -2_000.0);

    // B is sampled only through the exploration floor, so a reward of
    // 0.05 has importance-weighted value 2.0 and exactly closes the gap.
    exp3.update(Arm::B, 0.05);
    assert!(approx(exp3.log_weights[&Arm::A], 0.0, 1e-9));
    assert!(approx(exp3.log_weights[&Arm::B], 0.0, 1e-9));

    exp3.update(Arm::B, 1.0);
    let dist = exp3.distribution();
    assert!(dist[&Arm::B] > 0.9, "B did not recover: {dist:?}");
}

#[test]
fn exp3_learns_best_arm_with_partial_feedback() {
    // Bandit feedback: each round we pull ONE arm and observe its reward.
    // Rewards: A ~ 0.9, B ~ 0.3, C ~ 0.1 (deterministic for test stability).
    // With enough rounds both losers collapse to the exploration floor of
    // `gamma/K`, so we only assert that A dominates and that neither loser
    // exceeds the best arm.
    let mut exp3 = Exp3::new([Arm::A, Arm::B, Arm::C], 0.2, 0.05, 7);
    let expected = FxHashMap::from_iter([(Arm::A, 0.9), (Arm::B, 0.3), (Arm::C, 0.1)]);
    for _ in 0..2_000 {
        if let Some(arm) = exp3.sample() {
            exp3.update(arm, expected[&arm]);
        }
    }
    let dist = exp3.distribution();
    assert!(
        dist[&Arm::A] > dist[&Arm::B],
        "expected A > B, got {dist:?}"
    );
    assert!(
        dist[&Arm::A] > dist[&Arm::C],
        "expected A > C, got {dist:?}"
    );
    // Each loser sits at (or near) the exploration floor gamma/K.
    let floor = exp3.gamma / 3.0;
    assert!(
        dist[&Arm::B] >= floor - 1e-9 && dist[&Arm::B] <= floor + 0.05,
        "B should sit near the exploration floor {floor}, got {}",
        dist[&Arm::B]
    );
    assert!(
        dist[&Arm::C] >= floor - 1e-9 && dist[&Arm::C] <= floor + 0.05,
        "C should sit near the exploration floor {floor}, got {}",
        dist[&Arm::C]
    );
    // Even the best arm cannot push past `1 - gamma + gamma/K`.
    let cap = 1.0 - exp3.gamma + exp3.gamma / 3.0;
    assert!(
        dist[&Arm::A] <= cap + 1e-9,
        "best arm capped by exploration at {cap}: got {}",
        dist[&Arm::A]
    );
}

#[test]
fn exp3_rejects_nonfinite_parameters() {
    let e = Exp3::<Arm>::new([Arm::A], f64::NAN, -1.0, 0);
    // Defaults applied.
    assert!((e.eta - 0.1).abs() < 1e-12);
    assert!((e.gamma - 0.05).abs() < 1e-12);
}

#[test]
fn exp3_empty_arms_sample_is_none() {
    let mut e = Exp3::<Arm>::new([], 0.1, 0.05, 0);
    assert!(e.sample().is_none());
}

#[test]
fn mw_empty_arms_sample_is_none() {
    let mut mw = MultiplicativeWeights::<Arm>::new([], 0.1, 0);
    assert!(mw.sample().is_none());
}
