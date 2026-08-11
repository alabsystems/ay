// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Online-learning bandit primitives used by engine-dispatch schedulers.
//!
//! This module provides two classical adversarial-bandit algorithms:
//!
//! * [`MultiplicativeWeights`] (a.k.a. *Hedge*): full-information setting.
//!   After each round the learner observes the reward for *every* arm.
//!   Achieves `O(sqrt(T log K))` regret against the best fixed arm.
//!
//! * [`Exp3`]: partial-information (bandit) setting. After each round the
//!   learner observes the reward for the *pulled* arm only. Uses importance
//!   weighting to construct unbiased reward estimates. Achieves
//!   `O(sqrt(T K log K))` regret.
//!
//! Both implementations are generic over an engine-id type implementing
//! [`EngineId`]. Rewards are expected in `[0.0, 1.0]`; values outside that
//! range are clamped. Internal reward totals or weights are stored in a
//! numerically stable domain and projected to probabilities for sampling.
//!
//! # References
//!
//! * Auer, Cesa-Bianchi, Freund, Schapire. "The Nonstochastic Multiarmed
//!   Bandit Problem." SIAM J. Comput. 32(1), 2002. (EXP3)
//! * Freund, Schapire. "A Decision-Theoretic Generalization of On-Line
//!   Learning and an Application to Boosting." JCSS 55(1), 1997. (Hedge/MW)
//! * Cesa-Bianchi, Lugosi. *Prediction, Learning, and Games*, 2006. (survey)

use crate::EngineId;
use rustc_hash::FxHashMap;

// ---------------------------------------------------------------------------
// Deterministic xorshift PRNG
// ---------------------------------------------------------------------------

/// Minimal xorshift64* PRNG.
///
/// Bandit sampling needs a fast deterministic source of `f64`s in `[0, 1)`.
/// Pulling in `rand` would be overkill for the handful of floats we draw per
/// dispatch tick, so we use an inline xorshift64*. The period is
/// `2^64 - 1`, which is more than adequate for solver-side scheduling.
#[derive(Debug, Clone)]
pub struct Rng {
    state: u64,
}

impl Rng {
    /// Create a PRNG seeded with `seed`.
    ///
    /// `seed == 0` is remapped to `0x9e37_79b9_7f4a_7c15` (golden ratio mix)
    /// because xorshift64* degenerates on an all-zero state.
    #[must_use]
    pub fn new(seed: u64) -> Self {
        let state = if seed == 0 {
            0x9e37_79b9_7f4a_7c15
        } else {
            seed
        };
        Self { state }
    }

    fn next_u64(&mut self) -> u64 {
        let mut x = self.state;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.state = x;
        x.wrapping_mul(0x2545_f491_4f6c_dd1d)
    }

    /// Uniform `f64` in `[0.0, 1.0)`.
    pub fn next_f64(&mut self) -> f64 {
        // Top 53 bits → exact IEEE-754 mantissa.
        let bits = self.next_u64() >> 11;
        (bits as f64) * (1.0 / ((1u64 << 53) as f64))
    }
}

// ---------------------------------------------------------------------------
// Multiplicative-weights / Hedge
// ---------------------------------------------------------------------------

/// Multiplicative-weights (Hedge) bandit in the *full-information* setting.
///
/// Keeps a cumulative reward offset per arm. For sampling, each offset is
/// projected to the relative weight `exp(eta * (reward - best_reward))`, which
/// is equivalent to multiplying by `exp(eta * reward)` without overflowing or
/// losing a temporarily underflowed arm's reward history.
///
/// Full-information MW assumes the learner sees rewards for *all* arms each
/// round; [`Self::update_all`] implements that. [`Self::update`] is a
/// convenience for the single-arm case (equivalent to giving all other arms
/// reward `0.0`).
#[derive(Debug, Clone)]
pub struct MultiplicativeWeights<E: EngineId> {
    // Cumulative rewards translated so that the best score is zero. Keeping
    // these separately from the projected weights means an `exp` underflow is
    // only a temporary sampling result, not lost learning history.
    scores: FxHashMap<E, f64>,
    weights: FxHashMap<E, f64>,
    engines: Vec<E>,
    eta: f64,
    rng: Rng,
}

impl<E: EngineId> MultiplicativeWeights<E> {
    fn sorted_engines(engines: impl IntoIterator<Item = E>) -> (FxHashMap<E, f64>, Vec<E>) {
        let mut weights = FxHashMap::default();
        let mut ordered = Vec::new();
        for engine in engines {
            if weights.insert(engine, 1.0).is_none() {
                ordered.push(engine);
            }
        }
        ordered.sort_by(|a, b| format!("{a:?}").cmp(&format!("{b:?}")));
        (weights, ordered)
    }

    /// Construct a bandit with a uniform prior over `engines`.
    ///
    /// `eta` is the learning rate; typical values are in `[0.05, 0.5]`.
    /// Non-finite or non-positive `eta` is clamped to `0.1` to keep the
    /// algorithm well-defined.
    #[must_use]
    pub fn new(engines: impl IntoIterator<Item = E>, eta: f64, seed: u64) -> Self {
        let (weights, engines) = Self::sorted_engines(engines);
        let scores = engines
            .iter()
            .copied()
            .map(|engine| (engine, 0.0))
            .collect();
        let eta = if eta.is_finite() && eta > 0.0 {
            eta
        } else {
            0.1
        };
        Self {
            scores,
            weights,
            engines,
            eta,
            rng: Rng::new(seed),
        }
    }

    /// Read-only view of the relative weights.
    ///
    /// The largest weight is `1.0`; other entries are the exponential
    /// projection of their cumulative-reward gap from the leader. A very
    /// large gap may therefore appear as zero when the projection underflows.
    /// The cumulative score is retained separately, so later rewards can make
    /// a zero-valued projected weight recover.
    #[must_use]
    pub fn weights(&self) -> &FxHashMap<E, f64> {
        &self.weights
    }

    /// Probability distribution over engines (normalised weights).
    ///
    /// Returns an empty map if the bandit has no arms.
    #[must_use]
    pub fn distribution(&self) -> FxHashMap<E, f64> {
        let sum: f64 = self
            .engines
            .iter()
            .filter_map(|engine| self.weights.get(engine))
            .sum();
        if sum <= 0.0 {
            return FxHashMap::default();
        }
        self.engines
            .iter()
            .filter_map(|engine| {
                self.weights
                    .get(engine)
                    .map(|weight| (*engine, weight / sum))
            })
            .collect()
    }

    /// Sample an engine proportional to its weight.
    ///
    /// Returns `None` only when the bandit has no arms.
    pub fn sample(&mut self) -> Option<E> {
        let sum: f64 = self
            .engines
            .iter()
            .filter_map(|engine| self.weights.get(engine))
            .sum();
        if sum <= 0.0 {
            // Re-uniformise if the weights collapsed (numerical underflow).
            for engine in &self.engines {
                if let Some(weight) = self.weights.get_mut(engine) {
                    *weight = 1.0;
                }
            }
        }
        let sum: f64 = self
            .engines
            .iter()
            .filter_map(|engine| self.weights.get(engine))
            .sum();
        if sum <= 0.0 {
            return None;
        }
        let target = self.rng.next_f64() * sum;
        let mut acc = 0.0;
        let mut last = None;
        for &e in &self.engines {
            let w = self.weights[&e];
            acc += w;
            last = Some(e);
            if acc >= target {
                return Some(e);
            }
        }
        last
    }

    /// Update the weight of a single arm.
    ///
    /// `reward` is clamped to `[0.0, 1.0]` (with NaN treated as zero). The
    /// projected relative weights are refreshed from cumulative reward
    /// offsets after the update.
    pub fn update(&mut self, engine: E, reward: f64) {
        let Some(score) = self.scores.get_mut(&engine) else {
            return;
        };
        *score += finite_reward(reward);
        self.refresh_weights();
    }

    /// Update all arms from a full-information reward vector.
    ///
    /// Missing arms default to reward `0.0`. Values outside `[0.0, 1.0]` are
    /// clamped.
    pub fn update_all(&mut self, rewards: &FxHashMap<E, f64>) {
        for engine in &self.engines {
            let reward = finite_reward(rewards.get(engine).copied().unwrap_or(0.0));
            if let Some(score) = self.scores.get_mut(engine) {
                *score += reward;
            }
        }
        self.refresh_weights();
    }

    fn refresh_weights(&mut self) {
        let max_score = self
            .engines
            .iter()
            .filter_map(|engine| self.scores.get(engine))
            .copied()
            .fold(f64::NEG_INFINITY, f64::max);
        if max_score.is_finite() && max_score != 0.0 {
            for engine in &self.engines {
                if let Some(score) = self.scores.get_mut(engine) {
                    *score -= max_score;
                }
            }
        }
        for engine in &self.engines {
            if let (Some(score), Some(weight)) =
                (self.scores.get(engine), self.weights.get_mut(engine))
            {
                *weight = (self.eta * *score).exp();
            }
        }
    }
}

// ---------------------------------------------------------------------------
// EXP3
// ---------------------------------------------------------------------------

/// Adversarial bandit algorithm (Auer et al. 2002) for the partial-information
/// setting.
///
/// Maintains log-weights `L[a]` per arm. Sampling probability for arm `a` is
/// `(1 - gamma) * p_a + gamma / K` where
/// `p_a = exp(L[a]) / sum_a exp(L[a])` and `K` is the number of arms. On each
/// pull the reward for the chosen arm is upweighted by `reward / p_a`
/// (importance-weighted); unchosen arms receive no update.
///
/// `gamma` controls the exploration floor; typical values are in
/// `[0.01, 0.2]`. Higher `gamma` → more uniform sampling.
#[derive(Debug, Clone)]
pub struct Exp3<E: EngineId> {
    log_weights: FxHashMap<E, f64>,
    engines: Vec<E>,
    eta: f64,
    gamma: f64,
    rng: Rng,
}

impl<E: EngineId> Exp3<E> {
    fn sorted_engines(engines: impl IntoIterator<Item = E>) -> (FxHashMap<E, f64>, Vec<E>) {
        let mut log_weights = FxHashMap::default();
        let mut ordered = Vec::new();
        for engine in engines {
            if log_weights.insert(engine, 0.0).is_none() {
                ordered.push(engine);
            }
        }
        ordered.sort_by(|a, b| format!("{a:?}").cmp(&format!("{b:?}")));
        (log_weights, ordered)
    }

    /// Construct an EXP3 bandit with uniform log-weights.
    ///
    /// `eta` is the learning rate and `gamma` the exploration rate.
    /// Non-finite or out-of-range parameters are clamped to sensible defaults
    /// (`eta = 0.1`, `gamma = 0.05`).
    #[must_use]
    pub fn new(engines: impl IntoIterator<Item = E>, eta: f64, gamma: f64, seed: u64) -> Self {
        let (log_weights, engines) = Self::sorted_engines(engines);
        let eta = if eta.is_finite() && eta > 0.0 {
            eta
        } else {
            0.1
        };
        let gamma = if gamma.is_finite() && (0.0..=1.0).contains(&gamma) {
            gamma
        } else {
            0.05
        };
        Self {
            log_weights,
            engines,
            eta,
            gamma,
            rng: Rng::new(seed),
        }
    }

    /// Read-only view of the log-weights.
    #[must_use]
    pub fn log_weights(&self) -> &FxHashMap<E, f64> {
        &self.log_weights
    }

    /// Sampling distribution used on the next pull.
    #[must_use]
    pub fn distribution(&self) -> FxHashMap<E, f64> {
        let k = self.engines.len();
        if k == 0 {
            return FxHashMap::default();
        }
        let max_log = self
            .engines
            .iter()
            .filter_map(|engine| self.log_weights.get(engine))
            .copied()
            .fold(f64::NEG_INFINITY, f64::max);
        let weights: Vec<(E, f64)> = self
            .engines
            .iter()
            .filter_map(|engine| {
                self.log_weights
                    .get(engine)
                    .map(|log_weight| (*engine, (log_weight - max_log).exp()))
            })
            .collect();
        let sum: f64 = weights.iter().map(|(_, weight)| *weight).sum();
        let k_f = k as f64;
        weights
            .into_iter()
            .map(|(e, w)| {
                let p = if sum > 0.0 { w / sum } else { 1.0 / k_f };
                let mixed = (1.0 - self.gamma).mul_add(p, self.gamma / k_f);
                (e, mixed)
            })
            .collect()
    }

    /// Sample an arm proportional to the mixed distribution.
    pub fn sample(&mut self) -> Option<E> {
        let dist = self.distribution();
        if dist.is_empty() {
            return None;
        }
        let target = self.rng.next_f64();
        let mut acc = 0.0;
        let mut last = None;
        for &e in &self.engines {
            let Some(probability) = dist.get(&e).copied() else {
                continue;
            };
            acc += probability;
            last = Some(e);
            if acc >= target {
                return Some(e);
            }
        }
        last
    }

    /// Update the pulled arm using an importance-weighted reward.
    ///
    /// `reward` is clamped to `[0.0, 1.0]`. If the arm has zero sampling
    /// probability (shouldn't happen with `gamma > 0`) the update is a no-op.
    pub fn update(&mut self, engine: E, reward: f64) {
        let reward = finite_reward(reward);
        let dist = self.distribution();
        let Some(p) = dist.get(&engine).copied() else {
            return;
        };
        if p <= 0.0 {
            return;
        }
        let estimate = reward / p;
        if let Some(l) = self.log_weights.get_mut(&engine) {
            let increment = self.eta * estimate;
            *l += if increment.is_finite() {
                increment
            } else {
                f64::MAX
            };
        }
        self.normalise_log_weights();
    }

    fn normalise_log_weights(&mut self) {
        // Log-weights are translation-invariant. Keep their maximum at zero so
        // repeated updates cannot overflow before `distribution` applies its
        // own log-sum-exp stabilisation. Finite negative gaps are retained even
        // when their exponential projection temporarily underflows: a later
        // reward can then close or reverse the stored gap.
        let max_log = self
            .engines
            .iter()
            .filter_map(|engine| self.log_weights.get(engine))
            .copied()
            .fold(f64::NEG_INFINITY, f64::max);
        if max_log.is_finite() && max_log != 0.0 {
            for engine in &self.engines {
                if let Some(log_weight) = self.log_weights.get_mut(engine) {
                    *log_weight -= max_log;
                }
            }
        }
    }
}

/// Clamp a reward to the algorithm's domain. NaN carries no ordering
/// information, so treat it as zero rather than poisoning every weight.
fn finite_reward(reward: f64) -> f64 {
    if reward.is_nan() {
        0.0
    } else {
        reward.clamp(0.0, 1.0)
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
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
}
