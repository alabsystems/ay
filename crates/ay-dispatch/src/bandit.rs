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
mod tests;
