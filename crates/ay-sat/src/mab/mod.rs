// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Multi-armed bandit selection for SAT branching heuristics.
//!
//! Implements UCB1-based online selection between EVSIDS, VMTF, and CHB
//! branching heuristics. The controller scores heuristic epochs at restart
//! boundaries using a composite reward signal (LBD quality + propagation
//! efficiency), then selects the next arm via the UCB1 formula.
//!
//! ## Reward Signal
//!
//! The reward combines two normalized components:
//! - **LBD quality** (weight 0.7): `1 / (1 + avg_lbd)` -- lower LBD means
//!   the heuristic is guiding the solver toward tighter learned clauses.
//! - **Propagation efficiency** (weight 0.3): `propagations / (decisions + 1)`
//!   normalized to [0, 1] via `min(ratio / PROP_EFF_CAP, 1)` -- higher
//!   propagations per decision means the heuristic is making decisions that
//!   lead to more unit propagations (focused search).
//!
//! ## EMA Reward Tracking
//!
//! To handle non-stationarity (heuristic effectiveness changes as the solver
//! learns), each arm tracks an exponential moving average (EMA) of rewards
//! alongside the cumulative total. UCB1 uses the EMA mean rather than the
//! global mean, giving recency bias. EMA alpha = 0.1 provides a ~10-epoch
//! half-life.
//!
//! ## AE-Kissat-MAB 2025 Winner Techniques
//!
//! Ports from AE-Kissat-MAB (SAT Competition 2025 winner, 327/400):
//! - **Alternative reward signal**: `log2(decisions)/log2(conflicts)` via [`RewardMode::DecisionConflictRatio`].
//! - **Momentum-adaptive exploration**: Sliding-window momentum replaces static UCB1
//!   exploration constant. `adaptive_c = base / (momentum * (total_pulls + 1))`.
//!   Reference: `reference/ae-kissat-mab/src/restart.c:restart_mab()`.
//! - **Stable-mode-only MAB**: Epoch scoring gated behind stable mode (caller responsibility).
//! - **Trail disable on arm switch**: Caller skips trail reuse when heuristic changes.
//!
//! ## Arm Count
//!
//! AE-Kissat-MAB uses 2 arms (EVSIDS + CHB). AY keeps 3 arms (EVSIDS + VMTF + CHB)
//! because VMTF provides value in focused mode and AY's mode-switching strategy
//! benefits from the additional diversity.
//!
//! ## References
//!
//! - Auer, Cesa-Bianchi, Fischer. "Finite-time Analysis of the Multiarmed
//!   Bandit Problem." Machine Learning, 2002.
//! - Liang, Ganesh, Poupart, Czarnecki. "Learning Rate Based Branching
//!   Heuristic for SAT Solvers." SAT 2016. (CHB)
//! - Kissat_MAB-DC (SAT Competition 2024, 2nd place): UCB1 over
//!   VSIDS/VMTF with LBD-based reward.
//! - AE-Kissat-MAB (SAT Competition 2025, 1st place, 327/400): momentum-adaptive
//!   UCB1 with `log2(decisions)/log2(conflicts)` reward.

/// Branching heuristics that can drive SAT decisions.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum BranchHeuristic {
    /// Exponential VSIDS with a max-heap.
    Evsids,
    /// Variable move-to-front queue.
    Vmtf,
    /// Conflict History-Based branching (Liang et al., SAT 2016).
    Chb,
}

impl BranchHeuristic {
    /// Stable telemetry name for the branching heuristic.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Evsids => "evsids",
            Self::Vmtf => "vmtf",
            Self::Chb => "chb",
        }
    }

    pub(crate) const fn arm_index(self) -> usize {
        match self {
            Self::Evsids => 0,
            Self::Vmtf => 1,
            Self::Chb => 2,
        }
    }

    /// All heuristic variants in arm-index order.
    #[allow(dead_code)] // audited-unused: kept pending the next dead-code cleanup slice
    pub(crate) const ALL: [Self; NUM_BRANCH_HEURISTIC_ARMS] = [Self::Evsids, Self::Vmtf, Self::Chb];
}

/// Branch-heuristic selection policy.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum BranchSelectorMode {
    /// Preserve the historical coupling: stable mode uses EVSIDS, focused mode uses VMTF.
    LegacyCoupled,
    /// Force a specific heuristic regardless of restart mode.
    Fixed(BranchHeuristic),
    /// Select heuristics online with a UCB1 multi-armed bandit.
    MabUcb1,
}

impl BranchSelectorMode {
    /// Stable telemetry name for the branch-selector policy.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::LegacyCoupled => "legacy_coupled",
            Self::Fixed(_) => "fixed",
            Self::MabUcb1 => "mab_ucb1",
        }
    }
}

/// Reward signal mode for the MAB controller.
///
/// Controls how epoch telemetry is converted into a scalar reward for UCB1.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
#[non_exhaustive]
pub(crate) enum RewardMode {
    /// LBD quality (70%) + propagation efficiency (30%). AY's original reward.
    #[allow(dead_code)] // audited-unused: kept pending the next dead-code cleanup slice
    LbdPropEfficiency,
    /// `log2(decisions + 1) / log2(conflicts + 1)`. AE-Kissat-MAB 2025 winner reward.
    /// Higher values mean the heuristic is making more decisions per conflict
    /// (exploring deeper before hitting conflicts).
    #[default]
    DecisionConflictRatio,
}

/// Per-arm reward statistics for heuristic selection.
#[derive(Debug, Clone, Copy, Default, PartialEq)]
#[non_exhaustive]
pub struct BranchHeuristicStats {
    /// Number of completed epochs scored for this arm.
    pub pulls: u64,
    /// Sum of all rewards observed for this arm (cumulative).
    pub total_reward: f64,
    /// Exponential moving average of rewards for this arm.
    pub ema_reward: f64,
    /// Reward from the most recent completed epoch for this arm.
    pub last_reward: f64,
}

#[derive(Debug, Clone, Copy, Default)]
struct EpochSnapshot {
    conflicts: u64,
    decisions: u64,
    propagations: u64,
    lbd_sum: u64,
    lbd_count: u64,
}

pub(crate) const DEFAULT_HEURISTIC_EPOCH_MIN_CONFLICTS: u64 = 128;
pub(crate) const NUM_BRANCH_HEURISTIC_ARMS: usize = 3;

/// Available branching heuristic arms in index order.
///
/// AE-Kissat-MAB uses only 2 arms (EVSIDS + CHB). AY retains 3 arms
/// (EVSIDS + VMTF + CHB) for additional diversity across mode switches.
pub(crate) const BRANCH_HEURISTIC_ARMS: [BranchHeuristic; NUM_BRANCH_HEURISTIC_ARMS] = [
    BranchHeuristic::Evsids,
    BranchHeuristic::Vmtf,
    BranchHeuristic::Chb,
];

/// AE-Kissat-MAB 2-arm configuration: {EVSIDS, CHB} only.
/// Matches the 2025 SAT-COMP winner's arm set.
pub(crate) const AE_KISSAT_MAB_ARMS: [BranchHeuristic; 2] =
    [BranchHeuristic::Evsids, BranchHeuristic::Chb];

/// Size of the sliding window for momentum computation.
/// AE-Kissat-MAB uses a 10-element window (`recent_gains[10]` in `restart.c`).
const MOMENTUM_WINDOW_SIZE: usize = 10;

/// Default base exploration constant for adaptive UCB1.
/// Standard UCB1 uses `c = 2`; AE-Kissat-MAB's `mabc` defaults to this.
const DEFAULT_EXPLORATION_BASE: f64 = 2.0;

/// EMA smoothing factor for reward tracking. Alpha = 0.1 gives ~10-epoch
/// half-life, balancing responsiveness to regime changes against noise.
const EMA_ALPHA: f64 = 0.1;

/// Weight of LBD quality in the composite reward signal.
const LBD_REWARD_WEIGHT: f64 = 0.7;

/// Weight of propagation efficiency in the composite reward signal.
const PROP_EFF_REWARD_WEIGHT: f64 = 0.3;

/// Cap for propagation efficiency normalization. A ratio of 50 propagations
/// per decision is considered excellent; ratios above this are clamped to 1.0.
const PROP_EFF_CAP: f64 = 50.0;

/// Restart-boundary UCB1 controller for branching heuristic selection.
///
/// Evaluates heuristic epochs at restart boundaries, computing a composite
/// reward from LBD quality and propagation efficiency. Uses UCB1 with
/// EMA-based mean rewards for non-stationary environments.
///
/// ## AE-Kissat-MAB Momentum
///
/// The exploration coefficient adapts based on a sliding-window momentum signal.
/// When the current arm outperforms the recent average, momentum increases (>1.0),
/// reducing exploration (exploit more). When it underperforms, momentum decreases
/// (<1.0), increasing exploration (try alternatives). This matches `restart_mab()`
/// in `reference/ae-kissat-mab/src/restart.c`.
#[derive(Debug, Clone)]
pub(crate) struct MabController {
    epoch_min_conflicts: u64,
    epoch_start: EpochSnapshot,
    total_epochs: u64,
    arm_stats: [BranchHeuristicStats; NUM_BRANCH_HEURISTIC_ARMS],
    /// Reward signal mode (LBD+prop or decision/conflict ratio).
    reward_mode: RewardMode,
    /// Sliding window of recent per-arm average rewards for momentum computation.
    recent_gains: [f64; MOMENTUM_WINDOW_SIZE],
    /// Current index into the sliding window (circular buffer).
    gain_index: usize,
    /// Momentum factor: >1 when current arm outperforms recent average, <1 otherwise.
    /// AE-Kissat-MAB `restart.c:148-152`.
    momentum: f64,
    /// Base exploration constant (AE's `mabc`). Default: 2.0 (standard UCB1).
    exploration_base: f64,
    /// Bitmask of active arms. Bit `i` set means arm index `i` is active.
    /// Default: all 3 arms active (0b111). AE-Kissat-MAB 2-arm: 0b101 (EVSIDS + CHB).
    active_arms_mask: u8,
}

impl Default for MabController {
    fn default() -> Self {
        Self::new()
    }
}

impl MabController {
    pub(crate) fn new() -> Self {
        Self {
            epoch_min_conflicts: DEFAULT_HEURISTIC_EPOCH_MIN_CONFLICTS,
            epoch_start: EpochSnapshot::default(),
            total_epochs: 0,
            arm_stats: [BranchHeuristicStats::default(); NUM_BRANCH_HEURISTIC_ARMS],
            reward_mode: RewardMode::default(),
            recent_gains: [0.0; MOMENTUM_WINDOW_SIZE],
            gain_index: 0,
            momentum: 1.0,
            exploration_base: DEFAULT_EXPLORATION_BASE,
            active_arms_mask: (1 << NUM_BRANCH_HEURISTIC_ARMS) - 1, // all arms active
        }
    }

    pub(crate) fn reset(&mut self) {
        self.epoch_start = EpochSnapshot::default();
        self.total_epochs = 0;
        self.arm_stats = [BranchHeuristicStats::default(); NUM_BRANCH_HEURISTIC_ARMS];
        self.recent_gains = [0.0; MOMENTUM_WINDOW_SIZE];
        self.gain_index = 0;
        self.momentum = 1.0;
    }

    pub(crate) fn set_epoch_min_conflicts(&mut self, epoch_min_conflicts: u64) {
        self.epoch_min_conflicts = epoch_min_conflicts.max(1);
    }

    pub(crate) fn arm_stats(&self) -> [BranchHeuristicStats; NUM_BRANCH_HEURISTIC_ARMS] {
        self.arm_stats
    }

    /// Set the reward signal mode.
    #[allow(dead_code)] // audited-unused: kept pending the next dead-code cleanup slice
    pub(crate) fn set_reward_mode(&mut self, mode: RewardMode) {
        self.reward_mode = mode;
    }

    /// Set the base exploration constant for adaptive UCB1.
    #[allow(dead_code)] // audited-unused: kept pending the next dead-code cleanup slice
    pub(crate) fn set_exploration_base(&mut self, base: f64) {
        self.exploration_base = base.max(0.01);
    }

    /// Configure the active arms for the MAB controller.
    ///
    /// Pass a slice of `BranchHeuristic` variants to activate. Arms not in the
    /// slice are excluded from UCB1 selection. At least one arm must be active.
    ///
    /// AE-Kissat-MAB 2-arm config: `set_active_arms(&AE_KISSAT_MAB_ARMS)`.
    pub(crate) fn set_active_arms(&mut self, arms: &[BranchHeuristic]) {
        let mut mask = 0u8;
        for &arm in arms {
            mask |= 1 << arm.arm_index();
        }
        if mask == 0 {
            // Fallback: at least EVSIDS must be active.
            mask = 1 << BranchHeuristic::Evsids.arm_index();
        }
        self.active_arms_mask = mask;
    }

    /// Check if a given arm is active (included in the current arm set).
    pub(crate) fn is_arm_active(&self, arm: BranchHeuristic) -> bool {
        self.active_arms_mask & (1 << arm.arm_index()) != 0
    }

    /// Current momentum value (for diagnostics/testing).
    #[cfg(test)]
    fn momentum(&self) -> f64 {
        self.momentum
    }

    pub(crate) fn start_epoch(
        &mut self,
        conflicts: u64,
        decisions: u64,
        propagations: u64,
        lbd_sum: u64,
        lbd_count: u64,
    ) {
        self.epoch_start = EpochSnapshot {
            conflicts,
            decisions,
            propagations,
            lbd_sum,
            lbd_count,
        };
    }

    /// Compute the composite reward from epoch telemetry deltas.
    ///
    /// Combines LBD quality (70%) and propagation efficiency (30%) into
    /// a single [0, 1] reward signal. This is the default
    /// [`RewardMode::LbdPropEfficiency`] mode.
    fn compute_reward(
        lbd_sum_delta: u64,
        lbd_count_delta: u64,
        decision_delta: u64,
        propagation_delta: u64,
    ) -> f64 {
        // LBD quality component: lower average LBD -> higher reward.
        let avg_lbd = lbd_sum_delta as f64 / lbd_count_delta.max(1) as f64;
        let lbd_reward = 1.0 / (1.0 + avg_lbd);

        // Propagation efficiency component: more propagations per decision
        // means the heuristic is making decisions that lead to focused search.
        let prop_eff = propagation_delta as f64 / (decision_delta as f64 + 1.0);
        let prop_reward = (prop_eff / PROP_EFF_CAP).min(1.0);

        LBD_REWARD_WEIGHT.mul_add(lbd_reward, PROP_EFF_REWARD_WEIGHT * prop_reward)
    }

    /// Compute reward using the AE-Kissat-MAB `log2(decisions)/log2(conflicts)` signal.
    ///
    /// Higher values indicate the heuristic explored deeper search trees before
    /// encountering conflicts. Both values are shifted by +1 to avoid `log2(0)`.
    /// Reference: `reference/ae-kissat-mab/src/restart.c:116`.
    fn compute_reward_decision_conflict(decision_delta: u64, conflict_delta: u64) -> f64 {
        let d = (decision_delta as f64 + 1.0).log2();
        let c = (conflict_delta as f64 + 1.0).log2();
        if c > 0.0 {
            d / c
        } else {
            1.0
        }
    }

    /// Dispatch reward computation based on the active reward mode.
    fn dispatch_reward(
        &self,
        lbd_sum_delta: u64,
        lbd_count_delta: u64,
        decision_delta: u64,
        propagation_delta: u64,
        conflict_delta: u64,
    ) -> f64 {
        match self.reward_mode {
            RewardMode::LbdPropEfficiency => Self::compute_reward(
                lbd_sum_delta,
                lbd_count_delta,
                decision_delta,
                propagation_delta,
            ),
            RewardMode::DecisionConflictRatio => {
                Self::compute_reward_decision_conflict(decision_delta, conflict_delta)
            }
        }
    }

    pub(crate) fn finalize_epoch(
        &mut self,
        heuristic: BranchHeuristic,
        conflicts: u64,
        decisions: u64,
        propagations: u64,
        lbd_sum: u64,
        lbd_count: u64,
    ) -> bool {
        if !self.is_arm_active(heuristic) {
            return false;
        }

        let conflict_delta = conflicts.saturating_sub(self.epoch_start.conflicts);
        if conflict_delta < self.epoch_min_conflicts {
            return false;
        }

        let decision_delta = decisions.saturating_sub(self.epoch_start.decisions);
        let propagation_delta = propagations.saturating_sub(self.epoch_start.propagations);
        let lbd_sum_delta = lbd_sum.saturating_sub(self.epoch_start.lbd_sum);
        let lbd_count_delta = lbd_count.saturating_sub(self.epoch_start.lbd_count);

        let reward = self.dispatch_reward(
            lbd_sum_delta,
            lbd_count_delta,
            decision_delta,
            propagation_delta,
            conflict_delta,
        );

        let arm_stats = &mut self.arm_stats[heuristic.arm_index()];
        arm_stats.pulls += 1;
        arm_stats.total_reward += reward;
        arm_stats.last_reward = reward;

        // EMA update: on first pull, initialize to the observed reward.
        if arm_stats.pulls == 1 {
            arm_stats.ema_reward = reward;
        } else {
            arm_stats.ema_reward += EMA_ALPHA * (reward - arm_stats.ema_reward);
        }

        self.total_epochs += 1;

        // Update momentum sliding window (AE-Kissat-MAB restart.c:136-152).
        let current_gain = arm_stats.total_reward / arm_stats.pulls as f64;
        self.recent_gains[self.gain_index] = current_gain;
        self.gain_index = (self.gain_index + 1) % MOMENTUM_WINDOW_SIZE;

        let avg_gain: f64 = self.recent_gains.iter().sum::<f64>() / MOMENTUM_WINDOW_SIZE as f64;
        if current_gain > avg_gain {
            self.momentum *= 1.1;
        } else {
            self.momentum *= 0.9;
        }
        self.momentum = self.momentum.clamp(0.01, 100.0);

        true
    }

    pub(crate) fn default_arm(&self) -> BranchHeuristic {
        BranchHeuristic::Evsids
    }

    /// Select the next arm using UCB1 with momentum-adaptive exploration.
    ///
    /// Untried arms are always explored first (in enum order). After all arms
    /// have been tried, UCB1 balances exploitation (EMA mean reward) against
    /// exploration (confidence bound with adaptive coefficient).
    ///
    /// The exploration coefficient adapts via momentum: when the current arm
    /// outperforms the sliding-window average, momentum increases and exploration
    /// decreases (exploit more). When it underperforms, exploration increases
    /// (try alternatives). This matches AE-Kissat-MAB `restart.c:155-167`.
    pub(crate) fn select_next_arm(&self) -> BranchHeuristic {
        // Explore untried active arms first (in enum order).
        for arm in BRANCH_HEURISTIC_ARMS {
            if self.is_arm_active(arm) && self.arm_stats[arm.arm_index()].pulls == 0 {
                return arm;
            }
        }

        // Total pulls across active arms (= stable_restarts in AE).
        let total_pulls: u64 = BRANCH_HEURISTIC_ARMS
            .iter()
            .filter(|a| self.is_arm_active(**a))
            .map(|a| self.arm_stats[a.arm_index()].pulls)
            .sum();
        let total_f = (total_pulls as f64 + 1.0).max(1.0);
        let ln_total = total_f.ln();

        // Adaptive exploration coefficient (AE-Kissat-MAB restart.c:155).
        let adaptive_c = self.exploration_base / (self.momentum * total_f);

        let mut best_arm = self.default_arm();
        let mut best_score = f64::NEG_INFINITY;

        for arm in BRANCH_HEURISTIC_ARMS {
            if !self.is_arm_active(arm) {
                continue;
            }
            let stats = self.arm_stats[arm.arm_index()];
            // Use EMA mean for exploitation (non-stationary environment).
            let mean_reward = stats.ema_reward;
            let exploration = (adaptive_c * ln_total / stats.pulls as f64).sqrt();
            let score = mean_reward + exploration;
            if score > best_score {
                best_score = score;
                best_arm = arm;
            }
        }

        best_arm
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_mab_initial_state() {
        let mab = MabController::new();
        assert_eq!(mab.total_epochs, 0);
        for arm in BRANCH_HEURISTIC_ARMS {
            let stats = mab.arm_stats[arm.arm_index()];
            assert_eq!(stats.pulls, 0);
            assert_eq!(stats.total_reward, 0.0);
            assert_eq!(stats.ema_reward, 0.0);
            assert_eq!(stats.last_reward, 0.0);
        }
    }

    #[test]
    fn test_mab_default_arm_is_evsids() {
        let mab = MabController::new();
        assert_eq!(mab.default_arm(), BranchHeuristic::Evsids);
    }

    #[test]
    fn test_mab_reset_clears_all_state() {
        let mut mab = MabController::new();
        mab.start_epoch(0, 0, 0, 0, 0);
        let _ = mab.finalize_epoch(BranchHeuristic::Evsids, 200, 300, 500, 800, 200);
        assert!(mab.total_epochs > 0);
        mab.reset();
        assert_eq!(mab.total_epochs, 0);
        for arm in BRANCH_HEURISTIC_ARMS {
            let s = mab.arm_stats[arm.arm_index()];
            assert_eq!(s.pulls, 0);
            assert_eq!(s.ema_reward, 0.0);
        }
    }

    #[test]
    fn test_mab_epoch_too_short_returns_false() {
        let mut mab = MabController::new();
        mab.start_epoch(0, 0, 0, 0, 0);
        let completed = mab.finalize_epoch(BranchHeuristic::Evsids, 10, 20, 30, 40, 10);
        assert!(!completed, "Epoch with too few conflicts must not complete");
        assert_eq!(mab.total_epochs, 0);
    }

    #[test]
    fn test_mab_epoch_at_threshold_completes() {
        let mut mab = MabController::new();
        mab.start_epoch(0, 0, 0, 0, 0);
        let completed = mab.finalize_epoch(
            BranchHeuristic::Evsids,
            DEFAULT_HEURISTIC_EPOCH_MIN_CONFLICTS,
            200,
            500,
            400,
            128,
        );
        assert!(completed, "Epoch at exact threshold must complete");
        assert_eq!(mab.arm_stats[BranchHeuristic::Evsids.arm_index()].pulls, 1);
    }

    #[test]
    fn test_mab_reward_inversely_proportional_to_lbd() {
        // Two epochs with same propagation efficiency but different LBD.
        // Lower LBD should yield higher composite reward.
        let mut mab = MabController::new();
        mab.set_reward_mode(RewardMode::LbdPropEfficiency);
        // EVSIDS: 200 conflicts, 300 decisions, 500 propagations, avg LBD = 400/200 = 2
        mab.start_epoch(0, 0, 0, 0, 0);
        mab.finalize_epoch(BranchHeuristic::Evsids, 200, 300, 500, 400, 200);
        let low_lbd_reward = mab.arm_stats[BranchHeuristic::Evsids.arm_index()].last_reward;
        // VMTF: 200 conflicts, 300 decisions, 500 propagations, avg LBD = 2000/200 = 10
        mab.start_epoch(200, 300, 500, 400, 200);
        mab.finalize_epoch(BranchHeuristic::Vmtf, 400, 600, 1000, 2400, 400);
        let high_lbd_reward = mab.arm_stats[BranchHeuristic::Vmtf.arm_index()].last_reward;
        assert!(
            low_lbd_reward > high_lbd_reward,
            "Lower LBD must yield higher reward: low={low_lbd_reward}, high={high_lbd_reward}"
        );
    }

    #[test]
    fn test_mab_reward_includes_propagation_efficiency() {
        // Two epochs with same LBD but different propagation efficiency.
        // Higher prop efficiency should yield higher reward.
        let mut mab = MabController::new();
        mab.set_reward_mode(RewardMode::LbdPropEfficiency);
        // Low prop efficiency: 100 decisions, 200 propagations -> ratio = 2
        mab.start_epoch(0, 0, 0, 0, 0);
        mab.finalize_epoch(BranchHeuristic::Evsids, 200, 100, 200, 600, 200);
        let low_eff_reward = mab.arm_stats[BranchHeuristic::Evsids.arm_index()].last_reward;
        // High prop efficiency: 100 decisions, 5000 propagations -> ratio = 50
        mab.start_epoch(200, 100, 200, 600, 200);
        mab.finalize_epoch(BranchHeuristic::Vmtf, 400, 200, 5200, 1200, 400);
        let high_eff_reward = mab.arm_stats[BranchHeuristic::Vmtf.arm_index()].last_reward;
        assert!(
            high_eff_reward > low_eff_reward,
            "Higher prop efficiency must yield higher reward: high={high_eff_reward}, low={low_eff_reward}"
        );
    }

    #[test]
    fn test_mab_ema_initialized_on_first_pull() {
        let mut mab = MabController::new();
        mab.start_epoch(0, 0, 0, 0, 0);
        mab.finalize_epoch(BranchHeuristic::Evsids, 200, 200, 1000, 400, 200);
        let stats = mab.arm_stats[BranchHeuristic::Evsids.arm_index()];
        assert_eq!(stats.pulls, 1);
        // On first pull, EMA should equal the observed reward.
        assert!(
            (stats.ema_reward - stats.last_reward).abs() < 1e-12,
            "EMA must be initialized to first reward: ema={}, last={}",
            stats.ema_reward,
            stats.last_reward
        );
    }

    #[test]
    fn test_mab_ema_tracks_recent_rewards() {
        let mut mab = MabController::new();
        mab.set_reward_mode(RewardMode::LbdPropEfficiency);
        // Give 20 epochs with consistently low LBD (high reward).
        for i in 0..20u64 {
            let base = i * 200;
            mab.start_epoch(base, base, base * 5, base * 2, base);
            mab.finalize_epoch(
                BranchHeuristic::Evsids,
                base + 200,
                base + 200,
                (base + 200) * 5,
                (base + 200) * 2 + 200,
                base + 200,
            );
        }
        let ema_good = mab.arm_stats[BranchHeuristic::Evsids.arm_index()].ema_reward;
        // Now give 20 epochs with very high LBD (low reward).
        for i in 20..40u64 {
            let base = i * 200;
            mab.start_epoch(base, base, base, base * 50, base);
            mab.finalize_epoch(
                BranchHeuristic::Evsids,
                base + 200,
                base + 200,
                base + 200,
                (base + 200) * 50,
                base + 200,
            );
        }
        let ema_bad = mab.arm_stats[BranchHeuristic::Evsids.arm_index()].ema_reward;
        assert!(
            ema_bad < ema_good,
            "EMA must decrease when recent rewards worsen: good={ema_good}, bad={ema_bad}"
        );
    }

    #[test]
    fn test_mab_ucb1_explores_untried_arms_first() {
        let mut mab = MabController::new();
        mab.start_epoch(0, 0, 0, 0, 0);
        mab.finalize_epoch(BranchHeuristic::Evsids, 200, 300, 500, 600, 200);
        let next = mab.select_next_arm();
        assert_eq!(
            next,
            BranchHeuristic::Vmtf,
            "UCB1 must explore untried VMTF before exploiting"
        );
    }

    #[test]
    fn test_mab_ucb1_explores_all_before_exploiting() {
        let mut mab = MabController::new();
        mab.start_epoch(0, 0, 0, 0, 0);
        mab.finalize_epoch(BranchHeuristic::Evsids, 200, 300, 500, 600, 200);
        mab.start_epoch(200, 300, 500, 600, 200);
        mab.finalize_epoch(BranchHeuristic::Vmtf, 400, 600, 1000, 1200, 400);
        let next = mab.select_next_arm();
        assert_eq!(next, BranchHeuristic::Chb, "UCB1 must explore untried CHB");
    }

    #[test]
    fn test_mab_ucb1_exploits_best_arm_after_exploration() {
        let mut mab = MabController::new();
        mab.set_reward_mode(RewardMode::LbdPropEfficiency);
        // Use compute_reward to derive the exact reward for each arm, then
        // validate the UCB1 selection.
        //
        // EVSIDS: avg LBD = 0 (best), prop ratio = 50 (at cap)
        //   lbd_reward = 1/(1+0) = 1.0, prop_reward = 1.0
        //   composite = 0.7*1.0 + 0.3*1.0 = 1.0
        let evsids_reward = MabController::compute_reward(0, 200, 0, 10_000);
        assert!(
            (evsids_reward - 1.0).abs() < 0.01,
            "EVSIDS reward: {evsids_reward}"
        );

        // VMTF: avg LBD = 20, prop ratio = 0
        //   lbd_reward = 1/(1+20) = 0.048, prop_reward = 0
        //   composite = 0.7*0.048 + 0.3*0 = 0.033
        let vmtf_reward = MabController::compute_reward(4000, 200, 200, 200);
        assert!(vmtf_reward < 0.1, "VMTF reward: {vmtf_reward}");

        // CHB: avg LBD = 50, prop ratio = 0
        //   composite ~ 0.7*0.02 = 0.014
        let chb_reward = MabController::compute_reward(10_000, 200, 200, 200);
        assert!(chb_reward < 0.05, "CHB reward: {chb_reward}");

        // Give each arm 30 pulls using start_epoch(0,...) / finalize_epoch(delta,...)
        // so the deltas are exact.
        for _ in 0..30 {
            // EVSIDS: best reward
            mab.start_epoch(0, 0, 0, 0, 0);
            mab.finalize_epoch(BranchHeuristic::Evsids, 200, 0, 10_000, 0, 200);
            // VMTF: poor reward
            mab.start_epoch(0, 0, 0, 0, 0);
            mab.finalize_epoch(BranchHeuristic::Vmtf, 200, 200, 200, 4000, 200);
            // CHB: very poor reward
            mab.start_epoch(0, 0, 0, 0, 0);
            mab.finalize_epoch(BranchHeuristic::Chb, 200, 200, 200, 10_000, 200);
        }
        // Give EVSIDS 300 more excellent pulls to dominate.
        for _ in 0..300 {
            mab.start_epoch(0, 0, 0, 0, 0);
            mab.finalize_epoch(BranchHeuristic::Evsids, 200, 0, 10_000, 0, 200);
        }
        // Total: 330 EVSIDS, 30 VMTF, 30 CHB = 390 epochs.
        // EMA(EVSIDS) ~ 1.0, EMA(VMTF) ~ 0.033, EMA(CHB) ~ 0.014
        // exploration(VMTF) = sqrt(2 * ln(390) / 30) = sqrt(2 * 5.97 / 30) = 0.63
        // exploration(EVSIDS) = sqrt(2 * 5.97 / 330) = 0.19
        // score(EVSIDS) = 1.0 + 0.19 = 1.19
        // score(VMTF) = 0.033 + 0.63 = 0.66
        let next = mab.select_next_arm();
        assert_eq!(
            next,
            BranchHeuristic::Evsids,
            "UCB1 must exploit arm with highest EMA reward after sufficient pulls"
        );
    }

    #[test]
    fn test_mab_arm_index_consistency() {
        assert_eq!(BranchHeuristic::Evsids.arm_index(), 0);
        assert_eq!(BranchHeuristic::Vmtf.arm_index(), 1);
        assert_eq!(BranchHeuristic::Chb.arm_index(), 2);
    }

    #[test]
    fn test_mab_branch_heuristic_all_matches_arms() {
        assert_eq!(BranchHeuristic::ALL.len(), NUM_BRANCH_HEURISTIC_ARMS);
        for (i, arm) in BranchHeuristic::ALL.iter().enumerate() {
            assert_eq!(arm.arm_index(), i);
        }
    }

    #[test]
    fn test_mab_set_epoch_min_conflicts_clamps_to_one() {
        let mut mab = MabController::new();
        mab.set_epoch_min_conflicts(0);
        mab.start_epoch(0, 0, 0, 0, 0);
        let completed = mab.finalize_epoch(BranchHeuristic::Evsids, 1, 1, 1, 2, 1);
        assert!(
            completed,
            "With min_conflicts=1, a single-conflict epoch must complete"
        );
    }

    #[test]
    fn test_mab_ucb1_exploration_bonus_decays_with_pulls() {
        let mut mab = MabController::new();
        // Give all arms 1 pull each with identical reward.
        for arm in BRANCH_HEURISTIC_ARMS {
            let base = arm.arm_index() as u64 * 200;
            mab.start_epoch(base, base, base * 10, base * 3, base);
            mab.finalize_epoch(
                arm,
                base + 200,
                base + 200,
                (base + 200) * 10,
                (base + 200) * 3,
                base + 200,
            );
        }
        // Give EVSIDS 50 more pulls with identical reward. Its exploration
        // bonus decays while VMTF/CHB retain high bonuses.
        for i in 0..50u64 {
            let base = 600 + i * 200;
            mab.start_epoch(base, base, base * 10, base * 3, base);
            mab.finalize_epoch(
                BranchHeuristic::Evsids,
                base + 200,
                base + 200,
                (base + 200) * 10,
                (base + 200) * 3,
                base + 200,
            );
        }
        let next = mab.select_next_arm();
        assert_ne!(
            next,
            BranchHeuristic::Evsids,
            "UCB1 must explore under-sampled arms when mean rewards are similar"
        );
    }

    #[test]
    fn test_mab_compute_reward_bounds() {
        // Minimum reward: infinite LBD, zero propagation efficiency.
        let r_min = MabController::compute_reward(u64::MAX / 2, 1, 0, 0);
        assert!(r_min >= 0.0, "Reward must be non-negative: {r_min}");
        // Maximum reward: LBD = 0, prop efficiency at cap.
        let r_max = MabController::compute_reward(0, 1, 1, PROP_EFF_CAP as u64);
        assert!(r_max <= 1.0, "Reward must be at most 1.0: {r_max}");
        assert!(r_max > r_min, "Max reward must exceed min reward");
    }

    #[test]
    fn test_mab_compute_reward_prop_efficiency_caps() {
        // Propagation efficiency beyond the cap should not increase reward further.
        // Use decision_delta=0 so denominator is 1 and prop ratio = propagation_delta.
        // Both values are well above PROP_EFF_CAP (50).
        let r_at_cap = MabController::compute_reward(200, 100, 0, 100);
        let r_above_cap = MabController::compute_reward(200, 100, 0, 200);
        assert!(
            (r_at_cap - r_above_cap).abs() < 1e-12,
            "Reward should be capped: at_cap={r_at_cap}, above_cap={r_above_cap}"
        );
    }

    #[test]
    fn test_branch_selector_mode_variants() {
        let legacy = BranchSelectorMode::LegacyCoupled;
        let fixed = BranchSelectorMode::Fixed(BranchHeuristic::Chb);
        let mab = BranchSelectorMode::MabUcb1;
        assert_eq!(legacy, BranchSelectorMode::LegacyCoupled);
        assert_eq!(fixed, BranchSelectorMode::Fixed(BranchHeuristic::Chb));
        assert_eq!(mab, BranchSelectorMode::MabUcb1);
    }

    #[test]
    fn test_mab_reward_mode_default_is_decision_conflict() {
        let mab = MabController::new();
        assert_eq!(mab.reward_mode, RewardMode::DecisionConflictRatio);
    }

    #[test]
    fn test_mab_decision_conflict_ratio_reward() {
        let mut mab = MabController::new();
        mab.set_reward_mode(RewardMode::DecisionConflictRatio);

        // Epoch with many decisions relative to conflicts -> high reward.
        mab.start_epoch(0, 0, 0, 0, 0);
        mab.finalize_epoch(BranchHeuristic::Evsids, 200, 10_000, 5000, 600, 200);
        let high_ratio = mab.arm_stats[BranchHeuristic::Evsids.arm_index()].last_reward;

        // Epoch with few decisions relative to conflicts -> lower reward.
        mab.start_epoch(200, 10_000, 5000, 600, 200);
        mab.finalize_epoch(BranchHeuristic::Vmtf, 400, 10_200, 5100, 1200, 400);
        let low_ratio = mab.arm_stats[BranchHeuristic::Vmtf.arm_index()].last_reward;

        assert!(
            high_ratio > low_ratio,
            "Higher decision/conflict ratio must yield higher reward: high={high_ratio}, low={low_ratio}"
        );
    }

    #[test]
    fn test_mab_decision_conflict_ratio_no_panic_on_zero() {
        // Ensure no division by zero or NaN when deltas are 0.
        let r = MabController::compute_reward_decision_conflict(0, 0);
        assert!(r.is_finite(), "Reward must be finite for zero deltas: {r}");
    }

    #[test]
    fn test_mab_momentum_increases_on_good_performance() {
        let mut mab = MabController::new();
        mab.set_reward_mode(RewardMode::LbdPropEfficiency);
        let initial_momentum = mab.momentum();

        // Fill the sliding window with low gains first (by giving poor epochs).
        for _ in 0..MOMENTUM_WINDOW_SIZE {
            mab.start_epoch(0, 0, 0, 0, 0);
            mab.finalize_epoch(BranchHeuristic::Evsids, 200, 200, 200, 4000, 200);
        }
        let after_poor = mab.momentum();

        // Now give consistently excellent epochs. The current gain will exceed the
        // sliding window average, so momentum should increase.
        for _ in 0..5 {
            mab.start_epoch(0, 0, 0, 0, 0);
            mab.finalize_epoch(BranchHeuristic::Evsids, 200, 0, 10_000, 0, 200);
        }
        let after_good = mab.momentum();
        assert!(
            after_good > after_poor,
            "Momentum must increase on good performance: after_poor={after_poor}, after_good={after_good}"
        );
        // Verify it moved from initial
        assert_ne!(
            initial_momentum, after_good,
            "Momentum must change from initial"
        );
    }

    #[test]
    fn test_mab_momentum_decreases_on_bad_performance() {
        let mut mab = MabController::new();
        mab.set_reward_mode(RewardMode::LbdPropEfficiency);
        // Fill the sliding window with good gains first.
        for _ in 0..MOMENTUM_WINDOW_SIZE {
            mab.start_epoch(0, 0, 0, 0, 0);
            mab.finalize_epoch(BranchHeuristic::Evsids, 200, 0, 10_000, 0, 200);
        }
        let after_good = mab.momentum();

        // Now give poor epochs. The current gain drops below the window average.
        for _ in 0..5 {
            mab.start_epoch(0, 0, 0, 0, 0);
            mab.finalize_epoch(BranchHeuristic::Evsids, 200, 200, 200, 20_000, 200);
        }
        let after_bad = mab.momentum();
        assert!(
            after_bad < after_good,
            "Momentum must decrease on bad performance: after_good={after_good}, after_bad={after_bad}"
        );
    }

    #[test]
    fn test_mab_momentum_clamped() {
        let mut mab = MabController::new();

        // Drive momentum down aggressively.
        for _ in 0..500 {
            mab.start_epoch(0, 0, 0, 0, 0);
            mab.finalize_epoch(BranchHeuristic::Evsids, 200, 200, 200, 20_000, 200);
        }
        assert!(
            mab.momentum() >= 0.01,
            "Momentum must not go below 0.01: {}",
            mab.momentum()
        );

        // Drive momentum up aggressively.
        for _ in 0..500 {
            mab.start_epoch(0, 0, 0, 0, 0);
            mab.finalize_epoch(BranchHeuristic::Evsids, 200, 0, 10_000, 0, 200);
        }
        assert!(
            mab.momentum() <= 100.0,
            "Momentum must not exceed 100.0: {}",
            mab.momentum()
        );
    }

    #[test]
    fn test_mab_adaptive_exploration_reduces_with_momentum() {
        // High momentum should make the controller exploit more (pick the
        // known-best arm) whereas low momentum should encourage exploration.
        // We set up two controllers with identical arm stats but different momentum.

        let make_controller = || {
            let mut mab = MabController::new();
            mab.set_reward_mode(RewardMode::LbdPropEfficiency);
            // Give all arms initial pulls with different rewards.
            // EVSIDS: excellent
            for _ in 0..5 {
                mab.start_epoch(0, 0, 0, 0, 0);
                mab.finalize_epoch(BranchHeuristic::Evsids, 200, 0, 10_000, 0, 200);
            }
            // VMTF: poor
            for _ in 0..5 {
                mab.start_epoch(0, 0, 0, 0, 0);
                mab.finalize_epoch(BranchHeuristic::Vmtf, 200, 200, 200, 4000, 200);
            }
            // CHB: very poor
            for _ in 0..5 {
                mab.start_epoch(0, 0, 0, 0, 0);
                mab.finalize_epoch(BranchHeuristic::Chb, 200, 200, 200, 10_000, 200);
            }
            mab
        };

        let mut high_momentum = make_controller();
        high_momentum.momentum = 50.0; // High momentum = low exploration

        let mut low_momentum = make_controller();
        low_momentum.momentum = 0.01; // Low momentum = high exploration

        // With high momentum, the best arm (EVSIDS) should be selected because
        // the exploration bonus is tiny. With low momentum, exploration bonus
        // is large and could favor under-sampled arms. Both should produce
        // valid selections without panicking.
        let high_pick = high_momentum.select_next_arm();
        let _low_pick = low_momentum.select_next_arm();

        // The high-momentum controller should pick EVSIDS (best EMA reward).
        assert_eq!(
            high_pick,
            BranchHeuristic::Evsids,
            "High momentum should exploit the best arm"
        );
    }

    #[test]
    fn test_mab_set_exploration_base() {
        let mut mab = MabController::new();
        mab.set_exploration_base(4.0);
        assert!((mab.exploration_base - 4.0).abs() < 1e-12);
        // Clamped to minimum 0.01
        mab.set_exploration_base(-1.0);
        assert!((mab.exploration_base - 0.01).abs() < 1e-12);
    }

    #[test]
    fn test_mab_reset_clears_momentum() {
        let mut mab = MabController::new();
        // Drive momentum away from 1.0
        for _ in 0..20 {
            mab.start_epoch(0, 0, 0, 0, 0);
            mab.finalize_epoch(BranchHeuristic::Evsids, 200, 0, 10_000, 0, 200);
        }
        assert!(
            (mab.momentum() - 1.0).abs() > 0.01,
            "Momentum should have changed"
        );
        mab.reset();
        assert!(
            (mab.momentum() - 1.0).abs() < 1e-12,
            "Reset must restore momentum to 1.0"
        );
    }

    #[test]
    fn test_mab_2arm_skips_vmtf() {
        let mut mab = MabController::new();
        mab.set_active_arms(&AE_KISSAT_MAB_ARMS);

        // First untried arm should be EVSIDS (index 0).
        assert_eq!(mab.select_next_arm(), BranchHeuristic::Evsids);

        // After EVSIDS pull, next untried should be CHB (skipping VMTF).
        mab.start_epoch(0, 0, 0, 0, 0);
        mab.finalize_epoch(BranchHeuristic::Evsids, 200, 300, 500, 600, 200);
        assert_eq!(
            mab.select_next_arm(),
            BranchHeuristic::Chb,
            "2-arm mode must skip VMTF and explore CHB"
        );
    }

    #[test]
    fn test_mab_2arm_never_selects_vmtf() {
        let mut mab = MabController::new();
        mab.set_active_arms(&AE_KISSAT_MAB_ARMS);

        // Give both active arms many pulls.
        for _ in 0..50 {
            mab.start_epoch(0, 0, 0, 0, 0);
            mab.finalize_epoch(BranchHeuristic::Evsids, 200, 0, 10_000, 0, 200);
            mab.start_epoch(0, 0, 0, 0, 0);
            mab.finalize_epoch(BranchHeuristic::Chb, 200, 200, 200, 4000, 200);
        }

        // Select 100 arms and verify VMTF is never chosen.
        for _ in 0..100 {
            let arm = mab.select_next_arm();
            assert_ne!(
                arm,
                BranchHeuristic::Vmtf,
                "2-arm mode must never select VMTF"
            );
        }
    }

    #[test]
    fn test_mab_finalize_ignores_inactive_arm_telemetry() {
        let mut mab = MabController::new();
        mab.set_active_arms(&AE_KISSAT_MAB_ARMS);
        mab.start_epoch(0, 0, 0, 0, 0);

        assert!(
            !mab.finalize_epoch(BranchHeuristic::Vmtf, 200, 300, 500, 600, 200),
            "inactive VMTF arm must not score telemetry in AE-Kissat 2-arm mode"
        );
        assert_eq!(mab.total_epochs, 0);
        assert_eq!(mab.arm_stats[BranchHeuristic::Vmtf.arm_index()].pulls, 0);
    }

    #[test]
    fn test_mab_set_active_arms_empty_falls_back_to_evsids() {
        let mut mab = MabController::new();
        mab.set_active_arms(&[]);
        // Empty set should fall back to EVSIDS.
        assert_eq!(mab.select_next_arm(), BranchHeuristic::Evsids);
    }

    #[test]
    fn test_mab_2arm_ucb1_exploits_best() {
        let mut mab = MabController::new();
        mab.set_active_arms(&AE_KISSAT_MAB_ARMS);
        // DecisionConflictRatio: log2(decisions+1)/log2(conflicts+1).
        // EVSIDS: many decisions per conflict (high reward).
        // CHB: few decisions per conflict (low reward).
        for _ in 0..100 {
            mab.start_epoch(0, 0, 0, 0, 0);
            mab.finalize_epoch(BranchHeuristic::Evsids, 200, 10_000, 5000, 600, 200);
        }
        for _ in 0..100 {
            mab.start_epoch(0, 0, 0, 0, 0);
            mab.finalize_epoch(BranchHeuristic::Chb, 200, 210, 200, 600, 200);
        }

        let arm = mab.select_next_arm();
        assert_eq!(
            arm,
            BranchHeuristic::Evsids,
            "2-arm UCB1 must exploit the best-performing arm"
        );
    }
}
