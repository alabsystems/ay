// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tiered compilation controller for progressive solver specialization.
//!
//! Coordinates T0-T4 compilation tiers based on solve difficulty:
//!
//! | Tier | Trigger | Compile time | What's compiled |
//! |------|---------|-------------|----------------|
//! | T0 | Immediate | 0 | Nothing — generic solver |
//! | T1 | After parse | ~100us | Hot loop native helpers (current ay-jit) |
//! | T2 | After 1K conflicts | ~5ms | Component solver-program artifacts |
//! | T3 | After 10K conflicts | ~50ms | Entire CDCL loop as one solver program |
//! | T4 | After 100K conflicts | ~200ms | Preprocess + solver, fully specialized |
//!
//! Easy instances solve at T0/T1 before higher tiers kick in. Hard instances
//! (seconds to minutes) amortize even 200ms of compilation. Background
//! compilation happens on a separate thread; the solver
//! never blocks on compilation. Tier swaps happen atomically at restart
//! boundaries.
//!
//! Currently T0 and T1 are fully functional. T2 (Component JIT) is wired:
//! component solver-program artifacts compile off the hot path, and completed
//! results are installed at restart boundaries.
//! T3-T4 return the correct tier from the controller but the compiled
//! artifacts don't exist yet — this controller is the coordination layer
//! that future phases plug into.

/// Compilation tier for the solver.
///
/// Ordered by specialization level — higher tiers produce faster code
/// at higher compile cost. The solver starts at `Interpret` and promotes
/// through tiers as the solve takes longer.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum CompilationTier {
    /// T0: Pure interpretation. No JIT. Always available immediately.
    Interpret,
    /// T1: Hot loop native helpers, such as simplex pivot rows.
    /// Compile time: ~100us. Triggered after parse.
    HotLoopJit,
    /// T2: Component solver-program artifacts.
    /// Compile time: ~5ms. Triggered after 1K conflicts.
    ComponentJit,
    /// T3: Solver program with the CDCL loop and theory hooks inlined.
    /// Compile time: ~50ms. Triggered after 10K conflicts.
    SolverJit,
    /// T4: Whole-program. Preprocessing + solver fully specialized.
    /// Compile time: ~200ms. Triggered after 100K conflicts.
    WholeProgram,
}

impl CompilationTier {
    /// Short display name for stats output.
    pub fn name(self) -> &'static str {
        match self {
            Self::Interpret => "T0:interpret",
            Self::HotLoopJit => "T1:hot-loop",
            Self::ComponentJit => "T2:component",
            Self::SolverJit => "T3:solver",
            Self::WholeProgram => "T4:whole-program",
        }
    }
}

impl std::fmt::Display for CompilationTier {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.name())
    }
}

/// Conflict count thresholds for tier promotion.
///
/// These are the minimum conflict counts at which the controller will
/// request promotion to each tier. The actual promotion may be delayed
/// if background compilation hasn't completed yet.
#[derive(Debug, Clone, Copy)]
pub struct TierThresholds {
    /// Conflicts before T1 promotion (0 = immediate after parse).
    pub t1_conflicts: u64,
    /// Conflicts before T2 promotion.
    pub t2_conflicts: u64,
    /// Conflicts before T3 promotion.
    pub t3_conflicts: u64,
    /// Conflicts before T4 promotion.
    pub t4_conflicts: u64,
}

impl Default for TierThresholds {
    fn default() -> Self {
        Self {
            t1_conflicts: 0,
            t2_conflicts: 1_000,
            t3_conflicts: 10_000,
            t4_conflicts: 100_000,
        }
    }
}

/// Formula characteristics used for difficulty estimation and tier capping.
///
/// Lightweight subset of the design doc's `FormulaProfile`. Kept minimal
/// to avoid cross-crate dependencies — the solver extracts these values
/// from `SatFeatures` and passes them as primitives.
#[derive(Debug, Clone, Copy)]
pub struct FormulaProfile {
    /// Number of variables.
    pub num_vars: usize,
    /// Number of clauses.
    pub num_clauses: usize,
    /// Clause-to-variable ratio.
    pub clause_var_ratio: f64,
    /// Whether the formula uses theories (LRA, LIA, EUF, etc.).
    pub has_theories: bool,
}

/// Record of a single tier promotion event.
#[derive(Debug, Clone)]
pub struct TierPromotion {
    /// Conflict count when promotion occurred.
    pub conflict_count: u64,
    /// The tier that was activated.
    pub tier: CompilationTier,
}

/// Controls tier promotion based on solve progress.
///
/// The controller tracks the current active tier, manages background
/// compilation requests, and decides when to promote based on conflict
/// count thresholds and formula difficulty.
///
/// Stored in the solver's cold state. Consulted at restart boundaries
/// to check for completed compilations and at conflict processing to
/// check if a new tier should be queued.
#[derive(Debug)]
pub struct TierController {
    /// Currently active compilation tier (code the solver is running).
    current_tier: CompilationTier,
    /// Target tier — the tier we want to reach. May be ahead of
    /// `current_tier` if background compilation is in progress or
    /// if the tier is capped by formula difficulty.
    target_tier: CompilationTier,
    /// Background compilation in progress for this tier.
    /// `None` if no compilation is pending.
    compiling_tier: Option<CompilationTier>,
    /// Conflict count thresholds for tier promotion.
    thresholds: TierThresholds,
    /// Maximum tier reachable for this formula (based on difficulty).
    max_tier: CompilationTier,
    /// Whether external code generation backend compilation is available.
    /// T2+ require the external code generation backend; without it, the controller caps at T1.
    backend_available: bool,
    /// History of tier promotions for stats output.
    promotions: Vec<TierPromotion>,
}

impl TierController {
    /// Create a new tier controller.
    ///
    /// # Arguments
    ///
    /// * `profile` — Formula characteristics for difficulty estimation.
    /// * `backend_available` — Whether external code generation backend compilation is available.
    ///
    /// The controller starts at T0 (interpret). Call `on_conflict()` with
    /// the current conflict count to trigger promotions.
    pub fn new(profile: FormulaProfile, backend_available: bool) -> Self {
        let max_tier = max_tier_for_formula(&profile, backend_available);
        let thresholds = thresholds_for_formula(&profile);

        Self {
            current_tier: CompilationTier::Interpret,
            target_tier: CompilationTier::Interpret,
            compiling_tier: None,
            thresholds,
            max_tier,
            backend_available,
            promotions: Vec::new(),
        }
    }

    /// Create a controller with default thresholds and no tier cap.
    ///
    /// Used when no formula features are available (e.g., programmatic API
    /// without feature extraction).
    pub fn default_controller(backend_available: bool) -> Self {
        let max_tier = if backend_available {
            CompilationTier::WholeProgram
        } else {
            CompilationTier::HotLoopJit
        };

        Self {
            current_tier: CompilationTier::Interpret,
            target_tier: CompilationTier::Interpret,
            compiling_tier: None,
            thresholds: TierThresholds::default(),
            max_tier,
            backend_available,
            promotions: Vec::new(),
        }
    }

    /// Check if the conflict count has reached a promotion threshold.
    ///
    /// Called from the conflict processing path. Returns `Some(tier)` if
    /// a new tier should be queued for background compilation. Returns
    /// `None` if no promotion is needed (already at max tier, compilation
    /// in progress, or threshold not reached).
    ///
    /// This method does NOT change the active tier — it only signals that
    /// compilation should be initiated. The actual swap happens in
    /// `on_compilation_complete()` + `on_restart()`.
    pub fn on_conflict(&mut self, conflict_count: u64) -> Option<CompilationTier> {
        // Already at max tier or compilation in progress.
        if self.target_tier >= self.max_tier {
            return None;
        }
        if self.compiling_tier.is_some() {
            return None;
        }

        let next_tier = match self.target_tier {
            CompilationTier::Interpret => {
                if conflict_count >= self.thresholds.t1_conflicts {
                    Some(CompilationTier::HotLoopJit)
                } else {
                    None
                }
            }
            CompilationTier::HotLoopJit => {
                if conflict_count >= self.thresholds.t2_conflicts {
                    Some(CompilationTier::ComponentJit)
                } else {
                    None
                }
            }
            CompilationTier::ComponentJit => {
                if conflict_count >= self.thresholds.t3_conflicts {
                    Some(CompilationTier::SolverJit)
                } else {
                    None
                }
            }
            CompilationTier::SolverJit => {
                if conflict_count >= self.thresholds.t4_conflicts {
                    Some(CompilationTier::WholeProgram)
                } else {
                    None
                }
            }
            CompilationTier::WholeProgram => None,
        };

        if let Some(tier) = next_tier {
            if tier <= self.max_tier {
                self.target_tier = tier;
                self.compiling_tier = Some(tier);
                return Some(tier);
            }
        }

        None
    }

    /// Called when a background compilation completes for a tier.
    ///
    /// Marks the tier as ready for swap. The actual swap to the new tier
    /// happens in `on_restart()`, which returns the tier to activate.
    pub fn on_compilation_complete(&mut self, tier: CompilationTier) {
        if self.compiling_tier == Some(tier) {
            // Compilation finished. Leave compiling_tier set so on_restart
            // knows there's a completed tier ready to swap in.
            // (We keep the value rather than clearing it, since on_restart
            // reads it to determine which tier to activate.)
        }
    }

    /// Check for completed background compilations at a restart boundary.
    ///
    /// Called from the CDCL loop at restart boundaries. Returns
    /// `Some(tier)` if a compiled tier is ready to be swapped in.
    /// The caller should then activate the new tier's compiled code.
    ///
    /// After this returns `Some`, the controller updates `current_tier`
    /// and records the promotion in the history.
    pub fn on_restart(&mut self, conflict_count: u64) -> Option<CompilationTier> {
        let ready_tier = self.compiling_tier?;

        // For T0->T1, we promote immediately (T1 compile is synchronous,
        // ~100us). For T2+, this is called after the background thread
        // signals completion.
        self.current_tier = ready_tier;
        self.compiling_tier = None;
        self.promotions.push(TierPromotion {
            conflict_count,
            tier: ready_tier,
        });

        Some(ready_tier)
    }

    /// Directly promote to a tier without background compilation.
    ///
    /// Used for T0->T1 promotion which is synchronous (the JIT compile
    /// runs inline, not on a background thread).
    pub fn promote_immediate(&mut self, tier: CompilationTier, conflict_count: u64) {
        if tier > self.max_tier {
            return;
        }
        self.current_tier = tier;
        self.target_tier = tier;
        self.compiling_tier = None;
        self.promotions.push(TierPromotion {
            conflict_count,
            tier,
        });
    }

    /// Current active compilation tier.
    #[inline]
    pub fn current_tier(&self) -> CompilationTier {
        self.current_tier
    }

    /// Target tier (may be ahead of current if compiling).
    #[inline]
    pub fn target_tier(&self) -> CompilationTier {
        self.target_tier
    }

    /// Whether a background compilation is in progress.
    #[inline]
    pub fn is_compiling(&self) -> bool {
        self.compiling_tier.is_some()
    }

    /// The tier currently being compiled, if any.
    #[inline]
    pub fn compiling_tier(&self) -> Option<CompilationTier> {
        self.compiling_tier
    }

    /// Maximum tier reachable for this formula.
    #[inline]
    pub fn max_tier(&self) -> CompilationTier {
        self.max_tier
    }

    /// Whether external code generation backend compilation is available for higher tiers.
    #[inline]
    pub fn backend_available(&self) -> bool {
        self.backend_available
    }

    /// Promotion history for stats output.
    pub fn promotions(&self) -> &[TierPromotion] {
        &self.promotions
    }

    /// Conflict count thresholds.
    pub fn thresholds(&self) -> &TierThresholds {
        &self.thresholds
    }

    /// Whether a specific tier is worth compiling for this formula.
    ///
    /// Returns `false` if:
    /// - The tier exceeds the formula's max tier (difficulty cap)
    /// - The tier requires backend compilation but no backend is available
    /// - The tier is below or equal to the current tier
    pub fn should_compile(&self, tier: CompilationTier) -> bool {
        if tier <= self.current_tier {
            return false;
        }
        if tier > self.max_tier {
            return false;
        }
        if tier >= CompilationTier::ComponentJit && !self.backend_available {
            return false;
        }
        true
    }

    /// Reset the controller for a new solve (incremental).
    ///
    /// Preserves the max_tier and thresholds (formula-dependent) but
    /// resets the current tier back to Interpret for a fresh promotion
    /// cycle. Preserves promotion history.
    pub fn reset_for_new_solve(&mut self) {
        self.current_tier = CompilationTier::Interpret;
        self.target_tier = CompilationTier::Interpret;
        self.compiling_tier = None;
        // Do not clear promotions — they are cumulative stats.
    }
}

/// Determine the maximum tier reachable for a formula based on its
/// characteristics.
///
/// Easy formulas (< 100 vars, < 500 clauses) cap at T1 — they solve
/// before higher tiers finish compiling, so the compile cost is wasted.
///
/// Medium formulas (< 10K vars) cap at T2 — component JIT gives most
/// of the benefit without the full solver compilation overhead.
///
/// Hard formulas (> 10K vars or > 50K clauses) can reach T4 — they
/// run for seconds to minutes and amortize even 200ms of compilation.
///
/// If external code generation backend compilation is unavailable, the cap is T1 regardless of formula size.
fn max_tier_for_formula(profile: &FormulaProfile, backend_available: bool) -> CompilationTier {
    if !backend_available {
        return CompilationTier::HotLoopJit;
    }

    let vars = profile.num_vars;
    let clauses = profile.num_clauses;

    if vars < 100 && clauses < 500 {
        // Tiny formula: solves in <100ms. T1 is already overkill.
        CompilationTier::HotLoopJit
    } else if vars < 1_000 && clauses < 5_000 {
        // Small formula: T2 provides benefit without excessive compile cost.
        CompilationTier::ComponentJit
    } else if vars < 10_000 && clauses < 50_000 {
        // Medium formula: T3 (solver JIT) is worthwhile.
        CompilationTier::SolverJit
    } else {
        // Large/hard formula: full T4 is justified.
        CompilationTier::WholeProgram
    }
}

/// Adjust thresholds based on formula characteristics.
///
/// Dense formulas (high clause/var ratio) promote earlier because
/// each conflict processes more clauses, making JIT benefits more
/// pronounced. Theory-heavy formulas promote slightly later because
/// theory overhead dominates BCP time and JIT of BCP alone helps less.
fn thresholds_for_formula(profile: &FormulaProfile) -> TierThresholds {
    let mut thresholds = TierThresholds::default();

    // Dense formulas: promote earlier (more BCP work per conflict).
    if profile.clause_var_ratio > 10.0 {
        thresholds.t2_conflicts = 500;
        thresholds.t3_conflicts = 5_000;
        thresholds.t4_conflicts = 50_000;
    }

    // Large formulas: promote earlier (expected long solve).
    if profile.num_vars > 50_000 {
        thresholds.t2_conflicts = 200;
        thresholds.t3_conflicts = 2_000;
        thresholds.t4_conflicts = 20_000;
    }

    // Theory-heavy: delay T2+ slightly (theory overhead > BCP overhead).
    if profile.has_theories {
        thresholds.t2_conflicts = thresholds.t2_conflicts.saturating_mul(2);
        thresholds.t3_conflicts = thresholds.t3_conflicts.saturating_mul(2);
        thresholds.t4_conflicts = thresholds.t4_conflicts.saturating_mul(2);
    }

    thresholds
}

#[cfg(test)]
#[path = "tier_controller/tests.rs"]
mod tests;
