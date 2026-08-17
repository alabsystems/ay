// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Static SAT instance feature extraction for algorithm selection.
//!
//! Computes SATzilla-style syntactic features from a CNF formula in O(n) time
//! where n is the total number of literal occurrences. These features are used
//! by the portfolio solver to select the best strategy per instance.
//!
//! ## Feature Set
//!
//! The feature vector captures:
//! - **Size features**: variable count, clause count, clause/variable ratio
//! - **Clause size distribution**: mean, std, min, max, fraction binary/ternary/horn
//! - **Variable-clause graph**: positive/negative literal balance, variable degree stats
//! - **Structure indicators**: pure literal count, unit clause count
//!
//! ## References
//!
//! - Xu, Hutter, Hoos, Leyton-Brown. "SATzilla: Portfolio-based Algorithm
//!   Selection for SAT." JAIR 2008.
//! - the development design notes (Phase 1a: Static
//!   Syntactic Features)

use crate::literal::Literal;

/// Static syntactic features extracted from a CNF formula.
///
/// All features are computed in a single pass over the clause database.
/// The feature vector is designed for algorithm selection: different
/// portfolio strategies perform differently on formulas with different
/// structural properties.
#[derive(Debug, Clone, PartialEq)]
pub struct SatFeatures {
    // --- Size features ---
    /// Number of variables in the formula.
    pub(crate) num_vars: usize,
    /// Number of clauses in the formula.
    pub(crate) num_clauses: usize,
    /// Clause-to-variable ratio (num_clauses / num_vars).
    /// High ratios (>4.26 for 3-SAT) indicate over-constrained instances.
    pub(crate) clause_var_ratio: f64,

    // --- Clause size distribution ---
    /// Number of unit clauses (size 1).
    pub(crate) num_unit: usize,
    /// Number of binary clauses (size 2).
    pub(crate) num_binary: usize,
    /// Number of ternary clauses (size 3).
    pub(crate) num_ternary: usize,
    /// Number of horn clauses (at most one positive literal).
    pub(crate) num_horn: usize,
    /// Fraction of clauses that are binary.
    pub(crate) frac_binary: f64,
    /// Fraction of clauses that are ternary.
    pub(crate) frac_ternary: f64,
    /// Fraction of clauses that are horn.
    pub(crate) frac_horn: f64,
    /// Mean clause size.
    pub(crate) clause_size_mean: f64,
    /// Standard deviation of clause sizes.
    pub(crate) clause_size_std: f64,
    /// Minimum clause size (0 if no clauses).
    pub(crate) clause_size_min: usize,
    /// Maximum clause size.
    pub(crate) clause_size_max: usize,

    // --- Variable polarity balance ---
    /// Mean ratio of positive to total occurrences per variable.
    /// 0.5 = balanced, near 0 or 1 = highly polarized.
    pub(crate) pos_neg_balance_mean: f64,
    /// Standard deviation of the positive/total ratio across variables.
    pub(crate) pos_neg_balance_std: f64,

    // --- Variable degree features ---
    /// Mean variable degree (number of clause occurrences per variable).
    pub(crate) var_degree_mean: f64,
    /// Standard deviation of variable degrees.
    pub(crate) var_degree_std: f64,
    /// Maximum variable degree.
    pub(crate) var_degree_max: usize,

    // --- Structural indicators ---
    /// Number of pure literals (appearing in only one polarity).
    pub(crate) num_pure_literals: usize,
    /// Fraction of variables that are pure.
    pub(crate) frac_pure: f64,
}

/// Probe-route band predicate on raw clause counts (the single source of truth
/// for [`SatFeatures::matches_probe_route_band`] and the streaming pre-scan).
///
/// `num_vars` must be the content-driven max-variable count (not the declared
/// header value) so it matches the solver's actual sizing. Band:
/// `frac_binary >= 0.70 && clause/var <= 4.0 && 10_000 <= num_vars <= 3_000_000`.
/// See [`SatFeatures::matches_probe_route_band`] for the derivation.
#[must_use]
pub(crate) fn probe_route_band_from_counts(
    num_vars: usize,
    num_clauses: usize,
    num_binary: usize,
) -> bool {
    const MIN_BINARY_FRACTION: f64 = 0.70;
    const MAX_CLAUSE_VAR_RATIO: f64 = 4.0;
    // 50_000 (not 10_000): the full in-band A/B showed Probe's lighter
    // preprocessing HELPS large binary-dominant instances (all currently
    // UNSOLVED on Default) but HURTS a smaller borderline one (`d0298807`,
    // 33_919 vars, solved on Default at 96.6 s, lost under Probe). Every
    // in-band instance above 50k vars is currently unsolved on Default, so
    // this floor makes a regression impossible on the measured set while
    // keeping all three flips (`c86b2611` 82_269v, `d2af3fde`/`30f64b3b`
    // ~1.7-1.9M v). The two sub-15k survivors solve fine on Default anyway.
    const MIN_VARS: usize = 50_000;
    const MAX_VARS: usize = 3_000_000;

    if num_vars == 0 || num_clauses == 0 {
        return false;
    }
    let frac_binary = num_binary as f64 / num_clauses as f64;
    let clause_var_ratio = num_clauses as f64 / num_vars as f64;
    frac_binary >= MIN_BINARY_FRACTION
        && clause_var_ratio <= MAX_CLAUSE_VAR_RATIO
        && (MIN_VARS..=MAX_VARS).contains(&num_vars)
}

/// Aggressive-route band predicate on raw clause counts (the single source of
/// truth for [`SatFeatures::matches_aggressive_route_band`] and the streaming
/// pre-scan). Disjoint from [`probe_route_band_from_counts`] by the clause/var
/// ratio: the probe band owns `ratio <= 4.0`, this band owns `4.0 < ratio <=
/// 6.5`, so no instance can match both.
///
/// `num_vars` must be the content-driven max-variable count (not the declared
/// header value) so it matches the solver's actual sizing. Band:
/// `frac_binary >= 0.70 && 4.0 < clause/var <= 6.5 && 50_000 <= num_vars <=
/// 250_000`. See [`SatFeatures::matches_aggressive_route_band`] for the
/// derivation and the measured flip.
#[must_use]
pub(crate) fn aggressive_route_band_from_counts(
    num_vars: usize,
    num_clauses: usize,
    num_binary: usize,
) -> bool {
    const MIN_BINARY_FRACTION: f64 = 0.70;
    // Strict lower bound: the probe-route band already owns `ratio <= 4.0`, so
    // this band starts just above it. This keeps the two auto-route bands
    // disjoint by construction (an instance is at most one of Probe/Aggressive).
    const MIN_CLAUSE_VAR_RATIO_EXCL: f64 = 4.0;
    const MAX_CLAUSE_VAR_RATIO: f64 = 6.5;
    // 50_000 lower / 250_000 upper: the measured flip (`16c999d0`, 50_277 vars)
    // sits at the floor of the band, and the 250k cap excludes the
    // multi-million-var giants (e.g. the 7.3M-var floor instance `4d6e18e5`,
    // ratio 5.58 but `frac_binary` 0.069) whose Default/giant path is already
    // tuned and is OOM-risky to re-route untested.
    const MIN_VARS: usize = 50_000;
    const MAX_VARS: usize = 250_000;

    if num_vars == 0 || num_clauses == 0 {
        return false;
    }
    let frac_binary = num_binary as f64 / num_clauses as f64;
    let clause_var_ratio = num_clauses as f64 / num_vars as f64;
    frac_binary >= MIN_BINARY_FRACTION
        && clause_var_ratio > MIN_CLAUSE_VAR_RATIO_EXCL
        && clause_var_ratio <= MAX_CLAUSE_VAR_RATIO
        && (MIN_VARS..=MAX_VARS).contains(&num_vars)
}

impl SatFeatures {
    /// Extract features from a set of clauses.
    ///
    /// Runs in O(total_literals) time with O(num_vars) auxiliary space.
    pub fn extract(num_vars: usize, clauses: &[Vec<Literal>]) -> Self {
        let num_clauses = clauses.len();

        if num_vars == 0 || num_clauses == 0 {
            return Self::empty(num_vars, num_clauses);
        }

        // Per-variable occurrence counts.
        let mut pos_count: Vec<u32> = vec![0; num_vars];
        let mut neg_count: Vec<u32> = vec![0; num_vars];

        // Clause size stats.
        let mut num_unit = 0usize;
        let mut num_binary = 0usize;
        let mut num_ternary = 0usize;
        let mut num_horn = 0usize;
        let mut clause_size_min = usize::MAX;
        let mut clause_size_max = 0usize;
        let mut size_sum = 0u64;
        let mut size_sq_sum = 0u64;

        for clause in clauses {
            let len = clause.len();
            size_sum += len as u64;
            size_sq_sum += (len as u64) * (len as u64);
            if len < clause_size_min {
                clause_size_min = len;
            }
            if len > clause_size_max {
                clause_size_max = len;
            }

            match len {
                1 => num_unit += 1,
                2 => num_binary += 1,
                3 => num_ternary += 1,
                _ => {}
            }

            // Count positive literals for horn clause detection.
            let mut pos_in_clause = 0u32;
            for &lit in clause {
                let var_idx = lit.variable().index();
                if var_idx < num_vars {
                    if lit.is_positive() {
                        pos_count[var_idx] += 1;
                        pos_in_clause += 1;
                    } else {
                        neg_count[var_idx] += 1;
                    }
                }
            }
            // Horn clause: at most one positive literal.
            if pos_in_clause <= 1 {
                num_horn += 1;
            }
        }

        if clause_size_min == usize::MAX {
            clause_size_min = 0;
        }

        let n = num_clauses as f64;
        let clause_size_mean = size_sum as f64 / n;
        let variance = clause_size_mean.mul_add(-clause_size_mean, size_sq_sum as f64 / n);
        let clause_size_std = if variance > 0.0 { variance.sqrt() } else { 0.0 };

        // Variable degree and polarity balance.
        let mut degree_sum = 0u64;
        let mut degree_sq_sum = 0u64;
        let mut var_degree_max = 0usize;
        let mut balance_sum = 0.0f64;
        let mut balance_sq_sum = 0.0f64;
        let mut num_pure_literals = 0usize;
        let mut active_vars = 0usize;

        for i in 0..num_vars {
            let p = u64::from(pos_count[i]);
            let ng = u64::from(neg_count[i]);
            let total = p + ng;
            if total == 0 {
                continue;
            }
            active_vars += 1;
            let degree = total as usize;
            degree_sum += total;
            degree_sq_sum += total * total;
            if degree > var_degree_max {
                var_degree_max = degree;
            }

            let balance = p as f64 / total as f64;
            balance_sum += balance;
            balance_sq_sum += balance * balance;

            if p == 0 || ng == 0 {
                num_pure_literals += 1;
            }
        }

        let active = active_vars.max(1) as f64;
        let var_degree_mean = degree_sum as f64 / active;
        let var_degree_variance =
            var_degree_mean.mul_add(-var_degree_mean, degree_sq_sum as f64 / active);
        let var_degree_std = if var_degree_variance > 0.0 {
            var_degree_variance.sqrt()
        } else {
            0.0
        };

        let pos_neg_balance_mean = balance_sum / active;
        let balance_variance =
            pos_neg_balance_mean.mul_add(-pos_neg_balance_mean, balance_sq_sum / active);
        let pos_neg_balance_std = if balance_variance > 0.0 {
            balance_variance.sqrt()
        } else {
            0.0
        };

        Self {
            num_vars,
            num_clauses,
            clause_var_ratio: num_clauses as f64 / num_vars.max(1) as f64,
            num_unit,
            num_binary,
            num_ternary,
            num_horn,
            frac_binary: num_binary as f64 / n,
            frac_ternary: num_ternary as f64 / n,
            frac_horn: num_horn as f64 / n,
            clause_size_mean,
            clause_size_std,
            clause_size_min,
            clause_size_max,
            pos_neg_balance_mean,
            pos_neg_balance_std,
            var_degree_mean,
            var_degree_std,
            var_degree_max,
            num_pure_literals,
            frac_pure: num_pure_literals as f64 / active,
        }
    }

    /// Construct a partial feature set from streaming-parse counters.
    ///
    /// The streaming DIMACS path cannot buffer all clauses for a full
    /// `extract()` call. This constructor accepts the subset of counters
    /// that the streaming parser accumulates, filling the remaining fields
    /// with neutral defaults. The resulting `SatFeatures` is sufficient for
    /// `InstanceClass::classify()` and `adjust_features_for_instance()`.
    pub fn from_streaming_counters(
        num_vars: usize,
        num_clauses: usize,
        num_ternary: usize,
        num_horn: usize,
    ) -> Self {
        let n = num_clauses.max(1) as f64;
        Self {
            num_vars,
            num_clauses,
            clause_var_ratio: num_clauses as f64 / num_vars.max(1) as f64,
            num_unit: 0,
            num_binary: 0,
            num_ternary,
            num_horn,
            frac_binary: 0.0,
            frac_ternary: num_ternary as f64 / n,
            frac_horn: num_horn as f64 / n,
            clause_size_mean: 0.0,
            clause_size_std: 0.0,
            clause_size_min: 0,
            clause_size_max: 0,
            pos_neg_balance_mean: 0.5,
            pos_neg_balance_std: 0.0,
            var_degree_mean: 0.0,
            var_degree_std: 0.0,
            var_degree_max: 0,
            num_pure_literals: 0,
            frac_pure: 0.0,
        }
    }

    /// Recognize the narrow binary/ternary multiplier-equivalence CNF envelope.
    ///
    /// This helper is deterministic and non-routing: it is intentionally not
    /// used by [`InstanceClass::classify`] or any solver policy. The predicate
    /// only captures the observed Main 2025 multiplier-equivalence shape so a
    /// later default-off probe can measure heuristic overhead without changing
    /// SAT/model/proof authority.
    #[must_use]
    pub fn looks_like_binary_ternary_multiplier_equivalence(&self) -> bool {
        const MIN_VARS: usize = 2_500;
        const MAX_VARS: usize = 3_500;
        const MIN_CLAUSES: usize = 8_000;
        const MAX_CLAUSES: usize = 11_000;
        const MIN_CLAUSE_VAR_RATIO: f64 = 3.0;
        const MAX_CLAUSE_VAR_RATIO: f64 = 3.6;
        const MIN_BINARY_FRACTION: f64 = 0.30;
        const MAX_BINARY_FRACTION: f64 = 0.50;
        const MIN_TERNARY_FRACTION: f64 = 0.50;
        const MAX_TERNARY_FRACTION: f64 = 0.70;
        const MIN_HORN_FRACTION: f64 = 0.55;
        const MAX_HORN_FRACTION: f64 = 0.75;

        (MIN_VARS..=MAX_VARS).contains(&self.num_vars)
            && (MIN_CLAUSES..=MAX_CLAUSES).contains(&self.num_clauses)
            && self.num_unit == 1
            && self.clause_size_min == 1
            && self.clause_size_max == 3
            && self.num_unit + self.num_binary + self.num_ternary == self.num_clauses
            && (MIN_CLAUSE_VAR_RATIO..=MAX_CLAUSE_VAR_RATIO).contains(&self.clause_var_ratio)
            && (MIN_BINARY_FRACTION..=MAX_BINARY_FRACTION).contains(&self.frac_binary)
            && (MIN_TERNARY_FRACTION..=MAX_TERNARY_FRACTION).contains(&self.frac_ternary)
            && (MIN_HORN_FRACTION..=MAX_HORN_FRACTION).contains(&self.frac_horn)
    }

    /// Probe-route band: binary-dominant, low clause/var ratio, mid-size.
    ///
    /// When no explicit `--sat-variant` is given, load-time features in this
    /// band auto-route the Default preset to the Probe preset (light
    /// preprocessing + Luby-250 restarts + MAB branching), which measured 4
    /// clean flips (`c86b2611`, `d2af3fde`, `30f64b3b`) with zero in-band
    /// regressions in the full 17-instance A/B. The `num_vars <= 3_000_000`
    /// upper bound excludes the currently-solved binary-dominant giants
    /// (7.9M-58M vars, c/v ~2.69 — e.g. `1c21a43a`, `00fd8ac9`) which the
    /// giant-mode path already handles and which are OOM-risky to re-route
    /// untested; the flips sit at <= 1.87M vars, leaving a clean gap. The
    /// `num_vars >= 50_000` lower bound keeps smaller instances on Default,
    /// where full preprocessing pays off — Probe regressed `d0298807`
    /// (33_919 vars, Default SAT@96.6 s) but helps the larger unsolved band.
    #[must_use]
    pub fn matches_probe_route_band(&self) -> bool {
        probe_route_band_from_counts(self.num_vars, self.num_clauses, self.num_binary)
    }

    /// Aggressive-route band: binary-dominant, mid-ratio, mid-size.
    ///
    /// When no explicit `--sat-variant` is given and the probe-route band did
    /// not match, load-time features in this band auto-route the Default preset
    /// to the Aggressive preset (higher restart frequency + heavier
    /// vivify/subsume schedule). Verified flip: `16c999d0` (50_277 vars, c/v
    /// 5.65, `frac_binary` 0.875) goes from Default TIMEOUT@120 s to Aggressive
    /// UNSAT @76 s (cake_lpr `s VERIFIED UNSAT`, kissat oracle agrees). The
    /// mechanism is a restart-frequency + vivify/subsume schedule change
    /// (restarts 775 -> 18_164, BVE 12_219 -> 0), not "more preprocessing."
    ///
    /// This band is disjoint from [`Self::matches_probe_route_band`] by the
    /// clause/var ratio (probe: `<= 4.0`, aggressive: `4.0 < r <= 6.5`), and is
    /// evaluated after it. The `num_vars <= 250_000` cap excludes the
    /// multi-million-var giants (the giant path handles those); the
    /// `frac_binary >= 0.70` gate keeps non-binary-dominant mid-size instances
    /// on Default. Kill-switch: `--sat-no-aggressive-route`.
    #[must_use]
    pub fn matches_aggressive_route_band(&self) -> bool {
        aggressive_route_band_from_counts(self.num_vars, self.num_clauses, self.num_binary)
    }

    /// Features for an empty or trivial formula.
    fn empty(num_vars: usize, num_clauses: usize) -> Self {
        Self {
            num_vars,
            num_clauses,
            clause_var_ratio: if num_vars > 0 {
                num_clauses as f64 / num_vars as f64
            } else {
                0.0
            },
            num_unit: 0,
            num_binary: 0,
            num_ternary: 0,
            num_horn: 0,
            frac_binary: 0.0,
            frac_ternary: 0.0,
            frac_horn: 0.0,
            clause_size_mean: 0.0,
            clause_size_std: 0.0,
            clause_size_min: 0,
            clause_size_max: 0,
            pos_neg_balance_mean: 0.5,
            pos_neg_balance_std: 0.0,
            var_degree_mean: 0.0,
            var_degree_std: 0.0,
            var_degree_max: 0,
            num_pure_literals: 0,
            frac_pure: 0.0,
        }
    }
}

/// Single-pass SAT feature accumulator for streaming CNF ingestion.
///
/// This computes the same syntactic feature set as [`SatFeatures::extract`]
/// without requiring all clauses to be stored at once.
#[derive(Debug, Clone)]
pub struct SatFeatureAccumulator {
    num_vars: usize,
    num_clauses: usize,
    pos_count: Vec<u32>,
    neg_count: Vec<u32>,
    num_unit: usize,
    num_binary: usize,
    num_ternary: usize,
    num_horn: usize,
    clause_size_min: usize,
    clause_size_max: usize,
    size_sum: u64,
    size_sq_sum: u64,
}

impl SatFeatureAccumulator {
    /// Create an empty accumulator for a formula with `num_vars` variables.
    pub fn new(num_vars: usize) -> Self {
        Self {
            num_vars,
            num_clauses: 0,
            pos_count: vec![0; num_vars],
            neg_count: vec![0; num_vars],
            num_unit: 0,
            num_binary: 0,
            num_ternary: 0,
            num_horn: 0,
            clause_size_min: usize::MAX,
            clause_size_max: 0,
            size_sum: 0,
            size_sq_sum: 0,
        }
    }

    /// Add one parsed clause to the accumulator.
    pub fn add_clause(&mut self, clause: &[Literal]) {
        self.add_clause_shape(clause.len());
        let mut pos_in_clause = 0u32;
        for &lit in clause {
            self.add_literal_occurrence(lit, &mut pos_in_clause);
        }
        self.finish_clause_polarity(pos_in_clause);
    }

    /// Convert one raw DIMACS clause into `clause_buf` while accumulating features.
    ///
    /// `raw_clause` must contain non-zero DIMACS literals. The resulting buffer
    /// has the same internal literals as mapping each entry through
    /// [`Literal::from_dimacs`], and the counters match [`Self::add_clause`].
    pub fn add_dimacs_clause_to_buffer(
        &mut self,
        raw_clause: &[i32],
        clause_buf: &mut Vec<Literal>,
    ) {
        clause_buf.clear();
        clause_buf.reserve(raw_clause.len());

        self.add_clause_shape(raw_clause.len());
        let mut pos_in_clause = 0u32;
        for &raw_lit in raw_clause {
            let lit = Literal::from_dimacs(raw_lit);
            self.add_literal_occurrence(lit, &mut pos_in_clause);
            clause_buf.push(lit);
        }
        self.finish_clause_polarity(pos_in_clause);
    }

    /// Number of clauses observed so far.
    pub fn num_clauses(&self) -> usize {
        self.num_clauses
    }

    fn add_clause_shape(&mut self, len: usize) {
        self.num_clauses += 1;

        self.size_sum += len as u64;
        self.size_sq_sum += (len as u64) * (len as u64);
        if len < self.clause_size_min {
            self.clause_size_min = len;
        }
        if len > self.clause_size_max {
            self.clause_size_max = len;
        }

        match len {
            1 => self.num_unit += 1,
            2 => self.num_binary += 1,
            3 => self.num_ternary += 1,
            _ => {}
        }
    }

    fn add_literal_occurrence(&mut self, lit: Literal, pos_in_clause: &mut u32) {
        let var_idx = lit.variable().index();
        if var_idx < self.num_vars {
            if lit.is_positive() {
                self.pos_count[var_idx] += 1;
                *pos_in_clause += 1;
            } else {
                self.neg_count[var_idx] += 1;
            }
        }
    }

    fn finish_clause_polarity(&mut self, pos_in_clause: u32) {
        if pos_in_clause <= 1 {
            self.num_horn += 1;
        }
    }

    /// Finish accumulation and return the computed feature set.
    pub fn finish(self) -> SatFeatures {
        if self.num_vars == 0 || self.num_clauses == 0 {
            return SatFeatures::empty(self.num_vars, self.num_clauses);
        }

        let clause_size_min = if self.clause_size_min == usize::MAX {
            0
        } else {
            self.clause_size_min
        };

        let n = self.num_clauses as f64;
        let clause_size_mean = self.size_sum as f64 / n;
        let variance = clause_size_mean.mul_add(-clause_size_mean, self.size_sq_sum as f64 / n);
        let clause_size_std = if variance > 0.0 { variance.sqrt() } else { 0.0 };

        let mut degree_sum = 0u64;
        let mut degree_sq_sum = 0u64;
        let mut var_degree_max = 0usize;
        let mut balance_sum = 0.0f64;
        let mut balance_sq_sum = 0.0f64;
        let mut num_pure_literals = 0usize;
        let mut active_vars = 0usize;

        for i in 0..self.num_vars {
            let p = u64::from(self.pos_count[i]);
            let ng = u64::from(self.neg_count[i]);
            let total = p + ng;
            if total == 0 {
                continue;
            }
            active_vars += 1;
            let degree = total as usize;
            degree_sum += total;
            degree_sq_sum += total * total;
            if degree > var_degree_max {
                var_degree_max = degree;
            }

            let balance = p as f64 / total as f64;
            balance_sum += balance;
            balance_sq_sum += balance * balance;

            if p == 0 || ng == 0 {
                num_pure_literals += 1;
            }
        }

        let active = active_vars.max(1) as f64;
        let var_degree_mean = degree_sum as f64 / active;
        let var_degree_variance =
            var_degree_mean.mul_add(-var_degree_mean, degree_sq_sum as f64 / active);
        let var_degree_std = if var_degree_variance > 0.0 {
            var_degree_variance.sqrt()
        } else {
            0.0
        };

        let pos_neg_balance_mean = balance_sum / active;
        let balance_variance =
            pos_neg_balance_mean.mul_add(-pos_neg_balance_mean, balance_sq_sum / active);
        let pos_neg_balance_std = if balance_variance > 0.0 {
            balance_variance.sqrt()
        } else {
            0.0
        };

        SatFeatures {
            num_vars: self.num_vars,
            num_clauses: self.num_clauses,
            clause_var_ratio: self.num_clauses as f64 / self.num_vars.max(1) as f64,
            num_unit: self.num_unit,
            num_binary: self.num_binary,
            num_ternary: self.num_ternary,
            num_horn: self.num_horn,
            frac_binary: self.num_binary as f64 / n,
            frac_ternary: self.num_ternary as f64 / n,
            frac_horn: self.num_horn as f64 / n,
            clause_size_mean,
            clause_size_std,
            clause_size_min,
            clause_size_max: self.clause_size_max,
            pos_neg_balance_mean,
            pos_neg_balance_std,
            var_degree_mean,
            var_degree_std,
            var_degree_max,
            num_pure_literals,
            frac_pure: num_pure_literals as f64 / active,
        }
    }
}

/// Instance class derived from static features.
///
/// Used by the portfolio strategy selector to route instances to the best
/// portfolio configuration. Classes are based on structural properties that
/// empirically correlate with solver strategy performance:
///
/// - **Random3Sat**: High clause/variable ratio, mostly ternary clauses.
///   These benefit from aggressive inprocessing and strong BVE.
/// - **RandomKSat**: Uniform k-SAT with k != 3 (e.g., 5-SAT, 7-SAT).
///   Same strategy as Random3Sat: no exploitable structure.
/// - **Structured**: High fraction of binary/horn clauses, moderate density.
///   Gate extraction, congruence closure, and BVE are critical.
/// - **Industrial**: Very large formulas with heterogeneous structure.
///   Conservative search with targeted inprocessing works best.
/// - **Small**: Few variables. Any strategy works; use the default.
/// - **Unknown**: Formulas that don't match any recognized pattern.
///   Uses default strategy (no special rules).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum InstanceClass {
    /// Random 3-SAT near the phase transition.
    Random3Sat,
    /// Random k-SAT (k != 3) with uniform clause widths.
    RandomKSat,
    /// Structured/combinatorial instance (circuit, crypto, scheduling).
    Structured,
    /// Large industrial/application instance with heterogeneous structure.
    Industrial,
    /// Small instance (<1000 variables) where strategy matters little.
    Small,
    /// Unclassified formula that doesn't match any recognized pattern.
    Unknown,
}

impl InstanceClass {
    /// Classify an instance from its features.
    ///
    /// The thresholds are based on SATzilla feature analysis and CaDiCaL's
    /// internal heuristics. They are intentionally conservative: better to
    /// default to a robust strategy than to over-classify.
    pub fn classify(features: &SatFeatures) -> Self {
        // Small instances: strategy selection overhead exceeds benefit.
        if features.num_vars < 1000 {
            return Self::Small;
        }

        // Random 3-SAT: high clause/var ratio, mostly ternary, low horn fraction.
        // The phase transition for random 3-SAT is at ratio ~4.26.
        if features.frac_ternary > 0.8
            && features.clause_var_ratio > 3.5
            && features.frac_horn < 0.5
        {
            return Self::Random3Sat;
        }

        // Random k-SAT (k != 3): uniform clause widths (all same length),
        // non-binary, non-ternary, balanced polarity, high clause/var ratio.
        // These formulas are generated uniformly at random and have no
        // exploitable structure (same as Random3Sat).
        if features.clause_size_std < 0.1
            && features.clause_size_min == features.clause_size_max
            && features.clause_size_min > 3
            && features.clause_var_ratio > 2.0
            && (features.pos_neg_balance_mean - 0.5).abs() < 0.15
        {
            return Self::RandomKSat;
        }

        // Structured: high binary fraction, or high horn fraction, or
        // high clause size variance (mixed clause sizes typical of circuits).
        if features.frac_binary > 0.5
            || features.frac_horn > 0.7
            || (features.clause_size_std > 2.0 && features.clause_size_max > 10)
        {
            return Self::Structured;
        }

        // Industrial: very large formulas with heterogeneous structure.
        // Pure size alone is insufficient — large combinatorial puzzles have
        // uniform structure. Require structural heterogeneity: high variable-
        // degree variance OR high clause-width variance.
        if features.num_vars > 50_000 || features.num_clauses > 200_000 {
            let coeff_of_var_degree = if features.var_degree_mean > 0.0 {
                features.var_degree_std / features.var_degree_mean
            } else {
                0.0
            };
            let has_structural_heterogeneity =
                coeff_of_var_degree > 0.5 || features.clause_size_std > 1.0;
            if has_structural_heterogeneity {
                return Self::Industrial;
            }
            // Large but uniform → Unknown (not Industrial, not Structured).
            return Self::Unknown;
        }

        // Medium formulas that don't match any specific pattern.
        Self::Unknown
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::literal::{Literal, Variable};

    /// Helper: create a positive literal for variable index `v`.
    fn pos(v: u32) -> Literal {
        Literal::positive(Variable(v))
    }

    /// Helper: create a negative literal for variable index `v`.
    fn neg(v: u32) -> Literal {
        Literal::negative(Variable(v))
    }

    /// Build a feature set with a chosen size/binary-fraction for band tests.
    /// `clause_var_ratio` is derived from `nv`/`nc` exactly as `extract` does;
    /// `num_binary` is set so the band's derived `frac_binary` matches.
    fn band_feat(nv: usize, nc: usize, frac_binary: f64) -> SatFeatures {
        let mut f = SatFeatures::empty(nv, nc);
        f.num_binary = (frac_binary * nc as f64).round() as usize;
        f.frac_binary = frac_binary;
        f
    }

    #[test]
    fn probe_route_band_membership() {
        // In-band representative (c86b2611: 82269v, 271217c, fbin 0.735).
        assert!(band_feat(82_269, 271_217, 0.735).matches_probe_route_band());
        // In-band low-ratio dominant-binary (d2af3fde class).
        assert!(band_feat(1_692_960, 3_410_378, 0.9825).matches_probe_route_band());

        // Giant excluded by vars upper bound (7.9M-58M vars stay on Default).
        assert!(!band_feat(7_900_000, 21_000_000, 0.72).matches_probe_route_band());
        // Small-sparse excluded by vars lower bound (e.g. reduce-cap floor class).
        assert!(!band_feat(1_043, 3_649, 0.90).matches_probe_route_band());
        // The A/B regression (d0298807, 33_919 vars) is below the 50k floor.
        assert!(!band_feat(33_919, 133_179, 0.9296).matches_probe_route_band());
        // Ratio too high (over-constrained) excluded.
        assert!(!band_feat(100_000, 450_001, 0.90).matches_probe_route_band());
        // Not binary-dominant (fbin 0.667 candidates) excluded.
        assert!(!band_feat(100_000, 300_000, 0.667).matches_probe_route_band());

        // Boundary exactness.
        assert!(band_feat(50_000, 150_000, 0.70).matches_probe_route_band());
        assert!(band_feat(3_000_000, 6_000_000, 0.70).matches_probe_route_band());
        assert!(!band_feat(49_999, 150_000, 0.90).matches_probe_route_band());
        assert!(!band_feat(3_000_001, 6_000_000, 0.90).matches_probe_route_band());
        assert!(!band_feat(100_000, 300_000, 0.6999).matches_probe_route_band());
        assert!(!band_feat(100_000, 400_001, 0.90).matches_probe_route_band()); // ratio 4.00001
        assert!(band_feat(100_000, 400_000, 0.90).matches_probe_route_band()); // ratio == 4.0

        // Raw-count entry (streaming pre-scan) agrees with the feature method.
        assert!(probe_route_band_from_counts(82_269, 271_217, 199_345)); // c86b2611
        assert!(!probe_route_band_from_counts(
            7_900_000, 21_000_000, 15_120_000
        )); // giant
        assert!(!probe_route_band_from_counts(100_000, 300_000, 200_000)); // fbin 0.667
        assert!(!probe_route_band_from_counts(0, 0, 0)); // empty guard
    }

    #[test]
    fn aggressive_route_band_membership() {
        // In-band representatives (real content-driven shapes of the 3 in-band
        // instances from the batch-5 A/B).
        // 16c999d0: 50_277v, 283_903c, fbin 0.8749, ratio 5.647 (the flip).
        assert!(band_feat(50_277, 283_903, 0.8749).matches_aggressive_route_band());
        // 24075575: 199_290v, 1_005_792c, fbin 0.7525, ratio 5.047.
        assert!(band_feat(199_290, 1_005_792, 0.7525).matches_aggressive_route_band());
        // 9a839bad: 151_952v, 697_321c, fbin 0.7904, ratio 4.589.
        assert!(band_feat(151_952, 697_321, 0.7904).matches_aggressive_route_band());

        // Ratio in probe territory (<= 4.0) excluded — probe owns it.
        assert!(!band_feat(82_269, 271_217, 0.7354).matches_aggressive_route_band()); // c86b2611, r 3.30
                                                                                      // Ratio too high (> 6.5) excluded.
        assert!(!band_feat(100_000, 700_000, 0.90).matches_aggressive_route_band()); // r 7.0
                                                                                     // Not binary-dominant (fbin < 0.70) excluded.
        assert!(!band_feat(50_777, 304_370, 0.0).matches_aggressive_route_band()); // 03e852aa
        assert!(!band_feat(120_036, 704_717, 0.499).matches_aggressive_route_band()); // 27570c67
                                                                                      // Giant excluded by vars upper bound (e.g. the 4d6e18e5 floor, r 5.58).
        assert!(!band_feat(7_298_456, 40_703_521, 0.90).matches_aggressive_route_band());
        // Small excluded by vars lower bound.
        assert!(!band_feat(49_999, 250_000, 0.90).matches_aggressive_route_band());

        // Boundary exactness.
        assert!(band_feat(100_000, 400_001, 0.80).matches_aggressive_route_band()); // r 4.00001 in
        assert!(!band_feat(100_000, 400_000, 0.80).matches_aggressive_route_band()); // r == 4.0 out (probe)
        assert!(band_feat(100_000, 650_000, 0.80).matches_aggressive_route_band()); // r == 6.5 in
        assert!(!band_feat(100_000, 650_001, 0.80).matches_aggressive_route_band()); // r 6.50001 out
        assert!(band_feat(50_000, 250_000, 0.80).matches_aggressive_route_band()); // vars floor in
        assert!(band_feat(250_000, 1_250_000, 0.80).matches_aggressive_route_band()); // vars cap in
        assert!(!band_feat(250_001, 1_250_005, 0.80).matches_aggressive_route_band()); // vars cap out
        assert!(band_feat(100_000, 500_000, 0.70).matches_aggressive_route_band()); // fbin == 0.70 in
        assert!(!band_feat(100_000, 500_000, 0.6999).matches_aggressive_route_band()); // fbin < 0.70 out

        // Disjointness: every in-band aggressive instance is NOT in the probe
        // band, and every in-band probe instance is NOT in the aggressive band.
        for f in [
            band_feat(50_277, 283_903, 0.8749),
            band_feat(199_290, 1_005_792, 0.7525),
            band_feat(151_952, 697_321, 0.7904),
        ] {
            assert!(f.matches_aggressive_route_band());
            assert!(!f.matches_probe_route_band());
        }
        for f in [
            band_feat(82_269, 271_217, 0.7354),      // c86b2611 (probe flip)
            band_feat(1_692_960, 3_410_378, 0.9825), // d2af3fde (probe flip)
        ] {
            assert!(f.matches_probe_route_band());
            assert!(!f.matches_aggressive_route_band());
        }

        // Raw-count entry (streaming pre-scan) agrees with the feature method.
        assert!(aggressive_route_band_from_counts(50_277, 283_903, 248_386)); // 16c999d0
        assert!(!aggressive_route_band_from_counts(82_269, 271_217, 199_345)); // c86b2611 (probe)
        assert!(!aggressive_route_band_from_counts(0, 0, 0)); // empty guard
    }

    fn rotating_var(num_vars: usize, seed: usize, offset: usize) -> u32 {
        ((seed.wrapping_mul(17).wrapping_add(offset)) % num_vars) as u32
    }

    fn multiplier_equivalence_like_clauses(num_vars: usize) -> Vec<Vec<Literal>> {
        let mut clauses = Vec::with_capacity(8_500);
        clauses.push(vec![pos(0)]);

        for i in 0..3_400 {
            clauses.push(vec![
                neg(rotating_var(num_vars, i, 1)),
                pos(rotating_var(num_vars, i, 2)),
            ]);
        }

        for i in 0..2_299 {
            clauses.push(vec![
                neg(rotating_var(num_vars, i, 3)),
                neg(rotating_var(num_vars, i, 4)),
                pos(rotating_var(num_vars, i, 5)),
            ]);
        }

        for i in 0..2_800 {
            clauses.push(vec![
                pos(rotating_var(num_vars, i, 6)),
                pos(rotating_var(num_vars, i, 7)),
                neg(rotating_var(num_vars, i, 8)),
            ]);
        }

        clauses
    }

    #[test]
    fn test_features_empty_formula() {
        let features = SatFeatures::extract(10, &[]);
        assert_eq!(features.num_vars, 10);
        assert_eq!(features.num_clauses, 0);
        assert_eq!(features.clause_size_mean, 0.0);
        assert_eq!(features.num_binary, 0);
    }

    #[test]
    fn test_features_single_unit_clause() {
        let clauses = vec![vec![pos(0)]];
        let features = SatFeatures::extract(1, &clauses);
        assert_eq!(features.num_unit, 1);
        assert_eq!(features.num_binary, 0);
        assert_eq!(features.clause_size_mean, 1.0);
        assert_eq!(features.clause_size_min, 1);
        assert_eq!(features.clause_size_max, 1);
        assert_eq!(features.clause_size_std, 0.0);
    }

    #[test]
    fn test_features_all_binary() {
        // 3 binary clauses over 3 variables.
        let clauses = vec![
            vec![pos(0), neg(1)],
            vec![pos(1), neg(2)],
            vec![neg(0), pos(2)],
        ];
        let features = SatFeatures::extract(3, &clauses);
        assert_eq!(features.num_binary, 3);
        assert_eq!(features.frac_binary, 1.0);
        assert_eq!(features.clause_size_mean, 2.0);
        assert_eq!(features.clause_size_std, 0.0);
    }

    #[test]
    fn test_streaming_accumulator_matches_extract() {
        let clauses = vec![
            vec![pos(0), neg(1), pos(2)],
            vec![neg(0), neg(2)],
            vec![pos(3)],
            vec![],
        ];
        let expected = SatFeatures::extract(4, &clauses);
        let mut accumulator = SatFeatureAccumulator::new(4);
        for clause in &clauses {
            accumulator.add_clause(clause);
        }

        assert_eq!(accumulator.num_clauses(), clauses.len());
        assert_eq!(accumulator.finish(), expected);
    }

    #[test]
    fn test_streaming_accumulator_dimacs_buffer_matches_extract() {
        let raw_clauses: &[&[i32]] = &[&[1, -2, 3], &[-1, -3], &[4], &[]];
        let clauses: Vec<Vec<Literal>> = raw_clauses
            .iter()
            .map(|raw| raw.iter().map(|&lit| Literal::from_dimacs(lit)).collect())
            .collect();
        let expected = SatFeatures::extract(4, &clauses);
        let mut accumulator = SatFeatureAccumulator::new(4);
        let mut clause_buf = vec![pos(0)];

        for (raw, expected_clause) in raw_clauses.iter().zip(&clauses) {
            accumulator.add_dimacs_clause_to_buffer(raw, &mut clause_buf);
            assert_eq!(&clause_buf, expected_clause);
        }

        assert_eq!(accumulator.num_clauses(), clauses.len());
        assert_eq!(accumulator.finish(), expected);
    }

    #[test]
    fn test_features_horn_detection() {
        // Horn clause: at most 1 positive literal.
        let clauses = vec![
            vec![pos(0), neg(1), neg(2)], // 1 positive -> horn
            vec![neg(0), neg(1)],         // 0 positive -> horn
            vec![pos(0), pos(1), neg(2)], // 2 positive -> not horn
        ];
        let features = SatFeatures::extract(3, &clauses);
        assert_eq!(features.num_horn, 2);
    }

    #[test]
    fn test_features_pure_literal_detection() {
        // Variable 0: only positive. Variable 1: only negative. Variable 2: both.
        let clauses = vec![
            vec![pos(0), neg(1)],
            vec![pos(0), pos(2)],
            vec![neg(1), neg(2)],
        ];
        let features = SatFeatures::extract(3, &clauses);
        assert_eq!(features.num_pure_literals, 2); // var 0 and var 1 are pure
    }

    #[test]
    fn test_features_polarity_balance() {
        // Variable 0: 2 positive, 0 negative -> balance = 1.0
        // Variable 1: 0 positive, 2 negative -> balance = 0.0
        let clauses = vec![vec![pos(0), neg(1)], vec![pos(0), neg(1)]];
        let features = SatFeatures::extract(2, &clauses);
        // Mean of 1.0 and 0.0 = 0.5
        assert!((features.pos_neg_balance_mean - 0.5).abs() < 1e-10);
        // Std of [1.0, 0.0] = 0.5
        assert!((features.pos_neg_balance_std - 0.5).abs() < 1e-10);
    }

    #[test]
    fn test_features_clause_var_ratio() {
        // 4 clauses, 2 vars -> ratio 2.0
        let clauses = vec![vec![pos(0)], vec![neg(0)], vec![pos(1)], vec![neg(1)]];
        let features = SatFeatures::extract(2, &clauses);
        assert!((features.clause_var_ratio - 2.0).abs() < 1e-10);
    }

    #[test]
    fn test_classify_small() {
        let features = SatFeatures::extract(100, &vec![vec![pos(0), neg(1)]; 200]);
        assert_eq!(InstanceClass::classify(&features), InstanceClass::Small);
    }

    #[test]
    fn test_classify_random3sat() {
        // Build a large random-3-SAT-like instance: all ternary, high ratio.
        let num_vars = 2000;
        let num_clauses = 8000; // ratio ~4.0
        let clauses: Vec<Vec<Literal>> = (0..num_clauses)
            .map(|i| {
                let v0 = (i * 3) as u32 % num_vars as u32;
                let v1 = (i * 3 + 1) as u32 % num_vars as u32;
                let v2 = (i * 3 + 2) as u32 % num_vars as u32;
                vec![pos(v0), neg(v1), pos(v2)]
            })
            .collect();
        let features = SatFeatures::extract(num_vars, &clauses);
        assert!(features.frac_ternary > 0.8);
        assert!(features.clause_var_ratio > 3.5);
        assert_eq!(
            InstanceClass::classify(&features),
            InstanceClass::Random3Sat
        );
    }

    #[test]
    fn test_classify_structured_binary_heavy() {
        // Mostly binary clauses -> structured.
        let num_vars = 2000;
        let clauses: Vec<Vec<Literal>> = (0..4000)
            .map(|i| {
                let v0 = (i * 2) as u32 % num_vars as u32;
                let v1 = (i * 2 + 1) as u32 % num_vars as u32;
                vec![pos(v0), neg(v1)]
            })
            .collect();
        let features = SatFeatures::extract(num_vars, &clauses);
        assert!(features.frac_binary > 0.5);
        assert_eq!(
            InstanceClass::classify(&features),
            InstanceClass::Structured
        );
    }

    #[test]
    fn test_classify_industrial_large() {
        // Very large formula with heterogeneous clause sizes (mixed 2-8 literals).
        // Industrial formulas have high variable-degree variance or clause-width variance.
        let num_vars = 100_000;
        let clauses: Vec<Vec<Literal>> = (0..300_000)
            .map(|i| {
                let base_v = (i * 5) as u32 % num_vars as u32;
                // Vary clause length: 2, 3, 4, 5, 6, 7, 8 based on index
                let len = 2 + (i % 7);
                (0..len)
                    .map(|j| {
                        let v = (base_v + j as u32) % num_vars as u32;
                        if j % 2 == 0 {
                            pos(v)
                        } else {
                            neg(v)
                        }
                    })
                    .collect()
            })
            .collect();
        let features = SatFeatures::extract(num_vars, &clauses);
        assert!(
            features.clause_size_std > 1.0,
            "need clause size heterogeneity"
        );
        assert_eq!(
            InstanceClass::classify(&features),
            InstanceClass::Industrial
        );
    }

    #[test]
    fn test_classify_random_ksat() {
        // Uniform 5-SAT: all clauses have exactly 5 literals, balanced polarity.
        let num_vars = 2000;
        let num_clauses = 6000; // ratio 3.0
        let clauses: Vec<Vec<Literal>> = (0..num_clauses)
            .map(|i| {
                (0..5)
                    .map(|j| {
                        let v = ((i * 5 + j) as u32) % num_vars as u32;
                        if (i + j) % 2 == 0 {
                            pos(v)
                        } else {
                            neg(v)
                        }
                    })
                    .collect()
            })
            .collect();
        let features = SatFeatures::extract(num_vars, &clauses);
        assert_eq!(features.clause_size_min, 5);
        assert_eq!(features.clause_size_max, 5);
        assert!(features.clause_size_std < 0.1);
        assert_eq!(
            InstanceClass::classify(&features),
            InstanceClass::RandomKSat
        );
    }

    #[test]
    fn test_classify_large_uniform_is_unknown() {
        // Large uniform ternary formula (no structural heterogeneity) -> Unknown.
        let num_vars = 100_000;
        let clauses: Vec<Vec<Literal>> = (0..300_000)
            .map(|i| {
                let v0 = (i * 3) as u32 % num_vars as u32;
                let v1 = (i * 3 + 1) as u32 % num_vars as u32;
                let v2 = (i * 3 + 2) as u32 % num_vars as u32;
                vec![pos(v0), neg(v1), pos(v2)]
            })
            .collect();
        let features = SatFeatures::extract(num_vars, &clauses);
        assert_eq!(InstanceClass::classify(&features), InstanceClass::Unknown);
    }

    #[test]
    fn test_detects_binary_ternary_multiplier_equivalence_shape_without_classifying() {
        let clauses = multiplier_equivalence_like_clauses(2_500);
        let features = SatFeatures::extract(2_500, &clauses);

        assert_eq!(features.num_clauses, 8_500);
        assert_eq!(features.num_unit, 1);
        assert_eq!(features.num_binary, 3_400);
        assert_eq!(features.num_ternary, 5_099);
        assert!(features.frac_binary > 0.30 && features.frac_binary < 0.50);
        assert!(features.frac_ternary > 0.50 && features.frac_ternary < 0.70);
        assert!(features.frac_horn > 0.55 && features.frac_horn < 0.75);
        assert!(features.looks_like_binary_ternary_multiplier_equivalence());
        assert_eq!(
            InstanceClass::classify(&features),
            InstanceClass::Unknown,
            "helper must not alter generic routing classification"
        );
    }

    #[test]
    fn test_multiplier_equivalence_shape_rejects_nearby_nonmatches() {
        let clauses = multiplier_equivalence_like_clauses(2_500);
        let features = SatFeatures::extract(2_500, &clauses);
        assert!(features.looks_like_binary_ternary_multiplier_equivalence());

        let mut no_unit = features.clone();
        no_unit.num_unit = 0;
        assert!(!no_unit.looks_like_binary_ternary_multiplier_equivalence());

        let mut wide_clause = features.clone();
        wide_clause.clause_size_max = 4;
        assert!(!wide_clause.looks_like_binary_ternary_multiplier_equivalence());

        let mut fmla_sized = features;
        fmla_sized.num_vars = 54_411;
        fmla_sized.num_clauses = 437_952;
        fmla_sized.clause_var_ratio = 8.049;
        fmla_sized.frac_horn = 0.982;
        assert!(!fmla_sized.looks_like_binary_ternary_multiplier_equivalence());

        let streaming_partial = SatFeatures::from_streaming_counters(3_000, 9_000, 5_400, 6_000);
        assert!(!streaming_partial.looks_like_binary_ternary_multiplier_equivalence());
    }

    #[test]
    fn test_features_var_degree_stats() {
        // Variable 0 appears in 3 clauses, variable 1 in 2, variable 2 in 1.
        let clauses = vec![
            vec![pos(0), neg(1)],
            vec![pos(0), pos(1)],
            vec![neg(0), pos(2)],
        ];
        let features = SatFeatures::extract(3, &clauses);
        // Degrees: var0=3, var1=2, var2=1. Mean = 2.0
        assert!((features.var_degree_mean - 2.0).abs() < 1e-10);
        assert_eq!(features.var_degree_max, 3);
    }

    #[test]
    fn test_features_clause_size_stats_mixed() {
        let clauses = vec![
            vec![pos(0)],                         // size 1
            vec![pos(0), neg(1)],                 // size 2
            vec![pos(0), neg(1), pos(2)],         // size 3
            vec![pos(0), neg(1), pos(2), neg(3)], // size 4
        ];
        let features = SatFeatures::extract(4, &clauses);
        assert_eq!(features.clause_size_min, 1);
        assert_eq!(features.clause_size_max, 4);
        assert!((features.clause_size_mean - 2.5).abs() < 1e-10);
        assert_eq!(features.num_unit, 1);
        assert_eq!(features.num_binary, 1);
        assert_eq!(features.num_ternary, 1);
    }
}
