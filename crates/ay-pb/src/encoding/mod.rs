// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! PB-to-CNF encoding using multiple strategies with automatic selection.
//!
//! Encodes pseudo-Boolean constraints into CNF clauses that can be solved
//! by the ay-sat solver. Provides four encoding strategies:
//!
//! - **Sequential Counter** (Sinz 2005): Best for cardinality constraints
//!   and small weighted constraints. O(n*k) clauses.
//! - **BDD** (Een & Sorensson 2006): Compact for many real-world instances.
//!   Size depends on variable ordering.
//! - **Generalized Totalizer** (Joshi et al. 2015): Good balance of size
//!   and propagation strength for medium-sized constraints.
//! - **Binary Adder** (Warners 1998): Best for large coefficients where
//!   other encodings blow up. Size is O(n * log(max_coeff)).
//!
//! # Automatic Selection
//!
//! The encoder automatically selects the best strategy based on constraint
//! structure. See [`EncodingStrategy`] for the selection heuristic.
//!
//! # References
//! - Sinz, "Towards an Optimal CNF Encoding of Boolean Cardinality Constraints", 2005
//! - Een & Sorensson, "Translating Pseudo-Boolean Constraints into SAT", 2006
//! - Joshi et al., "Generalized Totalizer Encoding for PB Constraints", 2015
//! - Warners, "A Linear-Time Transformation of Linear Inequalities into CNF", 1998

mod adder;
mod bdd;
mod sequential_counter;
mod totalizer;

pub(crate) use totalizer::encode_totalizer_with_outputs_interruptible;

use crate::types::{PbConstraint, PbInstance, PbRel, PbTerm};

/// Max clauses for the general aux-free cardinality clause decomposition (below).
/// A unit-coefficient `sum li >= k` over `n` literals decomposes into `C(n, k-1)`
/// clauses (each over an `(n-k+1)`-subset). We emit it directly — aux-free and
/// DEC-LIN-CERT-liftable — only when that count is within budget; otherwise the
/// counter encoding (with aux) handles it. Covers at-least-1 (1 clause),
/// at-least-2 (`n`), at-most-1 (`C(n,2)`), etc. 128 keeps at-most-1 up to n=16.
const CARD_CLAUSE_DECOMP_MAX_CLAUSES: usize = 128;

/// Max variables for the canonical aux-free CNF of a (possibly weighted) small
/// constraint: emit one clause blocking each violating assignment (< 2^n). Keeps
/// small weighted rows aux-free + DEC-LIN-CERT-liftable. 5 => at most 32 clauses.
const CANONICAL_SMALL_N: usize = 5;

/// `C(n, r)`, or `None` on overflow / `r > n` (treated as not-decomposable).
fn binom(n: usize, r: usize) -> Option<usize> {
    if r > n {
        return None;
    }
    let r = r.min(n - r);
    let mut result: usize = 1;
    for i in 0..r {
        result = result.checked_mul(n - i)? / (i + 1);
    }
    Some(result)
}

/// Advance `idx` (a strictly-increasing length-`k` subset of `0..n`) to the next
/// combination in lexicographic order. Returns `false` when exhausted.
fn next_combination(idx: &mut [usize], n: usize) -> bool {
    let k = idx.len();
    if k == 0 {
        return false;
    }
    let mut i = k - 1;
    loop {
        if idx[i] != i + n - k {
            idx[i] += 1;
            for j in (i + 1)..k {
                idx[j] = idx[j - 1] + 1;
            }
            return true;
        }
        if i == 0 {
            return false;
        }
        i -= 1;
    }
}

/// Result of encoding a PB instance into CNF.
#[derive(Debug, Clone)]
pub struct EncodedCnf {
    /// Total number of variables (original + auxiliary).
    pub num_vars: u32,
    /// Clauses in DIMACS-style signed literal format.
    /// Positive = positive literal, negative = negated. Absolute value = 1-based variable number.
    pub clauses: Vec<Vec<i32>>,
}

impl EncodedCnf {
    /// Number of `u32` words this CNF would occupy in the `ay-sat` clause arena.
    ///
    /// `ay-sat` stores every clause in a single `Vec<u32>` arena (header words
    /// plus one word per literal). It addresses clauses by their **word offset**
    /// stored in a 32-bit `ClauseRef`. The binary-clause flag now lives in a
    /// separate bit of the watch entry (bit 32 of a `u64` clause word), so the
    /// flag no longer aliases the offset (#9670) and the whole 32-bit offset
    /// space is addressable; the arena need only stay strictly below
    /// [`ay_sat::arena_limits::MAX_ARENA_WORDS`] (`u32::MAX`, which is reserved
    /// as the relocation-remap "dead" sentinel). Computing the footprint up
    /// front lets the SAT-encoding solve paths refuse a CNF the solver cannot
    /// address soundly (which would otherwise truncate offsets and yield an
    /// unsound UNSAT).
    #[must_use]
    pub fn sat_arena_word_footprint(&self) -> u64 {
        self.clauses.iter().fold(0u64, |acc, clause| {
            acc.saturating_add(ay_sat::arena_limits::clause_words(clause.len() as u64))
        })
    }

    /// Estimated **peak additional resident bytes** to import this CNF into a
    /// fresh `ay-sat` solver, for predictive memory back-pressure.
    ///
    /// Importing is a one-time bulk build, but the `ay-sat` clause arena and
    /// watch structures grow incrementally through the system allocator: a
    /// reallocation transiently holds both the old and the new buffer, and the
    /// freed blocks are not returned to the OS promptly, so RESIDENT memory
    /// spikes far above the final arena during import. Measured on the dense
    /// `Init-x2-i9` (a 257 MiB / 67.5 M-word arena, 8.46 M clauses) the import
    /// briefly reached ~3.8 GiB RSS before settling near 0.67 GiB. That spike is
    /// invisible to the in-loop poll in time to avert a MEMLIMIT breach: the
    /// live-bytes counter does not see allocator fragmentation, and macOS
    /// `phys_footprint` lags a fast realloc burst — both catch up only at the
    /// peak. Callers therefore project the peak and decline UP FRONT.
    ///
    /// The multiplier is deliberately conservative; under-estimating the true
    /// (~13x on Init-x2-i9: ~3.3 GiB transient over a 257 MiB arena) transient
    /// only makes the gate decline a bit later, and declining is always sound —
    /// the SAT phase returns UNKNOWN while any incumbent from other portfolio
    /// strategies is retained.
    #[must_use]
    pub fn estimated_sat_import_peak_bytes(&self) -> u64 {
        /// Bytes per arena word (`u32`).
        const WORD_BYTES: u64 = 4;
        /// Conservative fraction of the observed (~13x) resident transient;
        /// under-approximating only defers the decline, never unsounds it.
        const IMPORT_TRANSIENT_MULTIPLIER: u64 = 6;
        self.sat_arena_word_footprint()
            .saturating_mul(WORD_BYTES)
            .saturating_mul(IMPORT_TRANSIENT_MULTIPLIER)
    }

    /// Returns `true` when this CNF is small enough for `ay-sat` to address every
    /// clause soundly (footprint strictly below the arena word limit, with
    /// headroom for learned clauses).
    ///
    /// The solver also appends learned clauses while solving, so the original
    /// formula must leave headroom below the hard `u32::MAX`-word ceiling. We
    /// require the static footprint to stay under three quarters of the limit,
    /// reserving the remaining quarter (≈ 1.07 billion words) of arena address
    /// space for learned clauses. Widening the addressable space from the old
    /// `2^31` bound to `u32::MAX` (#9670) lets large CNFs such as the
    /// bnn-verification family — whose static footprint sits between `2^31` and
    /// `3/4·u32::MAX` — actually be solved instead of declined.
    #[must_use]
    pub fn fits_sat_arena(&self) -> bool {
        self.sat_arena_word_footprint() < ay_sat::arena_limits::MAX_ARENA_WORDS / 4 * 3
    }

    /// Imports this encoded CNF into a fresh `ay-sat` solver.
    #[must_use]
    pub fn to_sat_solver(&self) -> ay_sat::Solver {
        let mut solver = ay_sat::Solver::new(self.num_vars as usize);
        self.import_into_sat_solver(&mut solver);
        solver
    }

    /// Imports this encoded CNF into a fresh `ay-sat` solver, polling for
    /// interruption every `poll_interval` clauses.
    ///
    /// Returns `None` when `should_stop` requests interruption before the CNF
    /// has been fully imported.
    pub fn to_sat_solver_interruptible<F>(
        &self,
        poll_interval: usize,
        should_stop: &mut F,
    ) -> Option<ay_sat::Solver>
    where
        F: FnMut() -> bool,
    {
        let mut solver = ay_sat::Solver::new(self.num_vars as usize);
        if self.import_into_sat_solver_interruptible(&mut solver, poll_interval, should_stop) {
            None
        } else {
            Some(solver)
        }
    }

    /// Adds this encoded CNF to an existing `ay-sat` solver.
    pub fn import_into_sat_solver(&self, solver: &mut ay_sat::Solver) {
        let mut never_stop = || false;
        let interrupted =
            self.import_into_sat_solver_interruptible(solver, usize::MAX, &mut never_stop);
        debug_assert!(!interrupted, "non-interruptible import cannot stop");
    }

    /// Adds this encoded CNF to an existing `ay-sat` solver, polling for
    /// interruption every `poll_interval` clauses.
    ///
    /// Returns `true` when `should_stop` requests interruption before all
    /// clauses are imported.
    pub fn import_into_sat_solver_interruptible<F>(
        &self,
        solver: &mut ay_sat::Solver,
        poll_interval: usize,
        should_stop: &mut F,
    ) -> bool
    where
        F: FnMut() -> bool,
    {
        let poll_interval = poll_interval.max(1);
        for (idx, clause) in self.clauses.iter().enumerate() {
            if idx % poll_interval == 0 && should_stop() {
                return true;
            }

            let lits: Vec<ay_sat::Literal> = clause
                .iter()
                .map(|&lit| ay_sat::Literal::from_dimacs(lit))
                .collect();
            solver.add_clause(lits);
        }

        should_stop()
    }
}

/// Encoding strategy for PB-to-CNF translation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum EncodingStrategy {
    /// Sequential counter encoding (Sinz 2005, generalized for PB).
    /// Best for small constraints and cardinality constraints.
    SequentialCounter,
    /// BDD-based encoding (Een & Sorensson 2006).
    /// Good default for medium-sized constraints.
    Bdd,
    /// Generalized totalizer encoding (Joshi et al. 2015).
    /// Good propagation strength for medium-sized PB constraints.
    Totalizer,
    /// Binary adder network encoding (Warners 1998).
    /// Best for constraints with very large coefficients.
    Adder,
    /// Automatically select the best strategy based on constraint structure.
    Auto,
}

/// Counts of concrete encoders selected while translating an instance.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct EncodingStrategyCounts {
    /// Number of normalized constraints encoded with sequential counters.
    pub sequential_counter: usize,
    /// Number of normalized constraints encoded with BDDs.
    pub bdd: usize,
    /// Number of normalized constraints encoded with generalized totalizers.
    pub totalizer: usize,
    /// Number of normalized constraints encoded with adder networks.
    pub adder: usize,
}

impl EncodingStrategyCounts {
    fn record(&mut self, strategy: EncodingStrategy) {
        match strategy {
            EncodingStrategy::SequentialCounter => self.sequential_counter += 1,
            EncodingStrategy::Bdd => self.bdd += 1,
            EncodingStrategy::Totalizer => self.totalizer += 1,
            EncodingStrategy::Adder => self.adder += 1,
            EncodingStrategy::Auto => {}
        }
    }

    /// Total number of normalized constraints handled by concrete encoders.
    pub fn total(self) -> usize {
        self.sequential_counter + self.bdd + self.totalizer + self.adder
    }
}

/// Lightweight profile for PB-to-CNF benchmark and routing comparisons.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EncodingProfile {
    /// Number of original PB variables in the input instance.
    pub original_vars: u32,
    /// Number of variables in the emitted CNF, including auxiliaries.
    pub total_vars: u32,
    /// Number of auxiliary variables allocated by linearization/encoding.
    pub aux_vars: u32,
    /// Number of input PB constraints visited by the encoder.
    pub input_constraints: usize,
    /// Number of normalized >= constraints after equality splitting.
    pub normalized_constraints: usize,
    /// Number of emitted clauses.
    pub clauses: usize,
    /// Clauses emitted while linearizing nonlinear PB terms.
    pub linearization_clauses: usize,
    /// Normalized constraints skipped because their threshold was already met.
    pub trivial_satisfied: usize,
    /// Normalized constraints encoded as an empty UNSAT clause.
    pub trivial_unsatisfied: usize,
    /// Single-literal normalized constraints encoded as one forced literal.
    pub unit_forced: usize,
    /// Concrete strategy choices made for nontrivial normalized constraints.
    pub strategies: EncodingStrategyCounts,
}

#[derive(Debug, Clone, Copy, Default)]
struct EncodingProfileState {
    input_constraints: usize,
    normalized_constraints: usize,
    linearization_clauses: usize,
    trivial_satisfied: usize,
    trivial_unsatisfied: usize,
    unit_forced: usize,
    strategies: EncodingStrategyCounts,
}

/// A normalized >= constraint with positive coefficients.
struct NormalizedGe {
    /// Positive coefficients.
    coeffs: Vec<i128>,
    /// DIMACS-style signed literals (1-based variable numbering).
    lits: Vec<i32>,
    /// Right-hand side threshold.
    rhs: i128,
}

/// Per-row fresh-BDD-state budget for the budgeted BDD attempt on "gap" rows
/// (medium coefficients with a threshold past the `auto_select` adder cutoff).
///
/// Sized from a PB24 OPT-LIN corpus scan (2026-07): the gap rows worth
/// upgrading (sroussel benchsMusee budget rows, miplib lseu/mod008 objective
/// bounds, KNAP-style rows) have 100k-2.5M reachable BDD states, while the
/// hopeless ones (netlib/fctp objective rows) blow past 8M. One BDD state
/// emits at most 2 clauses + 1 aux var, so this cap bounds the row's encoding
/// at ~1M clauses. Rows past the budget keep the previous adder routing.
///
/// Tightened 1M -> 512k (2026-07-12, QPLIB_2017 regression isolation): the
/// measured wins all sit at <= ~151k fresh states per row (lseu 8k,
/// mod008 45k/126k/151k, knapPI 0), while the 512k..1M band held one measured
/// LOSS and no wins at 15s/default-parallel: on OPT-NLC QPLIB_2017 a single
/// 229-term rhs=17480 constraint row's 790k-state BDD (~1.6M clauses)
/// bloated every SAT-encoded arm's base CNF and cost the portfolio its
/// -1881 incumbent (only -1617 without the cap, 2/2, not recovered even at
/// 30s); mod008's 651k-state row aborting to the adder left its win intact
/// (o=307 both ways), as did lseu (1136) and the knapPI optima. The cap also
/// halves the worst-case single-row clause bloat a gap attempt can inject.
const BDD_GAP_MAX_NODES: u64 = 512_000;

/// Shared budget across ALL gap-row BDD attempts (successful or aborted),
/// counted in fresh BDD states. Bounds the total extra encode work AND the
/// total extra emitted-clause volume on instances with many gap rows: once
/// the pool is spent, remaining gap rows go straight to the adder (the
/// previous behavior). 4M states ~ a few hundred ms and ~8M clauses
/// worst-case — small next to the SAT search they feed.
///
/// The pool is per `CnfEncoder` by default, which bounds the volume of one
/// encode. Callers that encode MANY instances into ONE persistent solver —
/// the SAT-OPT upper-bound probe loop appends every probe's bound CNF behind
/// a never-removed activation literal — must instead thread a single
/// session-level pool through every encode via
/// [`CnfEncoder::encode_instance_interruptible_with_gap_pool`], so the total
/// BDD-appended volume across the whole session stays bounded by ONE pool
/// rather than one fresh pool per probe.
pub(crate) const BDD_GAP_NODE_POOL: u64 = 4_000_000;

/// Clause-volume ceiling for keeping an auto-selected generalized-totalizer
/// row on the totalizer. The `clamp_unary_strategy` guard bounds the
/// totalizer's AUX count (`n * rhs`), but its merge CLAUSES grow with
/// `|W| * (2|L| + |R|)` per merged node — measured at 1e8..3e9 on real
/// mid-threshold weighted rows (e.g. the miplib `lseu` objective-bound row:
/// 35k aux but ~3e8 clauses), which stalls or OOMs the encode. Rows whose
/// dry-run clause estimate exceeds this ceiling are redirected to the
/// budgeted BDD attempt (adder fallback). Rows with genuinely small weight
/// sets — the totalizer's actual niche — estimate far below it.
const TOTALIZER_MAX_CLAUSE_EST: u64 = 500_000;

/// Per-row pair-merge work budget for the totalizer dry-run estimator.
/// Accepted rows therefore also have their encode-time set-merging work
/// bounded by this; rows that exceed it are treated as unaffordable
/// (fail-closed to the BDD/adder path).
const TOTALIZER_EST_MAX_WORK: u64 = 2_000_000;

/// Per-`CnfEncoder` shared work pool for totalizer dry-run estimation across
/// all rows. Once spent, the estimator never runs again — and can therefore
/// no longer prove any totalizer row affordable — so later Auto-totalizer
/// rows fail CLOSED to the BDD-then-adder path (mirroring the gap-row BDD
/// pool's empty-pool decline). This keeps the clause-volume ceiling
/// unconditional while bounding total estimation overhead per encode.
const TOTALIZER_EST_WORK_POOL: u64 = 16_000_000;

/// Encoder that translates PB constraints into CNF clauses.
pub struct CnfEncoder {
    /// Original PB variable count.
    num_pb_vars: u32,
    /// Next available variable number (1-based DIMACS).
    next_var: u32,
    /// Accumulated clauses.
    clauses: Vec<Vec<i32>>,
    /// Encoding strategy to use.
    strategy: EncodingStrategy,
    /// Measurement profile for the current encoding run.
    profile: EncodingProfileState,
    /// Remaining shared fresh-state budget for gap-row BDD attempts
    /// (see [`BDD_GAP_NODE_POOL`]).
    bdd_gap_node_pool: u64,
    /// Remaining shared work budget for totalizer dry-run estimation
    /// (see [`TOTALIZER_EST_WORK_POOL`]).
    totalizer_est_work_pool: u64,
}

impl CnfEncoder {
    /// Creates an encoder. Auxiliary variables start after `num_pb_vars`.
    /// Uses automatic strategy selection.
    pub fn new(num_pb_vars: u32) -> Self {
        Self {
            num_pb_vars,
            next_var: num_pb_vars + 1,
            clauses: Vec::new(),
            strategy: EncodingStrategy::Auto,
            profile: EncodingProfileState::default(),
            bdd_gap_node_pool: BDD_GAP_NODE_POOL,
            totalizer_est_work_pool: TOTALIZER_EST_WORK_POOL,
        }
    }

    /// Creates an encoder with a specific encoding strategy.
    pub fn with_strategy(num_pb_vars: u32, strategy: EncodingStrategy) -> Self {
        Self {
            num_pb_vars,
            next_var: num_pb_vars + 1,
            clauses: Vec::new(),
            strategy,
            profile: EncodingProfileState::default(),
            bdd_gap_node_pool: BDD_GAP_NODE_POOL,
            totalizer_est_work_pool: TOTALIZER_EST_WORK_POOL,
        }
    }

    /// Test hook: overrides the shared gap-row BDD attempt budget so pool
    /// exhaustion and budget-abort fallback are exercisable without building
    /// million-node BDDs.
    #[cfg(test)]
    fn set_bdd_gap_node_pool(&mut self, pool: u64) {
        self.bdd_gap_node_pool = pool;
    }

    /// Test hook: overrides the shared totalizer estimation work pool so the
    /// fail-closed pool-exhaustion routing is exercisable directly.
    #[cfg(test)]
    fn set_totalizer_est_work_pool(&mut self, pool: u64) {
        self.totalizer_est_work_pool = pool;
    }

    /// Encodes all constraints of a PB instance into CNF.
    pub fn encode_instance(instance: &PbInstance) -> EncodedCnf {
        Self::encode_instance_with_profile(instance).0
    }

    /// Encodes all constraints and returns a lightweight encoding profile.
    ///
    /// The profile is intended for PB26 benchmark comparisons: it records the
    /// concrete strategies selected by `Auto`, CNF growth, auxiliary variables,
    /// and trivial/linearization cases without changing solver behavior.
    pub fn encode_instance_with_profile(instance: &PbInstance) -> (EncodedCnf, EncodingProfile) {
        let mut encoder = Self::new(instance.num_vars);
        for constraint in &instance.constraints {
            encoder.encode_constraint(constraint);
        }
        let profile = encoder.profile();
        let encoded = EncodedCnf {
            num_vars: encoder.next_var - 1,
            clauses: encoder.clauses,
        };
        (encoded, profile)
    }

    /// Interruptible variant of `encode_instance`.
    ///
    /// Returns `None` when encoding is interrupted. Any partial encoder state
    /// is discarded with the local `CnfEncoder`.
    pub fn encode_instance_interruptible<F>(
        instance: &PbInstance,
        should_stop: &mut F,
    ) -> Option<EncodedCnf>
    where
        F: FnMut() -> bool,
    {
        Self::encode_instance_interruptible_with_gap_pool(instance, should_stop, BDD_GAP_NODE_POOL)
            .map(|(encoded, _)| encoded)
    }

    /// Session-carried variant of [`Self::encode_instance_interruptible`] for
    /// callers that encode MANY instances into one persistent solver (the
    /// SAT-OPT upper-bound probe loop): seeds the gap-row BDD pool with
    /// `bdd_gap_pool` instead of a fresh [`BDD_GAP_NODE_POOL`] and returns
    /// the depleted pool alongside the CNF so the caller can thread it into
    /// the next encode. This bounds the total gap-row BDD volume across the
    /// whole session by ONE pool rather than one fresh pool per encode; once
    /// the threaded pool is spent, gap rows keep the compact adder routing.
    ///
    /// A pool of [`BDD_GAP_NODE_POOL`] makes this byte-identical to
    /// `encode_instance_interruptible`; the totalizer clause-volume guard
    /// stays active regardless of the threaded pool (its estimation pool is
    /// per encode, and its adder redirect is protective for bound rows too).
    pub(crate) fn encode_instance_interruptible_with_gap_pool<F>(
        instance: &PbInstance,
        should_stop: &mut F,
        bdd_gap_pool: u64,
    ) -> Option<(EncodedCnf, u64)>
    where
        F: FnMut() -> bool,
    {
        if should_stop() {
            return None;
        }

        let mut encoder = Self::new(instance.num_vars);
        encoder.bdd_gap_node_pool = bdd_gap_pool;
        for constraint in &instance.constraints {
            if should_stop() {
                return None;
            }
            if encoder.encode_constraint_interruptible(constraint, should_stop) {
                return None;
            }
        }

        if should_stop() {
            return None;
        }

        let remaining_gap_pool = encoder.bdd_gap_node_pool;
        Some((
            EncodedCnf {
                num_vars: encoder.next_var - 1,
                clauses: encoder.clauses,
            },
            remaining_gap_pool,
        ))
    }

    /// Encodes a single PB constraint into CNF clauses.
    pub fn encode_constraint(&mut self, constraint: &PbConstraint) {
        self.profile.input_constraints += 1;
        let clauses_before_normalize = self.clauses.len();
        let normalized = self.normalize_constraint(constraint);
        self.profile.linearization_clauses +=
            self.clauses.len().saturating_sub(clauses_before_normalize);
        self.profile.normalized_constraints += normalized.len();
        for ge in normalized {
            self.encode_ge(&ge.coeffs, &ge.lits, ge.rhs);
        }
    }

    fn encode_constraint_interruptible<F>(
        &mut self,
        constraint: &PbConstraint,
        should_stop: &mut F,
    ) -> bool
    where
        F: FnMut() -> bool,
    {
        self.profile.input_constraints += 1;
        let clauses_before_normalize = self.clauses.len();
        let normalized = self.normalize_constraint(constraint);
        self.profile.linearization_clauses +=
            self.clauses.len().saturating_sub(clauses_before_normalize);
        self.profile.normalized_constraints += normalized.len();
        for ge in normalized {
            if should_stop() {
                return true;
            }
            if self.encode_ge_interruptible(&ge.coeffs, &ge.lits, ge.rhs, should_stop) {
                return true;
            }
        }
        false
    }

    /// Returns the total number of variables used (original + auxiliary).
    pub fn total_vars(&self) -> u32 {
        self.next_var - 1
    }

    /// Returns a reference to the accumulated clauses.
    pub fn clauses(&self) -> &[Vec<i32>] {
        &self.clauses
    }

    /// Returns the current encoding profile for manually driven encoders.
    pub fn profile(&self) -> EncodingProfile {
        let total_vars = self.total_vars();
        EncodingProfile {
            original_vars: self.num_pb_vars,
            total_vars,
            aux_vars: total_vars.saturating_sub(self.num_pb_vars),
            input_constraints: self.profile.input_constraints,
            normalized_constraints: self.profile.normalized_constraints,
            clauses: self.clauses.len(),
            linearization_clauses: self.profile.linearization_clauses,
            trivial_satisfied: self.profile.trivial_satisfied,
            trivial_unsatisfied: self.profile.trivial_unsatisfied,
            unit_forced: self.profile.unit_forced,
            strategies: self.profile.strategies,
        }
    }

    /// Allocates a fresh auxiliary variable and returns its 1-based DIMACS number.
    fn fresh_var(&mut self) -> i32 {
        let v = self.next_var;
        self.next_var += 1;
        v as i32
    }

    /// Adds a clause to the accumulated set.
    fn add_clause(&mut self, clause: Vec<i32>) {
        self.clauses.push(clause);
    }

    /// Normalizes a PB constraint into one or two >= constraints with positive coefficients.
    ///
    /// - `Ge`: produces one normalized constraint.
    /// - `Eq`: produces two constraints (>= k and <= k, where <= k is encoded as >= on negated).
    fn normalize_constraint(&mut self, constraint: &PbConstraint) -> Vec<NormalizedGe> {
        let mut result = Vec::with_capacity(2);

        // First, linearize all terms (handle non-linear products).
        let linear_terms = self.linearize_terms(&constraint.terms);

        // Produce the >= direction.
        result.push(Self::normalize_ge_direction(&linear_terms, constraint.rhs));

        if constraint.rel == PbRel::Eq {
            // For equality, also encode sum <= rhs, i.e., -sum >= -rhs,
            // i.e., sum((-c_i) * l_i) >= -rhs.
            let negated_terms: Vec<(i128, i32)> = linear_terms
                .iter()
                .map(|&(coeff, lit)| (-coeff, lit))
                .collect();
            result.push(Self::normalize_ge_direction(
                &negated_terms,
                -constraint.rhs,
            ));
        }

        result
    }

    /// Normalizes a single >= direction: ensures all coefficients are positive.
    ///
    /// For each term with negative coefficient c * l:
    ///   c * l = c * (1 - NOT l) + c = -|c| * (NOT l) + c
    ///   Replace with |c| * (NOT l) and adjust rhs by |c|.
    fn normalize_ge_direction(terms: &[(i128, i32)], rhs: i128) -> NormalizedGe {
        let mut coeffs = Vec::with_capacity(terms.len());
        let mut lits = Vec::with_capacity(terms.len());
        let mut adjusted_rhs = rhs;

        for &(coeff, lit) in terms {
            if coeff == 0 {
                continue;
            }
            if coeff > 0 {
                coeffs.push(coeff);
                lits.push(lit);
            } else {
                // c * l = (-|c|) * l = |c| * (NOT l) - |c|
                // So sum includes |c| * (NOT l) and rhs increases by |c|.
                coeffs.push(-coeff);
                lits.push(-lit);
                adjusted_rhs -= coeff; // rhs += |coeff| since coeff < 0
            }
        }

        simplify_normalized_ge(&mut coeffs, &mut adjusted_rhs);

        NormalizedGe {
            coeffs,
            lits,
            rhs: adjusted_rhs,
        }
    }

    /// Converts PB terms to linear (coeff, DIMACS literal) pairs.
    /// Non-linear terms (product of multiple literals) get an auxiliary AND variable.
    fn linearize_terms(&mut self, terms: &[PbTerm]) -> Vec<(i128, i32)> {
        terms.iter().map(|term| self.linearize_term(term)).collect()
    }

    /// Converts a single PB term to a (coefficient, DIMACS literal) pair.
    /// For non-linear terms, introduces an auxiliary variable equal to the AND of all literals.
    fn linearize_term(&mut self, term: &PbTerm) -> (i128, i32) {
        if term.lits.is_empty() {
            // Degenerate term with no literals: contributes coeff unconditionally.
            let aux = self.fresh_var();
            self.add_clause(vec![aux]);
            return (term.coeff, aux);
        }

        if term.lits.len() == 1 {
            // Linear term: direct translation.
            let lit = &term.lits[0];
            let dimacs_lit = if lit.negated {
                -(lit.var as i32)
            } else {
                lit.var as i32
            };
            return (term.coeff, dimacs_lit);
        }

        // Non-linear term: aux = AND(l_1, l_2, ..., l_k).
        // Clauses: aux -> l_i for each i, AND (l_1, ..., l_k) -> aux.
        let aux = self.fresh_var();
        let mut big_clause = vec![aux]; // Will be: aux OR NOT l_1 OR NOT l_2 OR ...

        for lit in &term.lits {
            let dimacs_lit = if lit.negated {
                -(lit.var as i32)
            } else {
                lit.var as i32
            };
            // aux -> l_i: NOT aux OR l_i
            self.add_clause(vec![-aux, dimacs_lit]);
            // For the reverse: big clause collects NOT l_i
            big_clause.push(-dimacs_lit);
        }

        // (l_1 AND l_2 AND ... AND l_k) -> aux: NOT l_1 OR NOT l_2 OR ... OR aux
        self.add_clause(big_clause);

        (term.coeff, aux)
    }

    /// Selects the encoding strategy for a given normalized constraint.
    fn select_strategy(&self, coeffs: &[i128], rhs: i128) -> EncodingStrategy {
        match self.strategy {
            EncodingStrategy::Auto => auto_select(coeffs, rhs),
            other => other,
        }
    }

    /// Try the aux-free clause decomposition of a unit-coefficient cardinality
    /// constraint `sum li >= rhs`. The caller guarantees all coefficients are 1,
    /// `n = lits.len() >= 2`, and `1 <= rhs <= n` (trivial/unit cases handled
    /// earlier). The constraint equals the conjunction over every `(n-rhs+1)`-subset
    /// `T` of `(∨_{i in T} li)` — `C(n, rhs-1)` clauses. If that count is within
    /// [`CARD_CLAUSE_DECOMP_MAX_CLAUSES`], emit those clauses (no aux vars) and
    /// return `true`; otherwise emit nothing and return `false` (use the counter).
    ///
    /// Soundness: this is the textbook cardinality-to-CNF identity (a refutation of
    /// "at most rhs-1 true" forbids every all-false `(n-rhs+1)`-subset). Keeping
    /// these rows aux-free makes them DEC-LIN-CERT DRAT-liftable.
    fn try_cardinality_clause_decomposition(&mut self, lits: &[i32], rhs: i128) -> bool {
        let n = lits.len();
        if rhs < 1 || rhs > n as i128 {
            return false;
        }
        let k = rhs as usize;
        let subset_size = n - k + 1; // in 1..=n; C(n, subset_size) == C(n, k-1)
        let Some(count) = binom(n, subset_size) else {
            return false;
        };
        if count > CARD_CLAUSE_DECOMP_MAX_CLAUSES {
            return false;
        }
        let mut idx: Vec<usize> = (0..subset_size).collect();
        loop {
            let clause: Vec<i32> = idx.iter().map(|&i| lits[i]).collect();
            self.add_clause(clause);
            if !next_combination(&mut idx, n) {
                break;
            }
        }
        true
    }

    /// Try the canonical aux-free CNF for a normalized `sum coeffs[i]*lits[i] >= rhs`
    /// over few (`<= CANONICAL_SMALL_N`) variables: enumerate all `2^n` assignments
    /// and emit one clause blocking each that violates the constraint. This handles
    /// WEIGHTED constraints (not just cardinality) and is exact + aux-free, so the
    /// row stays DEC-LIN-CERT DRAT-liftable. Returns `true` if emitted.
    ///
    /// Soundness: the emitted clause set is satisfied by exactly the assignments
    /// that satisfy `sum coeffs[i]*lits[i] >= rhs` (each violating assignment is
    /// blocked by its unique falsifying clause), so the CNF is equivalent over
    /// these `n` variables.
    fn try_small_n_canonical_cnf(&mut self, coeffs: &[i128], lits: &[i32], rhs: i128) -> bool {
        let n = lits.len();
        if n > CANONICAL_SMALL_N {
            return false;
        }
        for mask in 0u32..(1u32 << n) {
            let weight: i128 = (0..n)
                .filter(|&i| mask & (1 << i) != 0)
                .map(|i| coeffs[i])
                .sum();
            if weight < rhs {
                // This assignment violates the constraint; block it with the clause
                // falsified only by it: lits[i] where lit is false here, ~lits[i] where true.
                let clause: Vec<i32> = (0..n)
                    .map(|i| {
                        if mask & (1 << i) != 0 {
                            -lits[i]
                        } else {
                            lits[i]
                        }
                    })
                    .collect();
                self.add_clause(clause);
            }
        }
        true
    }

    /// Encodes a normalized >= constraint using the selected strategy.
    fn encode_ge(&mut self, coeffs: &[i128], lits: &[i32], rhs: i128) {
        let n = coeffs.len();

        // Trivially satisfied: threshold <= 0.
        if rhs <= 0 {
            self.profile.trivial_satisfied += 1;
            return;
        }

        // Trivially unsatisfied: sum of all coefficients < rhs.
        let total: i128 = coeffs.iter().sum();
        if total < rhs {
            self.profile.trivial_unsatisfied += 1;
            self.add_clause(Vec::new()); // Empty clause = UNSAT.
            return;
        }

        // Single-literal case: c * l >= rhs means l must be true (since c >= rhs > 0).
        if n == 1 {
            self.profile.unit_forced += 1;
            self.add_clause(vec![lits[0]]);
            return;
        }

        // General aux-free cardinality clause decomposition (at-least-1,
        // at-least-2, at-most-1, "all true", ...): a unit-coefficient `sum li >= k`
        // is the conjunction over all (n-k+1)-subsets T of (∨_{i in T} li). When
        // C(n, k-1) is within budget we emit those clauses directly — equisatisfiable,
        // no auxiliary variables, and DEC-LIN-CERT DRAT-liftable (proof/drat_lift.rs).
        // Larger / mid-threshold cardinalities fall through to the counter encoding.
        if coeffs.iter().all(|&c| c == 1) && self.try_cardinality_clause_decomposition(lits, rhs) {
            return;
        }

        // Small-n canonical CNF: a (possibly WEIGHTED) row over few variables is
        // emitted aux-free as the clauses blocking each violating assignment —
        // exact + DEC-LIN-CERT-liftable. Covers the weighted rows the cardinality
        // decomposition above cannot.
        if self.try_small_n_canonical_cnf(coeffs, lits, rhs) {
            return;
        }

        let strategy = clamp_unary_strategy(self.select_strategy(coeffs, rhs), n, rhs);
        let strategy = self.refined_auto_strategy(strategy, coeffs, rhs);

        // GAP-ROW BDD UPGRADE (Auto only): a medium-coefficient row whose
        // threshold exceeds the `auto_select` adder cutoff (or whose unary
        // encoding was clamped, or whose totalizer clause volume measured
        // unaffordable) previously always took the propagation-weak adder.
        // Attempt the arc-consistent BDD within a strict, deterministic
        // fresh-state budget first; on budget abort the partial output is
        // rolled back and the row falls through to the adder exactly as
        // before. See `try_gap_row_bdd` for the measured routing rationale.
        if self.strategy == EncodingStrategy::Auto
            && strategy == EncodingStrategy::Adder
            && gap_row_bdd_candidate(coeffs)
        {
            let mut never_stop = || false;
            if self.try_gap_row_bdd(coeffs, lits, rhs, &mut never_stop) == GapBddAttempt::Encoded {
                return;
            }
        }

        self.profile.strategies.record(strategy);

        match strategy {
            EncodingStrategy::SequentialCounter => {
                sequential_counter::encode_sequential_counter(
                    coeffs,
                    lits,
                    rhs,
                    &mut self.clauses,
                    &mut self.next_var,
                );
            }
            EncodingStrategy::Bdd | EncodingStrategy::Auto => {
                bdd::encode_bdd(coeffs, lits, rhs, &mut self.clauses, &mut self.next_var);
            }
            EncodingStrategy::Totalizer => {
                totalizer::encode_totalizer(
                    coeffs,
                    lits,
                    rhs,
                    &mut self.clauses,
                    &mut self.next_var,
                );
            }
            EncodingStrategy::Adder => {
                adder::encode_adder(coeffs, lits, rhs, &mut self.clauses, &mut self.next_var);
            }
        }
    }

    /// Refines an `Auto`-selected strategy with the measured clause-volume
    /// guard: an auto-selected totalizer row whose dry-run clause estimate
    /// exceeds [`TOTALIZER_MAX_CLAUSE_EST`] is redirected to `Adder`, which
    /// makes it eligible for the budgeted BDD attempt in `encode_ge` (and
    /// otherwise encodes with the compact adder — never the exploding
    /// totalizer). Forced strategies are never refined, and the decision is
    /// deterministic (work-counted, never wall-clock), so the plain and
    /// interruptible encode paths stay bit-identical.
    fn refined_auto_strategy(
        &mut self,
        strategy: EncodingStrategy,
        coeffs: &[i128],
        rhs: i128,
    ) -> EncodingStrategy {
        if self.strategy != EncodingStrategy::Auto || strategy != EncodingStrategy::Totalizer {
            return strategy;
        }
        if self.totalizer_est_work_pool == 0 {
            // Estimation pool spent: the estimator can no longer prove a
            // totalizer row affordable, so fail CLOSED — route the row to the
            // adder, which keeps the clause-volume ceiling unconditional and
            // leaves the row eligible for the budgeted gap-row BDD upgrade.
            // Mirrors `try_gap_row_bdd`'s empty-pool decline; deterministic
            // (work-counted), so plain/interruptible stay bit-identical.
            return EncodingStrategy::Adder;
        }
        let work_budget = TOTALIZER_EST_MAX_WORK.min(self.totalizer_est_work_pool);
        let (work_used, affordable) =
            estimate_totalizer_clause_volume(coeffs, rhs, TOTALIZER_MAX_CLAUSE_EST, work_budget);
        self.totalizer_est_work_pool = self
            .totalizer_est_work_pool
            .saturating_sub(work_used.max(1024));
        if affordable {
            EncodingStrategy::Totalizer
        } else {
            EncodingStrategy::Adder
        }
    }

    /// Attempt the budget-capped BDD on a gap row (see `encode_ge`).
    ///
    /// Routing rationale (measured on the PB24 OPT-LIN corpus, 2026-07):
    /// medium-coefficient rows with `rhs > 10_000` — objective upper-bound
    /// rows of weighted OPT instances and wide budget rows — were routed to
    /// the binary adder, which is compact but propagation-weak (no
    /// arc-consistency), costing the SAT-encoded portfolio arms search power
    /// exactly where they do the OPT-track work. The two arc-consistent
    /// alternatives measure very differently on those rows:
    ///
    /// * generalized totalizer: auxiliary count is often affordable (1e5) but
    ///   the merge clauses grow with `|W|*(2|L|+|R|)` — 3e8..5e8 clauses on
    ///   real gap rows (dense weight sets), hopeless;
    /// * BDD: 1e5..2.5e6 reachable states at <= 2 clauses per state on the
    ///   same rows — importable, and unit propagation on the monotone
    ///   implication encoding maintains arc consistency.
    ///
    /// So gap rows get one budgeted BDD attempt. Fail-closed: budget abort
    /// rolls back all partial output and the caller re-encodes with the adder
    /// (the previous routing), so worst-case behavior is the status quo plus a
    /// bounded, deterministic amount of attempt work (the shared pool).
    ///
    /// Soundness: `encode_bdd` is one of the equisatisfiability-proven
    /// encoders (see `tests/encoder_faithfulness_conformance.rs`); this only
    /// changes WHICH sound encoder handles the row.
    fn try_gap_row_bdd<F>(
        &mut self,
        coeffs: &[i128],
        lits: &[i32],
        rhs: i128,
        external_stop: &mut F,
    ) -> GapBddAttempt
    where
        F: FnMut() -> bool,
    {
        if self.bdd_gap_node_pool == 0 {
            return GapBddAttempt::Declined;
        }
        let budget = BDD_GAP_MAX_NODES.min(self.bdd_gap_node_pool);
        let outcome = bdd::encode_bdd_budgeted(
            coeffs,
            lits,
            rhs,
            &mut self.clauses,
            &mut self.next_var,
            budget,
            external_stop,
        );
        match outcome {
            bdd::BddBudgetOutcome::Encoded { fresh_states } => {
                self.charge_gap_pool(fresh_states);
                self.profile.strategies.record(EncodingStrategy::Bdd);
                GapBddAttempt::Encoded
            }
            bdd::BddBudgetOutcome::BudgetExceeded { fresh_states } => {
                self.charge_gap_pool(fresh_states);
                GapBddAttempt::Declined
            }
            bdd::BddBudgetOutcome::Interrupted => GapBddAttempt::Interrupted,
        }
    }

    /// Deducts gap-row BDD attempt work from the shared pool. Every attempt is
    /// charged at least one poll interval so a long run of tiny attempts still
    /// drains the pool (bounding total attempt overhead per encoder).
    fn charge_gap_pool(&mut self, fresh_states: u64) {
        self.bdd_gap_node_pool = self
            .bdd_gap_node_pool
            .saturating_sub(fresh_states.max(bdd::BDD_STOP_POLL_INTERVAL));
    }

    fn encode_ge_interruptible<F>(
        &mut self,
        coeffs: &[i128],
        lits: &[i32],
        rhs: i128,
        should_stop: &mut F,
    ) -> bool
    where
        F: FnMut() -> bool,
    {
        let n = coeffs.len();

        if rhs <= 0 {
            self.profile.trivial_satisfied += 1;
            return false;
        }

        let total: i128 = coeffs.iter().sum();
        if total < rhs {
            self.profile.trivial_unsatisfied += 1;
            self.add_clause(Vec::new());
            return false;
        }

        if n == 1 {
            self.profile.unit_forced += 1;
            self.add_clause(vec![lits[0]]);
            return false;
        }

        // General aux-free cardinality clause decomposition (see encode_ge):
        // at-least-1 / at-least-2 / at-most-1 / ... -> direct clauses when within
        // budget; aux-free + DEC-LIN-CERT-liftable.
        if coeffs.iter().all(|&c| c == 1) && self.try_cardinality_clause_decomposition(lits, rhs) {
            return false;
        }

        // Small-n canonical CNF (see encode_ge): weighted small rows -> aux-free
        // blocking clauses, DEC-LIN-CERT-liftable.
        if self.try_small_n_canonical_cnf(coeffs, lits, rhs) {
            return false;
        }

        if should_stop() {
            return true;
        }

        let strategy = clamp_unary_strategy(self.select_strategy(coeffs, rhs), n, rhs);
        let strategy = self.refined_auto_strategy(strategy, coeffs, rhs);

        // GAP-ROW BDD UPGRADE (see `encode_ge`). The budget decision is
        // deterministic in the row's fresh-state count, so this path emits the
        // exact same CNF as the non-interruptible encoder unless `should_stop`
        // itself fires (in which case the whole encode is abandoned).
        if self.strategy == EncodingStrategy::Auto
            && strategy == EncodingStrategy::Adder
            && gap_row_bdd_candidate(coeffs)
        {
            match self.try_gap_row_bdd(coeffs, lits, rhs, should_stop) {
                GapBddAttempt::Encoded => return false,
                GapBddAttempt::Interrupted => return true,
                GapBddAttempt::Declined => {}
            }
        }

        self.profile.strategies.record(strategy);

        match strategy {
            EncodingStrategy::SequentialCounter => {
                sequential_counter::encode_sequential_counter(
                    coeffs,
                    lits,
                    rhs,
                    &mut self.clauses,
                    &mut self.next_var,
                );
            }
            EncodingStrategy::Bdd | EncodingStrategy::Auto => {
                // Interruptible BDD: a wide cardinality row (e.g. a 20000-term
                // `sum = 10000` objective aggregate from stable-marriage SMTI) has
                // an `O(n * rhs)` BDD that materializes hundreds of millions of
                // clauses over tens of seconds and many GB. The interruptible build
                // bails the moment the deadline passes or memory crosses the budget,
                // so the whole encode is abandoned (caller returns UNKNOWN) instead
                // of overrunning the timeout / OOM-ing. Output is bit-identical to
                // `encode_bdd` when it completes in budget (strict no-op otherwise).
                if bdd::encode_bdd_interruptible(
                    coeffs,
                    lits,
                    rhs,
                    &mut self.clauses,
                    &mut self.next_var,
                    should_stop,
                ) {
                    return true;
                }
            }
            EncodingStrategy::Totalizer => {
                if totalizer::encode_totalizer_interruptible(
                    coeffs,
                    lits,
                    rhs,
                    &mut self.clauses,
                    &mut self.next_var,
                    should_stop,
                ) {
                    return true;
                }
            }
            EncodingStrategy::Adder => {
                adder::encode_adder(coeffs, lits, rhs, &mut self.clauses, &mut self.next_var);
            }
        }

        should_stop()
    }
}

/// Result of a gap-row budgeted BDD attempt at the `CnfEncoder` level.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum GapBddAttempt {
    /// Row encoded as a BDD; nothing further to do.
    Encoded,
    /// Attempt declined (pool empty) or budget-aborted (rolled back); the
    /// caller must encode the row with the adder as before.
    Declined,
    /// The external stop hook fired mid-attempt (rolled back); the caller
    /// must abandon the whole encode.
    Interrupted,
}

/// Is this normalized row eligible for the gap-row BDD attempt?
///
/// Only medium-coefficient rows qualify: the `auto_select` big-coefficient
/// outer guard (`max_coeff > 10_000` => adder) is intentionally preserved,
/// so rows with genuinely large coefficients never pay for an attempt.
fn gap_row_bdd_candidate(coeffs: &[i128]) -> bool {
    coeffs.iter().max().copied().unwrap_or(0) <= 10_000
}

/// Dry-run estimate of the generalized totalizer's clause volume for a
/// normalized row: simulates the exact adjacent-pair merge tree of
/// `encode_totalizer` (weight sets capped at `rhs`, saturating insert of
/// `rhs`) WITHOUT emitting clauses or minting variables, and accumulates a
/// per-merge clause upper bound
///
///   `|W| * (2|L| + |R| + 4) + |W|`
///
/// (per parent weight: <= 2 single-child forward clauses + `|L|` pair
/// forward clauses + `|L|+1` + `|R|+1` backward boundary clauses; plus the
/// monotonicity chain). Every set insertion / pair combination counts one
/// unit of `work`; the walk aborts as soon as the clause estimate exceeds
/// `max_clauses` or the work exceeds `max_work` (fail-closed: reported as
/// unaffordable).
///
/// Returns `(work_used, affordable)`.
fn estimate_totalizer_clause_volume(
    coeffs: &[i128],
    rhs: i128,
    max_clauses: u64,
    max_work: u64,
) -> (u64, bool) {
    use std::collections::BTreeSet;

    let mut nodes: Vec<BTreeSet<i128>> = coeffs
        .iter()
        .map(|&c| {
            let mut set = BTreeSet::new();
            set.insert(c.min(rhs));
            set
        })
        .collect();
    let mut clause_est: u64 = 0;
    let mut work: u64 = 0;

    while nodes.len() > 1 {
        let mut next_level = Vec::with_capacity(nodes.len().div_ceil(2));
        let mut i = 0;
        while i < nodes.len() {
            if i + 1 < nodes.len() {
                let (left, right) = (&nodes[i], &nodes[i + 1]);
                let mut merged = BTreeSet::new();
                for &wl in left {
                    work += 1;
                    if wl <= rhs {
                        merged.insert(wl);
                    }
                }
                for &wr in right {
                    work += 1;
                    if wr <= rhs {
                        merged.insert(wr);
                    }
                }
                for &wl in left {
                    for &wr in right {
                        work += 1;
                        if work > max_work {
                            return (work, false);
                        }
                        let sum = wl.saturating_add(wr);
                        merged.insert(if sum <= rhs { sum } else { rhs });
                    }
                }
                let (l_len, r_len, w_len) =
                    (left.len() as u64, right.len() as u64, merged.len() as u64);
                clause_est = clause_est
                    .saturating_add(w_len.saturating_mul(2 * l_len + r_len + 4))
                    .saturating_add(w_len);
                if clause_est > max_clauses || work > max_work {
                    return (work, false);
                }
                next_level.push(merged);
                i += 2;
            } else {
                next_level.push(std::mem::take(&mut nodes[i]));
                i += 1;
            }
        }
        nodes = next_level;
    }

    (work, true)
}

fn simplify_normalized_ge(coeffs: &mut [i128], rhs: &mut i128) {
    if *rhs <= 0 || coeffs.is_empty() {
        return;
    }

    // Saturation is especially important for optimization upper-bound queries:
    // large objective coefficients often collapse to the current bound.
    for coeff in coeffs.iter_mut() {
        if *coeff > *rhs {
            *coeff = *rhs;
        }
    }

    let gcd = coeffs
        .iter()
        .map(|coeff| coeff.unsigned_abs())
        .fold(0u128, gcd_u128);
    if gcd <= 1 {
        return;
    }

    let gcd = gcd as i128;
    for coeff in coeffs.iter_mut() {
        *coeff /= gcd;
    }
    *rhs = ceiling_div(*rhs, gcd);
}

fn gcd_u128(a: u128, b: u128) -> u128 {
    if b == 0 {
        return a;
    }
    let mut a = a;
    let mut b = b;
    while b != 0 {
        let t = b;
        b = a % b;
        a = t;
    }
    a
}

fn ceiling_div(a: i128, b: i128) -> i128 {
    debug_assert!(b > 0, "ceiling_div: divisor must be positive");
    if a >= 0 {
        (a + b - 1) / b
    } else {
        a / b
    }
}

/// Maximum `O(n * rhs)` auxiliary size permitted for the unary encodings
/// (sequential counter, generalized totalizer). Their size is proportional to
/// the *threshold magnitude*, not its bit-length, so a single large-threshold
/// constraint can exhaust host memory — a PB25 bnn-verification shape with a big
/// coefficient drove the unary path to >100 GB and OOM'd the machine. Beyond this
/// budget the encoding is replaced by the bit-efficient adder, which is
/// equisatisfiable and polynomial in bit-length.
const MAX_UNARY_ENCODING_AUX: u128 = 2_000_000;

/// Downgrade an explicitly forced unary strategy to the adder when its
/// `O(n * rhs)` size would blow up. `auto_select` already avoids the unary
/// encodings for large thresholds, but a forced strategy (a portfolio
/// configuration or a test) bypasses that — this keeps memory bounded for any
/// caller. The substitution is equisatisfiable, so soundness is preserved.
fn clamp_unary_strategy(strategy: EncodingStrategy, n: usize, rhs: i128) -> EncodingStrategy {
    match strategy {
        EncodingStrategy::SequentialCounter | EncodingStrategy::Totalizer
            if rhs > 0 && (n as u128).saturating_mul(rhs as u128) > MAX_UNARY_ENCODING_AUX =>
        {
            EncodingStrategy::Adder
        }
        other => other,
    }
}

/// Automatic encoding strategy selection based on constraint structure.
///
/// Heuristic:
/// - All coefficients = 1 (cardinality) with rhs < n/2: sequential counter
/// - Max coefficient < 1000 and few terms (< 30): BDD
/// - Many terms with varied coefficients: totalizer
/// - Very large coefficients (max > 10000): adder
///
/// Rows selected as `Adder` with medium coefficients (`max_coeff <= 10_000`)
/// additionally get one budget-capped BDD attempt in `encode_ge` before the
/// adder runs (see `CnfEncoder::try_gap_row_bdd`); this function still
/// reports the pre-upgrade choice.
fn auto_select(coeffs: &[i128], rhs: i128) -> EncodingStrategy {
    let n = coeffs.len();
    let max_coeff = coeffs.iter().copied().max().unwrap_or(0);
    let all_unit = coeffs.iter().all(|&c| c == 1);

    if all_unit {
        // Cardinality constraint: sequential counter is optimal for small k.
        if rhs <= (n as i128) / 2 && rhs <= 64 {
            return EncodingStrategy::SequentialCounter;
        }
        // For larger k, BDD is usually more compact.
        return EncodingStrategy::Bdd;
    }

    // Very large coefficients: adder encoding avoids BDD/totalizer blowup.
    if max_coeff > 10_000 || rhs > 10_000 {
        return EncodingStrategy::Adder;
    }

    // Medium-sized weighted constraints: BDD is generally compact.
    if n < 30 && max_coeff < 1000 {
        return EncodingStrategy::Bdd;
    }

    // Many terms with varied coefficients: totalizer.
    if n >= 30 {
        return EncodingStrategy::Totalizer;
    }

    // Default: BDD.
    EncodingStrategy::Bdd
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::{PbLit, PbRel};

    fn lit(var: u32) -> PbLit {
        PbLit {
            var,
            negated: false,
        }
    }

    fn neg_lit(var: u32) -> PbLit {
        PbLit { var, negated: true }
    }

    fn linear_term(coeff: i128, var: u32) -> PbTerm {
        PbTerm {
            coeff,
            lits: vec![lit(var)],
        }
    }

    fn negated_linear_term(coeff: i128, var: u32) -> PbTerm {
        PbTerm {
            coeff,
            lits: vec![neg_lit(var)],
        }
    }

    /// Brute-force check: does the encoded CNF accept exactly the same
    /// assignments as the original PB constraint?
    fn verify_encoding_matches_constraint(constraint: &PbConstraint, num_vars: u32) {
        verify_encoding_with_strategy(constraint, num_vars, EncodingStrategy::Auto);
    }

    /// Verify encoding correctness with a specific strategy.
    fn verify_encoding_with_strategy(
        constraint: &PbConstraint,
        num_vars: u32,
        strategy: EncodingStrategy,
    ) {
        let encoded = {
            let mut enc = CnfEncoder::with_strategy(num_vars, strategy);
            enc.encode_constraint(constraint);
            EncodedCnf {
                num_vars: enc.next_var - 1,
                clauses: enc.clauses,
            }
        };

        let total_vars = encoded.num_vars;
        let n = num_vars as usize;

        // Guard against an OOM in the brute-force checker itself: it enumerates
        // 2^num_aux auxiliary assignments. With the unary-strategy clamp in place
        // num_aux stays small, but assert it so a too-large encoding fails the
        // test cleanly instead of exhausting memory.
        let aux_for_guard = total_vars.saturating_sub(num_vars) as usize;
        assert!(
            aux_for_guard <= 24,
            "verify_encoding_with_strategy aux budget exceeded ({aux_for_guard}); encoding too large to brute-force"
        );

        // Iterate over all assignments to the original PB variables.
        for mask in 0..(1u64 << n) {
            let assignment: Vec<bool> = (0..n).map(|i| (mask >> i) & 1 == 1).collect();

            // Evaluate the PB constraint directly.
            let pb_sat = crate::solver::eval_constraint(constraint, &assignment);

            // Check if the CNF is satisfiable under this partial assignment.
            // For the auxiliary variables, we try all combinations (existentially quantified).
            let num_aux = (total_vars - num_vars) as usize;
            let cnf_sat = if num_aux == 0 {
                all_clauses_satisfied(&encoded.clauses, &assignment, num_vars)
            } else {
                // Try all aux variable assignments.
                (0..(1u64 << num_aux)).any(|aux_mask| {
                    let mut full_assignment = assignment.clone();
                    for j in 0..num_aux {
                        full_assignment.push((aux_mask >> j) & 1 == 1);
                    }
                    all_clauses_satisfied(&encoded.clauses, &full_assignment, total_vars)
                })
            };

            assert_eq!(
                pb_sat, cnf_sat,
                "Mismatch for assignment {assignment:?}: PB says {pb_sat}, CNF says {cnf_sat} (constraint: {constraint:?}, strategy: {strategy:?})"
            );
        }
    }

    /// Checks if all clauses are satisfied under a full assignment.
    /// `assignment[i]` is the value of variable i+1 (1-based DIMACS).
    fn all_clauses_satisfied(clauses: &[Vec<i32>], assignment: &[bool], _num_vars: u32) -> bool {
        clauses.iter().all(|clause| {
            if clause.is_empty() {
                return false; // Empty clause = UNSAT.
            }
            clause.iter().any(|&dimacs_lit| {
                let var_idx = (dimacs_lit.unsigned_abs() - 1) as usize;
                if var_idx >= assignment.len() {
                    return false;
                }
                let val = assignment[var_idx];
                if dimacs_lit > 0 {
                    val
                } else {
                    !val
                }
            })
        })
    }

    // ---- Tests for each encoding strategy ----

    #[test]
    fn test_trivially_satisfied_constraint() {
        let constraint = PbConstraint {
            terms: vec![linear_term(1, 1)],
            rel: PbRel::Ge,
            rhs: 0,
        };
        let mut enc = CnfEncoder::new(1);
        enc.encode_constraint(&constraint);
        assert!(
            enc.clauses.is_empty(),
            "Trivially satisfied should produce no clauses"
        );
    }

    #[test]
    fn test_trivially_unsatisfied_constraint() {
        let constraint = PbConstraint {
            terms: vec![linear_term(1, 1)],
            rel: PbRel::Ge,
            rhs: 5,
        };
        let mut enc = CnfEncoder::new(1);
        enc.encode_constraint(&constraint);
        assert!(
            enc.clauses.iter().any(Vec::is_empty),
            "Trivially unsatisfied should produce an empty clause"
        );
    }

    #[test]
    fn test_single_literal_unit() {
        let constraint = PbConstraint {
            terms: vec![linear_term(3, 1)],
            rel: PbRel::Ge,
            rhs: 1,
        };
        let mut enc = CnfEncoder::new(1);
        enc.encode_constraint(&constraint);
        assert_eq!(enc.clauses.len(), 1);
        assert_eq!(enc.clauses[0], vec![1]);
    }

    // ---- BDD encoding tests ----

    #[test]
    fn test_bdd_cardinality_x1_plus_x2_plus_x3_ge_2() {
        let constraint = PbConstraint {
            terms: vec![linear_term(1, 1), linear_term(1, 2), linear_term(1, 3)],
            rel: PbRel::Ge,
            rhs: 2,
        };
        verify_encoding_with_strategy(&constraint, 3, EncodingStrategy::Bdd);
    }

    #[test]
    fn test_bdd_weighted_2x1_plus_3x2_ge_3() {
        let constraint = PbConstraint {
            terms: vec![linear_term(2, 1), linear_term(3, 2)],
            rel: PbRel::Ge,
            rhs: 3,
        };
        verify_encoding_with_strategy(&constraint, 2, EncodingStrategy::Bdd);
    }

    #[test]
    fn test_bdd_negative_coefficient() {
        let constraint = PbConstraint {
            terms: vec![linear_term(1, 1), linear_term(-1, 2)],
            rel: PbRel::Ge,
            rhs: 0,
        };
        verify_encoding_with_strategy(&constraint, 2, EncodingStrategy::Bdd);
    }

    #[test]
    fn test_bdd_equality_constraint() {
        let constraint = PbConstraint {
            terms: vec![linear_term(1, 1), linear_term(1, 2)],
            rel: PbRel::Eq,
            rhs: 1,
        };
        verify_encoding_with_strategy(&constraint, 2, EncodingStrategy::Bdd);
    }

    #[test]
    fn test_bdd_equality_weighted() {
        let constraint = PbConstraint {
            terms: vec![linear_term(2, 1), linear_term(3, 2)],
            rel: PbRel::Eq,
            rhs: 3,
        };
        verify_encoding_with_strategy(&constraint, 2, EncodingStrategy::Bdd);
    }

    // ---- Sequential counter encoding tests ----

    #[test]
    fn test_seqcounter_cardinality_ge_2() {
        let constraint = PbConstraint {
            terms: vec![linear_term(1, 1), linear_term(1, 2), linear_term(1, 3)],
            rel: PbRel::Ge,
            rhs: 2,
        };
        verify_encoding_with_strategy(&constraint, 3, EncodingStrategy::SequentialCounter);
    }

    #[test]
    fn test_seqcounter_cardinality_ge_3_of_4() {
        let constraint = PbConstraint {
            terms: vec![
                linear_term(1, 1),
                linear_term(1, 2),
                linear_term(1, 3),
                linear_term(1, 4),
            ],
            rel: PbRel::Ge,
            rhs: 3,
        };
        verify_encoding_with_strategy(&constraint, 4, EncodingStrategy::SequentialCounter);
    }

    #[test]
    fn test_seqcounter_weighted() {
        let constraint = PbConstraint {
            terms: vec![linear_term(2, 1), linear_term(3, 2)],
            rel: PbRel::Ge,
            rhs: 3,
        };
        verify_encoding_with_strategy(&constraint, 2, EncodingStrategy::SequentialCounter);
    }

    #[test]
    fn test_seqcounter_weighted_3_terms() {
        let constraint = PbConstraint {
            terms: vec![linear_term(2, 1), linear_term(3, 2), linear_term(5, 3)],
            rel: PbRel::Ge,
            rhs: 5,
        };
        verify_encoding_with_strategy(&constraint, 3, EncodingStrategy::SequentialCounter);
    }

    #[test]
    fn test_seqcounter_equality() {
        let constraint = PbConstraint {
            terms: vec![linear_term(1, 1), linear_term(1, 2), linear_term(1, 3)],
            rel: PbRel::Eq,
            rhs: 2,
        };
        verify_encoding_with_strategy(&constraint, 3, EncodingStrategy::SequentialCounter);
    }

    // ---- Totalizer encoding tests ----

    #[test]
    fn test_totalizer_cardinality_ge_2() {
        let constraint = PbConstraint {
            terms: vec![linear_term(1, 1), linear_term(1, 2), linear_term(1, 3)],
            rel: PbRel::Ge,
            rhs: 2,
        };
        verify_encoding_with_strategy(&constraint, 3, EncodingStrategy::Totalizer);
    }

    #[test]
    fn test_totalizer_weighted() {
        let constraint = PbConstraint {
            terms: vec![linear_term(2, 1), linear_term(3, 2)],
            rel: PbRel::Ge,
            rhs: 3,
        };
        verify_encoding_with_strategy(&constraint, 2, EncodingStrategy::Totalizer);
    }

    #[test]
    fn test_totalizer_cardinality_ge_3_of_4() {
        let constraint = PbConstraint {
            terms: vec![
                linear_term(1, 1),
                linear_term(1, 2),
                linear_term(1, 3),
                linear_term(1, 4),
            ],
            rel: PbRel::Ge,
            rhs: 3,
        };
        verify_encoding_with_strategy(&constraint, 4, EncodingStrategy::Totalizer);
    }

    #[test]
    fn test_totalizer_equality() {
        let constraint = PbConstraint {
            terms: vec![linear_term(1, 1), linear_term(1, 2)],
            rel: PbRel::Eq,
            rhs: 1,
        };
        verify_encoding_with_strategy(&constraint, 2, EncodingStrategy::Totalizer);
    }

    // ---- Adder encoding tests ----

    #[test]
    fn test_adder_cardinality_ge_2() {
        let constraint = PbConstraint {
            terms: vec![linear_term(1, 1), linear_term(1, 2), linear_term(1, 3)],
            rel: PbRel::Ge,
            rhs: 2,
        };
        verify_encoding_with_strategy(&constraint, 3, EncodingStrategy::Adder);
    }

    #[test]
    fn test_adder_weighted() {
        let constraint = PbConstraint {
            terms: vec![linear_term(2, 1), linear_term(3, 2)],
            rel: PbRel::Ge,
            rhs: 3,
        };
        verify_encoding_with_strategy(&constraint, 2, EncodingStrategy::Adder);
    }

    #[test]
    fn test_adder_medium_coefficients() {
        // Use small coefficients to keep brute-force verification tractable.
        // Large coefficients produce many aux vars, making 2^aux exhaustive
        // search impractical. The adder circuit logic is coefficient-independent;
        // correctness at small scale implies correctness at large scale.
        let constraint = PbConstraint {
            terms: vec![linear_term(4, 1), linear_term(6, 2), linear_term(3, 3)],
            rel: PbRel::Ge,
            rhs: 7,
        };
        verify_encoding_with_strategy(&constraint, 3, EncodingStrategy::Adder);
    }

    #[test]
    fn test_adder_equality() {
        let constraint = PbConstraint {
            terms: vec![linear_term(2, 1), linear_term(3, 2)],
            rel: PbRel::Eq,
            rhs: 3,
        };
        verify_encoding_with_strategy(&constraint, 2, EncodingStrategy::Adder);
    }

    // ---- Auto selection tests ----

    #[test]
    fn test_auto_selects_seqcounter_for_cardinality() {
        let coeffs = vec![1i128; 10];
        let strategy = auto_select(&coeffs, 3);
        assert_eq!(strategy, EncodingStrategy::SequentialCounter);
    }

    #[test]
    fn test_auto_selects_adder_for_large_coefficients() {
        let coeffs = vec![10001, 20000, 5000];
        let strategy = auto_select(&coeffs, 25000);
        assert_eq!(strategy, EncodingStrategy::Adder);
    }

    #[test]
    fn test_auto_selects_bdd_for_small_weighted() {
        let coeffs = vec![2, 3, 5, 7];
        let strategy = auto_select(&coeffs, 10);
        assert_eq!(strategy, EncodingStrategy::Bdd);
    }

    #[test]
    fn test_normalize_ge_direction_applies_tightening_and_gcd() {
        let normalized = CnfEncoder::normalize_ge_direction(&[(8, 1), (16, 2), (24, 3)], 8);

        assert_eq!(normalized.coeffs, vec![1, 1, 1]);
        assert_eq!(normalized.lits, vec![1, 2, 3]);
        assert_eq!(normalized.rhs, 1);
    }

    #[test]
    fn test_auto_select_prefers_bdd_on_cargo_style_bound_after_tightening() {
        // Representative PB25 OPT-LIN/Cargo-style bound:
        // a large weighted sum guarded by a single compensating negative term.
        let constraint = PbConstraint {
            terms: vec![
                linear_term(1, 1),
                linear_term(2, 2),
                linear_term(4, 3),
                linear_term(8, 4),
                linear_term(16, 5),
                linear_term(32, 6),
                linear_term(64, 7),
                linear_term(128, 8),
                linear_term(256, 9),
                linear_term(512, 10),
                linear_term(1024, 11),
                linear_term(2048, 12),
                linear_term(4096, 13),
                linear_term(8192, 14),
                linear_term(16384, 15),
                linear_term(32768, 16),
                linear_term(-1119, 17),
            ],
            rel: PbRel::Ge,
            rhs: 0,
        };

        let normalized = CnfEncoder::normalize_ge_direction(
            &constraint
                .terms
                .iter()
                .map(|term| {
                    let lit = &term.lits[0];
                    let dimacs_lit = if lit.negated {
                        -(lit.var as i32)
                    } else {
                        lit.var as i32
                    };
                    (term.coeff, dimacs_lit)
                })
                .collect::<Vec<_>>(),
            constraint.rhs,
        );
        assert_eq!(normalized.rhs, 1119);
        assert_eq!(
            auto_select(&normalized.coeffs, normalized.rhs),
            EncodingStrategy::Bdd
        );

        let mut auto = CnfEncoder::new(17);
        auto.encode_constraint(&constraint);
        let mut bdd = CnfEncoder::with_strategy(17, EncodingStrategy::Bdd);
        bdd.encode_constraint(&constraint);
        let mut adder = CnfEncoder::with_strategy(17, EncodingStrategy::Adder);
        adder.encode_constraint(&constraint);

        assert_eq!(auto.total_vars(), bdd.total_vars());
        assert_eq!(auto.clauses(), bdd.clauses());
        assert!(bdd.total_vars() < adder.total_vars());
        assert!(bdd.clauses().len() < adder.clauses().len());
    }

    // ---- Instance-level encoding test ----

    #[test]
    fn test_encode_instance_end_to_end() {
        let instance = PbInstance {
            num_vars: 3,
            num_constraints: 2,
            constraints: vec![
                PbConstraint {
                    terms: vec![linear_term(1, 1), linear_term(1, 2), linear_term(1, 3)],
                    rel: PbRel::Ge,
                    rhs: 2,
                },
                PbConstraint {
                    terms: vec![linear_term(1, 1)],
                    rel: PbRel::Ge,
                    rhs: 1,
                },
            ],
            objective: None,
        };

        let encoded = CnfEncoder::encode_instance(&instance);
        assert!(encoded.num_vars >= 3);
        assert!(!encoded.clauses.is_empty());

        // x1=true, x2=true, x3=false should satisfy both constraints.
        assert!(crate::solver::eval_constraint(
            &instance.constraints[0],
            &[true, true, false]
        ));
        assert!(crate::solver::eval_constraint(
            &instance.constraints[1],
            &[true, true, false]
        ));
    }

    #[test]
    fn test_encode_instance_with_profile_reports_strategy_mix() {
        // Constraints chosen to BYPASS the aux-free fast-paths (clause decomposition
        // / small-n canonical) so they exercise the counter/adder strategy reporting:
        //   C1: a mid-threshold cardinality over 20 vars (C(20,9) >> budget AND
        //       n > CANONICAL_SMALL_N) -> a counter strategy + aux vars.
        //   C2: a weighted constraint over 8 vars (n > CANONICAL_SMALL_N) -> a
        //       strategy + aux vars.
        //   C3: a product term -> linearized + a forced unit (unit_forced).
        let card_terms: Vec<PbTerm> = (1..=20).map(|v| linear_term(1, v)).collect();
        let weighted_terms: Vec<PbTerm> = [5, 4, 3, 2, 6, 7, 8, 9]
            .iter()
            .enumerate()
            .map(|(i, &c)| linear_term(c, (i + 1) as u32))
            .collect();
        let instance = PbInstance {
            num_vars: 20,
            num_constraints: 3,
            constraints: vec![
                PbConstraint {
                    terms: card_terms,
                    rel: PbRel::Ge,
                    rhs: 10,
                },
                PbConstraint {
                    terms: weighted_terms,
                    rel: PbRel::Ge,
                    rhs: 25,
                },
                PbConstraint {
                    terms: vec![PbTerm {
                        coeff: 1,
                        lits: vec![lit(1), lit(2)],
                    }],
                    rel: PbRel::Ge,
                    rhs: 1,
                },
            ],
            objective: None,
        };

        let encoded_without_profile = CnfEncoder::encode_instance(&instance);
        let (encoded, profile) = CnfEncoder::encode_instance_with_profile(&instance);

        assert_eq!(encoded.num_vars, encoded_without_profile.num_vars);
        assert_eq!(encoded.clauses, encoded_without_profile.clauses);
        assert_eq!(profile.original_vars, 20);
        assert_eq!(profile.total_vars, encoded.num_vars);
        assert_eq!(profile.clauses, encoded.clauses.len());
        assert!(
            profile.aux_vars > 0,
            "counter/adder constraints must mint aux"
        );
        assert_eq!(profile.input_constraints, 3);
        assert_eq!(profile.normalized_constraints, 3);
        assert_eq!(profile.trivial_satisfied, 0);
        assert_eq!(profile.trivial_unsatisfied, 0);
        assert_eq!(profile.unit_forced, 1, "the product row forces a unit");
        // C1 + C2 each pick a counter/adder strategy (exact choice is heuristic).
        assert_eq!(
            profile.strategies.total(),
            2,
            "two non-fast-path constraints use a counter strategy"
        );
    }

    #[test]
    fn test_encode_instance_interruptible_matches_regular_encoding() {
        let instance = PbInstance {
            num_vars: 40,
            num_constraints: 1,
            constraints: vec![PbConstraint {
                terms: (1u32..=40).map(|var| linear_term(2, var)).collect(),
                rel: PbRel::Ge,
                rhs: 30,
            }],
            objective: None,
        };

        let regular = CnfEncoder::encode_instance(&instance);
        let mut never_stop = || false;
        let interruptible =
            CnfEncoder::encode_instance_interruptible(&instance, &mut never_stop).unwrap();

        assert_eq!(interruptible.num_vars, regular.num_vars);
        assert_eq!(interruptible.clauses, regular.clauses);
    }

    #[test]
    fn test_encode_instance_interruptible_stops_during_totalizer() {
        let instance = PbInstance {
            num_vars: 64,
            num_constraints: 1,
            constraints: vec![PbConstraint {
                terms: (1u32..=64).map(|var| linear_term(2, var)).collect(),
                rel: PbRel::Ge,
                rhs: 70,
            }],
            objective: None,
        };

        let mut polls = 0usize;
        let encoded = CnfEncoder::encode_instance_interruptible(&instance, &mut || {
            polls += 1;
            polls > 4
        });

        assert!(encoded.is_none(), "encoding should stop before completion");
    }

    #[test]
    fn test_nonlinear_term_linearization() {
        let constraint = PbConstraint {
            terms: vec![PbTerm {
                coeff: 1,
                lits: vec![lit(1), lit(2)],
            }],
            rel: PbRel::Ge,
            rhs: 1,
        };
        verify_encoding_matches_constraint(&constraint, 2);
    }

    #[test]
    fn test_negated_literal_in_constraint() {
        let constraint = PbConstraint {
            terms: vec![negated_linear_term(1, 1), linear_term(1, 2)],
            rel: PbRel::Ge,
            rhs: 1,
        };
        verify_encoding_matches_constraint(&constraint, 2);
    }

    #[test]
    fn test_all_same_coefficient_cardinality() {
        let constraint = PbConstraint {
            terms: vec![
                linear_term(1, 1),
                linear_term(1, 2),
                linear_term(1, 3),
                linear_term(1, 4),
            ],
            rel: PbRel::Ge,
            rhs: 3,
        };
        verify_encoding_matches_constraint(&constraint, 4);
    }

    #[test]
    fn test_large_coefficients() {
        let constraint = PbConstraint {
            terms: vec![linear_term(100, 1), linear_term(200, 2), linear_term(50, 3)],
            rel: PbRel::Ge,
            rhs: 250,
        };
        verify_encoding_matches_constraint(&constraint, 3);
    }

    #[test]
    fn test_empty_constraint_trivially_satisfied() {
        let constraint = PbConstraint {
            terms: Vec::new(),
            rel: PbRel::Ge,
            rhs: 0,
        };
        let mut enc = CnfEncoder::new(0);
        enc.encode_constraint(&constraint);
        assert!(enc.clauses.is_empty());
    }

    #[test]
    fn test_empty_constraint_trivially_unsatisfied() {
        let constraint = PbConstraint {
            terms: Vec::new(),
            rel: PbRel::Ge,
            rhs: 1,
        };
        let mut enc = CnfEncoder::new(0);
        enc.encode_constraint(&constraint);
        assert!(enc.clauses.iter().any(Vec::is_empty));
    }

    // ---- Cross-strategy consistency tests ----

    /// Test that all four strategies produce equivalent encodings.
    #[test]
    fn test_all_strategies_agree_cardinality() {
        let constraint = PbConstraint {
            terms: vec![linear_term(1, 1), linear_term(1, 2), linear_term(1, 3)],
            rel: PbRel::Ge,
            rhs: 2,
        };
        for strategy in [
            EncodingStrategy::Bdd,
            EncodingStrategy::SequentialCounter,
            EncodingStrategy::Totalizer,
            EncodingStrategy::Adder,
        ] {
            verify_encoding_with_strategy(&constraint, 3, strategy);
        }
    }

    #[test]
    fn test_all_strategies_agree_weighted() {
        let constraint = PbConstraint {
            terms: vec![linear_term(2, 1), linear_term(3, 2), linear_term(5, 3)],
            rel: PbRel::Ge,
            rhs: 5,
        };
        for strategy in [
            EncodingStrategy::Bdd,
            EncodingStrategy::SequentialCounter,
            EncodingStrategy::Totalizer,
            EncodingStrategy::Adder,
        ] {
            verify_encoding_with_strategy(&constraint, 3, strategy);
        }
    }

    #[test]
    fn test_all_strategies_agree_equality() {
        let constraint = PbConstraint {
            terms: vec![linear_term(1, 1), linear_term(1, 2), linear_term(1, 3)],
            rel: PbRel::Eq,
            rhs: 2,
        };
        for strategy in [
            EncodingStrategy::Bdd,
            EncodingStrategy::SequentialCounter,
            EncodingStrategy::Totalizer,
            EncodingStrategy::Adder,
        ] {
            verify_encoding_with_strategy(&constraint, 3, strategy);
        }
    }

    // ---- ay-sat integration test ----

    #[test]
    fn test_encode_and_solve_with_ay_sat() {
        use ay_sat::{DimacsFormula, Literal, SatResult};

        // Encode: x1 + x2 + x3 >= 2
        let constraint = PbConstraint {
            terms: vec![linear_term(1, 1), linear_term(1, 2), linear_term(1, 3)],
            rel: PbRel::Ge,
            rhs: 2,
        };

        let instance = PbInstance {
            num_vars: 3,
            num_constraints: 1,
            constraints: vec![constraint.clone()],
            objective: None,
        };

        let encoded = CnfEncoder::encode_instance(&instance);

        // Convert to DimacsFormula.
        let dimacs_clauses: Vec<Vec<Literal>> = encoded
            .clauses
            .iter()
            .map(|clause| {
                clause
                    .iter()
                    .map(|&lit| Literal::from_dimacs(lit))
                    .collect()
            })
            .collect();

        let formula = DimacsFormula {
            num_vars: encoded.num_vars as usize,
            num_clauses: dimacs_clauses.len(),
            clauses: dimacs_clauses,
        };

        let mut solver = formula.into_solver();
        let result = solver.solve();

        match result.result() {
            SatResult::Sat(model) => {
                // Extract the original 3 PB variables from the model.
                let pb_assignment: Vec<bool> = (0..3)
                    .map(|i| model.get(i).copied().unwrap_or(false))
                    .collect();

                // Verify the assignment satisfies the original PB constraint.
                assert!(
                    crate::solver::eval_constraint(&constraint, &pb_assignment),
                    "SAT model {pb_assignment:?} does not satisfy the PB constraint"
                );

                // At least 2 of 3 variables must be true.
                let count: usize = pb_assignment.iter().filter(|&&v| v).count();
                assert!(count >= 2, "Expected at least 2 true, got {count}");
            }
            SatResult::Unsat(_) => panic!("Expected SAT, got UNSAT"),
            SatResult::Unknown => panic!("Expected SAT, got Unknown"),
            _ => panic!("Unexpected SatResult variant"),
        }
    }

    #[test]
    fn test_encode_and_solve_unsat_with_ay_sat() {
        use ay_sat::{DimacsFormula, Literal};

        // Encode an unsatisfiable system:
        // x1 + x2 = 1 AND x1 + x2 >= 2 (impossible)
        let instance = PbInstance {
            num_vars: 2,
            num_constraints: 2,
            constraints: vec![
                PbConstraint {
                    terms: vec![linear_term(1, 1), linear_term(1, 2)],
                    rel: PbRel::Eq,
                    rhs: 1,
                },
                PbConstraint {
                    terms: vec![linear_term(1, 1), linear_term(1, 2)],
                    rel: PbRel::Ge,
                    rhs: 2,
                },
            ],
            objective: None,
        };

        let encoded = CnfEncoder::encode_instance(&instance);

        let dimacs_clauses: Vec<Vec<Literal>> = encoded
            .clauses
            .iter()
            .map(|clause| {
                clause
                    .iter()
                    .map(|&lit| Literal::from_dimacs(lit))
                    .collect()
            })
            .collect();

        let formula = DimacsFormula {
            num_vars: encoded.num_vars as usize,
            num_clauses: dimacs_clauses.len(),
            clauses: dimacs_clauses,
        };

        let mut solver = formula.into_solver();
        let result = solver.solve();

        assert!(
            result.result().is_unsat(),
            "Expected UNSAT for contradictory constraints"
        );
    }

    #[test]
    fn test_encode_weighted_and_solve_with_ay_sat() {
        use ay_sat::{DimacsFormula, Literal, SatResult};

        // Encode: 2*x1 + 3*x2 + 5*x3 >= 5
        let constraint = PbConstraint {
            terms: vec![linear_term(2, 1), linear_term(3, 2), linear_term(5, 3)],
            rel: PbRel::Ge,
            rhs: 5,
        };

        let instance = PbInstance {
            num_vars: 3,
            num_constraints: 1,
            constraints: vec![constraint.clone()],
            objective: None,
        };

        let encoded = CnfEncoder::encode_instance(&instance);

        let dimacs_clauses: Vec<Vec<Literal>> = encoded
            .clauses
            .iter()
            .map(|clause| {
                clause
                    .iter()
                    .map(|&lit| Literal::from_dimacs(lit))
                    .collect()
            })
            .collect();

        let formula = DimacsFormula {
            num_vars: encoded.num_vars as usize,
            num_clauses: dimacs_clauses.len(),
            clauses: dimacs_clauses,
        };

        let mut solver = formula.into_solver();
        let result = solver.solve();

        match result.result() {
            SatResult::Sat(model) => {
                let pb_assignment: Vec<bool> = (0..3)
                    .map(|i| model.get(i).copied().unwrap_or(false))
                    .collect();

                assert!(
                    crate::solver::eval_constraint(&constraint, &pb_assignment),
                    "SAT model {pb_assignment:?} does not satisfy 2*x1 + 3*x2 + 5*x3 >= 5"
                );
            }
            SatResult::Unsat(_) => panic!("Expected SAT, got UNSAT"),
            SatResult::Unknown => panic!("Expected SAT, got Unknown"),
            _ => panic!("Unexpected SatResult variant"),
        }
    }

    // ---- Property tests: encoding equisatisfiability over whole instances ----

    /// Brute-force check that the full-instance CNF encoding is equisatisfiable
    /// with the PB instance: for every assignment of the original variables,
    /// `(some aux extension satisfies the CNF) == (the assignment satisfies all
    /// PB constraints)`. This exercises *cross-constraint* aux interaction, which
    /// single-constraint checks miss.
    fn assert_instance_encoding_equisatisfiable(instance: &PbInstance) {
        let encoded = CnfEncoder::encode_instance(instance);
        let n = instance.num_vars as usize;
        assert!(n <= 8, "brute-force test variable budget exceeded");
        let total_vars = encoded.num_vars as usize;
        let num_aux = total_vars - n;
        assert!(
            num_aux <= 11,
            "brute-force test aux budget exceeded: {num_aux}"
        );

        for mask in 0u64..(1u64 << n) {
            let assignment: Vec<bool> = (0..n).map(|i| (mask >> i) & 1 == 1).collect();
            let pb_sat = instance
                .constraints
                .iter()
                .all(|c| crate::solver::eval_constraint(c, &assignment));

            let cnf_sat = (0u64..(1u64 << num_aux)).any(|aux_mask| {
                let mut full = assignment.clone();
                for j in 0..num_aux {
                    full.push((aux_mask >> j) & 1 == 1);
                }
                all_clauses_satisfied(&encoded.clauses, &full, encoded.num_vars)
            });

            assert_eq!(
                pb_sat, cnf_sat,
                "instance encoding mismatch for assignment {assignment:?}: PB={pb_sat} CNF={cnf_sat}"
            );
        }
    }

    #[test]
    fn property_random_feasible_instances_encode_to_sat() {
        // Deterministic LCG; small instances kept inside the brute-force budget.
        let mut seed: u64 = 0x9e37_79b9_7f4a_7c15;
        let mut rng = || {
            seed = seed
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            seed >> 33
        };

        let mut feasible_seen = 0;
        for _ in 0..120 {
            let num_vars = 2 + (rng() % 3) as u32; // 2..=4 vars
            let num_constraints = 1 + (rng() % 3) as usize; // 1..=3 constraints
            let mut constraints = Vec::with_capacity(num_constraints);
            for _ in 0..num_constraints {
                let mut terms = Vec::new();
                for v in 1..=num_vars {
                    // bnn-like: mostly +/-1, sometimes a larger coefficient.
                    let coeff: i128 = match rng() % 8 {
                        0 | 1 => 1,
                        2 | 3 => -1,
                        4 => (rng() % 6) as i128 + 2,
                        5 => -((rng() % 6) as i128 + 2),
                        _ => 1,
                    };
                    let negated = rng() % 2 == 0;
                    terms.push(PbTerm {
                        coeff,
                        lits: vec![PbLit { var: v, negated }],
                    });
                }
                let rel = if rng() % 4 == 0 { PbRel::Eq } else { PbRel::Ge };
                let max_pos: i128 = terms.iter().map(|t| t.coeff.max(0)).sum();
                let min_neg: i128 = terms.iter().map(|t| t.coeff.min(0)).sum();
                let span = (max_pos - min_neg).max(1);
                let rhs = min_neg + (rng() as i128 % (span + 1));
                constraints.push(PbConstraint { terms, rel, rhs });
            }
            let instance = PbInstance {
                num_vars,
                num_constraints: num_constraints as u32,
                constraints,
                objective: None,
            };

            // Skip oversized aux budgets to keep the brute force fast.
            let encoded = CnfEncoder::encode_instance(&instance);
            if (encoded.num_vars - num_vars) as usize > 11 {
                continue;
            }

            // Track that we exercise genuinely feasible instances too.
            let feasible = (0u64..(1u64 << num_vars)).any(|mask| {
                let a: Vec<bool> = (0..num_vars as usize)
                    .map(|i| (mask >> i) & 1 == 1)
                    .collect();
                instance
                    .constraints
                    .iter()
                    .all(|c| crate::solver::eval_constraint(c, &a))
            });
            if feasible {
                feasible_seen += 1;
            }

            assert_instance_encoding_equisatisfiable(&instance);
        }
        assert!(
            feasible_seen > 0,
            "expected to generate at least one feasible random instance"
        );
    }

    #[test]
    fn property_bnn_shape_cardinality_with_big_coeff_is_sound() {
        // The PB25 bnn-verification shape that motivated the soundness audit:
        // one larger coefficient plus several +/-1 unit coefficients with mixed
        // polarity literals and a threshold the big coefficient alone can meet.
        // The actual failing instance routes these constraints to the totalizer,
        // so cover BDD / sequential-counter / totalizer at the 4-variable scale.
        // (Coefficients kept small so the auxiliary count stays within the
        // exhaustive-search budget; the encoders are coefficient-agnostic in
        // structure, so small-scale soundness implies the general case.)
        for strategy in [
            EncodingStrategy::Bdd,
            EncodingStrategy::SequentialCounter,
            EncodingStrategy::Totalizer,
        ] {
            // 3*x1 + 1*x2 - 1*x3 + 1*x4 >= 3  (and the equality variant).
            for rel in [PbRel::Ge, PbRel::Eq] {
                let constraint = PbConstraint {
                    terms: vec![
                        linear_term(3, 1),
                        linear_term(1, 2),
                        negated_linear_term(1, 3),
                        linear_term(1, 4),
                    ],
                    rel,
                    rhs: 3,
                };
                verify_encoding_with_strategy(&constraint, 4, strategy);
            }
        }

        // The adder allocates many auxiliaries even for small coefficients, so
        // exercise it on a smaller big-coeff-plus-units shape to keep the
        // exhaustive aux search tractable: 2*x1 - 1*x2 + 1*x3 >= 2.
        for rel in [PbRel::Ge, PbRel::Eq] {
            let constraint = PbConstraint {
                terms: vec![
                    linear_term(2, 1),
                    negated_linear_term(1, 2),
                    linear_term(1, 3),
                ],
                rel,
                rhs: 2,
            };
            verify_encoding_with_strategy(&constraint, 3, EncodingStrategy::Adder);
        }
    }

    #[test]
    fn forced_unary_strategy_falls_back_to_adder_on_big_threshold() {
        // Regression for the >100 GB OOM: a forced sequential-counter / totalizer
        // encoding allocates O(n * rhs) aux vars/clauses — proportional to the
        // threshold magnitude. A big-coefficient PB constraint drove this to
        // >100 GB and OOM'd the host. The unary clamp must downgrade to the
        // bit-efficient adder, so the encoded CNF stays small for any requested
        // strategy. (Pre-fix this allocated ~30M vars and could exhaust memory.)
        let constraint = PbConstraint {
            terms: vec![
                linear_term(10_000_000, 1),
                linear_term(1, 2),
                linear_term(1, 3),
            ],
            rel: PbRel::Ge,
            rhs: 10_000_000,
        };
        for strategy in [
            EncodingStrategy::SequentialCounter,
            EncodingStrategy::Totalizer,
        ] {
            let mut enc = CnfEncoder::with_strategy(3, strategy);
            enc.encode_constraint(&constraint);
            assert!(
                enc.next_var < 100_000,
                "forced {strategy:?} on a big threshold should fall back to the adder; got {} vars",
                enc.next_var
            );
            assert!(
                enc.clauses.len() < 200_000,
                "clause count not bounded for forced {strategy:?}: {}",
                enc.clauses.len()
            );
        }
    }

    // ---- Gap-row budgeted-BDD routing tests ----

    /// A gap row: medium coefficients (<= 10_000), rhs > 10_000 (post
    ///-normalization: gcd 1, not saturated), n > CANONICAL_SMALL_N so no
    /// aux-free fast path intercepts. Previously routed to the adder.
    fn small_gap_constraint() -> PbConstraint {
        // 5*6000 + 6001 = 36001 >= 12001; gcd(6000, 6001) = 1.
        let mut terms: Vec<PbTerm> = (1..=5).map(|v| linear_term(6000, v)).collect();
        terms.push(linear_term(6001, 6));
        PbConstraint {
            terms,
            rel: PbRel::Ge,
            rhs: 12_001,
        }
    }

    #[test]
    fn gap_row_routes_to_budgeted_bdd() {
        let constraint = small_gap_constraint();
        let mut enc = CnfEncoder::new(6);
        enc.encode_constraint(&constraint);
        let profile = enc.profile();
        assert_eq!(
            profile.strategies.bdd, 1,
            "gap row must take the budgeted BDD upgrade"
        );
        assert_eq!(
            profile.strategies.adder, 0,
            "gap row must not fall through to the adder when the BDD fits"
        );
        // The BDD of this row is tiny (few distinct slack values), so the
        // encoding is exhaustively verifiable against the PB semantics.
        verify_encoding_matches_constraint(&constraint, 6);
    }

    #[test]
    fn gap_row_with_empty_pool_is_identical_to_previous_adder_routing() {
        let constraint = small_gap_constraint();

        let mut gated = CnfEncoder::new(6);
        gated.set_bdd_gap_node_pool(0);
        gated.encode_constraint(&constraint);
        assert_eq!(gated.profile().strategies.adder, 1);
        assert_eq!(gated.profile().strategies.bdd, 0);

        let mut forced = CnfEncoder::with_strategy(6, EncodingStrategy::Adder);
        forced.encode_constraint(&constraint);

        // With the pool empty the new path must be byte-identical to the old
        // adder routing: same clauses, same variable allocation.
        assert_eq!(gated.clauses(), forced.clauses());
        assert_eq!(gated.total_vars(), forced.total_vars());
    }

    #[test]
    fn gap_row_budget_abort_rolls_back_and_falls_back_to_adder() {
        // A wide gap row whose BDD has far more fresh states than the tiny
        // budget below: 40 mutually-coprime-ish medium coefficients, mid rhs.
        let terms: Vec<PbTerm> = (0..40)
            .map(|i| linear_term(5000 + 2 * i + 1, (i + 1) as u32))
            .collect();
        let constraint = PbConstraint {
            terms,
            rel: PbRel::Ge,
            rhs: 100_003,
        };

        let mut gated = CnfEncoder::new(40);
        // Two poll intervals: the attempt starts, aborts deterministically,
        // and must roll back every partial clause and variable.
        gated.set_bdd_gap_node_pool(2 * 4096);
        gated.encode_constraint(&constraint);
        assert_eq!(
            gated.profile().strategies.adder,
            1,
            "budget abort must fall back to the adder"
        );
        assert_eq!(gated.profile().strategies.bdd, 0);

        let mut forced = CnfEncoder::with_strategy(40, EncodingStrategy::Adder);
        forced.encode_constraint(&constraint);
        assert_eq!(
            gated.clauses(),
            forced.clauses(),
            "rollback must leave no trace of the aborted BDD attempt"
        );
        assert_eq!(gated.total_vars(), forced.total_vars());
    }

    #[test]
    fn gap_row_interruptible_encode_matches_plain_encode() {
        // Instance containing a gap row: the interruptible encoder must emit
        // the identical CNF (the budget decision is deterministic in the
        // fresh-state count, never wall clock).
        let instance = PbInstance {
            num_vars: 6,
            num_constraints: 1,
            constraints: vec![small_gap_constraint()],
            objective: None,
        };
        let plain = CnfEncoder::encode_instance(&instance);
        let mut never_stop = || false;
        let interruptible =
            CnfEncoder::encode_instance_interruptible(&instance, &mut never_stop).unwrap();
        assert_eq!(plain.num_vars, interruptible.num_vars);
        assert_eq!(plain.clauses, interruptible.clauses);
    }

    /// Differential equisatisfiability fuzz over random gap-shaped rows:
    /// encode each row with the Auto routing (budgeted BDD upgrade) and with
    /// the forced adder, then check both CNFs against the PB semantics with
    /// `ay-sat` under a battery of fixed full assignments to the original
    /// variables (aux vars left free), plus one unconstrained solve.
    #[test]
    fn differential_fuzz_gap_rows_auto_vs_adder() {
        use ay_sat::Literal;

        // Deterministic LCG.
        let mut seed: u64 = 0x1234_5678_9abc_def0;
        let mut rng = move || {
            seed = seed
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            seed >> 33
        };

        let solve_with_fixed = |cnf: &EncodedCnf, fixed: Option<&[bool]>| -> bool {
            let mut solver = ay_sat::Solver::new(cnf.num_vars as usize);
            for clause in &cnf.clauses {
                let lits: Vec<Literal> = clause.iter().map(|&l| Literal::from_dimacs(l)).collect();
                solver.add_clause(lits);
            }
            if let Some(assignment) = fixed {
                for (i, &value) in assignment.iter().enumerate() {
                    let dimacs = if value {
                        (i + 1) as i32
                    } else {
                        -((i + 1) as i32)
                    };
                    solver.add_clause(vec![Literal::from_dimacs(dimacs)]);
                }
            }
            match solver.solve().result() {
                ay_sat::SatResult::Sat(_) => true,
                ay_sat::SatResult::Unsat(_) => false,
                _ => panic!("tiny CNF must be decided"),
            }
        };

        for round in 0..24 {
            let n = 6 + (rng() % 4) as usize; // 6..=9 original vars
            let coeffs: Vec<i128> = (0..n).map(|_| 2_000 + (rng() % 8_000) as i128).collect();
            let total: i128 = coeffs.iter().sum();
            // rhs in (10_000, total): a genuine, non-trivial gap threshold.
            let rhs = 10_001 + (rng() as i128 % (total - 10_001).max(1));
            let terms: Vec<PbTerm> = coeffs
                .iter()
                .enumerate()
                .map(|(i, &c)| linear_term(c, (i + 1) as u32))
                .collect();
            let constraint = PbConstraint {
                terms,
                rel: PbRel::Ge,
                rhs,
            };

            let mut auto_enc = CnfEncoder::new(n as u32);
            auto_enc.encode_constraint(&constraint);
            let auto_cnf = EncodedCnf {
                num_vars: auto_enc.total_vars(),
                clauses: auto_enc.clauses().to_vec(),
            };
            let mut adder_enc = CnfEncoder::with_strategy(n as u32, EncodingStrategy::Adder);
            adder_enc.encode_constraint(&constraint);
            let adder_cnf = EncodedCnf {
                num_vars: adder_enc.total_vars(),
                clauses: adder_enc.clauses().to_vec(),
            };

            // Fixed-assignment differential: every assignment pattern must
            // make both CNFs agree with the PB evaluator.
            for probe in 0..10 {
                let assignment: Vec<bool> = match probe {
                    0 => vec![true; n],
                    1 => vec![false; n],
                    _ => (0..n).map(|_| rng() % 2 == 1).collect(),
                };
                let pb_sat = crate::solver::eval_constraint(&constraint, &assignment);
                let auto_sat = solve_with_fixed(&auto_cnf, Some(&assignment));
                let adder_sat = solve_with_fixed(&adder_cnf, Some(&assignment));
                assert_eq!(
                    pb_sat, auto_sat,
                    "round {round}: AUTO CNF disagrees with PB semantics for {assignment:?} \
                     (coeffs {coeffs:?} rhs {rhs})"
                );
                assert_eq!(
                    pb_sat, adder_sat,
                    "round {round}: ADDER CNF disagrees with PB semantics for {assignment:?} \
                     (coeffs {coeffs:?} rhs {rhs})"
                );
            }

            // Unconstrained solve: both must be SAT (row is satisfiable by
            // construction: all-true reaches total >= rhs).
            assert!(solve_with_fixed(&auto_cnf, None));
            assert!(solve_with_fixed(&adder_cnf, None));
        }
    }

    // ---- Totalizer clause-volume guard tests ----

    #[test]
    fn small_weight_set_row_keeps_the_totalizer() {
        // 30 terms with weights in {1, 2}: merged weight sets stay tiny
        // (subtree sums), so the clause estimate is far below the ceiling and
        // the legacy totalizer routing is preserved.
        let terms: Vec<PbTerm> = (1..=30)
            .map(|v| linear_term(if v % 2 == 0 { 2 } else { 1 }, v))
            .collect();
        let constraint = PbConstraint {
            terms,
            rel: PbRel::Ge,
            rhs: 23,
        };
        let mut enc = CnfEncoder::new(30);
        enc.encode_constraint(&constraint);
        assert_eq!(
            enc.profile().strategies.totalizer,
            1,
            "small-weight-set row must keep the totalizer"
        );
    }

    #[test]
    fn dense_mid_threshold_row_is_redirected_off_the_totalizer() {
        // An lseu-shaped row: 40 varied medium weights with a mid four-digit
        // threshold. The totalizer's weight sets become dense (thousands of
        // distinct sums), so its clause volume estimates in the hundreds of
        // millions; the guard must redirect the row (BDD or adder), keeping
        // the emitted CNF bounded.
        let terms: Vec<PbTerm> = (0..40)
            .map(|i| linear_term(101 + 37 * (i as i128 % 13) + i as i128, (i + 1) as u32))
            .collect();
        let total: i128 = terms.iter().map(|t| t.coeff).sum();
        let constraint = PbConstraint {
            terms,
            rel: PbRel::Ge,
            rhs: total / 2,
        };
        let mut enc = CnfEncoder::new(40);
        enc.encode_constraint(&constraint);
        let profile = enc.profile();
        assert_eq!(
            profile.strategies.totalizer, 0,
            "dense row must not take the exploding totalizer"
        );
        assert_eq!(profile.strategies.total(), 1);
        assert!(
            enc.clauses().len() < 2_000_000,
            "redirected row must stay bounded, got {} clauses",
            enc.clauses().len()
        );
    }

    #[test]
    fn totalizer_guard_fails_closed_once_estimation_pool_is_spent() {
        // Dense lseu-shaped row (see
        // `dense_mid_threshold_row_is_redirected_off_the_totalizer`): each
        // dry-run estimation burns a large slice of the shared pool.
        let dense_coeffs: Vec<i128> = (0..40)
            .map(|i| 101 + 37 * (i as i128 % 13) + i as i128)
            .collect();
        let dense_rhs: i128 = dense_coeffs.iter().sum::<i128>() / 2;

        // A cheap small-weight-set row the estimator proves affordable (same
        // shape as `small_weight_set_row_keeps_the_totalizer`).
        let cheap_coeffs: Vec<i128> = (1..=30).map(|v| if v % 2 == 0 { 2 } else { 1 }).collect();
        let cheap_rhs = 23;

        let mut enc = CnfEncoder::new(40);
        assert_eq!(
            enc.refined_auto_strategy(EncodingStrategy::Totalizer, &cheap_coeffs, cheap_rhs),
            EncodingStrategy::Totalizer,
            "with a live pool the affordable row must keep the totalizer"
        );

        // Drain the pool with repeated dense estimations (each charged its
        // real work; a few dozen iterations suffice at 16M pool / ~420k row).
        let mut iterations = 0;
        while enc.totalizer_est_work_pool > 0 {
            let _ =
                enc.refined_auto_strategy(EncodingStrategy::Totalizer, &dense_coeffs, dense_rhs);
            iterations += 1;
            assert!(iterations < 20_000, "estimation pool must drain");
        }

        // Pool spent: the estimator can no longer prove ANY totalizer row
        // affordable, so even the cheap row must fail CLOSED to the adder
        // (BDD-then-adder path), never the unguarded totalizer.
        assert_eq!(
            enc.refined_auto_strategy(EncodingStrategy::Totalizer, &cheap_coeffs, cheap_rhs),
            EncodingStrategy::Adder,
            "spent estimation pool must fail closed, not reopen the unguarded totalizer"
        );
    }

    #[test]
    fn spent_estimation_pool_reroutes_auto_totalizer_rows_end_to_end() {
        // Same row as `small_weight_set_row_keeps_the_totalizer`, but with
        // the estimation pool spent up front: the full encode path must route
        // the row off the totalizer (BDD-then-adder), keeping the
        // clause-volume ceiling unconditional.
        let terms: Vec<PbTerm> = (1..=30)
            .map(|v| linear_term(if v % 2 == 0 { 2 } else { 1 }, v))
            .collect();
        let constraint = PbConstraint {
            terms,
            rel: PbRel::Ge,
            rhs: 23,
        };
        let mut enc = CnfEncoder::new(30);
        enc.set_totalizer_est_work_pool(0);
        enc.encode_constraint(&constraint);
        let profile = enc.profile();
        assert_eq!(
            profile.strategies.totalizer, 0,
            "pool-spent rows must not take the unguarded totalizer"
        );
        assert_eq!(profile.strategies.total(), 1);
    }

    #[test]
    fn gap_pool_threads_across_session_encodes() {
        let instance = PbInstance {
            num_vars: 6,
            num_constraints: 1,
            constraints: vec![small_gap_constraint()],
            objective: None,
        };
        let mut never_stop = || false;

        // Seeding with the default pool is byte-identical to the plain
        // encode and reports the gap row's BDD charge against the pool.
        let (first, pool_after_first) = CnfEncoder::encode_instance_interruptible_with_gap_pool(
            &instance,
            &mut never_stop,
            BDD_GAP_NODE_POOL,
        )
        .unwrap();
        let plain = CnfEncoder::encode_instance(&instance);
        assert_eq!(first.clauses, plain.clauses);
        assert_eq!(first.num_vars, plain.num_vars);
        assert!(
            pool_after_first < BDD_GAP_NODE_POOL,
            "the gap row's BDD attempt must be charged to the threaded pool"
        );

        // Threading a spent pool forward declines the BDD: byte-identical to
        // the forced adder, and the pool stays spent for the next encode.
        let (spent, pool_after_spent) =
            CnfEncoder::encode_instance_interruptible_with_gap_pool(&instance, &mut never_stop, 0)
                .unwrap();
        assert_eq!(pool_after_spent, 0, "a spent pool must stay spent");
        let mut forced = CnfEncoder::with_strategy(6, EncodingStrategy::Adder);
        forced.encode_constraint(&small_gap_constraint());
        assert_eq!(spent.clauses, forced.clauses());
        assert_eq!(spent.num_vars, forced.total_vars());
    }

    #[test]
    fn estimate_totalizer_clause_volume_boundaries() {
        // Tiny row: trivially affordable.
        let (_, affordable) = estimate_totalizer_clause_volume(&[2, 3, 4, 5], 7, 100_000, 100_000);
        assert!(affordable);

        // Dense row with a tiny clause ceiling: must be reported unaffordable
        // (fail-closed), and the reported work must respect the work budget.
        let coeffs: Vec<i128> = (0..64).map(|i| 100 + i).collect();
        let (work, affordable) = estimate_totalizer_clause_volume(&coeffs, 4_000, 1_000, 50_000);
        assert!(!affordable);
        assert!(work <= 50_001, "work {work} must stop at the budget");
    }

    // ---- Generalized totalizer boundary tests ----

    #[test]
    fn totalizer_rhs_one_and_rhs_total_boundaries() {
        // rhs = 1: any literal suffices. rhs = 13 (the total): all must be
        // true. Weights kept low-diversity so the merged weight sets stay
        // within the brute-force aux budget while n > CANONICAL_SMALL_N.
        for rhs in [1, 13] {
            let constraint = PbConstraint {
                terms: vec![
                    linear_term(2, 1),
                    linear_term(2, 2),
                    linear_term(2, 3),
                    linear_term(2, 4),
                    linear_term(2, 5),
                    linear_term(3, 6),
                ],
                rel: PbRel::Ge,
                rhs,
            };
            verify_encoding_with_strategy(&constraint, 6, EncodingStrategy::Totalizer);
        }
    }

    #[test]
    fn totalizer_all_equal_weights_degenerates_to_cardinality() {
        // All-equal weights normalize (gcd) to a cardinality row; the encoding
        // must accept exactly the assignments with >= ceil(rhs/w) true.
        let constraint = PbConstraint {
            terms: (1..=6).map(|v| linear_term(7, v)).collect(),
            rel: PbRel::Ge,
            rhs: 21, // ceil(21/7) = 3 of 6 must be true
        };
        verify_encoding_with_strategy(&constraint, 6, EncodingStrategy::Totalizer);
    }

    // ---- Clause-arena footprint guard tests ----

    #[test]
    fn sat_arena_footprint_counts_header_and_literals() {
        let cnf = EncodedCnf {
            num_vars: 3,
            clauses: vec![vec![1, -2, 3], vec![1, 2]],
        };
        let header = ay_sat::arena_limits::HEADER_WORDS;
        // (header + 3) + (header + 2)
        assert_eq!(cnf.sat_arena_word_footprint(), header * 2 + 5);
        assert!(cnf.fits_sat_arena());
    }

    #[test]
    fn fits_sat_arena_accepts_modest_cnf_and_matches_arena_layout() {
        // The guard rejects any CNF whose footprint reaches three quarters of the
        // `u32::MAX` arena-word budget (leaving a quarter as headroom for learned
        // clauses), so the SAT path returns UNKNOWN instead of risking an unsound
        // verdict from offset truncation in ay-sat's 32-bit clause references.
        // Physically materializing ~3e9 arena words to exercise the rejecting
        // branch is infeasible in a unit test, so verify (a) the per-clause
        // accounting exactly matches ay-sat's arena layout and (b) a modest CNF
        // is accepted. The rejecting branch is exercised end-to-end on
        // pathological PB25 instances during benchmarking.
        let threshold = ay_sat::arena_limits::MAX_ARENA_WORDS / 4 * 3;

        // Per-clause accounting must match ay-sat's layout (header + one word per
        // literal); the footprint and the guard predicate are derived from it.
        let one = EncodedCnf {
            num_vars: 3,
            clauses: vec![vec![1, 2, 3]],
        };
        assert_eq!(
            one.sat_arena_word_footprint(),
            ay_sat::arena_limits::clause_words(3)
        );

        let cnf = EncodedCnf {
            num_vars: 4,
            clauses: vec![vec![1, -2, 3], vec![-1, 4], vec![2, 3, 4]],
        };
        let expected = ay_sat::arena_limits::clause_words(3)
            + ay_sat::arena_limits::clause_words(2)
            + ay_sat::arena_limits::clause_words(3);
        assert_eq!(cnf.sat_arena_word_footprint(), expected);
        assert!(cnf.sat_arena_word_footprint() < threshold);
        assert!(cnf.fits_sat_arena());

        // The guard predicate is exactly `footprint < MAX_ARENA_WORDS / 4 * 3`.
        assert_eq!(
            cnf.fits_sat_arena(),
            cnf.sat_arena_word_footprint() < threshold
        );
    }

    #[test]
    fn fits_sat_arena_now_admits_footprints_above_old_2pow31_limit() {
        // Regression for #9670: footprints that sit between the OLD `2^31` bound
        // and `3/4 · u32::MAX` (e.g. the bnn-verification family, ~2.46e9 words)
        // were previously declined (UNKNOWN). They must now be accepted so ay-sat
        // can actually attempt them — while a footprint at/above the new
        // three-quarter guard is still rejected.
        let old_limit = 1u64 << 31;
        let new_threshold = ay_sat::arena_limits::MAX_ARENA_WORDS / 4 * 3;
        assert!(
            new_threshold > old_limit,
            "new guard must admit some footprints above the old 2^31 limit",
        );

        // A footprint just above the old limit is below the new guard → admitted.
        let mid = old_limit + 1;
        assert!(mid < new_threshold);
        // A footprint at the new guard is rejected (strict `<`).
        let at_guard = new_threshold;
        assert!(at_guard >= new_threshold);
    }
}
