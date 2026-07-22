// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Learned-clause profile descriptors for future external code generation evaluation (#8391).
//!
//! ## Scope
//!
//! This module deliberately does **not** compile SAT BCP, install native
//! dispatch, detach watches, or revive the retired full-BCP/watch JIT path.
//! It provides a bounded, deterministic contract for extracting learned-clause
//! descriptors from solver-owned metadata. The descriptors are profile-only:
//! they identify clauses that are worth studying later, and they are shaped for
//! a future external code generation lowering experiment, but the scalar SAT solver remains
//! the only propagation/proof authority today.
//!
//! The contract separates three outcomes:
//!
//! 1. [`LearnedClauseDescriptor`] for structurally supported, profile-hot,
//!    proof-safe learned clauses.
//! 2. [`LearnedClauseFallback`] for clauses that must continue through scalar
//!    SAT handling (for example proof metadata is unavailable or the profile
//!    budget is exhausted).
//! 3. [`LearnedClauseRejection`] for unsupported or unsafe inputs such as
//!    deleted, non-learned, empty, unit, too-large, duplicate, or tautological
//!    clauses.
//!
//! The interpreted [`LearnedClausePropagator`] below is retained as a local
//! reference oracle for descriptor tests. It is not a native dispatch surface.
//!
//! ## Why stand-in `Literal`/`Trail`/`CodegenContext`?
//!
//! The solver's concrete literal/trail types live in `ay-sat` and `ay-dpll`;
//! wiring this profile surface into those crates belongs to a later solver lane.
//! For now we define minimal stand-in types here so the descriptor and
//! interpreter contracts can be unit-tested standalone within `ay-jit`.
//!
//! ## Literal encoding
//!
//! We reuse the `var_idx = lit >> 1`, `polarity = lit & 1` convention used
//! throughout ay-sat/ay-jit (see `crate::conflict_jit` doc-comment). A
//! [`Literal`] stores the raw `u32` code.
//!
//! ## Semantics
//!
//! For a clause `C = l_1 ∨ l_2 ∨ … ∨ l_k` evaluated under a partial trail:
//!
//! - If any `l_i` is `True` under the trail → the clause is satisfied
//!   ([`PropagatorResult::NoOp`]).
//! - If every `l_i` is `False` under the trail → the clause is violated
//!   ([`PropagatorResult::Falsified`]).
//! - If exactly one `l_i` is `Unassigned` and every other literal is `False` →
//!   the clause unit-propagates that literal
//!   ([`PropagatorResult::Unit`]).
//! - Otherwise → [`PropagatorResult::NoOp`].
//!
//! These semantics mirror the classical watched-literal propagator and are the
//! scalar reference used by this module's tests.

use std::sync::Arc;

// ---------------------------------------------------------------------------
// Stand-in types for standalone ay-jit tests.
// ---------------------------------------------------------------------------

/// A DIMACS-style literal.
///
/// Encodes `var_idx = code >> 1` and `polarity = code & 1`. A `polarity` of
/// `0` means the positive literal, `1` means the negative literal. This matches
/// the convention used by SAT helper code.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Literal(u32);

impl Literal {
    /// Create a literal from its raw encoded form.
    #[inline]
    #[must_use]
    pub const fn from_code(code: u32) -> Self {
        Self(code)
    }

    /// Create a literal from a variable index and polarity.
    ///
    /// `positive = true` creates `+var`, `positive = false` creates `-var`.
    #[inline]
    #[must_use]
    pub const fn new(var: u32, positive: bool) -> Self {
        Self((var << 1) | if positive { 0 } else { 1 })
    }

    /// The raw encoded literal.
    #[inline]
    #[must_use]
    pub const fn code(self) -> u32 {
        self.0
    }

    /// The underlying variable index.
    #[inline]
    #[must_use]
    pub const fn var(self) -> u32 {
        self.0 >> 1
    }

    /// `true` for `+var`, `false` for `-var`.
    #[inline]
    #[must_use]
    pub const fn is_positive(self) -> bool {
        (self.0 & 1) == 0
    }
}

// ---------------------------------------------------------------------------
// Profile-only learned-clause extraction contract.
// ---------------------------------------------------------------------------

/// Semantic version for [`LearnedClauseDescriptor`].
///
/// Bump this when descriptor fields or interpretation change in a way that a
/// persisted profile consumer cannot safely ignore.
pub const LEARNED_CLAUSE_DESCRIPTOR_VERSION: u32 = 1;

/// Learned-clause descriptors are metadata-only today; no SAT propagation path
/// dispatches through native code from this module.
pub const LEARNED_CLAUSE_NATIVE_DISPATCH_ENABLED: bool = false;

/// Default cap for one extraction round.
pub const DEFAULT_LEARNED_CLAUSE_MAX_CANDIDATES: usize = 64;

/// Default literal bound for a descriptor.
///
/// This is intentionally conservative: large learned clauses stay scalar until
/// a later external code generation experiment proves that lowering them is worthwhile.
pub const DEFAULT_LEARNED_CLAUSE_MAX_LITERALS: usize = 16;

/// Default minimum profile count for descriptor extraction.
pub const DEFAULT_LEARNED_CLAUSE_MIN_PROFILE_COUNT: u32 = 1;

/// The only lowering target admitted by this metadata contract.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
#[repr(u8)]
pub enum LearnedClauseLoweringTarget {
    /// Future typed-MIR emission lowered by the EXTERNAL_CODEGEN backend.
    ExternalCodegenBackend = 1,
}

/// How extracted descriptors may be used.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
#[repr(u8)]
pub enum LearnedClauseEvaluationMode {
    /// Record deterministic metadata only; scalar SAT remains authoritative.
    ProfileOnly = 1,
}

/// Proof status attached to a solver-owned learned clause.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum LearnedClauseProofStatus {
    /// Proof output/checking is disabled for this solve.
    ProofDisabled,
    /// The clause has a concrete proof identifier already tracked by SAT.
    ProofTracked {
        /// Solver/proof-manager clause identifier.
        proof_id: u64,
    },
    /// LRAT backward reconstruction reserved the identifier for later output.
    ReservedForBackward {
        /// Reserved proof-manager clause identifier.
        proof_id: u64,
    },
    /// Proof mode is active but this clause cannot be tied to a live proof ID.
    Missing,
}

impl LearnedClauseProofStatus {
    /// Returns `true` when profiling this clause cannot bypass required proof
    /// accounting.
    #[must_use]
    pub const fn is_profile_safe(self) -> bool {
        match self {
            Self::ProofDisabled => true,
            Self::ProofTracked { proof_id } | Self::ReservedForBackward { proof_id } => {
                proof_id != 0
            }
            Self::Missing => false,
        }
    }

    const fn tag(self) -> u8 {
        match self {
            Self::ProofDisabled => 0,
            Self::ProofTracked { .. } => 1,
            Self::ReservedForBackward { .. } => 2,
            Self::Missing => 3,
        }
    }

    const fn id(self) -> u64 {
        match self {
            Self::ProofTracked { proof_id } | Self::ReservedForBackward { proof_id } => proof_id,
            Self::ProofDisabled | Self::Missing => 0,
        }
    }
}

/// Solver-side snapshot of one learned clause at extraction time.
///
/// The SAT solver owns liveness, deletion, proof, and profile counters. This
/// borrowed record is the narrow boundary that future integration should feed
/// into [`extract_learned_clause_candidates`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LearnedClauseSnapshot<'a> {
    /// Solver/proof visible clause ID.
    pub clause_id: u64,
    /// Clause literals in solver order.
    pub literals: &'a [Literal],
    /// Stored LBD/glue value.
    pub lbd: u32,
    /// Profile counter for this clause.
    pub profile_count: u32,
    /// `true` only for solver-learned clauses.
    pub learned: bool,
    /// `true` if the clause has already been deleted or garbage-marked.
    pub deleted: bool,
    /// Conservative liveness epoch supplied by the solver/deletion hook.
    pub deletion_epoch: u64,
    /// Proof metadata needed to keep profiling advisory in proof modes.
    pub proof_status: LearnedClauseProofStatus,
}

impl<'a> LearnedClauseSnapshot<'a> {
    /// Construct a learned, live, proof-disabled snapshot with zero profile.
    #[must_use]
    pub const fn new(clause_id: u64, literals: &'a [Literal]) -> Self {
        Self {
            clause_id,
            literals,
            lbd: 0,
            profile_count: 0,
            learned: true,
            deleted: false,
            deletion_epoch: 0,
            proof_status: LearnedClauseProofStatus::ProofDisabled,
        }
    }

    /// Return a copy with LBD and profile count populated.
    #[must_use]
    pub const fn with_profile(mut self, lbd: u32, profile_count: u32) -> Self {
        self.lbd = lbd;
        self.profile_count = profile_count;
        self
    }

    /// Return a copy with proof metadata populated.
    #[must_use]
    pub const fn with_proof_status(mut self, proof_status: LearnedClauseProofStatus) -> Self {
        self.proof_status = proof_status;
        self
    }

    /// Return a copy with deletion state populated.
    #[must_use]
    pub const fn with_deletion_state(mut self, deleted: bool, deletion_epoch: u64) -> Self {
        self.deleted = deleted;
        self.deletion_epoch = deletion_epoch;
        self
    }
}

/// Budget for one learned-clause extraction pass.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LearnedClauseExtractionBudget {
    /// Maximum descriptors returned from one pass.
    pub max_candidates: usize,
    /// Maximum literals allowed in any descriptor.
    pub max_literals_per_clause: usize,
    /// Minimum profile count required before a supported clause is described.
    pub min_profile_count: u32,
}

impl LearnedClauseExtractionBudget {
    /// Conservative profile-only default.
    pub const DEFAULT: Self = Self {
        max_candidates: DEFAULT_LEARNED_CLAUSE_MAX_CANDIDATES,
        max_literals_per_clause: DEFAULT_LEARNED_CLAUSE_MAX_LITERALS,
        min_profile_count: DEFAULT_LEARNED_CLAUSE_MIN_PROFILE_COUNT,
    };
}

impl Default for LearnedClauseExtractionBudget {
    fn default() -> Self {
        Self::DEFAULT
    }
}

/// Deterministic metadata for one learned clause.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LearnedClauseDescriptor {
    /// Descriptor schema version.
    pub version: u32,
    /// Lowering target admitted by this contract.
    pub target: LearnedClauseLoweringTarget,
    /// Profile-only evaluation mode; no native SAT dispatch is installed.
    pub mode: LearnedClauseEvaluationMode,
    /// Solver/proof visible clause ID.
    pub clause_id: u64,
    /// Stored LBD/glue at extraction time.
    pub lbd: u32,
    /// Profile counter at extraction time.
    pub profile_count: u32,
    /// Conservative liveness epoch at extraction time.
    pub deletion_epoch: u64,
    /// Proof metadata that made this descriptor admissible.
    pub proof_status: LearnedClauseProofStatus,
    /// Stable content fingerprint for cache/profile comparisons.
    pub fingerprint: u64,
    literal_codes: Box<[u32]>,
}

impl LearnedClauseDescriptor {
    /// Encoded literals in solver order.
    #[must_use]
    pub fn literal_codes(&self) -> &[u32] {
        &self.literal_codes
    }

    /// Number of literals in the descriptor.
    #[must_use]
    pub fn arity(&self) -> usize {
        self.literal_codes.len()
    }

    /// Conservative stale-descriptor check against the solver's current
    /// deletion/liveness epoch.
    #[must_use]
    pub fn is_live_at_epoch(&self, current_deletion_epoch: u64) -> bool {
        self.deletion_epoch == current_deletion_epoch
    }
}

/// Reason an otherwise scalar-safe clause was not extracted as a descriptor.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum LearnedClauseFallbackReason {
    /// Profile count is below [`LearnedClauseExtractionBudget::min_profile_count`].
    ProfileBelowThreshold,
    /// Proof mode is active but no live proof ID was available.
    ProofUnavailable,
    /// The profile-only extraction cap was exhausted.
    BudgetExhausted,
}

/// Scalar fallback record for an active learned clause.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct LearnedClauseFallback {
    /// Solver/proof visible clause ID.
    pub clause_id: u64,
    /// Why this active clause stays scalar-only.
    pub reason: LearnedClauseFallbackReason,
}

/// Reason a clause is unsupported by the descriptor contract.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum LearnedClauseRejectionReason {
    /// Input was not marked as a learned clause.
    NotLearned,
    /// Input was already deleted or garbage-marked.
    Deleted,
    /// Empty clauses are terminal conflicts, not profile candidates.
    EmptyClause,
    /// Unit clauses are handled directly by scalar SAT propagation.
    UnitClause,
    /// Clause exceeds the extraction literal bound.
    TooManyLiterals {
        /// Clause length.
        len: usize,
        /// Budgeted maximum.
        max: usize,
    },
    /// Two literals share the same encoded literal.
    DuplicateLiteral {
        /// Variable index that appeared more than once.
        var: u32,
    },
    /// The clause contains both polarities of a variable.
    TautologicalVariable {
        /// Variable index that appeared with both polarities.
        var: u32,
    },
}

/// Unsupported learned-clause extraction input.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct LearnedClauseRejection {
    /// Solver/proof visible clause ID.
    pub clause_id: u64,
    /// Why this input was rejected.
    pub reason: LearnedClauseRejectionReason,
}

/// Result of one profile-only extraction pass.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LearnedClauseExtraction {
    /// Descriptors selected by profile, bounded by the extraction budget.
    pub descriptors: Vec<LearnedClauseDescriptor>,
    /// Active learned clauses that remain scalar-only.
    pub fallbacks: Vec<LearnedClauseFallback>,
    /// Unsupported or unsafe inputs.
    pub rejections: Vec<LearnedClauseRejection>,
}

impl LearnedClauseExtraction {
    /// Returns `true` if the pass found no descriptors, fallbacks, or
    /// rejections.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.descriptors.is_empty() && self.fallbacks.is_empty() && self.rejections.is_empty()
    }
}

/// Extract deterministic learned-clause descriptors from solver snapshots.
///
/// The function is intentionally advisory: unsupported inputs are rejected,
/// proof-unsafe or cold inputs are reported as scalar fallbacks, and selected
/// descriptors carry [`LearnedClauseEvaluationMode::ProfileOnly`].
#[must_use]
pub fn extract_learned_clause_candidates(
    snapshots: &[LearnedClauseSnapshot<'_>],
    budget: LearnedClauseExtractionBudget,
) -> LearnedClauseExtraction {
    let mut descriptors = Vec::new();
    let mut fallbacks = Vec::new();
    let mut rejections = Vec::new();

    for snapshot in snapshots {
        match classify_snapshot(snapshot, budget) {
            SnapshotDecision::Descriptor(descriptor) => descriptors.push(descriptor),
            SnapshotDecision::Fallback(fallback) => fallbacks.push(fallback),
            SnapshotDecision::Rejection(rejection) => rejections.push(rejection),
        }
    }

    descriptors.sort_by(|a, b| {
        b.profile_count
            .cmp(&a.profile_count)
            .then_with(|| a.lbd.cmp(&b.lbd))
            .then_with(|| a.arity().cmp(&b.arity()))
            .then_with(|| a.clause_id.cmp(&b.clause_id))
            .then_with(|| a.fingerprint.cmp(&b.fingerprint))
    });

    if descriptors.len() > budget.max_candidates {
        for descriptor in descriptors.split_off(budget.max_candidates) {
            fallbacks.push(LearnedClauseFallback {
                clause_id: descriptor.clause_id,
                reason: LearnedClauseFallbackReason::BudgetExhausted,
            });
        }
    }

    fallbacks.sort_unstable();
    rejections.sort_unstable();

    LearnedClauseExtraction {
        descriptors,
        fallbacks,
        rejections,
    }
}

enum SnapshotDecision {
    Descriptor(LearnedClauseDescriptor),
    Fallback(LearnedClauseFallback),
    Rejection(LearnedClauseRejection),
}

fn classify_snapshot(
    snapshot: &LearnedClauseSnapshot<'_>,
    budget: LearnedClauseExtractionBudget,
) -> SnapshotDecision {
    if !snapshot.learned {
        return reject(snapshot, LearnedClauseRejectionReason::NotLearned);
    }
    if snapshot.deleted {
        return reject(snapshot, LearnedClauseRejectionReason::Deleted);
    }
    let len = snapshot.literals.len();
    if len == 0 {
        return reject(snapshot, LearnedClauseRejectionReason::EmptyClause);
    }
    if len == 1 {
        return reject(snapshot, LearnedClauseRejectionReason::UnitClause);
    }
    if len > budget.max_literals_per_clause {
        return reject(
            snapshot,
            LearnedClauseRejectionReason::TooManyLiterals {
                len,
                max: budget.max_literals_per_clause,
            },
        );
    }
    if let Some(reason) = repeated_var_rejection(snapshot.literals) {
        return reject(snapshot, reason);
    }
    if !snapshot.proof_status.is_profile_safe() {
        return fallback(snapshot, LearnedClauseFallbackReason::ProofUnavailable);
    }
    if snapshot.profile_count < budget.min_profile_count {
        return fallback(snapshot, LearnedClauseFallbackReason::ProfileBelowThreshold);
    }

    SnapshotDecision::Descriptor(descriptor_from_snapshot(snapshot))
}

fn reject(
    snapshot: &LearnedClauseSnapshot<'_>,
    reason: LearnedClauseRejectionReason,
) -> SnapshotDecision {
    SnapshotDecision::Rejection(LearnedClauseRejection {
        clause_id: snapshot.clause_id,
        reason,
    })
}

fn fallback(
    snapshot: &LearnedClauseSnapshot<'_>,
    reason: LearnedClauseFallbackReason,
) -> SnapshotDecision {
    SnapshotDecision::Fallback(LearnedClauseFallback {
        clause_id: snapshot.clause_id,
        reason,
    })
}

fn repeated_var_rejection(literals: &[Literal]) -> Option<LearnedClauseRejectionReason> {
    for (i, &left) in literals.iter().enumerate() {
        for &right in &literals[i + 1..] {
            if left.var() != right.var() {
                continue;
            }
            return Some(if left.code() == right.code() {
                LearnedClauseRejectionReason::DuplicateLiteral { var: left.var() }
            } else {
                LearnedClauseRejectionReason::TautologicalVariable { var: left.var() }
            });
        }
    }
    None
}

fn descriptor_from_snapshot(snapshot: &LearnedClauseSnapshot<'_>) -> LearnedClauseDescriptor {
    let literal_codes: Box<[u32]> = snapshot
        .literals
        .iter()
        .map(|lit| lit.code())
        .collect::<Vec<_>>()
        .into_boxed_slice();
    let fingerprint = descriptor_fingerprint(snapshot, &literal_codes);

    LearnedClauseDescriptor {
        version: LEARNED_CLAUSE_DESCRIPTOR_VERSION,
        target: LearnedClauseLoweringTarget::ExternalCodegenBackend,
        mode: LearnedClauseEvaluationMode::ProfileOnly,
        clause_id: snapshot.clause_id,
        lbd: snapshot.lbd,
        profile_count: snapshot.profile_count,
        deletion_epoch: snapshot.deletion_epoch,
        proof_status: snapshot.proof_status,
        fingerprint,
        literal_codes,
    }
}

fn descriptor_fingerprint(snapshot: &LearnedClauseSnapshot<'_>, literal_codes: &[u32]) -> u64 {
    let mut hash = FNV_OFFSET;
    fn mix(hash: &mut u64, bytes: &[u8]) {
        for byte in bytes {
            *hash ^= u64::from(*byte);
            *hash = hash.wrapping_mul(FNV_PRIME);
        }
    }

    mix(&mut hash, &LEARNED_CLAUSE_DESCRIPTOR_VERSION.to_le_bytes());
    mix(
        &mut hash,
        &[LearnedClauseLoweringTarget::ExternalCodegenBackend as u8],
    );
    mix(&mut hash, &[LearnedClauseEvaluationMode::ProfileOnly as u8]);
    mix(&mut hash, &snapshot.clause_id.to_le_bytes());
    mix(&mut hash, &snapshot.lbd.to_le_bytes());
    mix(&mut hash, &snapshot.profile_count.to_le_bytes());
    mix(&mut hash, &snapshot.deletion_epoch.to_le_bytes());
    mix(&mut hash, &[snapshot.proof_status.tag()]);
    mix(&mut hash, &snapshot.proof_status.id().to_le_bytes());
    for code in literal_codes {
        mix(&mut hash, &code.to_le_bytes());
    }
    hash
}

const FNV_OFFSET: u64 = 0xcbf2_9ce4_8422_2325;
const FNV_PRIME: u64 = 0x0000_0001_0000_01b3;

/// Truth value of a variable under a trail.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LitValue {
    /// Variable unassigned.
    Unassigned,
    /// Variable assigned to `true`.
    True,
    /// Variable assigned to `false`.
    False,
}

/// Minimal trail abstraction used by the scalar reference interpreter.
///
/// Future solver integration can adapt the real trail to this behavior. For
/// now it is a flat per-variable value array.
#[derive(Debug, Clone)]
pub struct Trail {
    values: Vec<LitValue>,
}

impl Trail {
    /// Create a trail with `num_vars` initially-unassigned variables.
    #[must_use]
    pub fn new(num_vars: usize) -> Self {
        Self {
            values: vec![LitValue::Unassigned; num_vars],
        }
    }

    /// Assign `var` to `value`.
    ///
    /// Extends storage if `var` exceeds the current capacity. No-op for
    /// [`LitValue::Unassigned`] except to resize capacity.
    pub fn assign(&mut self, var: u32, value: LitValue) {
        let idx = var as usize;
        if idx >= self.values.len() {
            self.values.resize(idx + 1, LitValue::Unassigned);
        }
        self.values[idx] = value;
    }

    /// Return the current value of a variable.
    #[must_use]
    pub fn value(&self, var: u32) -> LitValue {
        let idx = var as usize;
        if idx >= self.values.len() {
            LitValue::Unassigned
        } else {
            self.values[idx]
        }
    }

    /// Return the current value of a literal under this trail.
    #[must_use]
    pub fn literal_value(&self, lit: Literal) -> LitValue {
        match self.value(lit.var()) {
            LitValue::Unassigned => LitValue::Unassigned,
            LitValue::True => {
                if lit.is_positive() {
                    LitValue::True
                } else {
                    LitValue::False
                }
            }
            LitValue::False => {
                if lit.is_positive() {
                    LitValue::False
                } else {
                    LitValue::True
                }
            }
        }
    }
}

/// Opaque codegen context handed to [`emit_learned_clause`].
///
/// This is a reference-evaluator context only. It mints deterministic handle
/// IDs for unit tests and does not carry executable memory, backend state, or a
/// native dispatch table.
#[derive(Debug, Default)]
pub struct CodegenContext {
    next_id: u64,
}

impl CodegenContext {
    /// Create an empty context.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    fn mint_handle(&mut self) -> u64 {
        let id = self.next_id;
        self.next_id = self.next_id.wrapping_add(1);
        id
    }
}

// ---------------------------------------------------------------------------
// Public API
// ---------------------------------------------------------------------------

/// Result of evaluating a learned-clause propagator against a trail.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PropagatorResult {
    /// The clause became unit: the returned literal must be propagated.
    Unit(Literal),
    /// Every literal in the clause is falsified — conflict.
    Falsified,
    /// The clause is satisfied or has ≥2 unassigned literals; no propagation.
    NoOp,
}

/// Interpreted reference handle for a single learned clause.
///
/// Cheap to clone (shares the underlying scalar closure via `Arc`). This is a
/// local oracle for tests; it is not installed into SAT propagation.
#[derive(Clone)]
pub struct LearnedClausePropagator {
    /// Unique identifier minted by the [`CodegenContext`] that created this
    /// reference handle.
    id: u64,
    /// The original clause literals, retained for diagnostics, descriptor
    /// checks, and scalar-reference testing.
    clause: Arc<[Literal]>,
    /// Scalar interpreter.
    check_fn: Arc<dyn Fn(&Trail) -> PropagatorResult + Send + Sync>,
}

impl std::fmt::Debug for LearnedClausePropagator {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("LearnedClausePropagator")
            .field("id", &self.id)
            .field("clause_len", &self.clause.len())
            .finish_non_exhaustive()
    }
}

impl LearnedClausePropagator {
    /// Unique code-cache slot identifier for this propagator.
    #[must_use]
    pub fn id(&self) -> u64 {
        self.id
    }

    /// Number of literals in the underlying learned clause.
    #[must_use]
    pub fn arity(&self) -> usize {
        self.clause.len()
    }

    /// The literals of the learned clause this propagator was emitted for.
    #[must_use]
    pub fn clause(&self) -> &[Literal] {
        &self.clause
    }

    /// Evaluate this propagator against `trail`.
    ///
    /// Returns [`PropagatorResult::Unit`] if the clause has exactly one
    /// unassigned literal and every other literal is false,
    /// [`PropagatorResult::Falsified`] if every literal is false, and
    /// [`PropagatorResult::NoOp`] otherwise.
    #[must_use]
    pub fn check(&self, trail: &Trail) -> PropagatorResult {
        (self.check_fn)(trail)
    }
}

/// Emit a propagator for a learned clause.
///
/// # Reference semantics
///
/// Builds an interpreted reference handle (boxed closure) that implements the
/// watched-literal evaluation described on [`PropagatorResult`]. The returned
/// [`LearnedClausePropagator`] is immediately usable via
/// [`LearnedClausePropagator::check`].
///
/// The empty clause is treated as [`PropagatorResult::Falsified`] under every
/// trail (it is trivially UNSAT). The unit clause `[l]` returns
/// `PropagatorResult::Unit(l)` while `l` is unassigned and either
/// [`PropagatorResult::NoOp`] (if `l` is already satisfied) or
/// [`PropagatorResult::Falsified`] (if `l` is already falsified) afterwards.
///
/// This function does not compile BCP or install native dispatch. Use
/// [`extract_learned_clause_candidates`] for the metadata-only external code generation
/// candidate contract.
pub fn emit_learned_clause(
    clause: &[Literal],
    codegen_ctx: &mut CodegenContext,
) -> LearnedClausePropagator {
    let id = codegen_ctx.mint_handle();
    let clause: Arc<[Literal]> = Arc::from(clause.to_vec().into_boxed_slice());

    let check_fn: Arc<dyn Fn(&Trail) -> PropagatorResult + Send + Sync> = {
        let clause = Arc::clone(&clause);
        Arc::new(move |trail: &Trail| interpret_clause(&clause, trail))
    };

    LearnedClausePropagator {
        id,
        clause,
        check_fn,
    }
}

/// Interpreted reference implementation of the watched-literal propagator.
///
/// Exposed `pub(crate)` so [`crate::batch_recompile`] unit tests and descriptor
/// checks can call it directly.
pub(crate) fn interpret_clause(clause: &[Literal], trail: &Trail) -> PropagatorResult {
    if clause.is_empty() {
        // The empty clause is vacuously falsified.
        return PropagatorResult::Falsified;
    }

    let mut unassigned: Option<Literal> = None;
    let mut all_false = true;

    for &lit in clause {
        match trail.literal_value(lit) {
            LitValue::True => return PropagatorResult::NoOp,
            LitValue::False => {}
            LitValue::Unassigned => {
                all_false = false;
                if unassigned.is_some() {
                    // Two or more unassigned literals → no propagation.
                    return PropagatorResult::NoOp;
                }
                unassigned = Some(lit);
            }
        }
    }

    match (unassigned, all_false) {
        (Some(lit), _) => PropagatorResult::Unit(lit),
        (None, true) => PropagatorResult::Falsified,
        (None, false) => PropagatorResult::NoOp, // unreachable but defensive
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    fn pos(var: u32) -> Literal {
        Literal::new(var, true)
    }
    fn neg(var: u32) -> Literal {
        Literal::new(var, false)
    }

    fn hot_snapshot(
        clause_id: u64,
        literals: &[Literal],
        lbd: u32,
        profile_count: u32,
    ) -> LearnedClauseSnapshot<'_> {
        LearnedClauseSnapshot::new(clause_id, literals).with_profile(lbd, profile_count)
    }

    #[test]
    fn learned_clause_extraction_is_deterministic_and_profile_sorted() {
        const { assert!(!LEARNED_CLAUSE_NATIVE_DISPATCH_ENABLED) };

        let clause_a = [pos(1), neg(2), pos(3)];
        let clause_b = [pos(4), neg(5)];
        let clause_c = [neg(6), pos(7), neg(8)];
        let budget = LearnedClauseExtractionBudget {
            max_candidates: 8,
            max_literals_per_clause: 8,
            min_profile_count: 1,
        };

        let first = extract_learned_clause_candidates(
            &[
                hot_snapshot(30, &clause_a, 3, 7),
                hot_snapshot(10, &clause_b, 2, 7),
                hot_snapshot(20, &clause_c, 4, 11),
            ],
            budget,
        );
        let second = extract_learned_clause_candidates(
            &[
                hot_snapshot(20, &clause_c, 4, 11),
                hot_snapshot(10, &clause_b, 2, 7),
                hot_snapshot(30, &clause_a, 3, 7),
            ],
            budget,
        );

        assert_eq!(first, second);
        assert!(first.fallbacks.is_empty());
        assert!(first.rejections.is_empty());
        let ids: Vec<u64> = first.descriptors.iter().map(|d| d.clause_id).collect();
        assert_eq!(ids, vec![20, 10, 30]);

        let descriptor = &first.descriptors[0];
        assert_eq!(descriptor.version, LEARNED_CLAUSE_DESCRIPTOR_VERSION);
        assert_eq!(
            descriptor.target,
            LearnedClauseLoweringTarget::ExternalCodegenBackend
        );
        assert_eq!(descriptor.mode, LearnedClauseEvaluationMode::ProfileOnly);
        assert_eq!(
            descriptor.literal_codes(),
            &[neg(6).code(), pos(7).code(), neg(8).code()]
        );
        assert_ne!(descriptor.fingerprint, 0);
    }

    #[test]
    fn learned_clause_extraction_caps_candidates_with_scalar_fallback() {
        let clause_a = [pos(0), pos(1)];
        let clause_b = [pos(2), pos(3)];
        let clause_c = [pos(4), pos(5)];
        let budget = LearnedClauseExtractionBudget {
            max_candidates: 2,
            max_literals_per_clause: 8,
            min_profile_count: 1,
        };

        let extracted = extract_learned_clause_candidates(
            &[
                hot_snapshot(1, &clause_a, 2, 30),
                hot_snapshot(2, &clause_b, 2, 20),
                hot_snapshot(3, &clause_c, 2, 10),
            ],
            budget,
        );

        let ids: Vec<u64> = extracted
            .descriptors
            .iter()
            .map(|descriptor| descriptor.clause_id)
            .collect();
        assert_eq!(ids, vec![1, 2]);
        assert_eq!(
            extracted.fallbacks,
            vec![LearnedClauseFallback {
                clause_id: 3,
                reason: LearnedClauseFallbackReason::BudgetExhausted,
            }]
        );
        assert!(extracted.rejections.is_empty());
    }

    #[test]
    fn learned_clause_extraction_rejects_deleted_and_tracks_epoch() {
        let live_clause = [pos(0), neg(1)];
        let deleted_clause = [pos(2), neg(3)];
        let live = hot_snapshot(10, &live_clause, 2, 5).with_deletion_state(false, 42);
        let deleted = hot_snapshot(11, &deleted_clause, 2, 50).with_deletion_state(true, 43);

        let extracted = extract_learned_clause_candidates(
            &[deleted, live],
            LearnedClauseExtractionBudget::default(),
        );

        assert_eq!(extracted.descriptors.len(), 1);
        let descriptor = &extracted.descriptors[0];
        assert_eq!(descriptor.clause_id, 10);
        assert!(descriptor.is_live_at_epoch(42));
        assert!(!descriptor.is_live_at_epoch(43));
        assert_eq!(
            extracted.rejections,
            vec![LearnedClauseRejection {
                clause_id: 11,
                reason: LearnedClauseRejectionReason::Deleted,
            }]
        );
    }

    #[test]
    fn learned_clause_extraction_uses_proof_safe_fallback() {
        let proof_safe_clause = [pos(0), neg(1)];
        let reserved_clause = [pos(2), neg(3)];
        let missing_proof_clause = [pos(4), neg(5)];

        let proof_safe = hot_snapshot(1, &proof_safe_clause, 2, 9)
            .with_proof_status(LearnedClauseProofStatus::ProofTracked { proof_id: 100 });
        let reserved = hot_snapshot(2, &reserved_clause, 3, 8)
            .with_proof_status(LearnedClauseProofStatus::ReservedForBackward { proof_id: 200 });
        let missing = hot_snapshot(3, &missing_proof_clause, 2, 100)
            .with_proof_status(LearnedClauseProofStatus::Missing);

        let extracted = extract_learned_clause_candidates(
            &[missing, reserved, proof_safe],
            LearnedClauseExtractionBudget::default(),
        );

        let ids: Vec<u64> = extracted
            .descriptors
            .iter()
            .map(|descriptor| descriptor.clause_id)
            .collect();
        assert_eq!(ids, vec![1, 2]);
        assert_eq!(
            extracted.fallbacks,
            vec![LearnedClauseFallback {
                clause_id: 3,
                reason: LearnedClauseFallbackReason::ProofUnavailable,
            }]
        );
        assert!(extracted.rejections.is_empty());
    }

    #[test]
    fn learned_clause_extraction_rejects_unsupported_clauses() {
        let non_learned_clause = [pos(0), neg(1)];
        let empty_clause: [Literal; 0] = [];
        let unit_clause = [pos(2)];
        let too_long_clause = [pos(3), pos(4), pos(5), pos(6)];
        let duplicate_clause = [pos(7), pos(7)];
        let tautological_clause = [pos(8), neg(8)];
        let budget = LearnedClauseExtractionBudget {
            max_candidates: 8,
            max_literals_per_clause: 3,
            min_profile_count: 1,
        };

        let mut non_learned = hot_snapshot(1, &non_learned_clause, 2, 10);
        non_learned.learned = false;

        let extracted = extract_learned_clause_candidates(
            &[
                non_learned,
                hot_snapshot(2, &empty_clause, 1, 10),
                hot_snapshot(3, &unit_clause, 1, 10),
                hot_snapshot(4, &too_long_clause, 2, 10),
                hot_snapshot(5, &duplicate_clause, 2, 10),
                hot_snapshot(6, &tautological_clause, 2, 10),
            ],
            budget,
        );

        assert!(extracted.descriptors.is_empty());
        assert!(extracted.fallbacks.is_empty());
        assert_eq!(
            extracted.rejections,
            vec![
                LearnedClauseRejection {
                    clause_id: 1,
                    reason: LearnedClauseRejectionReason::NotLearned,
                },
                LearnedClauseRejection {
                    clause_id: 2,
                    reason: LearnedClauseRejectionReason::EmptyClause,
                },
                LearnedClauseRejection {
                    clause_id: 3,
                    reason: LearnedClauseRejectionReason::UnitClause,
                },
                LearnedClauseRejection {
                    clause_id: 4,
                    reason: LearnedClauseRejectionReason::TooManyLiterals { len: 4, max: 3 },
                },
                LearnedClauseRejection {
                    clause_id: 5,
                    reason: LearnedClauseRejectionReason::DuplicateLiteral { var: 7 },
                },
                LearnedClauseRejection {
                    clause_id: 6,
                    reason: LearnedClauseRejectionReason::TautologicalVariable { var: 8 },
                },
            ]
        );
    }

    #[test]
    fn literal_encoding_roundtrip() {
        let l = Literal::new(42, true);
        assert_eq!(l.var(), 42);
        assert!(l.is_positive());
        assert_eq!(l.code(), 42 << 1);

        let n = Literal::new(42, false);
        assert_eq!(n.var(), 42);
        assert!(!n.is_positive());
        assert_eq!(n.code(), (42 << 1) | 1);
    }

    #[test]
    fn trail_literal_value_handles_polarity() {
        let mut trail = Trail::new(4);
        trail.assign(0, LitValue::True);
        trail.assign(1, LitValue::False);

        assert_eq!(trail.literal_value(pos(0)), LitValue::True);
        assert_eq!(trail.literal_value(neg(0)), LitValue::False);
        assert_eq!(trail.literal_value(pos(1)), LitValue::False);
        assert_eq!(trail.literal_value(neg(1)), LitValue::True);
        assert_eq!(trail.literal_value(pos(2)), LitValue::Unassigned);
    }

    #[test]
    fn trail_extends_on_out_of_range_assign() {
        let mut trail = Trail::new(2);
        trail.assign(10, LitValue::True);
        assert_eq!(trail.value(10), LitValue::True);
        assert_eq!(trail.value(5), LitValue::Unassigned);
    }

    #[test]
    fn empty_clause_is_falsified() {
        let mut cx = CodegenContext::new();
        let p = emit_learned_clause(&[], &mut cx);
        let trail = Trail::new(1);
        assert_eq!(p.check(&trail), PropagatorResult::Falsified);
        assert_eq!(p.arity(), 0);
    }

    #[test]
    fn unit_clause_propagates_when_unassigned() {
        let mut cx = CodegenContext::new();
        let p = emit_learned_clause(&[pos(0)], &mut cx);
        let trail = Trail::new(1);
        assert_eq!(p.check(&trail), PropagatorResult::Unit(pos(0)));
    }

    #[test]
    fn unit_clause_noop_when_satisfied() {
        let mut cx = CodegenContext::new();
        let p = emit_learned_clause(&[pos(0)], &mut cx);
        let mut trail = Trail::new(1);
        trail.assign(0, LitValue::True);
        assert_eq!(p.check(&trail), PropagatorResult::NoOp);
    }

    #[test]
    fn unit_clause_falsified_when_false() {
        let mut cx = CodegenContext::new();
        let p = emit_learned_clause(&[pos(0)], &mut cx);
        let mut trail = Trail::new(1);
        trail.assign(0, LitValue::False);
        assert_eq!(p.check(&trail), PropagatorResult::Falsified);
    }

    #[test]
    fn binary_clause_noop_on_two_unassigned() {
        let mut cx = CodegenContext::new();
        let p = emit_learned_clause(&[pos(0), neg(1)], &mut cx);
        let trail = Trail::new(2);
        assert_eq!(p.check(&trail), PropagatorResult::NoOp);
    }

    #[test]
    fn binary_clause_unit_on_one_false_one_unassigned() {
        // Clause (x0 ∨ ¬x1). Assign x0 = false → clause is unit on ¬x1.
        let mut cx = CodegenContext::new();
        let p = emit_learned_clause(&[pos(0), neg(1)], &mut cx);
        let mut trail = Trail::new(2);
        trail.assign(0, LitValue::False);
        assert_eq!(p.check(&trail), PropagatorResult::Unit(neg(1)));
    }

    #[test]
    fn binary_clause_falsified_on_both_false() {
        let mut cx = CodegenContext::new();
        let p = emit_learned_clause(&[pos(0), neg(1)], &mut cx);
        let mut trail = Trail::new(2);
        trail.assign(0, LitValue::False);
        trail.assign(1, LitValue::True); // ¬x1 is False
        assert_eq!(p.check(&trail), PropagatorResult::Falsified);
    }

    #[test]
    fn ternary_clause_transitions() {
        // Walk a learned clause (x0 ∨ x1 ∨ x2) through every transition we care
        // about: NoOp (all unassigned), NoOp (one true), Unit, Falsified.
        let mut cx = CodegenContext::new();
        let p = emit_learned_clause(&[pos(0), pos(1), pos(2)], &mut cx);

        let mut trail = Trail::new(3);
        assert_eq!(p.check(&trail), PropagatorResult::NoOp);

        trail.assign(0, LitValue::False);
        assert_eq!(p.check(&trail), PropagatorResult::NoOp); // still 2 unassigned

        trail.assign(1, LitValue::False);
        assert_eq!(p.check(&trail), PropagatorResult::Unit(pos(2)));

        trail.assign(2, LitValue::False);
        assert_eq!(p.check(&trail), PropagatorResult::Falsified);

        // NoOp if any literal is true, even if others are false.
        let mut trail2 = Trail::new(3);
        trail2.assign(0, LitValue::False);
        trail2.assign(1, LitValue::True);
        trail2.assign(2, LitValue::False);
        assert_eq!(p.check(&trail2), PropagatorResult::NoOp);
    }

    #[test]
    fn codegen_context_mints_unique_ids() {
        let mut cx = CodegenContext::new();
        let a = emit_learned_clause(&[pos(0)], &mut cx);
        let b = emit_learned_clause(&[pos(1)], &mut cx);
        let c = emit_learned_clause(&[pos(2)], &mut cx);
        assert_ne!(a.id(), b.id());
        assert_ne!(b.id(), c.id());
        assert_ne!(a.id(), c.id());
    }

    #[test]
    fn propagator_retains_clause_for_reference_checks() {
        let mut cx = CodegenContext::new();
        let lits = [pos(0), neg(1), pos(2)];
        let p = emit_learned_clause(&lits, &mut cx);
        assert_eq!(p.clause(), lits);
        assert_eq!(p.arity(), 3);
    }

    #[test]
    fn propagator_is_send_sync_clone() {
        // Compile-time assertion that the reference handle remains cheap to
        // share across tests and profile collection helpers.
        fn assert_traits<T: Send + Sync + Clone>() {}
        assert_traits::<LearnedClausePropagator>();
    }

    #[test]
    fn interpreted_matches_direct_spec_on_varied_clauses() {
        // Cross-check interpret_clause vs the propagator entry point on a
        // handful of trails.
        let clauses: &[&[Literal]] = &[
            &[pos(0)],
            &[neg(0)],
            &[pos(0), pos(1)],
            &[neg(0), pos(1), neg(2)],
            &[pos(0), pos(0)], // the reference evaluator tolerates duplicates
        ];

        for clause in clauses {
            let mut cx = CodegenContext::new();
            let p = emit_learned_clause(clause, &mut cx);
            for bits in 0u32..(1 << 4) {
                let mut trail = Trail::new(3);
                for v in 0..3 {
                    let two = (bits >> (2 * v)) & 0b11;
                    let val = match two {
                        0 => LitValue::Unassigned,
                        1 => LitValue::True,
                        _ => LitValue::False,
                    };
                    trail.assign(v, val);
                }
                let expected = interpret_clause(clause, &trail);
                let actual = p.check(&trail);
                assert_eq!(
                    expected, actual,
                    "clause {clause:?} bits {bits:#b}: expected {expected:?}, got {actual:?}"
                );
            }
        }
    }
}
