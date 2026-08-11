// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact block-angular route for bounded integral conservation chains.
//!
//! The recognizer in this module is deliberately formulation-based.  It does
//! not inspect model, row, or column names.  It accepts a set of nonnegative
//! integral flow chains coupled only by nonnegative covering rows.  A source
//! block has one bounded capacity row over its chain roots; an initial-stock
//! block has one fixed-inflow conservation row.  Every other local row must be
//! a unit-coefficient conservation equality, and every active column and row
//! must be consumed by that interpretation.
//!
//! Once admitted, each chain extreme point sends all of its integral inflow to
//! one exit.  Source-block pricing therefore consists of one cheapest exit per
//! chain followed by an exact bounded-knapsack minimization over the capacity
//! row.  Production uses a meet-in-the-middle oracle when the row has an exact
//! primitive `i128` representation; public certificate replay deliberately
//! retains the independent exhaustive oracle.  This is the standard
//! Dantzig--Wolfe pricing oracle for the recognized integer hull.  The
//! production solve uses a restricted master, but no answer rests on it: an
//! optimum is returned only when an exact source point attains the independently
//! replayed Lagrangian lower bound.

use std::collections::{BTreeSet, HashMap};
use std::mem::size_of;
use std::sync::Arc;
use std::time::{Duration, Instant};

use num_bigint::BigInt;
use num_integer::Integer as _;
use num_rational::BigRational;
use num_traits::{One, Signed, ToPrimitive, Zero};

use crate::model::exact;
use crate::{BoundSide, Col, ColKind, FactRef, LpSession, Model, Outcome, Row, Sense, SolveOpts};

const MAX_MASTER_ROWS: usize = 64;
const MAX_BLOCKS: usize = 128;
const MAX_CHAINS_PER_BLOCK: usize = 8;
const MAX_CHAIN_LENGTH: usize = 32;
const MAX_CAPACITY_SUPPORT: usize = 8;
const MAX_CAPACITY_BOX: usize = 100_000;
const MAX_FEASIBLE_TUPLES: usize = 20_000;
const MAX_CANONICAL_TUPLE_SETS: usize = 64;
const MAX_COLUMN_GENERATION_ROUNDS: usize = 256;
const MAX_RESTRICTED_COLUMNS: usize = 20_000;
const MAX_MODEL_COLS: usize = 20_000;
const MAX_MODEL_ROWS: usize = 8_192;
const MAX_MODEL_TERMS: usize = 100_000;
/// Exact-value ceiling shared by recognition, solving, replay, and the public
/// certificate parser.  The parser must enforce this before constructing a
/// `BigInt`; otherwise an artifact rejected here can still consume unbounded
/// allocation and gcd work on its way to this verifier.
pub(crate) const MAX_RATIONAL_BITS: usize = 4_096;
/// A larger common denominator cannot fit a useful exact RMP inside the
/// route-local memory box.  Cap the preflight accumulator itself so inspecting
/// adversarial pairwise-coprime side-store values cannot become the allocation
/// the preflight was meant to prevent.
const MAX_RMP_COMMON_DENOMINATOR_BITS: u64 = (MAX_MASTER_ROWS * MAX_RATIONAL_BITS) as u64;
// Production remains deliberately small: a speculative decline must not take
// a material share of the native solver's memory.  Explicit production caller
// budgets can only reduce this default.  Diagnostics may probe larger bounded
// classes so a memory decline can be separated from the next limiting stage.
const DEFAULT_ROUTE_MEMORY: usize = 64 << 20;
const MAX_DIAGNOSTIC_ROUTE_MEMORY: usize = 256 << 20;
const ROUTE_MEMORY_PARTS: usize = 2;
const ROUTE_METADATA_RESERVE: usize = 1 << 20;
const PROCESS_MEMORY_PERCENT: usize = 90;
const ROUTE_WALL_CAP: Duration = Duration::from_secs(2);
/// Recognition is speculative until every source row and column has been
/// consumed by the decomposition. Keep that pre-verdict tax small even for an
/// un-deadlined caller; an admitted model may use the remainder of the normal
/// route slice for column generation and exact replay.
const RECOGNITION_WALL_CAP: Duration = Duration::from_millis(50);
const REPLAY_WALL_CAP: Duration = Duration::from_secs(2);
/// Deterministic second line of defence behind the wall deadline.  The route
/// has several individually bounded loops (matrix census, zero propagation,
/// tuple enumeration, column generation, and certificate re-pricing); this
/// cap bounds their *sum*, so a public replay cannot concatenate many legal
/// local maxima into unbounded work.
const MAX_ROUTE_TERM_WORK: usize = 64_000_000;
const MAX_ROUTE_ROUND_WORK: usize = 1_000_000;
/// Cheap tuple/matrix visits between production wall-clock polls.  Logical
/// work is still charged on every visit; only the `Instant::now()` syscall is
/// amortized.  Exact-rational outer loops use the tighter round stride below.
const WALL_TERM_POLL_STRIDE: usize = 1_024;
const WALL_ROUND_POLL_STRIDE: usize = 32;
/// Route-local bytes charged between full RSS/physical-footprint polls.  Every
/// charge still checks the exact local ledger and the allocator's syscall-free
/// live-byte counter.  One MiB is also the route's metadata reserve, so every
/// material stage reaches a full process-envelope checkpoint.
const PROCESS_MEMORY_POLL_STRIDE: usize = 1 << 20;

/// Model-bound Lagrangian proof of an integral block-angular optimum.
///
/// The block minimizers are proposals, not trusted summaries.  Verification
/// recognizes the source formulation again, exhaustively re-prices every
/// bounded capacity tuple and chain exit, and requires their exact lower bound
/// to equal `value`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BlockAngularOptimalityCertificate {
    value: BigRational,
    master_multipliers: Vec<(u32, BigRational)>,
    minimizers: Vec<CertifiedBlockPattern>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum CertifiedBlockPattern {
    Source { amounts: Vec<i64>, exits: Vec<u8> },
    Initial { exit: u8 },
}

/// A conclusive result from the exact route.  The only shipped verdict is an
/// optimum with a model-bound artifact; all other states decline to native
/// branch-and-bound.
pub(crate) struct BlockAngularDecision {
    pub(crate) value: BigRational,
    pub(crate) model_values: Vec<BigRational>,
    pub(crate) certificate: BlockAngularOptimalityCertificate,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Decline {
    NotApplicable,
    Deadline,
    Memory,
    Resource,
    Arithmetic,
    Structure,
    Master,
    FractionalPrimal,
    Verification,
}

impl Decline {
    const fn token(self) -> &'static str {
        match self {
            Self::NotApplicable => "not-applicable",
            Self::Deadline => "deadline",
            Self::Memory => "memory",
            Self::Resource => "resource",
            Self::Arithmetic => "arithmetic",
            Self::Structure => "structure",
            Self::Master => "master",
            Self::FractionalPrimal => "fractional-primal",
            Self::Verification => "verification",
        }
    }
}

#[derive(Clone)]
struct Chain {
    root: Option<u32>,
    states: Vec<u32>,
    exits: Vec<u32>,
    quantity: Option<i64>,
    choices: Vec<ChainChoice>,
}

#[derive(Clone)]
struct ChainChoice {
    columns: Vec<u32>,
    cost_per_unit: BigRational,
    master_per_unit: Vec<(usize, BigRational)>,
}

#[derive(Clone)]
struct SourceBlock {
    chains: Vec<Chain>,
    tuples: Arc<[Vec<i64>]>,
    exact_domain: Option<Arc<ExactCapacityDomain>>,
}

/// Complete identity of the bounded integer half-space used by the fast tuple
/// enumerator.  `integral_capacity_row` has already cleared denominators and
/// divided by the gcd, so equality here means the two domains are exactly the
/// same inequality over exactly the same coordinate boxes.
#[derive(Clone, Debug, PartialEq, Eq)]
struct CapacityDomainSignature {
    maxima: Vec<i64>,
    weights: Vec<i128>,
    rhs: i128,
}

/// One side of a balanced exact capacity-domain split.  Values live inline so
/// a shared domain has one bounded allocation rather than one allocation per
/// partial assignment.  Only `width` leading entries are meaningful.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct CapacityHalfAssignment {
    activity: i128,
    values: [i64; MAX_CAPACITY_SUPPORT],
}

/// Immutable production pricing advice shared by source blocks with the same
/// primitive capacity domain.  It grants no proof authority: certificate
/// replay does not construct or consult this object.
#[derive(Debug)]
struct ExactCapacityDomain {
    signature: CapacityDomainSignature,
    mitm: Option<MitmCapacityAssignments>,
}

#[derive(Debug)]
struct MitmCapacityAssignments {
    split: usize,
    left: Vec<CapacityHalfAssignment>,
    right: Vec<CapacityHalfAssignment>,
}

struct PreparedCapacityDomain {
    maxima: Vec<i64>,
    integral: Option<(Vec<i128>, i128)>,
    storage_bytes: usize,
}

#[derive(Default)]
struct TupleSetCache {
    canonical: Vec<Arc<[Vec<i64>]>>,
    exact_domains: Vec<ExactCapacityDomainCacheEntry>,
}

struct ExactCapacityDomainCacheEntry {
    domain: Arc<ExactCapacityDomain>,
    tuples: Arc<[Vec<i64>]>,
}

#[derive(Clone)]
struct InitialBlock {
    chain: Chain,
}

#[derive(Clone)]
enum Block {
    Source(SourceBlock),
    Initial(InitialBlock),
}

struct Plan {
    fixed_zero: Vec<bool>,
    master_rows: Vec<u32>,
    master_rhs: Vec<BigRational>,
    blocks: Vec<Block>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum Pattern {
    Source { amounts: Vec<i64>, exits: Vec<u8> },
    Initial { exit: u8 },
}

struct PricedPattern {
    pattern: Pattern,
    reduced_without_convexity: BigRational,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum MasterPhase {
    Feasibility,
    Objective,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum MasterArithmetic {
    Advice,
    Exact,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum PricingPreparation {
    ProductionMitm,
    ExhaustiveReplay,
}

struct RestrictedMasterResult {
    value: BigRational,
    values: Vec<BigRational>,
    cover_duals: Vec<BigRational>,
    convexity_duals: Vec<BigRational>,
    column_map: Vec<(usize, usize)>,
    artificial_range: std::ops::Range<usize>,
}

struct MemoryMeter {
    used: usize,
    limit: usize,
    enforce_process_limit: bool,
    process_poll_remaining: usize,
    #[cfg(test)]
    full_process_polls: usize,
}

/// Cumulative deterministic work and wall control shared by one complete
/// production attempt or public certificate replay.
///
/// `terms` charges visits to matrix/pattern/tuple entries; `rounds` charges
/// outer fixed-point, component, and column-generation passes.  Both counters
/// are checked arithmetically before doing the requested work.  Deadline
/// checks live here as well, which makes every charged inner construction loop
/// pre-emptible instead of relying on a later solver call to notice expiry.
struct WorkMeter {
    deadline: Option<Instant>,
    terms: usize,
    rounds: usize,
    term_poll_remaining: usize,
    round_poll_remaining: usize,
    #[cfg(test)]
    test_deadline_after: Option<usize>,
    #[cfg(test)]
    wall_polls: std::cell::Cell<usize>,
}

impl WorkMeter {
    fn new(deadline: Option<Instant>) -> Self {
        Self {
            deadline,
            terms: 0,
            rounds: 0,
            term_poll_remaining: WALL_TERM_POLL_STRIDE,
            round_poll_remaining: WALL_ROUND_POLL_STRIDE,
            #[cfg(test)]
            test_deadline_after: None,
            #[cfg(test)]
            wall_polls: std::cell::Cell::new(0),
        }
    }

    #[cfg(test)]
    fn with_test_deadline_after(deadline_after: usize) -> Self {
        Self {
            deadline: None,
            terms: 0,
            rounds: 0,
            term_poll_remaining: WALL_TERM_POLL_STRIDE,
            round_poll_remaining: WALL_ROUND_POLL_STRIDE,
            test_deadline_after: Some(deadline_after),
            wall_polls: std::cell::Cell::new(0),
        }
    }

    fn test_checkpoint(&self) -> Result<(), Decline> {
        #[cfg(test)]
        if self
            .test_deadline_after
            .is_some_and(|limit| self.terms.saturating_add(self.rounds) >= limit)
        {
            return Err(Decline::Deadline);
        }
        Ok(())
    }

    fn wall_checkpoint(&self) -> Result<(), Decline> {
        if self.deadline.is_none() {
            return Ok(());
        }
        #[cfg(test)]
        self.wall_polls.set(self.wall_polls.get().saturating_add(1));
        if expired(self.deadline) {
            Err(Decline::Deadline)
        } else {
            Ok(())
        }
    }

    fn checkpoint(&self) -> Result<(), Decline> {
        self.test_checkpoint()?;
        self.wall_checkpoint()
    }

    fn poll_boundary_reached(remaining: &mut usize, charged: usize, stride: usize) -> bool {
        if charged == 0 {
            return false;
        }
        if charged < *remaining {
            *remaining -= charged;
            return false;
        }
        let past_boundary = charged - *remaining;
        let residue = past_boundary % stride;
        *remaining = if residue == 0 {
            stride
        } else {
            stride - residue
        };
        true
    }

    fn charge_terms(&mut self, count: usize) -> Result<(), Decline> {
        self.terms = self.terms.checked_add(count).ok_or(Decline::Resource)?;
        if self.terms > MAX_ROUTE_TERM_WORK {
            return Err(Decline::Resource);
        }
        self.test_checkpoint()?;
        if self.deadline.is_some()
            && Self::poll_boundary_reached(
                &mut self.term_poll_remaining,
                count,
                WALL_TERM_POLL_STRIDE,
            )
        {
            self.wall_checkpoint()?;
        }
        Ok(())
    }

    fn charge_round(&mut self) -> Result<(), Decline> {
        self.rounds = self.rounds.checked_add(1).ok_or(Decline::Resource)?;
        if self.rounds > MAX_ROUTE_ROUND_WORK {
            return Err(Decline::Resource);
        }
        self.test_checkpoint()?;
        if self.deadline.is_some()
            && Self::poll_boundary_reached(
                &mut self.round_poll_remaining,
                1,
                WALL_ROUND_POLL_STRIDE,
            )
        {
            self.wall_checkpoint()?;
        }
        Ok(())
    }
}

impl MemoryMeter {
    fn new(caller_limit: Option<usize>, enforce_process_limit: bool) -> Result<Self, Decline> {
        if enforce_process_limit && process_memory_exceeded() {
            return Err(Decline::Memory);
        }
        let process_limit = ay_sys::get_process_memory_limit();
        let process_remaining = if !enforce_process_limit || process_limit == 0 {
            usize::MAX
        } else {
            let current = ay_sys::current_live_bytes().max(ay_sys::current_footprint_bytes());
            process_limit
                .saturating_mul(PROCESS_MEMORY_PERCENT)
                .checked_div(100)
                .unwrap_or(0)
                .saturating_sub(current)
        };
        let limit = caller_limit
            .unwrap_or(DEFAULT_ROUTE_MEMORY)
            .min(MAX_DIAGNOSTIC_ROUTE_MEMORY)
            .min(process_remaining)
            .checked_div(ROUTE_MEMORY_PARTS)
            .unwrap_or(0);
        if limit == 0 {
            return Err(Decline::Memory);
        }
        Ok(Self {
            used: 0,
            limit,
            enforce_process_limit,
            process_poll_remaining: PROCESS_MEMORY_POLL_STRIDE,
            #[cfg(test)]
            full_process_polls: 0,
        })
    }

    fn charge(&mut self, bytes: usize) -> Result<(), Decline> {
        let next = self.used.checked_add(bytes).ok_or(Decline::Memory)?;
        if next > self.limit {
            return Err(Decline::Memory);
        }
        self.used = next;
        if !self.enforce_process_limit {
            return Ok(());
        }
        // This allocator-backed signal is exact and syscall-free in the AY
        // binaries, so retain it at every local allocation checkpoint.
        if ay_sys::live_bytes_exceeded_at_percent(PROCESS_MEMORY_PERCENT) {
            return Err(Decline::Memory);
        }
        // The hard-limit test hook is intentionally observed on every charge;
        // production pays only the batched full-footprint poll below.
        #[cfg(test)]
        if ay_sys::process_memory_exceeded() {
            return Err(Decline::Memory);
        }
        if WorkMeter::poll_boundary_reached(
            &mut self.process_poll_remaining,
            bytes,
            PROCESS_MEMORY_POLL_STRIDE,
        ) {
            #[cfg(test)]
            {
                self.full_process_polls = self.full_process_polls.saturating_add(1);
            }
            if process_memory_exceeded() {
                return Err(Decline::Memory);
            }
        }
        Ok(())
    }

    fn release(&mut self, bytes: usize) {
        self.used = self.used.saturating_sub(bytes);
    }

    fn remaining(&self) -> usize {
        self.limit.saturating_sub(self.used)
    }
}

fn process_memory_exceeded() -> bool {
    let exceeded = ay_sys::process_memory_exceeded_at_percent(PROCESS_MEMORY_PERCENT);
    #[cfg(test)]
    let exceeded = exceeded || ay_sys::process_memory_exceeded();
    exceeded
}

fn route_memory_limit(caller_limit: Option<usize>) -> usize {
    caller_limit
        .unwrap_or(DEFAULT_ROUTE_MEMORY)
        .min(DEFAULT_ROUTE_MEMORY)
}

fn expired(deadline: Option<Instant>) -> bool {
    deadline.is_some_and(|limit| Instant::now() >= limit)
}

/// Give a speculative route at most one tenth of a finite caller budget, and
/// never more than the fixed cap. A declined route therefore leaves at least
/// nine tenths of the original wall for native branch-and-bound.
fn route_deadlines(outer: Option<Instant>) -> Option<(Instant, Instant)> {
    let now = Instant::now();
    let slice = outer.map_or(ROUTE_WALL_CAP, |value| {
        value.saturating_duration_since(now) / 10
    });
    let route = now.checked_add(slice.min(ROUTE_WALL_CAP))?;
    let route = outer.map_or(route, |value| value.min(route));
    if route <= now {
        return None;
    }
    let recognition = now
        .checked_add(RECOGNITION_WALL_CAP)
        .map_or(route, |value| value.min(route));
    Some((recognition, route))
}

fn replay_deadline() -> Option<Instant> {
    Instant::now().checked_add(REPLAY_WALL_CAP)
}

fn rational_within_cap(value: &BigRational) -> bool {
    value.numer().bits() <= MAX_RATIONAL_BITS as u64
        && value.denom().bits() <= MAX_RATIONAL_BITS as u64
}

/// Conservative heap payload for a `BigInt` clone. `num-bigint` stores limbs
/// in a `Vec`; two words per logical limb plus allocator metadata deliberately
/// overestimates both 32- and 64-bit limb builds and spare capacity.
fn integer_payload_bytes(bits: u64) -> Result<usize, Decline> {
    let limb_bits = usize::BITS as u64;
    let limbs = usize::try_from(bits.div_ceil(limb_bits)).map_err(|_| Decline::Memory)?;
    limbs
        .checked_mul(size_of::<usize>())
        .and_then(|bytes| bytes.checked_mul(2))
        .and_then(|bytes| bytes.checked_add(2 * size_of::<usize>()))
        .ok_or(Decline::Memory)
}

fn rational_payload_bytes(value: &BigRational) -> Result<usize, Decline> {
    integer_payload_bytes(value.numer().bits())?
        .checked_add(integer_payload_bytes(value.denom().bits())?)
        .ok_or(Decline::Memory)
}

fn rational_storage_bytes(value: &BigRational) -> Result<usize, Decline> {
    size_of::<BigRational>()
        .checked_add(rational_payload_bytes(value)?)
        .ok_or(Decline::Memory)
}

fn max_rational_storage_bytes(bits: usize) -> Result<usize, Decline> {
    size_of::<BigRational>()
        .checked_add(
            integer_payload_bytes(bits as u64)?
                .checked_mul(2)
                .ok_or(Decline::Memory)?,
        )
        .ok_or(Decline::Memory)
}

/// Conservative footprint of one `ExactLp` tableau term in its heap-backed
/// representation: the `(variable, Rational)` cell, the boxed BigRational,
/// its two integer payloads, and allocator metadata for the box itself.
fn max_exact_tableau_cell_bytes(bits: usize) -> Result<usize, Decline> {
    let integer = integer_payload_bytes(bits as u64)?;
    size_of::<(u32, ay_lra::rational::Rational)>()
        .checked_add(size_of::<BigRational>())
        .and_then(|bytes| bytes.checked_add(2 * size_of::<usize>()))
        .and_then(|bytes| {
            integer
                .checked_mul(2)
                .and_then(|payload| bytes.checked_add(payload))
        })
        .ok_or(Decline::Memory)
}

/// Common-denominator shape for one family of exact inputs.
///
/// Keeping the actual (capped) LCM is important for ordinary decimal/dyadic
/// models: summing every denominator's bit width would treat thousands of
/// identical powers of two as pairwise coprime.  Conversely, a maximum
/// per-entry width is unsound for unrelated denominators, whose product can
/// appear in a basis determinant.
struct RationalScale {
    common_denominator: BigInt,
    max_numerator_bits: u64,
}

impl RationalScale {
    fn new() -> Self {
        Self {
            common_denominator: BigInt::one(),
            max_numerator_bits: 1,
        }
    }

    fn observe(&mut self, value: &BigRational) -> Result<(), Decline> {
        if !rational_within_cap(value) {
            return Err(Decline::Resource);
        }
        self.max_numerator_bits = self.max_numerator_bits.max(value.numer().bits());
        extend_common_denominator(&mut self.common_denominator, value.denom())
    }

    fn denominator_bits(&self) -> Result<usize, Decline> {
        usize::try_from(self.common_denominator.bits()).map_err(|_| Decline::Memory)
    }

    /// Bit bound for an input numerator after lifting it to this scale's
    /// common denominator.  Deliberately retains a spare bit instead of trying
    /// to recover the entry's own denominator here.
    fn scaled_numerator_bits(&self) -> Result<usize, Decline> {
        usize::try_from(self.max_numerator_bits)
            .map_err(|_| Decline::Memory)?
            .checked_add(self.denominator_bits()?)
            .and_then(|bits| bits.checked_add(1))
            .ok_or(Decline::Memory)
    }
}

fn extend_common_denominator(common: &mut BigInt, denominator: &BigInt) -> Result<(), Decline> {
    if denominator.is_one() {
        return Ok(());
    }
    if denominator.bits() > MAX_RMP_COMMON_DENOMINATOR_BITS {
        return Err(Decline::Memory);
    }
    let divisor = common.gcd(denominator);
    let factor = denominator / &divisor;
    if factor.is_one() {
        return Ok(());
    }
    // `bits(a*b) >= bits(a) + bits(b) - 1`: when even that lower bound is
    // outside the cap, decline without allocating the oversized product.
    let product_lower_bits = common
        .bits()
        .checked_add(factor.bits())
        .and_then(|bits| bits.checked_sub(1))
        .ok_or(Decline::Memory)?;
    if product_lower_bits > MAX_RMP_COMMON_DENOMINATOR_BITS {
        return Err(Decline::Memory);
    }
    *common *= factor;
    (common.bits() <= MAX_RMP_COMMON_DENOMINATOR_BITS)
        .then_some(())
        .ok_or(Decline::Memory)
}

fn bounded_add_assign(target: &mut BigRational, term: BigRational) -> Result<(), Decline> {
    if !rational_within_cap(&term) {
        return Err(Decline::Resource);
    }
    *target += term;
    rational_within_cap(target)
        .then_some(())
        .ok_or(Decline::Resource)
}

fn bounded_sub_assign(target: &mut BigRational, term: BigRational) -> Result<(), Decline> {
    if !rational_within_cap(&term) {
        return Err(Decline::Resource);
    }
    *target -= term;
    rational_within_cap(target)
        .then_some(())
        .ok_or(Decline::Resource)
}

fn bounded_mul(left: &BigRational, right: &BigRational) -> Result<BigRational, Decline> {
    if !rational_within_cap(left) || !rational_within_cap(right) {
        return Err(Decline::Resource);
    }
    let value = left * right;
    rational_within_cap(&value)
        .then_some(value)
        .ok_or(Decline::Resource)
}

fn bounded_div(left: &BigRational, right: &BigRational) -> Result<BigRational, Decline> {
    if !rational_within_cap(left) || !rational_within_cap(right) || right.is_zero() {
        return Err(Decline::Resource);
    }
    let value = left / right;
    rational_within_cap(&value)
        .then_some(value)
        .ok_or(Decline::Resource)
}

fn sparse_add(
    contribution: &mut Vec<(usize, BigRational)>,
    master: usize,
    coefficient: BigRational,
) -> Result<(), Decline> {
    match contribution.binary_search_by_key(&master, |(index, _)| *index) {
        Ok(position) => bounded_add_assign(&mut contribution[position].1, coefficient),
        Err(position) => {
            if !rational_within_cap(&coefficient) {
                return Err(Decline::Resource);
            }
            contribution.insert(position, (master, coefficient));
            Ok(())
        }
    }
}

fn exact_col_lb(model: &Model, column: u32) -> Option<BigRational> {
    let (lower, _) = model.col_bounds(Col(column));
    exact(lower)
}

fn exact_col_ub(model: &Model, column: u32) -> Option<BigRational> {
    let (_, upper) = model.col_bounds(Col(column));
    exact(upper)
}

fn exact_row(
    model: &Model,
    row: u32,
    meter: &mut MemoryMeter,
    work: &mut WorkMeter,
) -> Result<
    (
        Vec<(u32, BigRational)>,
        Option<BigRational>,
        Option<BigRational>,
        usize,
    ),
    Decline,
> {
    let (coefficients, lower, upper) = model.row(Row(row));
    work.charge_terms(1)?;
    let shell_bytes = coefficients
        .len()
        .checked_mul(size_of::<(u32, BigRational)>())
        .ok_or(Decline::Memory)?;
    meter.charge(shell_bytes)?;
    let mut charged = shell_bytes;
    let mut exact_coefficients = Vec::with_capacity(coefficients.len());
    for (index, &(column, coefficient)) in coefficients.iter().enumerate() {
        if index & 0xff == 0 {
            work.charge_terms(0x100.min(coefficients.len().saturating_sub(index)))?;
        }
        let value = model.row_coeff_exact_cow(row as usize, column, coefficient);
        if !rational_within_cap(&value) {
            return Err(Decline::Resource);
        }
        let payload = rational_payload_bytes(&value)?;
        meter.charge(payload)?;
        charged = charged.checked_add(payload).ok_or(Decline::Memory)?;
        exact_coefficients.push((column, value.into_owned()));
    }
    let lower = model.row_lb_exact_cow(row as usize, lower);
    let upper = model.row_ub_exact_cow(row as usize, upper);
    for value in lower.iter().chain(upper.iter()) {
        if !rational_within_cap(value) {
            return Err(Decline::Resource);
        }
        let payload = rational_payload_bytes(value)?;
        meter.charge(payload)?;
        charged = charged.checked_add(payload).ok_or(Decline::Memory)?;
    }
    Ok((
        exact_coefficients,
        lower.map(|value| value.into_owned()),
        upper.map(|value| value.into_owned()),
        charged,
    ))
}

fn objective_coefficient(model: &Model, column: u32) -> std::borrow::Cow<'_, BigRational> {
    let coefficient = model.obj_coeff(Col(column));
    model.obj_coeff_exact_cow(column, coefficient)
}

fn bounded_objective_value_at(
    model: &Model,
    values: &[BigRational],
    work: &mut WorkMeter,
) -> Result<BigRational, Decline> {
    if values.len() != model.num_cols() {
        return Err(Decline::Verification);
    }
    let offset = model.obj_offset_exact_cow();
    if !rational_within_cap(&offset) {
        return Err(Decline::Resource);
    }
    let mut value = offset.into_owned();
    for (column, point_value) in values.iter().enumerate() {
        if column & 0xff == 0 {
            work.charge_terms(0x100.min(values.len().saturating_sub(column)))?;
        }
        if !rational_within_cap(point_value) {
            return Err(Decline::Resource);
        }
        let coefficient = objective_coefficient(model, column as u32);
        if !rational_within_cap(&coefficient) {
            return Err(Decline::Resource);
        }
        if !coefficient.is_zero() && !point_value.is_zero() {
            bounded_add_assign(&mut value, bounded_mul(&coefficient, point_value)?)?;
        }
    }
    Ok(value)
}

fn check_point_bounded(
    model: &Model,
    values: &[BigRational],
    work: &mut WorkMeter,
) -> Result<(), Decline> {
    if values.len() != model.num_cols() {
        return Err(Decline::Verification);
    }
    for (column, value) in values.iter().enumerate() {
        if column & 0xff == 0 {
            work.charge_terms(0x100.min(values.len().saturating_sub(column)))?;
        }
        if !rational_within_cap(value) {
            return Err(Decline::Resource);
        }
        let lower = exact_col_lb(model, column as u32).ok_or(Decline::Structure)?;
        if value < &lower
            || exact_col_ub(model, column as u32).is_some_and(|upper| value > &upper)
            || (model.col_kind(Col(column as u32)) != ColKind::Continuous && !value.is_integer())
        {
            return Err(Decline::FractionalPrimal);
        }
    }
    let mut terms = 0usize;
    for row_index in 0..model.num_rows() {
        if row_index & 0x3f == 0 {
            work.charge_round()?;
        }
        let (coefficients, lower, upper) = model.row(Row(row_index as u32));
        let mut activity = BigRational::zero();
        for &(column, rounded) in coefficients {
            terms = terms.checked_add(1).ok_or(Decline::Resource)?;
            if terms & 0xff == 0 {
                work.charge_terms(0x100)?;
            }
            let point_value = values.get(column as usize).ok_or(Decline::Verification)?;
            if point_value.is_zero() {
                continue;
            }
            let coefficient = model.row_coeff_exact_cow(row_index, column, rounded);
            if !rational_within_cap(&coefficient) {
                return Err(Decline::Resource);
            }
            bounded_add_assign(&mut activity, bounded_mul(&coefficient, point_value)?)?;
        }
        if let Some(lower) = model.row_lb_exact_cow(row_index, lower) {
            if !rational_within_cap(&lower) {
                return Err(Decline::Resource);
            }
            if &activity < lower.as_ref() {
                return Err(Decline::FractionalPrimal);
            }
        }
        if let Some(upper) = model.row_ub_exact_cow(row_index, upper) {
            if !rational_within_cap(&upper) {
                return Err(Decline::Resource);
            }
            if &activity > upper.as_ref() {
                return Err(Decline::FractionalPrimal);
            }
        }
    }
    work.charge_terms(terms & 0xff)?;
    work.checkpoint()
}

/// Cheap advice-only rejection before any BigRational matrix census.  Every
/// admitted formulation is equality-heavy unit conservation with at least one
/// positive cover and one positive packing row.  A false negative merely
/// leaves the native solver authoritative; a positive result grants no proof
/// authority to the route below.
fn coarse_candidate(model: &Model, work: &mut WorkMeter) -> Result<bool, Decline> {
    let mut equalities = 0usize;
    let mut covers = 0usize;
    let mut capacities = 0usize;
    let mut terms = 0usize;
    for row_index in 0..model.num_rows() {
        work.charge_round()?;
        let (coefficients, lower, upper) = model.row(Row(row_index as u32));
        work.charge_terms(1)?;
        terms = match terms.checked_add(coefficients.len()) {
            Some(value) if value <= MAX_MODEL_TERMS => value,
            _ => return Ok(false),
        };
        let mut trivially_zero = true;
        let mut nonunit = false;
        let mut all_positive = true;
        for (index, &(column, coefficient)) in coefficients.iter().enumerate() {
            if index & 0xff == 0 {
                work.charge_terms(0x100.min(coefficients.len().saturating_sub(index)))?;
            }
            trivially_zero &= model.col_bounds(Col(column)).1 == 0.0;
            nonunit |= coefficient != 1.0 && coefficient != -1.0;
            all_positive &= coefficient > 0.0;
        }
        if trivially_zero && lower <= 0.0 && upper >= 0.0 {
            continue;
        } else if lower.is_finite() && upper.is_finite() && lower == upper {
            if nonunit {
                return Ok(false);
            }
            equalities += 1;
        } else if lower.is_finite()
            && lower > 0.0
            && !upper.is_finite()
            && !coefficients.is_empty()
            && all_positive
        {
            covers += 1;
        } else if !lower.is_finite()
            && upper.is_finite()
            && upper > 0.0
            && !coefficients.is_empty()
            && all_positive
        {
            capacities += 1;
        } else {
            // An admitted post-propagation model has only conservation
            // equalities, positive covers, and positive capacities. Reject a
            // coarse false positive here rather than paying an exact matrix
            // census merely to rediscover an unsupported ranged/mixed row.
            return Ok(false);
        }
    }
    Ok(equalities >= 2
        && equalities.saturating_mul(2) >= model.num_rows()
        && (1..=MAX_MASTER_ROWS).contains(&covers)
        && (1..=MAX_BLOCKS).contains(&capacities))
}

fn top_level_shape_supported(model: &Model) -> bool {
    model.sense() == Sense::Minimize
        && model.has_objective()
        && model.num_cols() > 0
        && model.num_cols() <= MAX_MODEL_COLS
        && model.num_rows() > 0
        && model.num_rows() <= MAX_MODEL_ROWS
}

/// Advice-only scout for callers deciding whether to offer this route early.
/// A positive result grants no authority: exact recognition still consumes
/// every active row and column before the route may construct a proof.
pub(crate) fn is_coarse_block_angular_candidate(model: &Model) -> bool {
    if !top_level_shape_supported(model) {
        return false;
    }
    let mut work = WorkMeter::new(None);
    let mut objective_declined = false;
    let zero_objective = {
        let mut objective_work = |units| match work.charge_terms(units) {
            Ok(()) => true,
            Err(_) => {
                objective_declined = true;
                false
            }
        };
        model.objective_is_identically_zero_with_work(&mut objective_work)
    };
    if objective_declined
        || zero_objective != Some(false)
        || !rational_within_cap(&model.obj_offset_exact_cow())
    {
        return false;
    }
    coarse_candidate(model, &mut work).unwrap_or(false)
}

/// Propagate only exact zero fixings.  An equality whose residual right-hand
/// side is zero and whose unfixed nonnegative terms all have the same sign
/// forces every such variable to zero.  Repeating this rule is enough to trim
/// terminal conservation tails without importing heuristic presolve state.
fn propagate_fixed_zeros(
    model: &Model,
    meter: &mut MemoryMeter,
    work: &mut WorkMeter,
) -> Result<Vec<bool>, Decline> {
    meter.charge(model.num_cols())?;
    let mut fixed_zero = vec![false; model.num_cols()];
    for column in 0..model.num_cols() {
        if column & 0x3ff == 0 {
            work.charge_terms(0x400.min(model.num_cols().saturating_sub(column)))?;
        }
        if model.col_kind(Col(column as u32)) == ColKind::Continuous {
            return Err(Decline::NotApplicable);
        }
        let lower = exact_col_lb(model, column as u32).ok_or(Decline::Structure)?;
        let upper = exact_col_ub(model, column as u32);
        let objective = objective_coefficient(model, column as u32);
        if !rational_within_cap(&lower)
            || upper
                .as_ref()
                .is_some_and(|value| !rational_within_cap(value))
            || !rational_within_cap(&objective)
        {
            return Err(Decline::Resource);
        }
        if !lower.is_zero() {
            return Err(Decline::NotApplicable);
        }
        if upper.is_some_and(|upper| upper.is_zero()) {
            fixed_zero[column] = true;
        }
    }

    let mut changed = true;
    let mut rounds = 0usize;
    while changed {
        work.charge_round()?;
        changed = false;
        rounds = rounds.checked_add(1).ok_or(Decline::Resource)?;
        if rounds > model.num_cols().saturating_add(1) {
            return Err(Decline::Resource);
        }
        for row in 0..model.num_rows() {
            let (coefficients, lower, upper, charged) = exact_row(model, row as u32, meter, work)?;
            let (Some(lower), Some(upper)) = (lower, upper) else {
                meter.release(charged);
                continue;
            };
            if lower != upper || !lower.is_zero() {
                meter.release(charged);
                continue;
            }
            let mut remaining = 0usize;
            let mut all_positive = true;
            let mut all_negative = true;
            for (index, (column, value)) in coefficients.iter().enumerate() {
                if index & 0xff == 0 {
                    work.charge_terms(0x100.min(coefficients.len().saturating_sub(index)))?;
                }
                if fixed_zero[*column as usize] {
                    continue;
                }
                remaining += 1;
                all_positive &= value.is_positive();
                all_negative &= value.is_negative();
            }
            if remaining == 0 {
                meter.release(charged);
                continue;
            }
            if all_positive || all_negative {
                for (index, (column, _)) in coefficients.iter().enumerate() {
                    if index & 0xff == 0 {
                        work.charge_terms(0x100.min(coefficients.len().saturating_sub(index)))?;
                    }
                    if !fixed_zero[*column as usize]
                        && !std::mem::replace(&mut fixed_zero[*column as usize], true)
                    {
                        changed = true;
                    }
                }
            }
            meter.release(charged);
        }
    }
    Ok(fixed_zero)
}

#[derive(Clone)]
struct ActiveRow {
    index: u32,
    coefficients: Vec<(u32, BigRational)>,
    lower: Option<BigRational>,
    upper: Option<BigRational>,
}

fn active_rows(
    model: &Model,
    fixed_zero: &[bool],
    meter: &mut MemoryMeter,
    work: &mut WorkMeter,
) -> Result<Vec<ActiveRow>, Decline> {
    meter.charge(
        model
            .num_rows()
            .checked_mul(size_of::<ActiveRow>())
            .ok_or(Decline::Memory)?,
    )?;
    let mut rows = Vec::with_capacity(model.num_rows());
    let mut terms = 0usize;
    for row in 0..model.num_rows() {
        let (mut coefficients, lower, upper, mut charged) =
            exact_row(model, row as u32, meter, work)?;
        let mut dropped_payload = 0usize;
        let mut retained = 0usize;
        for index in 0..coefficients.len() {
            if index & 0xff == 0 {
                work.charge_terms(0x100.min(coefficients.len().saturating_sub(index)))?;
            }
            if fixed_zero[coefficients[index].0 as usize] {
                dropped_payload = dropped_payload
                    .checked_add(rational_payload_bytes(&coefficients[index].1)?)
                    .ok_or(Decline::Memory)?;
            } else {
                if retained != index {
                    coefficients.swap(retained, index);
                }
                retained += 1;
            }
        }
        coefficients.truncate(retained);
        meter.release(dropped_payload);
        charged = charged.saturating_sub(dropped_payload);
        terms = terms
            .checked_add(coefficients.len())
            .ok_or(Decline::Resource)?;
        if terms > MAX_MODEL_TERMS {
            return Err(Decline::Resource);
        }
        if coefficients.is_empty() {
            let zero = BigRational::zero();
            if lower.as_ref().is_some_and(|bound| &zero < bound)
                || upper.as_ref().is_some_and(|bound| &zero > bound)
            {
                return Err(Decline::Structure);
            }
            meter.release(charged);
            continue;
        }
        rows.push(ActiveRow {
            index: row as u32,
            coefficients,
            lower,
            upper,
        });
    }
    Ok(rows)
}

fn is_master_candidate(row: &ActiveRow, work: &mut WorkMeter) -> Result<bool, Decline> {
    if !row.lower.as_ref().is_some_and(BigRational::is_positive) || row.upper.is_some() {
        return Ok(false);
    }
    for (index, (_, coefficient)) in row.coefficients.iter().enumerate() {
        if index & 0xff == 0 {
            work.charge_terms(0x100.min(row.coefficients.len().saturating_sub(index)))?;
        }
        if !coefficient.is_positive() {
            return Ok(false);
        }
    }
    Ok(true)
}

struct UnionFind {
    parent: Vec<u32>,
    rank: Vec<u8>,
}

impl UnionFind {
    fn new(size: usize) -> Self {
        Self {
            parent: (0..size as u32).collect(),
            rank: vec![0; size],
        }
    }

    fn find(&mut self, value: u32) -> u32 {
        let mut root = value;
        while self.parent[root as usize] != root {
            root = self.parent[root as usize];
        }
        let mut current = value;
        while self.parent[current as usize] != current {
            let next = self.parent[current as usize];
            self.parent[current as usize] = root;
            current = next;
        }
        root
    }

    fn union(&mut self, left: u32, right: u32) {
        let mut left = self.find(left);
        let mut right = self.find(right);
        if left == right {
            return;
        }
        if self.rank[left as usize] < self.rank[right as usize] {
            std::mem::swap(&mut left, &mut right);
        }
        self.parent[right as usize] = left;
        if self.rank[left as usize] == self.rank[right as usize] {
            self.rank[left as usize] = self.rank[left as usize].saturating_add(1);
        }
    }
}

#[cfg(test)]
fn recognize(
    model: &Model,
    deadline: Option<Instant>,
    memory_budget: Option<usize>,
) -> Result<Plan, Decline> {
    let mut work = WorkMeter::new(deadline);
    recognize_with_work(
        model,
        memory_budget,
        PricingPreparation::ProductionMitm,
        &mut work,
    )
}

fn recognize_with_work(
    model: &Model,
    memory_budget: Option<usize>,
    pricing_preparation: PricingPreparation,
    work: &mut WorkMeter,
) -> Result<Plan, Decline> {
    if !top_level_shape_supported(model) {
        return Err(Decline::NotApplicable);
    }
    work.checkpoint()?;
    let mut objective_decline = None;
    let zero_objective = {
        let mut objective_work = |units| match work.charge_terms(units) {
            Ok(()) => true,
            Err(reason) => {
                objective_decline.get_or_insert(reason);
                false
            }
        };
        model.objective_is_identically_zero_with_work(&mut objective_work)
    };
    if let Some(reason) = objective_decline {
        return Err(reason);
    }
    if zero_objective.ok_or(Decline::Resource)? {
        return Err(Decline::NotApplicable);
    }
    if !rational_within_cap(&model.obj_offset_exact_cow()) {
        return Err(Decline::Resource);
    }
    if !coarse_candidate(model, work)? {
        return Err(Decline::NotApplicable);
    }
    // Public replay and production both carry a wall deadline and a
    // deterministic local meter. Production additionally respects the ambient
    // process envelope so a loaded solve declines before allocating.
    let mut meter = MemoryMeter::new(memory_budget, work.deadline.is_some())?;
    meter.charge(ROUTE_METADATA_RESERVE)?;
    let fixed_zero = propagate_fixed_zeros(model, &mut meter, work)?;
    let rows = active_rows(model, &fixed_zero, &mut meter, work)?;
    let mut master_positions = Vec::new();
    for (position, row) in rows.iter().enumerate() {
        if position & 0xff == 0 {
            work.charge_terms(0x100.min(rows.len().saturating_sub(position)))?;
        }
        if is_master_candidate(row, work)? {
            master_positions.push(position);
        }
    }
    if master_positions.is_empty() || master_positions.len() > MAX_MASTER_ROWS {
        return Err(Decline::NotApplicable);
    }
    let master_set: BTreeSet<usize> = master_positions.iter().copied().collect();

    meter.charge(
        model
            .num_cols()
            .checked_mul(size_of::<u32>() + size_of::<u8>())
            .ok_or(Decline::Memory)?,
    )?;
    let mut union = UnionFind::new(model.num_cols());
    let mut active_column = vec![false; model.num_cols()];
    for (position, row) in rows.iter().enumerate() {
        work.charge_terms(1)?;
        for (entry, &(column, _)) in row.coefficients.iter().enumerate() {
            if entry & 0xff == 0 {
                work.charge_terms(0x100.min(row.coefficients.len().saturating_sub(entry)))?;
            }
            active_column[column as usize] = true;
            if !master_set.contains(&position) && entry > 0 {
                union.union(row.coefficients[0].0, column);
            }
        }
    }
    for column in 0..model.num_cols() {
        if column & 0xff == 0 {
            work.charge_terms(0x100.min(model.num_cols().saturating_sub(column)))?;
        }
        if !fixed_zero[column] && !active_column[column] {
            return Err(Decline::Structure);
        }
    }

    let mut component_map: HashMap<u32, usize> = HashMap::new();
    let mut components: Vec<Vec<u32>> = Vec::new();
    for column in 0..model.num_cols() {
        if column & 0xff == 0 {
            work.charge_terms(0x100.min(model.num_cols().saturating_sub(column)))?;
        }
        if fixed_zero[column] {
            continue;
        }
        let root = union.find(column as u32);
        let component = *component_map.entry(root).or_insert_with(|| {
            components.push(Vec::new());
            components.len() - 1
        });
        components[component].push(column as u32);
    }
    if components.len() < 2 || components.len() > MAX_BLOCKS {
        return Err(Decline::Structure);
    }
    components.sort_by_key(|columns| columns.first().copied().unwrap_or(u32::MAX));

    let mut column_component = vec![usize::MAX; model.num_cols()];
    for (component, columns) in components.iter().enumerate() {
        work.charge_terms(1)?;
        for (index, &column) in columns.iter().enumerate() {
            if index & 0xff == 0 {
                work.charge_terms(0x100.min(columns.len().saturating_sub(index)))?;
            }
            column_component[column as usize] = component;
        }
    }
    for &position in &master_positions {
        work.charge_terms(1)?;
        let coefficients = &rows[position].coefficients;
        let mut touched = BTreeSet::new();
        for (index, (column, _)) in coefficients.iter().enumerate() {
            if index & 0xff == 0 {
                work.charge_terms(0x100.min(coefficients.len().saturating_sub(index)))?;
            }
            touched.insert(column_component[*column as usize]);
        }
        if touched.len() < 2 {
            return Err(Decline::Structure);
        }
    }

    let mut local_by_component = vec![Vec::<usize>::new(); components.len()];
    for (position, row) in rows.iter().enumerate() {
        work.charge_terms(1)?;
        if master_set.contains(&position) {
            continue;
        }
        let component = column_component[row.coefficients[0].0 as usize];
        for (index, (column, _)) in row.coefficients.iter().enumerate() {
            if index & 0xff == 0 {
                work.charge_terms(0x100.min(row.coefficients.len().saturating_sub(index)))?;
            }
            if column_component[*column as usize] != component {
                return Err(Decline::Structure);
            }
        }
        local_by_component[component].push(position);
    }

    meter.charge(
        master_positions
            .len()
            .checked_mul(size_of::<u32>() + size_of::<BigRational>())
            .ok_or(Decline::Memory)?,
    )?;
    let mut master_rows = Vec::with_capacity(master_positions.len());
    let mut master_rhs = Vec::with_capacity(master_positions.len());
    for &position in &master_positions {
        let rhs = rows[position].lower.as_ref().ok_or(Decline::Structure)?;
        meter.charge(rational_payload_bytes(rhs)?)?;
        master_rows.push(rows[position].index);
        master_rhs.push(rhs.clone());
    }
    // `Block` includes both source Arc fields, so this also accounts for every
    // cache-hit SourceBlock. Arc clones only increment an in-allocation count;
    // the shared allocations and cache slots are charged separately below.
    let block_bytes = components
        .len()
        .checked_mul(size_of::<Block>())
        .and_then(|bytes| bytes.checked_add(2 * size_of::<usize>()))
        .ok_or(Decline::Memory)?;
    let canonical_capacity = components.len().min(MAX_CANONICAL_TUPLE_SETS);
    let cache_bytes = canonical_capacity
        .checked_mul(size_of::<Arc<[Vec<i64>]>>())
        .and_then(|bytes| {
            components
                .len()
                .checked_mul(size_of::<ExactCapacityDomainCacheEntry>())
                .and_then(|exact| bytes.checked_add(exact))
        })
        .and_then(|bytes| bytes.checked_add(4 * size_of::<usize>()))
        .ok_or(Decline::Memory)?;
    meter.charge(
        block_bytes
            .checked_add(cache_bytes)
            .ok_or(Decline::Memory)?,
    )?;
    let mut tuple_sets = TupleSetCache {
        canonical: Vec::with_capacity(canonical_capacity),
        exact_domains: Vec::with_capacity(components.len()),
    };
    let mut blocks = Vec::with_capacity(components.len());
    for (component, columns) in components.iter().enumerate() {
        work.charge_round()?;
        let positions = &local_by_component[component];
        let mut local_rows = Vec::with_capacity(positions.len());
        for (index, &position) in positions.iter().enumerate() {
            if index & 0xff == 0 {
                work.charge_terms(0x100.min(positions.len().saturating_sub(index)))?;
            }
            local_rows.push(&rows[position]);
        }
        blocks.push(recognize_component(
            model,
            columns,
            &local_rows,
            &master_rows,
            &mut meter,
            &mut tuple_sets,
            pricing_preparation,
            work,
        )?);
    }
    if blocks
        .iter()
        .all(|block| matches!(block, Block::Initial(_)))
    {
        return Err(Decline::Structure);
    }
    Ok(Plan {
        fixed_zero,
        master_rows,
        master_rhs,
        blocks,
    })
}

fn unit_sign(value: &BigRational) -> Option<i8> {
    if value == &BigRational::one() {
        Some(1)
    } else if value == &-BigRational::one() {
        Some(-1)
    } else {
        None
    }
}

fn equality_rhs(row: &ActiveRow) -> Option<BigRational> {
    match (&row.lower, &row.upper) {
        (Some(lower), Some(upper)) if lower == upper => Some(lower.clone()),
        _ => None,
    }
}

fn is_equality(row: &ActiveRow) -> bool {
    matches!((&row.lower, &row.upper), (Some(lower), Some(upper)) if lower == upper)
}

fn recognize_component(
    model: &Model,
    columns: &[u32],
    rows: &[&ActiveRow],
    master_rows: &[u32],
    meter: &mut MemoryMeter,
    tuple_sets: &mut TupleSetCache,
    pricing_preparation: PricingPreparation,
    work: &mut WorkMeter,
) -> Result<Block, Decline> {
    let mut capacity_rows = Vec::new();
    let mut equality_rows = Vec::new();
    for (position, &row) in rows.iter().enumerate() {
        if position & 0xff == 0 {
            work.charge_terms(0x100.min(rows.len().saturating_sub(position)))?;
        }
        if is_equality(row) {
            equality_rows.push(row);
        }
        if row.lower.is_none()
            && row.upper.as_ref().is_some_and(BigRational::is_positive)
            && !row.coefficients.is_empty()
        {
            let mut all_positive = true;
            for (index, (_, coefficient)) in row.coefficients.iter().enumerate() {
                if index & 0xff == 0 {
                    work.charge_terms(0x100.min(row.coefficients.len().saturating_sub(index)))?;
                }
                if !coefficient.is_positive() {
                    all_positive = false;
                    break;
                }
            }
            if all_positive {
                capacity_rows.push(row);
            }
        }
    }
    if capacity_rows.len() == 1 && equality_rows.len() + 1 == rows.len() {
        recognize_source_component(
            model,
            columns,
            capacity_rows[0],
            &equality_rows,
            master_rows,
            meter,
            tuple_sets,
            pricing_preparation,
            work,
        )
        .map(Block::Source)
    } else if capacity_rows.is_empty() && equality_rows.len() == rows.len() {
        recognize_initial_component(model, columns, &equality_rows, master_rows, meter, work)
            .map(Block::Initial)
    } else {
        Err(Decline::Structure)
    }
}

fn equality_incidence(
    rows: &[&ActiveRow],
    work: &mut WorkMeter,
) -> Result<HashMap<u32, Vec<(usize, i8)>>, Decline> {
    let mut incidence: HashMap<u32, Vec<(usize, i8)>> = HashMap::new();
    for (position, row) in rows.iter().enumerate() {
        work.charge_terms(1)?;
        for (index, (column, coefficient)) in row.coefficients.iter().enumerate() {
            if index & 0xff == 0 {
                work.charge_terms(0x100.min(row.coefficients.len().saturating_sub(index)))?;
            }
            if let Some(sign) = unit_sign(coefficient) {
                incidence.entry(*column).or_default().push((position, sign));
            }
        }
    }
    Ok(incidence)
}

fn orient_zero_equality(
    row: &ActiveRow,
    positive_column: u32,
    work: &mut WorkMeter,
) -> Result<Vec<(u32, i8)>, Decline> {
    let rhs = equality_rhs(row).ok_or(Decline::Structure)?;
    if !rhs.is_zero() {
        return Err(Decline::Structure);
    }
    let mut sign = None;
    for (index, (column, coefficient)) in row.coefficients.iter().enumerate() {
        if index & 0xff == 0 {
            work.charge_terms(0x100.min(row.coefficients.len().saturating_sub(index)))?;
        }
        if *column == positive_column {
            sign = unit_sign(coefficient);
            break;
        }
    }
    let sign = sign.ok_or(Decline::Structure)?;
    let mut oriented = Vec::with_capacity(row.coefficients.len());
    for (index, (column, coefficient)) in row.coefficients.iter().enumerate() {
        if index & 0xff == 0 {
            work.charge_terms(0x100.min(row.coefficients.len().saturating_sub(index)))?;
        }
        oriented.push((
            *column,
            unit_sign(coefficient).ok_or(Decline::Structure)? * sign,
        ));
    }
    Ok(oriented)
}

fn build_chain_from_root(
    model: &Model,
    root: u32,
    root_row_position: usize,
    rows: &[&ActiveRow],
    incidence: &HashMap<u32, Vec<(usize, i8)>>,
    master_rows: &[u32],
    consumed_rows: &mut BTreeSet<usize>,
    consumed_columns: &mut BTreeSet<u32>,
    meter: &mut MemoryMeter,
    work: &mut WorkMeter,
) -> Result<Chain, Decline> {
    work.charge_round()?;
    let root_terms = orient_zero_equality(rows[root_row_position], root, work)?;
    if root_terms.len() != 2
        || root_terms.iter().filter(|(_, sign)| *sign == 1).count() != 1
        || root_terms.iter().filter(|(_, sign)| *sign == -1).count() != 1
    {
        return Err(Decline::Structure);
    }
    let mut state = root_terms
        .iter()
        .find_map(|(column, sign)| (*sign == -1).then_some(*column))
        .ok_or(Decline::Structure)?;
    if !consumed_rows.insert(root_row_position) || !consumed_columns.insert(root) {
        return Err(Decline::Structure);
    }
    let mut states = Vec::new();
    let mut exits = Vec::new();
    loop {
        work.charge_round()?;
        if states.len() >= MAX_CHAIN_LENGTH {
            return Err(Decline::Resource);
        }
        states.push(state);
        if !consumed_columns.insert(state) {
            return Err(Decline::Structure);
        }
        let uses = incidence.get(&state).ok_or(Decline::Structure)?;
        if uses.len() != 2
            || uses
                .iter()
                .filter(|(position, _)| consumed_rows.contains(position))
                .count()
                != 1
        {
            return Err(Decline::Structure);
        }
        let next_row = uses
            .iter()
            .find_map(|(position, _)| (!consumed_rows.contains(position)).then_some(*position))
            .ok_or(Decline::Structure)?;
        let terms = orient_zero_equality(rows[next_row], state, work)?;
        if terms.len() != 2 && terms.len() != 3 {
            return Err(Decline::Structure);
        }
        if terms.iter().filter(|(_, sign)| *sign == 1).count() != 1
            || terms.iter().filter(|(_, sign)| *sign == -1).count() != terms.len() - 1
        {
            return Err(Decline::Structure);
        }
        let negative: Vec<u32> = terms
            .iter()
            .filter_map(|(column, sign)| (*sign == -1).then_some(*column))
            .collect();
        let (exit, next_state) = if negative.len() == 1 {
            (negative[0], None)
        } else {
            let mut next = None;
            let mut exit = None;
            for column in negative {
                let has_later_use = incidence
                    .get(&column)
                    .into_iter()
                    .flatten()
                    .any(|(position, _)| *position != next_row);
                if has_later_use {
                    if next.replace(column).is_some() {
                        return Err(Decline::Structure);
                    }
                } else if exit.replace(column).is_some() {
                    return Err(Decline::Structure);
                }
            }
            (
                exit.ok_or(Decline::Structure)?,
                Some(next.ok_or(Decline::Structure)?),
            )
        };
        if master_rows_for_column(model, exit, master_rows, work)?
            .next()
            .is_some()
            || incidence
                .get(&exit)
                .is_none_or(|uses| uses.len() != 1 || uses[0].0 != next_row)
        {
            return Err(Decline::Structure);
        }
        exits.push(exit);
        if !consumed_columns.insert(exit) || !consumed_rows.insert(next_row) {
            return Err(Decline::Structure);
        }
        if let Some(next_state) = next_state {
            state = next_state;
        } else {
            break;
        }
    }
    let chain = Chain {
        root: Some(root),
        states,
        exits,
        quantity: None,
        choices: Vec::new(),
    };
    with_chain_choices(model, chain, master_rows, meter, work)
}

fn master_rows_for_column<'a>(
    model: &'a Model,
    column: u32,
    master_rows: &'a [u32],
    work: &mut WorkMeter,
) -> Result<impl Iterator<Item = (usize, std::borrow::Cow<'a, BigRational>)> + 'a, Decline> {
    work.charge_terms(master_rows.len().saturating_add(1))?;
    Ok(master_rows
        .iter()
        .enumerate()
        .filter_map(move |(master, &row)| {
            let (coefficients, _, _) = model.row(Row(row));
            coefficients
                .binary_search_by_key(&column, |&(candidate, _)| candidate)
                .ok()
                .map(|position| {
                    let (_, coefficient) = coefficients[position];
                    (
                        master,
                        model.row_coeff_exact_cow(row as usize, column, coefficient),
                    )
                })
        }))
}

fn build_chain_choice(
    model: &Model,
    columns: Vec<u32>,
    master_rows: &[u32],
    meter: &mut MemoryMeter,
    work: &mut WorkMeter,
) -> Result<ChainChoice, Decline> {
    let transient = max_rational_storage_bytes(MAX_RATIONAL_BITS.saturating_mul(2))?
        .checked_mul(master_rows.len().saturating_add(1))
        .ok_or(Decline::Memory)?;
    meter.charge(transient)?;
    let mut cost = BigRational::zero();
    let mut contribution = Vec::new();
    for &column in &columns {
        work.charge_terms(1)?;
        let objective = objective_coefficient(model, column);
        if !rational_within_cap(&objective) {
            return Err(Decline::Resource);
        }
        bounded_add_assign(&mut cost, objective.into_owned())?;
        for (master, coefficient) in master_rows_for_column(model, column, master_rows, work)? {
            if !rational_within_cap(&coefficient) {
                return Err(Decline::Resource);
            }
            sparse_add(&mut contribution, master, coefficient.into_owned())?;
        }
    }
    let mut retained = size_of::<ChainChoice>()
        .checked_add(
            columns
                .len()
                .checked_mul(size_of::<u32>())
                .ok_or(Decline::Memory)?,
        )
        .ok_or(Decline::Memory)?;
    retained = retained
        .checked_add(rational_storage_bytes(&cost)?)
        .ok_or(Decline::Memory)?;
    for (_, value) in &contribution {
        let value_bytes = rational_storage_bytes(value)?;
        retained = retained
            .checked_add(size_of::<usize>())
            .and_then(|bytes| bytes.checked_add(value_bytes))
            .ok_or(Decline::Memory)?;
    }
    if retained > transient {
        meter.charge(retained - transient)?;
    } else {
        meter.release(transient - retained);
    }
    Ok(ChainChoice {
        columns,
        cost_per_unit: cost,
        master_per_unit: contribution,
    })
}

fn with_chain_choices(
    model: &Model,
    mut chain: Chain,
    master_rows: &[u32],
    meter: &mut MemoryMeter,
    work: &mut WorkMeter,
) -> Result<Chain, Decline> {
    if chain.states.len() != chain.exits.len() || chain.states.is_empty() {
        return Err(Decline::Structure);
    }
    let mut prefix_columns = Vec::new();
    if let Some(root) = chain.root {
        prefix_columns.push(root);
    }
    for (index, (&state, &exit)) in chain.states.iter().zip(&chain.exits).enumerate() {
        work.charge_round()?;
        prefix_columns.push(state);
        let touched: Vec<_> = master_rows_for_column(model, state, master_rows, work)?.collect();
        if touched.len() != 1 || !touched[0].1.is_positive() || !rational_within_cap(&touched[0].1)
        {
            return Err(Decline::Structure);
        }
        let mut columns = prefix_columns.clone();
        columns.push(exit);
        chain.choices.push(build_chain_choice(
            model,
            columns,
            master_rows,
            meter,
            work,
        )?);
        if index + 1 > MAX_CHAIN_LENGTH {
            return Err(Decline::Resource);
        }
    }
    Ok(chain)
}

fn all_columns_consumed(
    columns: &[u32],
    consumed: &BTreeSet<u32>,
    work: &mut WorkMeter,
) -> Result<bool, Decline> {
    for (index, column) in columns.iter().enumerate() {
        if index & 0xff == 0 {
            work.charge_terms(0x100.min(columns.len().saturating_sub(index)))?;
        }
        if !consumed.contains(column) {
            return Ok(false);
        }
    }
    Ok(true)
}

fn recognize_source_component(
    model: &Model,
    columns: &[u32],
    capacity_row: &ActiveRow,
    equality_rows: &[&ActiveRow],
    master_rows: &[u32],
    meter: &mut MemoryMeter,
    tuple_sets: &mut TupleSetCache,
    pricing_preparation: PricingPreparation,
    work: &mut WorkMeter,
) -> Result<SourceBlock, Decline> {
    if capacity_row.coefficients.is_empty()
        || capacity_row.coefficients.len() > MAX_CAPACITY_SUPPORT
        || capacity_row.coefficients.len() > MAX_CHAINS_PER_BLOCK
    {
        return Err(Decline::Resource);
    }
    let capacity = capacity_row.upper.clone().ok_or(Decline::Structure)?;
    let incidence = equality_incidence(equality_rows, work)?;
    let mut consumed_rows = BTreeSet::new();
    let mut consumed_columns = BTreeSet::new();
    let mut chains = Vec::with_capacity(capacity_row.coefficients.len());
    let mut capacity_coefficients = Vec::with_capacity(capacity_row.coefficients.len());
    for &(root, ref capacity_coefficient) in &capacity_row.coefficients {
        work.charge_round()?;
        let uses = incidence.get(&root).ok_or(Decline::Structure)?;
        let root_row = uses
            .first()
            .map(|(position, _)| *position)
            .ok_or(Decline::Structure)?;
        if uses.len() != 1
            || master_rows_for_column(model, root, master_rows, work)?
                .next()
                .is_some()
        {
            return Err(Decline::Structure);
        }
        chains.push(build_chain_from_root(
            model,
            root,
            root_row,
            equality_rows,
            &incidence,
            master_rows,
            &mut consumed_rows,
            &mut consumed_columns,
            meter,
            work,
        )?);
        capacity_coefficients.push(capacity_coefficient.clone());
    }
    if consumed_rows.len() != equality_rows.len()
        || consumed_columns.len() != columns.len()
        || !all_columns_consumed(columns, &consumed_columns, work)?
    {
        return Err(Decline::Structure);
    }
    let domain = prepare_capacity_domain(
        model,
        &chains,
        &capacity_coefficients,
        &capacity,
        meter,
        work,
    )?;
    if let Some((weights, rhs)) = &domain.integral {
        for existing in &tuple_sets.exact_domains {
            let signature = &existing.domain.signature;
            work.charge_terms(
                signature
                    .maxima
                    .len()
                    .saturating_add(signature.weights.len())
                    .saturating_add(1),
            )?;
            if signature.maxima.as_slice() == domain.maxima.as_slice()
                && signature.weights.as_slice() == weights.as_slice()
                && signature.rhs == *rhs
            {
                let tuples = Arc::clone(&existing.tuples);
                let exact_domain = Some(Arc::clone(&existing.domain));
                meter.release(domain.storage_bytes);
                return Ok(SourceBlock {
                    chains,
                    tuples,
                    exact_domain,
                });
            }
        }
    }
    let tuples =
        enumerate_capacity_tuples(&domain, &capacity_coefficients, &capacity, meter, work)?;
    let tuple_bytes = tuple_storage_bytes(tuples.len(), chains.len())?;
    let mut canonical = None;
    for existing in &tuple_sets.canonical {
        if tuple_sets_equal(existing.as_ref(), tuples.as_slice(), work)? {
            canonical = Some(Arc::clone(existing));
            break;
        }
    }
    let tuples = if let Some(existing) = canonical {
        // The just-enumerated vector is temporary when an identical canonical
        // set already exists; only the shared Arc remains live.
        meter.release(tuple_bytes);
        existing
    } else {
        if tuple_sets.canonical.len() >= MAX_CANONICAL_TUPLE_SETS {
            return Err(Decline::Resource);
        }
        let tuples: Arc<[Vec<i64>]> = Arc::from(tuples);
        tuple_sets.canonical.push(Arc::clone(&tuples));
        tuples
    };
    let PreparedCapacityDomain {
        maxima,
        integral,
        storage_bytes,
    } = domain;
    let mut exact_domain = None;
    if let Some((weights, rhs)) = integral {
        if tuple_sets.exact_domains.len() >= MAX_BLOCKS {
            return Err(Decline::Resource);
        }
        let signature = CapacityDomainSignature {
            maxima,
            weights,
            rhs,
        };
        let mitm = match pricing_preparation {
            PricingPreparation::ProductionMitm => {
                prepare_mitm_assignments_if_local_capacity(&signature, meter, work)?
            }
            PricingPreparation::ExhaustiveReplay => None,
        };
        let domain = Arc::new(ExactCapacityDomain { signature, mitm });
        exact_domain = Some(Arc::clone(&domain));
        tuple_sets
            .exact_domains
            .push(ExactCapacityDomainCacheEntry {
                domain,
                tuples: Arc::clone(&tuples),
            });
        // `storage_bytes` now accounts for the signature retained in the
        // exact-domain cache rather than the temporary prepared domain.
    } else {
        meter.release(storage_bytes);
    }
    Ok(SourceBlock {
        chains,
        tuples,
        exact_domain,
    })
}

fn recognize_initial_component(
    model: &Model,
    columns: &[u32],
    equality_rows: &[&ActiveRow],
    master_rows: &[u32],
    meter: &mut MemoryMeter,
    work: &mut WorkMeter,
) -> Result<InitialBlock, Decline> {
    work.charge_terms(1)?;
    let mut nonzero_rows = Vec::new();
    for (position, row) in equality_rows.iter().enumerate() {
        if position & 0xff == 0 {
            work.charge_terms(0x100.min(equality_rows.len().saturating_sub(position)))?;
        }
        if let Some(rhs) = equality_rhs(row).filter(|rhs| !rhs.is_zero()) {
            nonzero_rows.push((position, *row, rhs));
        }
    }
    if nonzero_rows.len() != 1 {
        return Err(Decline::Structure);
    }
    let (root_position, root_row, rhs) = &nonzero_rows[0];
    if root_row.coefficients.len() != 2 {
        return Err(Decline::Structure);
    }
    let signs: Vec<_> = root_row
        .coefficients
        .iter()
        .map(|(_, coefficient)| unit_sign(coefficient).ok_or(Decline::Structure))
        .collect::<Result<_, _>>()?;
    if signs[0] != signs[1] {
        return Err(Decline::Structure);
    }
    let oriented_rhs = if signs[0] > 0 {
        rhs.clone()
    } else {
        -rhs.clone()
    };
    if !oriented_rhs.is_positive() || !oriented_rhs.is_integer() {
        return Err(Decline::Structure);
    }
    let quantity = oriented_rhs
        .to_integer()
        .to_i64()
        .filter(|value| *value > 0)
        .ok_or(Decline::Resource)?;

    let incidence = equality_incidence(equality_rows, work)?;
    let (state, first_exit) = root_row
        .coefficients
        .iter()
        .map(|(column, _)| *column)
        .partition::<Vec<_>, _>(|column| {
            incidence
                .get(column)
                .into_iter()
                .flatten()
                .any(|(position, _)| *position != *root_position)
        });
    if state.len() != 1 || first_exit.len() != 1 {
        return Err(Decline::Structure);
    }
    if master_rows_for_column(model, first_exit[0], master_rows, work)?
        .next()
        .is_some()
        || incidence
            .get(&first_exit[0])
            .is_none_or(|uses| uses.len() != 1 || uses[0].0 != *root_position)
    {
        return Err(Decline::Structure);
    }
    let mut consumed_rows = BTreeSet::from([*root_position]);
    let mut consumed_columns = BTreeSet::from([first_exit[0]]);
    let mut states = Vec::new();
    let mut exits = vec![first_exit[0]];
    let mut current = state[0];
    loop {
        work.charge_round()?;
        if states.len() >= MAX_CHAIN_LENGTH {
            return Err(Decline::Resource);
        }
        states.push(current);
        let uses = incidence.get(&current).ok_or(Decline::Structure)?;
        if uses.len() != 2
            || uses
                .iter()
                .filter(|(position, _)| consumed_rows.contains(position))
                .count()
                != 1
        {
            return Err(Decline::Structure);
        }
        let next_row = uses
            .iter()
            .find_map(|(position, _)| (!consumed_rows.contains(position)).then_some(*position))
            .ok_or(Decline::Structure)?;
        let terms = orient_zero_equality(equality_rows[next_row], current, work)?;
        if terms.len() != 2 && terms.len() != 3 {
            return Err(Decline::Structure);
        }
        if terms.iter().filter(|(_, sign)| *sign == 1).count() != 1
            || terms.iter().filter(|(_, sign)| *sign == -1).count() != terms.len() - 1
        {
            return Err(Decline::Structure);
        }
        let negative: Vec<u32> = terms
            .iter()
            .filter_map(|(column, sign)| (*sign == -1).then_some(*column))
            .collect();
        if negative.len() != 1 && negative.len() != 2 {
            return Err(Decline::Structure);
        }
        let (exit, next_state) = if negative.len() == 1 {
            (negative[0], None)
        } else {
            let next = negative.iter().copied().find(|column| {
                incidence
                    .get(column)
                    .into_iter()
                    .flatten()
                    .any(|(position, _)| *position != next_row)
            });
            let exit = negative
                .iter()
                .copied()
                .find(|column| Some(*column) != next);
            (
                exit.ok_or(Decline::Structure)?,
                Some(next.ok_or(Decline::Structure)?),
            )
        };
        if master_rows_for_column(model, exit, master_rows, work)?
            .next()
            .is_some()
            || incidence
                .get(&exit)
                .is_none_or(|uses| uses.len() != 1 || uses[0].0 != next_row)
        {
            return Err(Decline::Structure);
        }
        if !consumed_rows.insert(next_row)
            || !consumed_columns.insert(current)
            || !consumed_columns.insert(exit)
        {
            return Err(Decline::Structure);
        }
        exits.push(exit);
        if let Some(next_state) = next_state {
            current = next_state;
        } else {
            break;
        }
    }
    if exits.len() != states.len() + 1 {
        return Err(Decline::Structure);
    }

    for &column in states.iter().chain(&exits) {
        let upper = exact_col_ub(model, column).ok_or(Decline::Structure)?;
        if upper < BigRational::from_integer(quantity.into()) {
            return Err(Decline::Structure);
        }
    }

    // The root equation offers exit 0 before any state is carried.  Convert it
    // plus each state-prefix exit into the same choice representation used by
    // source chains.
    let mut choices = Vec::with_capacity(exits.len());
    for exit_index in 0..exits.len() {
        let mut choice_columns = states[..exit_index].to_vec();
        choice_columns.push(exits[exit_index]);
        choices.push(build_chain_choice(
            model,
            choice_columns,
            master_rows,
            meter,
            work,
        )?);
    }
    if consumed_rows.len() != equality_rows.len()
        || consumed_columns.len() != columns.len()
        || !all_columns_consumed(columns, &consumed_columns, work)?
    {
        return Err(Decline::Structure);
    }
    Ok(InitialBlock {
        chain: Chain {
            root: None,
            states,
            exits,
            quantity: Some(quantity),
            choices,
        },
    })
}

#[cfg(test)]
thread_local! {
    static CAPACITY_TUPLE_ENUMERATIONS: std::cell::Cell<usize> = const {
        std::cell::Cell::new(0)
    };
    static MITM_ASSIGNMENT_PREPARATIONS: std::cell::Cell<usize> = const {
        std::cell::Cell::new(0)
    };
    static MITM_SOURCE_PRICINGS: std::cell::Cell<usize> = const {
        std::cell::Cell::new(0)
    };
    static EXHAUSTIVE_SOURCE_PRICINGS: std::cell::Cell<usize> = const {
        std::cell::Cell::new(0)
    };
}

#[cfg(test)]
fn note_capacity_tuple_enumeration() {
    CAPACITY_TUPLE_ENUMERATIONS.with(|count| count.set(count.get().saturating_add(1)));
}

#[cfg(not(test))]
fn note_capacity_tuple_enumeration() {}

#[cfg(test)]
fn note_mitm_assignment_preparation() {
    MITM_ASSIGNMENT_PREPARATIONS.with(|count| count.set(count.get().saturating_add(1)));
}

#[cfg(not(test))]
fn note_mitm_assignment_preparation() {}

#[cfg(test)]
fn note_mitm_source_pricing() {
    MITM_SOURCE_PRICINGS.with(|count| count.set(count.get().saturating_add(1)));
}

#[cfg(not(test))]
fn note_mitm_source_pricing() {}

#[cfg(test)]
fn note_exhaustive_source_pricing() {
    EXHAUSTIVE_SOURCE_PRICINGS.with(|count| count.set(count.get().saturating_add(1)));
}

#[cfg(not(test))]
fn note_exhaustive_source_pricing() {}

fn prepare_capacity_domain(
    model: &Model,
    chains: &[Chain],
    coefficients: &[BigRational],
    capacity: &BigRational,
    meter: &mut MemoryMeter,
    work: &mut WorkMeter,
) -> Result<PreparedCapacityDomain, Decline> {
    if chains.len() != coefficients.len() || chains.is_empty() {
        return Err(Decline::Structure);
    }
    let storage_bytes = capacity_domain_storage_bytes(chains.len())?;
    meter.charge(storage_bytes)?;
    let mut maxima = Vec::with_capacity(chains.len());
    let mut box_size = 1usize;
    for (chain, coefficient) in chains.iter().zip(coefficients) {
        work.charge_terms(1)?;
        let root = chain.root.ok_or(Decline::Structure)?;
        if !coefficient.is_positive() {
            return Err(Decline::Structure);
        }
        let capacity_max = bounded_div(capacity, coefficient)?.floor().to_integer();
        let declared_max = exact_col_ub(model, root)
            .ok_or(Decline::Structure)?
            .floor()
            .to_integer();
        let maximum = capacity_max
            .min(declared_max)
            .to_i64()
            .filter(|value| *value >= 0)
            .ok_or(Decline::Resource)?;
        let domain_size = maximum.checked_add(1).ok_or(Decline::Resource)?;
        box_size = box_size
            .checked_mul(usize::try_from(domain_size).map_err(|_| Decline::Resource)?)
            .ok_or(Decline::Resource)?;
        if box_size > MAX_CAPACITY_BOX {
            return Err(Decline::Resource);
        }
        maxima.push(maximum);
    }
    for (chain, maximum) in chains.iter().zip(&maxima) {
        work.charge_terms(chain.choices.len().saturating_add(1))?;
        let required = BigRational::from_integer((*maximum).into());
        for choice in &chain.choices {
            for &column in &choice.columns {
                let upper = exact_col_ub(model, column).ok_or(Decline::Structure)?;
                if upper < required {
                    return Err(Decline::Structure);
                }
            }
        }
    }
    let integral = integral_capacity_row(coefficients, capacity)?;
    Ok(PreparedCapacityDomain {
        maxima,
        integral,
        storage_bytes,
    })
}

fn enumerate_capacity_tuples(
    domain: &PreparedCapacityDomain,
    coefficients: &[BigRational],
    capacity: &BigRational,
    meter: &mut MemoryMeter,
    work: &mut WorkMeter,
) -> Result<Vec<Vec<i64>>, Decline> {
    if domain.maxima.len() != coefficients.len() || domain.maxima.is_empty() {
        return Err(Decline::Structure);
    }
    // `box_size` is a work cap, not an allocation: recursion streams through
    // the box and retains only feasible tuples. Reserve the maximum retained
    // frontier up front, then release the unused tail after enumeration.
    let reserved_bytes = tuple_storage_bytes(MAX_FEASIBLE_TUPLES, domain.maxima.len())?;
    meter.charge(reserved_bytes)?;
    let mut tuples = Vec::new();
    let mut current = vec![0i64; domain.maxima.len()];
    note_capacity_tuple_enumeration();
    if let Some((weights, rhs)) = &domain.integral {
        enumerate_capacity_tuples_i128(
            0,
            &domain.maxima,
            weights,
            *rhs,
            &mut current,
            0,
            &mut tuples,
            work,
        )?;
    } else {
        enumerate_capacity_tuples_recursive(
            0,
            &domain.maxima,
            coefficients,
            capacity,
            &mut current,
            BigRational::zero(),
            &mut tuples,
            work,
        )?;
    }
    if tuples.is_empty() || tuples.len() > MAX_FEASIBLE_TUPLES {
        return Err(Decline::Resource);
    }
    let retained_bytes = tuple_storage_bytes(tuples.len(), domain.maxima.len())?;
    meter.release(reserved_bytes.saturating_sub(retained_bytes));
    Ok(tuples)
}

fn capacity_domain_storage_bytes(width: usize) -> Result<usize, Decline> {
    width
        .checked_mul(size_of::<i64>() + size_of::<i128>())
        .and_then(|bytes| {
            bytes.checked_add(
                size_of::<ExactCapacityDomain>() + 4 * size_of::<usize>(), // Arc counters + allocator metadata.
            )
        })
        .ok_or(Decline::Memory)
}

fn tuple_storage_bytes(count: usize, width: usize) -> Result<usize, Decline> {
    let per_tuple = size_of::<Vec<i64>>()
        .checked_add(width.checked_mul(size_of::<i64>()).ok_or(Decline::Memory)?)
        .and_then(|bytes| bytes.checked_add(4 * size_of::<usize>()))
        .ok_or(Decline::Memory)?;
    count
        .checked_mul(per_tuple)
        .and_then(|bytes| bytes.checked_add(size_of::<Vec<Vec<i64>>>() + 64))
        .ok_or(Decline::Memory)
}

fn tuple_sets_equal(
    left: &[Vec<i64>],
    right: &[Vec<i64>],
    work: &mut WorkMeter,
) -> Result<bool, Decline> {
    work.charge_terms(1)?;
    if left.len() != right.len() {
        return Ok(false);
    }
    for (left_tuple, right_tuple) in left.iter().zip(right) {
        work.charge_terms(left_tuple.len().saturating_add(1))?;
        if left_tuple != right_tuple {
            return Ok(false);
        }
    }
    Ok(true)
}

/// Clear one positive rational capacity row to a primitive `i128` inequality.
/// This is an exact representation change, not approximate scaling.  Rows that
/// do not fit retain the BigRational enumerator below.
fn integral_capacity_row(
    coefficients: &[BigRational],
    capacity: &BigRational,
) -> Result<Option<(Vec<i128>, i128)>, Decline> {
    let mut denominator = capacity.denom().clone();
    for coefficient in coefficients {
        denominator = denominator.lcm(coefficient.denom());
        if denominator.bits() > MAX_RATIONAL_BITS as u64 {
            return Err(Decline::Resource);
        }
    }
    let mut weights = coefficients
        .iter()
        .map(|coefficient| coefficient.numer() * (&denominator / coefficient.denom()))
        .collect::<Vec<_>>();
    let mut rhs = capacity.numer() * (&denominator / capacity.denom());
    let mut divisor = rhs.abs();
    for weight in &weights {
        divisor = divisor.gcd(&weight.abs());
    }
    if !divisor.is_zero() && !divisor.is_one() {
        rhs /= &divisor;
        for weight in &mut weights {
            *weight /= &divisor;
        }
    }
    let Some(rhs) = rhs.to_i128() else {
        return Ok(None);
    };
    let Some(weights) = weights
        .iter()
        .map(|value| value.to_i128())
        .collect::<Option<Vec<_>>>()
    else {
        return Ok(None);
    };
    if rhs < 0 || weights.iter().any(|weight| *weight <= 0) {
        return Err(Decline::Structure);
    }
    Ok(Some((weights, rhs)))
}

fn capacity_half_box(maxima: &[i64]) -> Result<usize, Decline> {
    maxima.iter().try_fold(1usize, |count, maximum| {
        let width = maximum.checked_add(1).ok_or(Decline::Resource)?;
        count
            .checked_mul(usize::try_from(width).map_err(|_| Decline::Resource)?)
            .filter(|count| *count <= MAX_CAPACITY_BOX)
            .ok_or(Decline::Resource)
    })
}

/// Pick a prefix split whose larger Cartesian half is as small as possible.
/// Keeping the original coordinate order makes concatenated half assignments
/// compare exactly like the exhaustive tuple vector.
fn balanced_capacity_split(maxima: &[i64]) -> Result<(usize, usize, usize), Decline> {
    if maxima.is_empty() || maxima.len() > MAX_CAPACITY_SUPPORT {
        return Err(Decline::Structure);
    }
    if maxima.len() == 1 {
        return Ok((0, 1, capacity_half_box(maxima)?));
    }
    let mut best = None;
    for split in 1..maxima.len() {
        let left = capacity_half_box(&maxima[..split])?;
        let right = capacity_half_box(&maxima[split..])?;
        let key = (left.max(right), left.saturating_add(right), split);
        if best.as_ref().is_none_or(|(prior, _, _, _)| key < *prior) {
            best = Some((key, split, left, right));
        }
    }
    best.map(|(_, split, left, right)| (split, left, right))
        .ok_or(Decline::Structure)
}

fn mitm_assignments_storage_bytes(left: usize, right: usize) -> Result<usize, Decline> {
    left.checked_add(right)
        .and_then(|count| count.checked_mul(size_of::<CapacityHalfAssignment>()))
        // Vec headers are inline in `ExactCapacityDomain`; charge both backing
        // allocation headers in addition to their exact reserved payloads.
        .and_then(|bytes| bytes.checked_add(4 * size_of::<usize>()))
        .ok_or(Decline::Memory)
}

#[allow(clippy::too_many_arguments)]
fn enumerate_capacity_half_assignments(
    coordinate: usize,
    maxima: &[i64],
    weights: &[i128],
    capacity: i128,
    current: &mut [i64; MAX_CAPACITY_SUPPORT],
    activity: i128,
    assignments: &mut Vec<CapacityHalfAssignment>,
    work: &mut WorkMeter,
) -> Result<(), Decline> {
    work.charge_terms(1)?;
    if coordinate == maxima.len() {
        assignments.push(CapacityHalfAssignment {
            activity,
            values: *current,
        });
        return Ok(());
    }
    for value in 0..=maxima[coordinate] {
        let next_activity = weights[coordinate]
            .checked_mul(i128::from(value))
            .and_then(|term| activity.checked_add(term))
            .ok_or(Decline::Arithmetic)?;
        if next_activity > capacity {
            break;
        }
        current[coordinate] = value;
        enumerate_capacity_half_assignments(
            coordinate + 1,
            maxima,
            weights,
            capacity,
            current,
            next_activity,
            assignments,
            work,
        )?;
    }
    Ok(())
}

fn prepare_mitm_assignments(
    signature: &CapacityDomainSignature,
    meter: &mut MemoryMeter,
    work: &mut WorkMeter,
) -> Result<MitmCapacityAssignments, Decline> {
    note_mitm_assignment_preparation();
    if signature.maxima.len() != signature.weights.len()
        || signature.maxima.is_empty()
        || signature.maxima.len() > MAX_CAPACITY_SUPPORT
    {
        return Err(Decline::Structure);
    }
    let (split, left_box, right_box) = balanced_capacity_split(&signature.maxima)?;
    // Both vectors retain their reserved Cartesian capacities.  Charge the
    // actual allocation before constructing either one, even though capacity
    // pruning may leave some slots unused.
    meter.charge(mitm_assignments_storage_bytes(left_box, right_box)?)?;
    let mut left = Vec::with_capacity(left_box);
    let mut left_current = [0i64; MAX_CAPACITY_SUPPORT];
    enumerate_capacity_half_assignments(
        0,
        &signature.maxima[..split],
        &signature.weights[..split],
        signature.rhs,
        &mut left_current,
        0,
        &mut left,
        work,
    )?;
    let mut right = Vec::with_capacity(right_box);
    let mut right_current = [0i64; MAX_CAPACITY_SUPPORT];
    enumerate_capacity_half_assignments(
        0,
        &signature.maxima[split..],
        &signature.weights[split..],
        signature.rhs,
        &mut right_current,
        0,
        &mut right,
        work,
    )?;
    if left.is_empty() || right.is_empty() {
        return Err(Decline::Structure);
    }
    let right_width = signature.maxima.len() - split;
    let sort_work = right
        .len()
        .checked_mul((usize::BITS - right.len().max(1).leading_zeros()) as usize + 1)
        .and_then(|count| count.checked_mul(2))
        .ok_or(Decline::Resource)?;
    work.charge_terms(sort_work)?;
    right.sort_unstable_by(|left, right| {
        left.activity
            .cmp(&right.activity)
            .then_with(|| left.values[..right_width].cmp(&right.values[..right_width]))
    });
    work.checkpoint()?;
    Ok(MitmCapacityAssignments { split, left, right })
}

/// Prepare production pricing advice only when it fits the recognition
/// phase's remaining local ledger. The exact exhaustive tuple oracle has
/// already been retained, so local MITM capacity pressure is not a reason to
/// decline an otherwise supported model. Once admitted by this preflight,
/// process-memory, arithmetic, resource, and deadline failures still propagate
/// normally rather than being disguised as an advice miss.
fn prepare_mitm_assignments_if_local_capacity(
    signature: &CapacityDomainSignature,
    meter: &mut MemoryMeter,
    work: &mut WorkMeter,
) -> Result<Option<MitmCapacityAssignments>, Decline> {
    work.checkpoint()?;
    let (_, left_box, right_box) = balanced_capacity_split(&signature.maxima)?;
    let required = mitm_assignments_storage_bytes(left_box, right_box)?;
    if required > meter.remaining() {
        if meter.enforce_process_limit && process_memory_exceeded() {
            return Err(Decline::Memory);
        }
        return Ok(None);
    }
    prepare_mitm_assignments(signature, meter, work).map(Some)
}

#[allow(clippy::too_many_arguments)]
fn enumerate_capacity_tuples_i128(
    coordinate: usize,
    maxima: &[i64],
    weights: &[i128],
    capacity: i128,
    current: &mut [i64],
    activity: i128,
    tuples: &mut Vec<Vec<i64>>,
    work: &mut WorkMeter,
) -> Result<(), Decline> {
    work.charge_terms(1)?;
    if coordinate == maxima.len() {
        return push_capacity_tuple_in_order(current, tuples, work);
    }
    for value in 0..=maxima[coordinate] {
        let next_activity = weights[coordinate]
            .checked_mul(i128::from(value))
            .and_then(|term| activity.checked_add(term))
            .ok_or(Decline::Arithmetic)?;
        if next_activity > capacity {
            break;
        }
        current[coordinate] = value;
        enumerate_capacity_tuples_i128(
            coordinate + 1,
            maxima,
            weights,
            capacity,
            current,
            next_activity,
            tuples,
            work,
        )?;
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn enumerate_capacity_tuples_recursive(
    coordinate: usize,
    maxima: &[i64],
    coefficients: &[BigRational],
    capacity: &BigRational,
    current: &mut [i64],
    activity: BigRational,
    tuples: &mut Vec<Vec<i64>>,
    work: &mut WorkMeter,
) -> Result<(), Decline> {
    work.charge_terms(1)?;
    if coordinate == maxima.len() {
        return push_capacity_tuple_in_order(current, tuples, work);
    }
    for value in 0..=maxima[coordinate] {
        let amount = BigRational::from_integer(value.into());
        let mut next_activity = activity.clone();
        bounded_add_assign(
            &mut next_activity,
            bounded_mul(&coefficients[coordinate], &amount)?,
        )?;
        if &next_activity > capacity {
            break;
        }
        current[coordinate] = value;
        enumerate_capacity_tuples_recursive(
            coordinate + 1,
            maxima,
            coefficients,
            capacity,
            current,
            next_activity,
            tuples,
            work,
        )?;
    }
    Ok(())
}

/// Retain the lexicographic order generated by the coordinate-first recursive
/// enumerators. Restricted-master reconstruction relies on this checked
/// invariant for logarithmic exact membership tests; a future enumerator that
/// changes order must fail closed here instead of silently accepting an
/// invalid pattern or forcing repeated full-domain scans.
fn push_capacity_tuple_in_order(
    current: &[i64],
    tuples: &mut Vec<Vec<i64>>,
    work: &mut WorkMeter,
) -> Result<(), Decline> {
    if tuples.len() >= MAX_FEASIBLE_TUPLES {
        return Err(Decline::Resource);
    }
    if let Some(previous) = tuples.last() {
        work.charge_terms(current.len().saturating_add(1))?;
        if previous.as_slice() >= current {
            return Err(Decline::Structure);
        }
    }
    tuples.push(current.to_vec());
    Ok(())
}

fn choice_reduced_cost(
    choice: &ChainChoice,
    cover_duals: &[BigRational],
    phase: MasterPhase,
    work: &mut WorkMeter,
) -> Result<BigRational, Decline> {
    let mut value = match phase {
        MasterPhase::Feasibility => BigRational::zero(),
        MasterPhase::Objective => choice.cost_per_unit.clone(),
    };
    work.charge_terms(choice.master_per_unit.len().saturating_add(1))?;
    for (master, coefficient) in &choice.master_per_unit {
        let dual = cover_duals.get(*master).ok_or(Decline::Structure)?;
        bounded_sub_assign(&mut value, bounded_mul(coefficient, dual)?)?;
    }
    Ok(value)
}

fn source_assignment_cost(
    values: &[i64],
    unit_costs: &[BigRational],
    work: &mut WorkMeter,
) -> Result<BigRational, Decline> {
    if values.len() != unit_costs.len() {
        return Err(Decline::Structure);
    }
    work.charge_terms(values.len().saturating_add(1))?;
    let mut value = BigRational::zero();
    for (amount, cost) in values.iter().zip(unit_costs) {
        bounded_add_assign(
            &mut value,
            bounded_mul(cost, &BigRational::from_integer((*amount).into()))?,
        )?;
    }
    Ok(value)
}

fn price_source_amounts_exhaustive(
    tuples: &[Vec<i64>],
    unit_costs: &[BigRational],
    work: &mut WorkMeter,
) -> Result<(BigRational, Vec<i64>), Decline> {
    note_exhaustive_source_pricing();
    let mut best: Option<(BigRational, Vec<i64>)> = None;
    for tuple in tuples {
        let value = source_assignment_cost(tuple, unit_costs, work)?;
        if best.as_ref().is_none_or(|(prior_value, prior_tuple)| {
            value < *prior_value || (value == *prior_value && tuple < prior_tuple)
        }) {
            best = Some((value, tuple.clone()));
        }
    }
    best.ok_or(Decline::Structure)
}

fn half_assignment_cost(
    assignment: &CapacityHalfAssignment,
    width: usize,
    unit_costs: &[BigRational],
    work: &mut WorkMeter,
) -> Result<BigRational, Decline> {
    if width > MAX_CAPACITY_SUPPORT || width != unit_costs.len() {
        return Err(Decline::Structure);
    }
    source_assignment_cost(&assignment.values[..width], unit_costs, work)
}

fn right_activity_upper_bound(
    assignments: &[CapacityHalfAssignment],
    capacity: i128,
    work: &mut WorkMeter,
) -> Result<usize, Decline> {
    let mut lower = 0usize;
    let mut upper = assignments.len();
    while lower < upper {
        work.charge_terms(1)?;
        let middle = lower + (upper - lower) / 2;
        if assignments[middle].activity <= capacity {
            lower = middle + 1;
        } else {
            upper = middle;
        }
    }
    Ok(lower)
}

fn joined_halves_less(
    left: &CapacityHalfAssignment,
    right: &CapacityHalfAssignment,
    prior_left: &CapacityHalfAssignment,
    prior_right: &CapacityHalfAssignment,
    split: usize,
    width: usize,
) -> bool {
    left.values[..split]
        .cmp(&prior_left.values[..split])
        .then_with(|| right.values[..width - split].cmp(&prior_right.values[..width - split]))
        .is_lt()
}

fn mitm_prefix_storage_bytes(count: usize) -> Result<usize, Decline> {
    count
        .checked_mul(size_of::<usize>())
        .and_then(|bytes| bytes.checked_add(size_of::<Vec<usize>>() + 2 * size_of::<usize>()))
        .ok_or(Decline::Memory)
}

/// Exact meet-in-the-middle bounded-knapsack pricing.  The right side is
/// already sorted by activity.  Its exact per-dual prefix argmin turns every
/// left assignment into one binary search and one exact candidate comparison.
fn price_source_amounts_mitm(
    domain: &ExactCapacityDomain,
    unit_costs: &[BigRational],
    meter: &mut MemoryMeter,
    work: &mut WorkMeter,
) -> Result<(BigRational, Vec<i64>), Decline> {
    note_mitm_source_pricing();
    let mitm = domain.mitm.as_ref().ok_or(Decline::Structure)?;
    let width = domain.signature.maxima.len();
    if width != unit_costs.len()
        || mitm.split > width
        || mitm.left.is_empty()
        || mitm.right.is_empty()
    {
        return Err(Decline::Structure);
    }
    let scratch_bytes = mitm_prefix_storage_bytes(mitm.right.len())?;
    meter.charge(scratch_bytes)?;
    let mut prefix_argmin = Vec::with_capacity(mitm.right.len());
    let right_width = width - mitm.split;
    let mut best_right: Option<(BigRational, usize)> = None;
    for (index, assignment) in mitm.right.iter().enumerate() {
        let cost = half_assignment_cost(assignment, right_width, &unit_costs[mitm.split..], work)?;
        if best_right.as_ref().is_none_or(|(prior_cost, prior_index)| {
            cost < *prior_cost
                || (cost == *prior_cost
                    && assignment.values[..right_width]
                        < mitm.right[*prior_index].values[..right_width])
        }) {
            best_right = Some((cost, index));
        }
        prefix_argmin.push(best_right.as_ref().ok_or(Decline::Structure)?.1);
    }

    let mut best: Option<(BigRational, usize, usize)> = None;
    for (left_index, left) in mitm.left.iter().enumerate() {
        let residual = domain
            .signature
            .rhs
            .checked_sub(left.activity)
            .ok_or(Decline::Arithmetic)?;
        let feasible_rights = right_activity_upper_bound(&mitm.right, residual, work)?;
        if feasible_rights == 0 {
            continue;
        }
        let right_index = prefix_argmin[feasible_rights - 1];
        let left_cost = half_assignment_cost(left, mitm.split, &unit_costs[..mitm.split], work)?;
        let right_cost = half_assignment_cost(
            &mitm.right[right_index],
            right_width,
            &unit_costs[mitm.split..],
            work,
        )?;
        let mut value = left_cost;
        bounded_add_assign(&mut value, right_cost)?;
        if best
            .as_ref()
            .is_none_or(|(prior_value, prior_left, prior_right)| {
                value < *prior_value
                    || (value == *prior_value
                        && joined_halves_less(
                            left,
                            &mitm.right[right_index],
                            &mitm.left[*prior_left],
                            &mitm.right[*prior_right],
                            mitm.split,
                            width,
                        ))
            })
        {
            best = Some((value, left_index, right_index));
        }
    }
    let (value, left_index, right_index) = best.ok_or(Decline::Structure)?;
    let mut amounts = Vec::with_capacity(width);
    amounts.extend_from_slice(&mitm.left[left_index].values[..mitm.split]);
    amounts.extend_from_slice(&mitm.right[right_index].values[..right_width]);
    meter.release(scratch_bytes);
    Ok((value, amounts))
}

#[derive(Clone, Copy)]
enum SourcePricing {
    ProductionMitm,
    ExhaustiveReplay,
}

fn price_block_with_strategy(
    block: &Block,
    cover_duals: &[BigRational],
    phase: MasterPhase,
    source_pricing: SourcePricing,
    pricing_meter: Option<&mut MemoryMeter>,
    work: &mut WorkMeter,
) -> Result<PricedPattern, Decline> {
    work.charge_round()?;
    match block {
        Block::Initial(block) => {
            let quantity = block.chain.quantity.ok_or(Decline::Structure)?;
            let (exit, unit) = block
                .chain
                .choices
                .iter()
                .enumerate()
                .map(|(exit, choice)| {
                    Ok((exit, choice_reduced_cost(choice, cover_duals, phase, work)?))
                })
                .collect::<Result<Vec<_>, Decline>>()?
                .into_iter()
                .min_by(|left, right| left.1.cmp(&right.1))
                .ok_or(Decline::Structure)?;
            let reduced = bounded_mul(&unit, &BigRational::from_integer(quantity.into()))?;
            Ok(PricedPattern {
                pattern: Pattern::Initial {
                    exit: u8::try_from(exit).map_err(|_| Decline::Resource)?,
                },
                reduced_without_convexity: reduced,
            })
        }
        Block::Source(block) => {
            let mut exits = Vec::with_capacity(block.chains.len());
            let mut unit_costs = Vec::with_capacity(block.chains.len());
            for chain in &block.chains {
                let (exit, cost) = chain
                    .choices
                    .iter()
                    .enumerate()
                    .map(|(exit, choice)| {
                        Ok((exit, choice_reduced_cost(choice, cover_duals, phase, work)?))
                    })
                    .collect::<Result<Vec<_>, Decline>>()?
                    .into_iter()
                    .min_by(|left, right| left.1.cmp(&right.1))
                    .ok_or(Decline::Structure)?;
                exits.push(u8::try_from(exit).map_err(|_| Decline::Resource)?);
                unit_costs.push(cost);
            }
            let (value, amounts) = match (source_pricing, block.exact_domain.as_deref()) {
                (SourcePricing::ProductionMitm, Some(domain)) if domain.mitm.is_some() => {
                    let meter = pricing_meter.ok_or(Decline::Structure)?;
                    price_source_amounts_mitm(domain, &unit_costs, meter, work)?
                }
                _ => price_source_amounts_exhaustive(&block.tuples, &unit_costs, work)?,
            };
            Ok(PricedPattern {
                pattern: Pattern::Source { amounts, exits },
                reduced_without_convexity: value,
            })
        }
    }
}

fn price_block_production(
    block: &Block,
    cover_duals: &[BigRational],
    phase: MasterPhase,
    meter: &mut MemoryMeter,
    work: &mut WorkMeter,
) -> Result<PricedPattern, Decline> {
    price_block_with_strategy(
        block,
        cover_duals,
        phase,
        SourcePricing::ProductionMitm,
        Some(meter),
        work,
    )
}

fn price_block_exhaustive(
    block: &Block,
    cover_duals: &[BigRational],
    phase: MasterPhase,
    work: &mut WorkMeter,
) -> Result<PricedPattern, Decline> {
    price_block_with_strategy(
        block,
        cover_duals,
        phase,
        SourcePricing::ExhaustiveReplay,
        None,
        work,
    )
}

fn pattern_cost_and_master(
    block: &Block,
    pattern: &Pattern,
    master_count: usize,
    work: &mut WorkMeter,
) -> Result<(BigRational, Vec<(usize, BigRational)>), Decline> {
    work.charge_round()?;
    let mut cost = BigRational::zero();
    let mut contribution = Vec::new();
    match (block, pattern) {
        (Block::Initial(block), Pattern::Initial { exit }) => {
            let quantity = block.chain.quantity.ok_or(Decline::Structure)?;
            let choice = block
                .chain
                .choices
                .get(*exit as usize)
                .ok_or(Decline::Structure)?;
            let quantity = BigRational::from_integer(quantity.into());
            cost = bounded_mul(&choice.cost_per_unit, &quantity)?;
            work.charge_terms(choice.master_per_unit.len().saturating_add(1))?;
            for (master, value) in &choice.master_per_unit {
                if *master >= master_count {
                    return Err(Decline::Structure);
                }
                sparse_add(&mut contribution, *master, bounded_mul(value, &quantity)?)?;
            }
        }
        (Block::Source(block), Pattern::Source { amounts, exits }) => {
            if amounts.len() != block.chains.len() || exits.len() != block.chains.len() {
                return Err(Decline::Structure);
            }
            if !contains_capacity_tuple(&block.tuples, amounts, work)? {
                return Err(Decline::Structure);
            }
            for ((chain, amount), exit) in block.chains.iter().zip(amounts).zip(exits) {
                work.charge_round()?;
                let choice = chain
                    .choices
                    .get(*exit as usize)
                    .ok_or(Decline::Structure)?;
                let amount = BigRational::from_integer((*amount).into());
                bounded_add_assign(&mut cost, bounded_mul(&choice.cost_per_unit, &amount)?)?;
                work.charge_terms(choice.master_per_unit.len().saturating_add(1))?;
                for (master, value) in &choice.master_per_unit {
                    if *master >= master_count {
                        return Err(Decline::Structure);
                    }
                    sparse_add(&mut contribution, *master, bounded_mul(value, &amount)?)?;
                }
            }
        }
        _ => return Err(Decline::Structure),
    }
    Ok((cost, contribution))
}

/// Exact membership in the construction-checked lexicographic tuple set.
/// Manual binary search keeps every inspected tuple inside the cumulative
/// deadline/work envelope; slice::binary_search cannot expose those polls.
fn contains_capacity_tuple(
    tuples: &[Vec<i64>],
    target: &[i64],
    work: &mut WorkMeter,
) -> Result<bool, Decline> {
    let mut low = 0usize;
    let mut high = tuples.len();
    while low < high {
        let middle = low + (high - low) / 2;
        let tuple = &tuples[middle];
        work.charge_terms(tuple.len().saturating_add(1))?;
        match tuple.as_slice().cmp(target) {
            std::cmp::Ordering::Less => low = middle + 1,
            std::cmp::Ordering::Equal => return Ok(true),
            std::cmp::Ordering::Greater => high = middle,
        }
    }
    Ok(false)
}

fn initial_pattern(block: &Block) -> Pattern {
    match block {
        Block::Source(block) => Pattern::Source {
            amounts: vec![0; block.chains.len()],
            exits: vec![0; block.chains.len()],
        },
        Block::Initial(_) => Pattern::Initial { exit: 0 },
    }
}

fn pattern_heap_storage_bytes(pattern: &Pattern) -> Result<usize, Decline> {
    let mut bytes = 0usize;
    if let Pattern::Source { amounts, exits } = pattern {
        bytes = bytes
            .checked_add(
                amounts
                    .len()
                    .checked_mul(size_of::<i64>())
                    .ok_or(Decline::Memory)?,
            )
            .and_then(|total| total.checked_add(exits.len()))
            .and_then(|total| total.checked_add(4 * size_of::<usize>()))
            .ok_or(Decline::Memory)?;
    }
    Ok(bytes)
}

fn pattern_cache_storage_bytes(
    patterns: &[Vec<Pattern>],
    work: &mut WorkMeter,
) -> Result<usize, Decline> {
    let mut bytes = patterns
        .len()
        .checked_mul(size_of::<Vec<Pattern>>())
        .and_then(|bytes| bytes.checked_add(4 * size_of::<usize>()))
        .ok_or(Decline::Memory)?;
    for block in patterns {
        bytes = bytes
            .checked_add(
                block
                    .capacity()
                    .checked_mul(size_of::<Pattern>())
                    .ok_or(Decline::Memory)?,
            )
            .ok_or(Decline::Memory)?;
        for (index, pattern) in block.iter().enumerate() {
            if index & 0xff == 0 {
                work.charge_terms(0x100.min(block.len().saturating_sub(index)))?;
            }
            bytes = bytes
                .checked_add(pattern_heap_storage_bytes(pattern)?)
                .ok_or(Decline::Memory)?;
        }
    }
    Ok(bytes)
}

fn restricted_result_storage_bytes(
    result: &RestrictedMasterResult,
    work: &mut WorkMeter,
) -> Result<usize, Decline> {
    let mut bytes = size_of::<RestrictedMasterResult>()
        .checked_add(rational_payload_bytes(&result.value)?)
        .ok_or(Decline::Memory)?;
    for values in [&result.values, &result.cover_duals, &result.convexity_duals] {
        bytes = bytes
            .checked_add(
                values
                    .capacity()
                    .checked_mul(size_of::<BigRational>())
                    .ok_or(Decline::Memory)?,
            )
            .ok_or(Decline::Memory)?;
        for (index, value) in values.iter().enumerate() {
            if index & 0xff == 0 {
                work.charge_terms(0x100.min(values.len().saturating_sub(index)))?;
            }
            bytes = bytes
                .checked_add(rational_payload_bytes(value)?)
                .ok_or(Decline::Memory)?;
        }
    }
    bytes = bytes
        .checked_add(
            result
                .column_map
                .capacity()
                .checked_mul(size_of::<(usize, usize)>())
                .ok_or(Decline::Memory)?,
        )
        .ok_or(Decline::Memory)?;
    Ok(bytes)
}

fn pricing_pattern_heap_upper_bound(block: &Block) -> Result<usize, Decline> {
    match block {
        Block::Initial(_) => Ok(0),
        Block::Source(block) => block
            .chains
            .len()
            .checked_mul(size_of::<i64>() + size_of::<u8>())
            .and_then(|bytes| bytes.checked_add(4 * size_of::<usize>()))
            .ok_or(Decline::Memory),
    }
}

/// Aggregate second-half peak for one complete pricing pass. Existing
/// patterns and the restricted-master result remain live; the pass also
/// retains one priced candidate per block and may clone one candidate into
/// every block's pattern cache. MITM prefix scratch is charged separately and
/// released per block.
fn pricing_pass_storage_bytes(
    plan: &Plan,
    patterns: &[Vec<Pattern>],
    result: &RestrictedMasterResult,
    work: &mut WorkMeter,
) -> Result<usize, Decline> {
    let maximum_rational = max_rational_storage_bytes(MAX_RATIONAL_BITS.saturating_mul(2))?;
    let maximum_rational_payload = maximum_rational
        .checked_sub(size_of::<BigRational>())
        .ok_or(Decline::Memory)?;
    let pattern_bytes = pattern_cache_storage_bytes(patterns, work)?;
    let result_bytes = restricted_result_storage_bytes(result, work)?;
    let mut bytes = ROUTE_METADATA_RESERVE
        .checked_add(pattern_bytes)
        .and_then(|bytes| bytes.checked_add(result_bytes))
        .and_then(|bytes| {
            bytes.checked_add(size_of::<Vec<PricedPattern>>() + 4 * size_of::<usize>())
        })
        .ok_or(Decline::Memory)?;
    // A push into every at-capacity pattern vector can retain its old backing
    // allocation while Rust allocates a grown buffer. Their combined old
    // lengths cannot exceed the restricted-column cap. Conservatively reserve
    // another two cap-sized buffers for the complete new allocation; the old
    // buffers themselves are already included in `pattern_bytes`.
    bytes = bytes
        .checked_add(
            MAX_RESTRICTED_COLUMNS
                .checked_mul(size_of::<Pattern>())
                .and_then(|bytes| bytes.checked_mul(2))
                .ok_or(Decline::Memory)?,
        )
        .ok_or(Decline::Memory)?;
    for block in &plan.blocks {
        work.charge_terms(1)?;
        let heap = pricing_pattern_heap_upper_bound(block)?;
        let candidate = size_of::<PricedPattern>()
            .checked_add(heap)
            .and_then(|bytes| bytes.checked_add(maximum_rational_payload))
            .ok_or(Decline::Memory)?;
        let possible_clone = size_of::<Pattern>()
            .checked_add(heap)
            .ok_or(Decline::Memory)?;
        bytes = bytes
            .checked_add(candidate)
            .and_then(|bytes| bytes.checked_add(possible_clone))
            .ok_or(Decline::Memory)?;
    }
    Ok(bytes)
}

fn priced_patterns_storage_bytes(
    priced: &[PricedPattern],
    work: &mut WorkMeter,
) -> Result<usize, Decline> {
    let inline = priced
        .len()
        .checked_mul(size_of::<PricedPattern>())
        .ok_or(Decline::Memory)?;
    let mut bytes = size_of::<Vec<PricedPattern>>()
        .checked_add(4 * size_of::<usize>())
        .and_then(|bytes| bytes.checked_add(inline))
        .ok_or(Decline::Memory)?;
    for (index, candidate) in priced.iter().enumerate() {
        if index & 0xff == 0 {
            work.charge_terms(0x100.min(priced.len().saturating_sub(index)))?;
        }
        let pattern_payload = pattern_heap_storage_bytes(&candidate.pattern)?;
        let rational_payload = rational_payload_bytes(&candidate.reduced_without_convexity)?;
        bytes = bytes
            .checked_add(pattern_payload)
            .and_then(|bytes| bytes.checked_add(rational_payload))
            .ok_or(Decline::Memory)?;
    }
    Ok(bytes)
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum RmpEngine {
    CertifiedFloat,
    BoundedExact,
}

struct RmpMaterialization {
    bytes: usize,
    engine: RmpEngine,
    #[cfg(test)]
    exact_cell_bytes: usize,
    #[cfg(test)]
    exact_cell_bits: usize,
}

/// Conservative peak for the nested LP session used by an RMP.
///
/// The prior fixed `512 * columns` allowance omitted the session's model clone,
/// the CSC+CSR float lowering, simplex scratch/eta files, a possible dense row
/// mirror, exact basis adjudication, and an inexact master's ExactLp tableau.
/// This estimate derives those terms from the fully built master before
/// `LpSession` is allowed to clone or lower it. Advice masters are float-only;
/// a truth-preserving exact master may use ExactLp only after its worst dense
/// tableau fits the same route-local box.
fn rmp_materialization(
    master: &Model,
    allow_exact: bool,
    work: &mut WorkMeter,
) -> Result<RmpMaterialization, Decline> {
    let engine = if allow_exact {
        // The second pass is the authoritative RMP.  Preserve ExactLp even
        // when every rational happens to round-trip through f64: a failed or
        // disabled float lane must never turn that exact pass into a decline.
        // Its dense worst case is admitted only by the preflight below.
        RmpEngine::BoundedExact
    } else {
        // Float simplex supplies only a combinatorial basis.  The session's
        // true-model basis certifier reconstructs the vertex, dual, objective,
        // and final certificate from the authoritative exact side store.
        RmpEngine::CertifiedFloat
    };
    let n = master.num_cols();
    let m = master.num_rows();
    let cols = n.checked_add(m).ok_or(Decline::Memory)?;
    let mut nnz = 0usize;
    let dimension_bits =
        usize::try_from(m.max(1).next_power_of_two().ilog2()).map_err(|_| Decline::Memory)?;
    let mut basis_minor_bits = 1usize;
    let mut bound_scale = RationalScale::new();
    let mut objective_scale = RationalScale::new();
    let mut exact_side_bytes = 0usize;
    for row_index in 0..m {
        work.charge_round()?;
        let (coefficients, lower, upper) = master.row(Row(row_index as u32));
        work.charge_terms(1)?;
        nnz = nnz.checked_add(coefficients.len()).ok_or(Decline::Memory)?;
        let mut row_scale = RationalScale::new();
        for (entry, &(column, rounded)) in coefficients.iter().enumerate() {
            if entry & 0xff == 0 {
                work.charge_terms(0x100.min(coefficients.len().saturating_sub(entry)))?;
            }
            let value = master.row_coeff_exact_cow(row_index, column, rounded);
            row_scale.observe(&value)?;
            if exact(rounded).as_ref() != Some(value.as_ref()) {
                exact_side_bytes = exact_side_bytes
                    .checked_add(rational_storage_bytes(&value)?)
                    .and_then(|bytes| bytes.checked_add(4 * size_of::<usize>()))
                    .ok_or(Decline::Memory)?;
            }
        }
        for (rounded, value) in [
            (lower, master.row_lb_exact_cow(row_index, lower)),
            (upper, master.row_ub_exact_cow(row_index, upper)),
        ] {
            let Some(value) = value else { continue };
            bound_scale.observe(&value)?;
            if exact(rounded).as_ref() != Some(value.as_ref()) {
                exact_side_bytes = exact_side_bytes
                    .checked_add(rational_storage_bytes(&value)?)
                    .and_then(|bytes| bytes.checked_add(2 * size_of::<usize>()))
                    .ok_or(Decline::Memory)?;
            }
        }
        // Scale this complete row by its LCM.  Every possible basis entry in
        // the row (including the logical variable's unit coefficient) is then
        // an integer.  Summing the per-row Hadamard bounds accounts for up to
        // m² unrelated basis denominators rather than only the largest entry.
        let scaled_row_bits = row_scale
            .scaled_numerator_bits()?
            .max(row_scale.denominator_bits()?);
        basis_minor_bits = basis_minor_bits
            .checked_add(scaled_row_bits)
            .and_then(|bits| bits.checked_add(dimension_bits))
            .and_then(|bits| bits.checked_add(4))
            .ok_or(Decline::Memory)?;
    }
    for column in 0..n {
        if column & 0xff == 0 {
            work.charge_terms(0x100.min(n.saturating_sub(column)))?;
        }
        let (lower, upper) = master.col_bounds(Col(column as u32));
        for value in [exact(lower), exact(upper)].into_iter().flatten() {
            bound_scale.observe(&value)?;
        }
        let rounded = master.obj_coeff(Col(column as u32));
        let value = master.obj_coeff_exact_cow(column as u32, rounded);
        objective_scale.observe(&value)?;
        if exact(rounded).as_ref() != Some(value.as_ref()) {
            exact_side_bytes = exact_side_bytes
                .checked_add(rational_storage_bytes(&value)?)
                .and_then(|bytes| bytes.checked_add(4 * size_of::<usize>()))
                .ok_or(Decline::Memory)?;
        }
    }
    let rounded_offset = master.objective_offset();
    let exact_offset = master.obj_offset_exact_cow();
    objective_scale.observe(&exact_offset)?;
    if exact(rounded_offset).as_ref() != Some(exact_offset.as_ref()) {
        exact_side_bytes = exact_side_bytes
            .checked_add(rational_storage_bytes(&exact_offset)?)
            .and_then(|bytes| bytes.checked_add(2 * size_of::<usize>()))
            .ok_or(Decline::Memory)?;
    }

    let vec_bytes = |count: usize, width: usize| -> Result<usize, Decline> {
        count.checked_mul(width).ok_or(Decline::Memory)
    };
    let add = |left: usize, right: usize| -> Result<usize, Decline> {
        left.checked_add(right).ok_or(Decline::Memory)
    };

    // One `Model` clone retained by LpSession, including exact-side payloads.
    let model_clone = add(
        vec_bytes(n, size_of::<crate::model::ColSpec>())?,
        add(
            vec_bytes(m, size_of::<crate::model::RowSpec>())?,
            add(vec_bytes(nnz, size_of::<(u32, f64)>())?, exact_side_bytes)?,
        )?,
    )?;

    // FloatLp owns CSC and CSR copies, bound/cost arrays, construction cursors,
    // and (conservatively, although the bounded entry skips scaling) a second
    // numeric matrix.
    let cells = m.checked_mul(n).ok_or(Decline::Memory)?;
    let dense_cells = if cells > 0 && cells <= (1 << 20) && nnz.saturating_mul(2) >= cells {
        cells
    } else {
        0
    };
    let matrix_bytes = add(
        vec_bytes(nnz, 2 * size_of::<usize>() + 4 * size_of::<f64>())?,
        vec_bytes(dense_cells, 2 * size_of::<f64>())?,
    )?;
    let float_vectors = vec_bytes(
        cols.checked_add(n)
            .and_then(|v| v.checked_add(m))
            .ok_or(Decline::Memory)?,
        16 * size_of::<usize>(),
    )?;

    // Simplex keeps two eta files during a rebuild, alongside peel/bump
    // factorization scratch. `plain_cold` keeps the RMP out of the separately
    // environment-sized LU lane.
    let eta_entries = nnz
        .saturating_mul(4)
        .max(m.saturating_mul(16))
        .max(m.saturating_mul(m))
        .max(1024);
    let simplex = add(
        vec_bytes(cols.checked_add(m).ok_or(Decline::Memory)?, 256)?,
        vec_bytes(eta_entries, 256)?,
    )?;

    // Exact tableau entries are ratios of integer minors after the per-row
    // scaling above.  Basic values and reduced costs additionally multiply by
    // bounds/objective coefficients.  Their family-wide LCMs matter: unrelated
    // RHS or objective denominators can otherwise grow during accumulation
    // even when each individual rational is tiny.
    let column_bits =
        usize::try_from(cols.max(1).next_power_of_two().ilog2()).map_err(|_| Decline::Memory)?;
    let bound_bits = bound_scale.scaled_numerator_bits()?;
    let objective_bits = objective_scale.scaled_numerator_bits()?;
    // A shifted value can transiently multiply a basic value by a tableau
    // ratio twice before canonical cancellation (three minor factors total).
    // The independently bounded objective value uses two minor factors plus
    // both input families.  Reserve the larger of those peaks.
    let value_transient_bits = basis_minor_bits
        .checked_mul(3)
        .and_then(|bits| bits.checked_add(bound_bits))
        .and_then(|bits| bits.checked_add(column_bits))
        .and_then(|bits| bits.checked_add(16))
        .ok_or(Decline::Memory)?;
    let objective_transient_bits = basis_minor_bits
        .checked_mul(2)
        .and_then(|bits| bits.checked_add(bound_bits))
        .and_then(|bits| bits.checked_add(objective_bits))
        .and_then(|bits| bits.checked_add(column_bits.saturating_mul(2)))
        .and_then(|bits| bits.checked_add(16))
        .ok_or(Decline::Memory)?;
    let exact_bits = value_transient_bits.max(objective_transient_bits);
    let exact_cell = max_exact_tableau_cell_bytes(exact_bits.max(1))?;
    work.charge_terms(
        m.checked_mul(m)
            .and_then(|value| value.checked_mul(m))
            .and_then(|value| value.checked_mul(2))
            .ok_or(Decline::Resource)?,
    )?;
    let exact_vectors = vec_bytes(cols.checked_mul(8).ok_or(Decline::Memory)?, exact_cell)?;
    let engine_bytes = match engine {
        RmpEngine::CertifiedFloat => {
            let dense_exact = vec_bytes(
                m.checked_mul(m)
                    .and_then(|value| value.checked_mul(2))
                    .ok_or(Decline::Memory)?,
                exact_cell,
            )?;
            [
                matrix_bytes,
                float_vectors,
                simplex,
                dense_exact,
                exact_vectors,
            ]
            .into_iter()
            .try_fold(0usize, |total, bytes| {
                total.checked_add(bytes).ok_or(Decline::Memory)
            })?
        }
        RmpEngine::BoundedExact => {
            // ExactLp may densify every row. Substitution holds a replacement
            // beside the prior row, so reserve two full tableaux.
            let tableau = vec_bytes(
                m.checked_mul(cols)
                    .and_then(|value| value.checked_mul(2))
                    .ok_or(Decline::Memory)?,
                exact_cell,
            )?;
            add(tableau, exact_vectors)?
        }
    };
    let bytes = [model_clone, engine_bytes, ROUTE_METADATA_RESERVE]
        .into_iter()
        .try_fold(0usize, |total, bytes| {
            total.checked_add(bytes).ok_or(Decline::Memory)
        })?;
    Ok(RmpMaterialization {
        bytes,
        engine,
        #[cfg(test)]
        exact_cell_bytes: exact_cell,
        #[cfg(test)]
        exact_cell_bits: exact_bits,
    })
}

#[cfg(test)]
thread_local! {
    static RMP_SESSION_MATERIALIZATIONS: std::cell::Cell<usize> = const {
        std::cell::Cell::new(0)
    };
}

#[cfg(test)]
fn note_rmp_session_materialization() {
    RMP_SESSION_MATERIALIZATIONS.with(|count| count.set(count.get().saturating_add(1)));
}

#[cfg(not(test))]
fn note_rmp_session_materialization() {}

fn rational_to_f64(value: &BigRational) -> Result<f64, Decline> {
    let rounded = value
        .to_f64()
        .filter(|value| value.is_finite())
        .ok_or(Decline::Arithmetic)?;
    // `Model`'s exact side store overrides a retained rounded coefficient; it
    // cannot introduce a term that `add_row`/`set_objective` dropped as zero.
    // Decline extreme underflow instead of silently building a different RMP.
    if !value.is_zero() && rounded == 0.0 {
        return Err(Decline::Arithmetic);
    }
    Ok(rounded)
}

fn record_row_truth(
    model: &mut Model,
    row: Row,
    coefficients: &[(Col, BigRational)],
    lower: Option<&BigRational>,
    upper: Option<&BigRational>,
    work: &mut WorkMeter,
) -> Result<(), Decline> {
    for (index, (column, value)) in coefficients.iter().enumerate() {
        if index & 0xff == 0 {
            work.charge_terms(0x100.min(coefficients.len().saturating_sub(index)))?;
        }
        let rounded = rational_to_f64(value)?;
        if exact(rounded).as_ref() != Some(value) {
            model.record_inexact_row_coeff(row, column.0, value.clone());
        }
    }
    if let Some(value) = lower {
        let rounded = rational_to_f64(value)?;
        if exact(rounded).as_ref() != Some(value) {
            model.record_inexact_row_bound(row, true, value.clone());
        }
    }
    if let Some(value) = upper {
        let rounded = rational_to_f64(value)?;
        if exact(rounded).as_ref() != Some(value) {
            model.record_inexact_row_bound(row, false, value.clone());
        }
    }
    Ok(())
}

/// Round one exact RMP row into the float advice lane while preserving
/// `Model::add_row`'s established zero-filter semantics. A true nonzero that
/// underflows to `0.0` remains an arithmetic decline (enforced by
/// [`rational_to_f64`]); only an exact zero may disappear from the advice row.
/// The exact input stays untouched for side-store recording after insertion.
fn rounded_row_advice(
    coefficients: &[(Col, BigRational)],
    work: &mut WorkMeter,
) -> Result<Vec<(u32, f64)>, Decline> {
    let mut rounded = Vec::with_capacity(coefficients.len());
    for (index, (column, value)) in coefficients.iter().enumerate() {
        if index & 0xff == 0 {
            work.charge_terms(0x100.min(coefficients.len().saturating_sub(index)))?;
        }
        let advice = rational_to_f64(value)?;
        if advice != 0.0 {
            rounded.push((column.0, advice));
        }
    }
    Ok(rounded)
}

fn solve_restricted_master(
    plan: &Plan,
    patterns: &[Vec<Pattern>],
    phase: MasterPhase,
    arithmetic: MasterArithmetic,
    memory_budget: Option<usize>,
    work: &mut WorkMeter,
) -> Result<RestrictedMasterResult, Decline> {
    work.checkpoint()?;
    let real_columns: usize = patterns.iter().map(Vec::len).sum();
    let artificial_columns =
        usize::from(phase == MasterPhase::Feasibility) * plan.master_rows.len();
    let total_columns = real_columns
        .checked_add(artificial_columns)
        .ok_or(Decline::Resource)?;
    if total_columns > MAX_RESTRICTED_COLUMNS {
        return Err(Decline::Resource);
    }
    // Recognition and the RMP each receive half the route-local envelope.
    // Pattern/rational construction is charged incrementally below; once the
    // complete master shape is known, `rmp_materialization` preflights and
    // charges the nested model/engine/certificate peak before LpSession exists.
    let mut meter = MemoryMeter::new(memory_budget, work.deadline.is_some())?;
    meter.charge(ROUTE_METADATA_RESERVE)?;
    meter.charge(pattern_cache_storage_bytes(patterns, work)?)?;
    let mut master = Model::new();
    let mut column_map = Vec::with_capacity(real_columns);
    let mut pattern_data = Vec::with_capacity(real_columns);
    for (block_index, block_patterns) in patterns.iter().enumerate() {
        for (pattern_index, pattern) in block_patterns.iter().enumerate() {
            work.charge_round()?;
            let transient = max_rational_storage_bytes(MAX_RATIONAL_BITS.saturating_mul(2))?
                .checked_mul(plan.master_rows.len().saturating_add(1))
                .ok_or(Decline::Memory)?;
            meter.charge(transient)?;
            let column = master.add_col(0.0, f64::INFINITY);
            column_map.push((block_index, pattern_index));
            let (cost, contribution) = pattern_cost_and_master(
                &plan.blocks[block_index],
                pattern,
                plan.master_rows.len(),
                work,
            )?;
            let mut retained = rational_storage_bytes(&cost)?;
            for (_, value) in &contribution {
                let value_bytes = rational_storage_bytes(value)?;
                retained = retained
                    .checked_add(size_of::<usize>())
                    .and_then(|bytes| bytes.checked_add(value_bytes))
                    .ok_or(Decline::Memory)?;
            }
            retained = retained.checked_mul(4).ok_or(Decline::Memory)?;
            if retained > transient {
                meter.charge(retained - transient)?;
            } else {
                meter.release(transient - retained);
            }
            pattern_data.push((column, cost, contribution));
        }
    }
    let artificial_start = master.num_cols();
    let mut artificial = Vec::new();
    if phase == MasterPhase::Feasibility {
        for _ in &plan.master_rows {
            work.charge_terms(1)?;
            artificial.push(master.add_col(0.0, f64::INFINITY));
        }
    }
    let artificial_range = artificial_start..master.num_cols();

    let mut cover_rows = Vec::with_capacity(plan.master_rows.len());
    for master_index in 0..plan.master_rows.len() {
        work.charge_round()?;
        let mut exact_coefficients = Vec::new();
        for (column, _, contribution) in &pattern_data {
            work.charge_terms(1)?;
            if let Ok(position) =
                contribution.binary_search_by_key(&master_index, |(index, _)| *index)
            {
                exact_coefficients.push((*column, contribution[position].1.clone()));
            }
        }
        if let Some(column) = artificial.get(master_index) {
            exact_coefficients.push((*column, BigRational::one()));
        }
        let rounded = rounded_row_advice(&exact_coefficients, work)?;
        let lower = rational_to_f64(&plan.master_rhs[master_index])?;
        let mut row_decline = None;
        let row = {
            let mut row_work = |units| match work.charge_terms(units) {
                Ok(()) => true,
                Err(reason) => {
                    row_decline.get_or_insert(reason);
                    false
                }
            };
            master.add_row_sorted_unique_with_work(lower, f64::INFINITY, rounded, &mut row_work)
        };
        if let Some(reason) = row_decline {
            return Err(reason);
        }
        let row = row.ok_or(Decline::Resource)?;
        record_row_truth(
            &mut master,
            row,
            &exact_coefficients,
            Some(&plan.master_rhs[master_index]),
            None,
            work,
        )?;
        cover_rows.push(row);
    }
    let mut convexity_rows = Vec::with_capacity(plan.blocks.len());
    for block_index in 0..plan.blocks.len() {
        work.charge_round()?;
        let mut coefficients = Vec::new();
        for (column, (block, _)) in column_map.iter().enumerate() {
            if column & 0xff == 0 {
                work.charge_terms(0x100.min(column_map.len().saturating_sub(column)))?;
            }
            if *block == block_index {
                coefficients.push((column as u32, 1.0));
            }
        }
        let mut row_decline = None;
        let row = {
            let mut row_work = |units| match work.charge_terms(units) {
                Ok(()) => true,
                Err(reason) => {
                    row_decline.get_or_insert(reason);
                    false
                }
            };
            master.add_row_sorted_unique_with_work(1.0, 1.0, coefficients, &mut row_work)
        };
        if let Some(reason) = row_decline {
            return Err(reason);
        }
        convexity_rows.push(row.ok_or(Decline::Resource)?);
    }
    let mut objective_exact = Vec::new();
    match phase {
        MasterPhase::Feasibility => {
            for (index, column) in artificial.iter().enumerate() {
                if index & 0xff == 0 {
                    work.charge_terms(0x100.min(artificial.len().saturating_sub(index)))?;
                }
                objective_exact.push((*column, BigRational::one()));
            }
        }
        MasterPhase::Objective => {
            for (index, (column, cost, _)) in pattern_data.iter().enumerate() {
                if index & 0xff == 0 {
                    work.charge_terms(0x100.min(pattern_data.len().saturating_sub(index)))?;
                }
                if !cost.is_zero() {
                    objective_exact.push((*column, cost.clone()));
                }
            }
        }
    }
    let mut objective_rounded = Vec::with_capacity(objective_exact.len());
    for (index, (column, value)) in objective_exact.iter().enumerate() {
        if index & 0xff == 0 {
            work.charge_terms(0x100.min(objective_exact.len().saturating_sub(index)))?;
        }
        objective_rounded.push((*column, rational_to_f64(value)?));
    }
    let mut objective_decline = None;
    let objective_installed = {
        let mut objective_work = |units| match work.charge_terms(units) {
            Ok(()) => true,
            Err(reason) => {
                objective_decline.get_or_insert(reason);
                false
            }
        };
        master.set_objective_with_work(&objective_rounded, Sense::Minimize, &mut objective_work)
    };
    if let Some(reason) = objective_decline {
        return Err(reason);
    }
    if !objective_installed {
        return Err(Decline::Resource);
    }
    for (column, value) in &objective_exact {
        work.charge_terms(1)?;
        let rounded = rational_to_f64(value)?;
        if exact(rounded).as_ref() != Some(value) {
            master.record_inexact_obj_coeff(column.0, value.clone());
        }
    }

    work.checkpoint()?;
    let materialization =
        rmp_materialization(&master, arithmetic == MasterArithmetic::Exact, work)?;
    if materialization.bytes > meter.remaining() {
        return Err(Decline::Memory);
    }
    meter.charge(materialization.bytes)?;
    if meter.enforce_process_limit && process_memory_exceeded() {
        return Err(Decline::Memory);
    }
    let mut opts = SolveOpts::new().with_memory_budget(memory_budget);
    opts = if let Some(deadline) = work.deadline {
        opts.with_deadline(deadline)
    } else {
        opts.with_time_limit(ROUTE_WALL_CAP)
    };
    opts.require_certificates = true;
    opts.structure_routing = false;
    note_rmp_session_materialization();
    let mut clone_decline = None;
    let session = {
        let mut clone_work = |units| match work.charge_terms(units) {
            Ok(()) => true,
            Err(reason) => {
                clone_decline.get_or_insert(reason);
                false
            }
        };
        LpSession::new_prevalidated_with_work(&master, &opts, &mut clone_work)
    };
    if let Some(reason) = clone_decline {
        return Err(reason);
    }
    let mut session = session
        .map_err(|_| Decline::Master)?
        .ok_or(Decline::Master)?;
    work.checkpoint()?;
    if meter.enforce_process_limit && process_memory_exceeded() {
        return Err(Decline::Memory);
    }
    let mut nested_decline = None;
    let attempt = {
        let mut nested_work = |units| match work.charge_terms(units) {
            Ok(()) => true,
            Err(reason) => {
                nested_decline.get_or_insert(reason);
                false
            }
        };
        match materialization.engine {
            RmpEngine::CertifiedFloat => {
                session.optimize_model_objective_float_only(&mut nested_work)
            }
            RmpEngine::BoundedExact => {
                session.optimize_model_objective_exact_only(&mut nested_work)
            }
        }
    };
    if let Some(reason) = nested_decline {
        return Err(reason);
    }
    let outcome = attempt
        .map_err(|_| Decline::Master)?
        .ok_or(Decline::Master)?;
    work.checkpoint()?;
    if meter.enforce_process_limit && process_memory_exceeded() {
        return Err(Decline::Memory);
    }
    let Outcome::Optimal {
        value,
        model_values,
        cert: Some(certificate),
    } = outcome
    else {
        return Err(if work.checkpoint().is_err() {
            Decline::Deadline
        } else {
            Decline::Master
        });
    };
    let mut replay_decline = None;
    let replayed = {
        let mut replay_work = |units| match work.charge_terms(units) {
            Ok(()) => Ok(()),
            Err(reason) => {
                replay_decline.get_or_insert(reason);
                Err(crate::CertificateError::DeadlineExceeded)
            }
        };
        certificate.verify_with_work(&master, &mut replay_work)
    };
    if let Some(reason) = replay_decline {
        return Err(reason);
    }
    replayed.map_err(|_| Decline::Verification)?;
    work.checkpoint()?;
    let mut row_duals = vec![BigRational::zero(); master.num_rows()];
    for multiplier in &certificate.multipliers {
        work.charge_terms(1)?;
        if !rational_within_cap(&multiplier.coeff) {
            return Err(Decline::Resource);
        }
        match multiplier.fact {
            FactRef::RowBound { row, side } => {
                let slot = row_duals
                    .get_mut(row.index())
                    .ok_or(Decline::Verification)?;
                match side {
                    BoundSide::Lower => {
                        bounded_add_assign(slot, multiplier.coeff.clone())?;
                    }
                    BoundSide::Upper => {
                        bounded_sub_assign(slot, multiplier.coeff.clone())?;
                    }
                }
            }
            FactRef::ColBound { .. } => {}
            #[allow(unreachable_patterns)]
            _ => return Err(Decline::Verification),
        }
    }
    let cover_duals = cover_rows
        .iter()
        .map(|row| row_duals[row.index()].clone())
        .collect::<Vec<_>>();
    if cover_duals.iter().any(BigRational::is_negative) {
        return Err(Decline::Verification);
    }
    let convexity_duals = convexity_rows
        .iter()
        .map(|row| row_duals[row.index()].clone())
        .collect::<Vec<_>>();
    if !rational_within_cap(&value) {
        return Err(Decline::Resource);
    }
    for values in [model_values.as_slice(), convexity_duals.as_slice()] {
        for (index, value) in values.iter().enumerate() {
            if index & 0xff == 0 {
                work.charge_terms(0x100.min(values.len().saturating_sub(index)))?;
            }
            if !rational_within_cap(value) {
                return Err(Decline::Resource);
            }
        }
    }
    Ok(RestrictedMasterResult {
        value,
        values: model_values,
        cover_duals,
        convexity_duals,
        column_map,
        artificial_range,
    })
}

fn patterns_equal_with_work(
    left: &Pattern,
    right: &Pattern,
    work: &mut WorkMeter,
) -> Result<bool, Decline> {
    work.charge_terms(1)?;
    match (left, right) {
        (Pattern::Initial { exit: left }, Pattern::Initial { exit: right }) => Ok(left == right),
        (
            Pattern::Source {
                amounts: left_amounts,
                exits: left_exits,
            },
            Pattern::Source {
                amounts: right_amounts,
                exits: right_exits,
            },
        ) => {
            if left_amounts.len() != right_amounts.len() || left_exits.len() != right_exits.len() {
                return Ok(false);
            }
            for index in 0..left_amounts.len() {
                if index & 0xff == 0 {
                    work.charge_terms(0x100.min(left_amounts.len().saturating_sub(index)))?;
                }
                if left_amounts[index] != right_amounts[index] {
                    return Ok(false);
                }
            }
            for index in 0..left_exits.len() {
                if index & 0xff == 0 {
                    work.charge_terms(0x100.min(left_exits.len().saturating_sub(index)))?;
                }
                if left_exits[index] != right_exits[index] {
                    return Ok(false);
                }
            }
            Ok(true)
        }
        _ => Ok(false),
    }
}

fn contains_pattern_with_work(
    patterns: &[Pattern],
    candidate: &Pattern,
    work: &mut WorkMeter,
) -> Result<bool, Decline> {
    for pattern in patterns {
        if patterns_equal_with_work(pattern, candidate, work)? {
            return Ok(true);
        }
    }
    Ok(false)
}

fn add_priced_columns(
    plan: &Plan,
    patterns: &mut [Vec<Pattern>],
    result: &RestrictedMasterResult,
    phase: MasterPhase,
    memory_budget: Option<usize>,
    work: &mut WorkMeter,
) -> Result<(bool, bool, Vec<PricedPattern>), Decline> {
    let mut added = false;
    let mut duplicate_negative = false;
    // One ledger covers the complete pricing pass.  MITM prefix scratch is
    // charged and released per block. The aggregate preflight includes every
    // already-live second-half object plus all candidates and possible pattern
    // clones, so recognition's first half plus this peak stays within the
    // advertised route budget.
    let mut pricing_meter = MemoryMeter::new(memory_budget, work.deadline.is_some())?;
    pricing_meter.charge(pricing_pass_storage_bytes(plan, patterns, result, work)?)?;
    let mut priced = Vec::with_capacity(plan.blocks.len());
    for (block_index, block) in plan.blocks.iter().enumerate() {
        let candidate =
            price_block_production(block, &result.cover_duals, phase, &mut pricing_meter, work)?;
        let mut reduced = candidate.reduced_without_convexity.clone();
        bounded_sub_assign(&mut reduced, result.convexity_duals[block_index].clone())?;
        if reduced.is_negative() {
            if contains_pattern_with_work(&patterns[block_index], &candidate.pattern, work)? {
                duplicate_negative = true;
            } else {
                patterns[block_index].push(candidate.pattern.clone());
                added = true;
            }
        }
        priced.push(candidate);
    }
    Ok((added, duplicate_negative, priced))
}

fn reconstruct_pattern_values(
    block: &Block,
    pattern: &Pattern,
    work: &mut WorkMeter,
) -> Result<Vec<(u32, BigRational)>, Decline> {
    work.charge_round()?;
    let mut values = Vec::new();
    match (block, pattern) {
        (Block::Initial(block), Pattern::Initial { exit }) => {
            let quantity = block.chain.quantity.ok_or(Decline::Structure)?;
            let choice = block
                .chain
                .choices
                .get(*exit as usize)
                .ok_or(Decline::Structure)?;
            let quantity = BigRational::from_integer(quantity.into());
            work.charge_terms(choice.columns.len().saturating_add(1))?;
            values.extend(
                choice
                    .columns
                    .iter()
                    .map(|column| (*column, quantity.clone())),
            );
        }
        (Block::Source(block), Pattern::Source { amounts, exits }) => {
            if amounts.len() != block.chains.len() || exits.len() != block.chains.len() {
                return Err(Decline::Structure);
            }
            for ((chain, amount), exit) in block.chains.iter().zip(amounts).zip(exits) {
                work.charge_round()?;
                let choice = chain
                    .choices
                    .get(*exit as usize)
                    .ok_or(Decline::Structure)?;
                let amount = BigRational::from_integer((*amount).into());
                work.charge_terms(choice.columns.len().saturating_add(1))?;
                values.extend(
                    choice
                        .columns
                        .iter()
                        .map(|column| (*column, amount.clone())),
                );
            }
        }
        _ => return Err(Decline::Structure),
    }
    Ok(values)
}

fn reconstruct_master_point(
    model: &Model,
    plan: &Plan,
    patterns: &[Vec<Pattern>],
    result: &RestrictedMasterResult,
    priced: &[PricedPattern],
    memory_budget: Option<usize>,
    work: &mut WorkMeter,
) -> Result<(Vec<BigRational>, MemoryMeter), Decline> {
    let mut meter = MemoryMeter::new(memory_budget, work.deadline.is_some())?;
    meter.charge(ROUTE_METADATA_RESERVE)?;
    meter.charge(pattern_cache_storage_bytes(patterns, work)?)?;
    meter.charge(restricted_result_storage_bytes(result, work)?)?;
    meter.charge(priced_patterns_storage_bytes(priced, work)?)?;
    let zero = BigRational::zero();
    let zero_payload = rational_payload_bytes(&zero)?;
    meter.charge(
        model
            .num_cols()
            .checked_mul(
                size_of::<BigRational>()
                    .checked_add(zero_payload)
                    .ok_or(Decline::Memory)?,
            )
            .ok_or(Decline::Memory)?,
    )?;
    let mut source = Vec::with_capacity(model.num_cols());
    for column in 0..model.num_cols() {
        if column & 0xff == 0 {
            work.charge_terms(0x100.min(model.num_cols().saturating_sub(column)))?;
        }
        source.push(BigRational::zero());
    }
    for (rmp_column, &(block_index, pattern_index)) in result.column_map.iter().enumerate() {
        work.charge_round()?;
        let weight = result.values.get(rmp_column).ok_or(Decline::Verification)?;
        if !rational_within_cap(weight) {
            return Err(Decline::Resource);
        }
        if weight.is_zero() {
            continue;
        }
        let block = plan.blocks.get(block_index).ok_or(Decline::Verification)?;
        let pattern = patterns
            .get(block_index)
            .and_then(|patterns| patterns.get(pattern_index))
            .ok_or(Decline::Verification)?;
        for (column, value) in reconstruct_pattern_values(block, pattern, work)? {
            let slot = source
                .get_mut(column as usize)
                .ok_or(Decline::Verification)?;
            let old_payload = rational_payload_bytes(slot)?;
            let mut next = slot.clone();
            bounded_add_assign(&mut next, bounded_mul(weight, &value)?)?;
            let new_payload = rational_payload_bytes(&next)?;
            if new_payload > old_payload {
                meter.charge(new_payload - old_payload)?;
            } else {
                meter.release(old_payload - new_payload);
            }
            *slot = next;
        }
    }
    for (column, fixed) in plan.fixed_zero.iter().enumerate() {
        if column & 0xff == 0 {
            work.charge_terms(0x100.min(plan.fixed_zero.len().saturating_sub(column)))?;
        }
        if *fixed && !source[column].is_zero() {
            return Err(Decline::Verification);
        }
    }
    check_point_bounded(model, &source, work)?;
    Ok((source, meter))
}

fn certificate_storage_bytes(
    value: &BigRational,
    master_multipliers: &[(u32, BigRational)],
    priced: &[PricedPattern],
) -> Result<usize, Decline> {
    let mut bytes = rational_storage_bytes(value)?;
    for (_, multiplier) in master_multipliers {
        let multiplier_bytes = rational_storage_bytes(multiplier)?;
        bytes = bytes
            .checked_add(size_of::<u32>())
            .and_then(|total| total.checked_add(multiplier_bytes))
            .ok_or(Decline::Memory)?;
    }
    for pattern in priced {
        bytes = bytes
            .checked_add(size_of::<CertifiedBlockPattern>())
            .ok_or(Decline::Memory)?;
        match &pattern.pattern {
            Pattern::Source { amounts, exits } => {
                bytes = bytes
                    .checked_add(
                        amounts
                            .len()
                            .checked_mul(size_of::<i64>())
                            .ok_or(Decline::Memory)?,
                    )
                    .and_then(|total| total.checked_add(exits.len()))
                    .and_then(|total| total.checked_add(4 * size_of::<usize>()))
                    .ok_or(Decline::Memory)?;
            }
            Pattern::Initial { .. } => {}
        }
    }
    Ok(bytes)
}

fn lagrangian_bound(
    model: &Model,
    plan: &Plan,
    cover_duals: &[BigRational],
    priced: &[PricedPattern],
    work: &mut WorkMeter,
) -> Result<BigRational, Decline> {
    if cover_duals.len() != plan.master_rhs.len() || priced.len() != plan.blocks.len() {
        return Err(Decline::Verification);
    }
    let offset = model.obj_offset_exact_cow();
    if !rational_within_cap(&offset) {
        return Err(Decline::Resource);
    }
    let mut bound = offset.into_owned();
    for (dual, rhs) in cover_duals.iter().zip(&plan.master_rhs) {
        work.charge_terms(1)?;
        if dual.is_negative() || !rational_within_cap(dual) || !rational_within_cap(rhs) {
            return Err(Decline::Verification);
        }
        bounded_add_assign(&mut bound, bounded_mul(dual, rhs)?)?;
    }
    for pattern in priced {
        work.charge_terms(1)?;
        bounded_add_assign(&mut bound, pattern.reduced_without_convexity.clone())?;
    }
    Ok(bound)
}

fn certified_patterns(
    priced: &[PricedPattern],
    work: &mut WorkMeter,
) -> Result<Vec<CertifiedBlockPattern>, Decline> {
    work.charge_terms(priced.len())?;
    priced
        .iter()
        .map(|priced| match &priced.pattern {
            Pattern::Source { amounts, exits } => Ok(CertifiedBlockPattern::Source {
                amounts: amounts.clone(),
                exits: exits.clone(),
            }),
            Pattern::Initial { exit } => Ok(CertifiedBlockPattern::Initial { exit: *exit }),
        })
        .collect()
}

/// Turn only a rounded-advice solver miss into one explicit exact attempt.
/// Every other resource/verdict decline remains authoritative, and an exact
/// miss is never retried.  The caller keeps the same `WorkMeter` and memory
/// budget when it loops, so the transition cannot restart either envelope.
fn adjudicate_master_attempt(
    arithmetic: MasterArithmetic,
    attempt: Result<RestrictedMasterResult, Decline>,
    work: &WorkMeter,
) -> Result<Option<RestrictedMasterResult>, Decline> {
    match attempt {
        Ok(result) => Ok(Some(result)),
        Err(Decline::Master) if arithmetic == MasterArithmetic::Advice => {
            work.checkpoint()?;
            Ok(None)
        }
        Err(reason) => Err(reason),
    }
}

fn solve(
    model: &Model,
    plan: &Plan,
    memory_budget: Option<usize>,
    work: &mut WorkMeter,
) -> Result<BlockAngularDecision, Decline> {
    let mut patterns: Vec<Vec<Pattern>> = plan
        .blocks
        .iter()
        .map(|block| vec![initial_pattern(block)])
        .collect();
    let mut phase = MasterPhase::Feasibility;
    let mut force_exact = false;
    for _round in 0..MAX_COLUMN_GENERATION_ROUNDS {
        work.charge_round()?;
        let arithmetic = if force_exact {
            MasterArithmetic::Exact
        } else {
            MasterArithmetic::Advice
        };
        let attempt =
            solve_restricted_master(plan, &patterns, phase, arithmetic, memory_budget, work);
        let Some(result) = adjudicate_master_attempt(arithmetic, attempt, work)? else {
            force_exact = true;
            continue;
        };
        let (added, duplicate_negative, priced) =
            add_priced_columns(plan, &mut patterns, &result, phase, memory_budget, work)?;
        if added {
            force_exact = false;
            continue;
        }
        if duplicate_negative && arithmetic == MasterArithmetic::Advice {
            force_exact = true;
            continue;
        }
        if duplicate_negative {
            return Err(Decline::Verification);
        }
        match phase {
            MasterPhase::Feasibility => {
                if !result.value.is_zero()
                    || result
                        .artificial_range
                        .clone()
                        .any(|column| !result.values[column].is_zero())
                {
                    // This is a valid LP infeasibility lower bound, but this
                    // first route exports only optimality artifacts.  Leave a
                    // proof-producing native lane authoritative.
                    return Err(Decline::Master);
                }
                phase = MasterPhase::Objective;
                force_exact = false;
            }
            MasterPhase::Objective => {
                let (model_values, mut decision_meter) = reconstruct_master_point(
                    model,
                    plan,
                    &patterns,
                    &result,
                    &priced,
                    memory_budget,
                    work,
                )?;
                let value = bounded_objective_value_at(model, &model_values, work)?;
                let bound = lagrangian_bound(model, plan, &result.cover_duals, &priced, work)?;
                let offset = model.obj_offset_exact_cow();
                if !rational_within_cap(&offset) {
                    return Err(Decline::Resource);
                }
                let mut restricted_value = result.value.clone();
                bounded_add_assign(&mut restricted_value, offset.into_owned())?;
                if value != bound || restricted_value != value {
                    return Err(Decline::FractionalPrimal);
                }
                let master_multipliers = plan
                    .master_rows
                    .iter()
                    .copied()
                    .zip(result.cover_duals)
                    .collect::<Vec<_>>();
                decision_meter.charge(certificate_storage_bytes(
                    &value,
                    &master_multipliers,
                    &priced,
                )?)?;
                let certificate = BlockAngularOptimalityCertificate {
                    value: value.clone(),
                    master_multipliers,
                    minimizers: certified_patterns(&priced, work)?,
                };
                return Ok(BlockAngularDecision {
                    value,
                    model_values,
                    certificate,
                });
            }
        }
    }
    Err(Decline::Resource)
}

/// Try the bounded production route and independently replay its certificate
/// before returning a verdict to the session.
#[derive(Debug, Clone, Copy)]
enum ProductionStage {
    Budget,
    Recognition,
    Solve,
    Replay,
}

impl ProductionStage {
    const fn token(self) -> &'static str {
        match self {
            Self::Budget => "budget",
            Self::Recognition => "recognition",
            Self::Solve => "solve",
            Self::Replay => "replay",
        }
    }
}

struct ProductionFailure {
    stage: ProductionStage,
    reason: Decline,
    terms: usize,
    rounds: usize,
    master_rows: usize,
    blocks: usize,
}

struct ProductionSuccess {
    decision: BlockAngularDecision,
    terms: usize,
    rounds: usize,
    master_rows: usize,
    blocks: usize,
}

fn try_solve_certified_detailed(
    model: &Model,
    outer_deadline: Option<Instant>,
    route_memory_budget: usize,
) -> Result<ProductionSuccess, ProductionFailure> {
    let Some((recognition_deadline, deadline)) = route_deadlines(outer_deadline) else {
        return Err(ProductionFailure {
            stage: ProductionStage::Budget,
            reason: Decline::Deadline,
            terms: 0,
            rounds: 0,
            master_rows: 0,
            blocks: 0,
        });
    };
    let memory_budget = Some(route_memory_budget.min(MAX_DIAGNOSTIC_ROUTE_MEMORY));
    let mut work = WorkMeter::new(Some(recognition_deadline));
    let plan = recognize_with_work(
        model,
        memory_budget,
        PricingPreparation::ProductionMitm,
        &mut work,
    )
    .map_err(|reason| ProductionFailure {
        stage: ProductionStage::Recognition,
        reason,
        terms: work.terms,
        rounds: work.rounds,
        master_rows: 0,
        blocks: 0,
    })?;
    let master_rows = plan.master_rows.len();
    let blocks = plan.blocks.len();
    work.deadline = Some(deadline);
    work.checkpoint().map_err(|reason| ProductionFailure {
        stage: ProductionStage::Solve,
        reason,
        terms: work.terms,
        rounds: work.rounds,
        master_rows,
        blocks,
    })?;
    let decision =
        solve(model, &plan, memory_budget, &mut work).map_err(|reason| ProductionFailure {
            stage: ProductionStage::Solve,
            reason,
            terms: work.terms,
            rounds: work.rounds,
            master_rows,
            blocks,
        })?;
    drop(plan);
    verify_optimality_certificate_with_work(
        model,
        &decision.value,
        &decision.certificate,
        memory_budget,
        &mut work,
    )
    .map_err(|reason| ProductionFailure {
        stage: ProductionStage::Replay,
        reason,
        terms: work.terms,
        rounds: work.rounds,
        master_rows,
        blocks,
    })?;
    Ok(ProductionSuccess {
        decision,
        terms: work.terms,
        rounds: work.rounds,
        master_rows,
        blocks,
    })
}

pub(crate) fn try_solve_certified(
    model: &Model,
    outer_deadline: Option<Instant>,
    memory_budget: Option<usize>,
) -> Option<BlockAngularDecision> {
    try_solve_certified_detailed(model, outer_deadline, route_memory_limit(memory_budget))
        .ok()
        .map(|success| success.decision)
}

/// Run the exact production attempt and report the precise fail-closed stage.
/// This is explicit diagnostic tooling: it grants no proof authority and adds
/// no branch, clock, or environment read to the normal solve path.
#[doc(hidden)]
#[must_use]
pub fn diag_block_angular(model: &Model, seconds: f64, memory_budget: Option<usize>) -> String {
    let started = Instant::now();
    let duration = if seconds.is_finite() && seconds > 0.0 {
        Duration::from_secs_f64(seconds)
    } else {
        Duration::ZERO
    };
    let outer_deadline = started.checked_add(duration);
    let candidate = is_coarse_block_angular_candidate(model);
    let route_budget = memory_budget
        .unwrap_or(DEFAULT_ROUTE_MEMORY)
        .min(MAX_DIAGNOSTIC_ROUTE_MEMORY);
    let phase_cap = route_budget / ROUTE_MEMORY_PARTS;
    match try_solve_certified_detailed(model, outer_deadline, route_budget) {
        Ok(success) => format!(
            "block-angular candidate={candidate} status=optimal stage=replay \
             elapsed_ms={:.3} terms={} rounds={} master_rows={} blocks={} \
             route_budget_bytes={route_budget} phase_cap_bytes={phase_cap}",
            started.elapsed().as_secs_f64() * 1_000.0,
            success.terms,
            success.rounds,
            success.master_rows,
            success.blocks,
        ),
        Err(failure) => format!(
            "block-angular candidate={candidate} status=declined stage={} reason={} \
             elapsed_ms={:.3} terms={} rounds={} master_rows={} blocks={} \
             route_budget_bytes={route_budget} phase_cap_bytes={phase_cap}",
            failure.stage.token(),
            failure.reason.token(),
            started.elapsed().as_secs_f64() * 1_000.0,
            failure.terms,
            failure.rounds,
            failure.master_rows,
            failure.blocks,
        ),
    }
}

/// Independently rebuild the exact decomposition and replay a Lagrangian
/// optimality artifact against `model`.
pub fn verify_optimality_certificate(
    model: &Model,
    claimed_value: &BigRational,
    certificate: &BlockAngularOptimalityCertificate,
) -> Result<(), String> {
    let deadline = replay_deadline()
        .ok_or_else(|| "block-angular certificate rejected: Deadline".to_owned())?;
    verify_optimality_certificate_with_deadline(
        model,
        claimed_value,
        certificate,
        Some(deadline),
        Some(DEFAULT_ROUTE_MEMORY),
    )
    .map_err(|reason| format!("block-angular certificate rejected: {reason:?}"))
}

fn verify_optimality_certificate_with_deadline(
    model: &Model,
    claimed_value: &BigRational,
    certificate: &BlockAngularOptimalityCertificate,
    deadline: Option<Instant>,
    memory_budget: Option<usize>,
) -> Result<(), Decline> {
    let mut work = WorkMeter::new(deadline);
    verify_optimality_certificate_with_work(
        model,
        claimed_value,
        certificate,
        memory_budget,
        &mut work,
    )
}

fn verify_optimality_certificate_with_work(
    model: &Model,
    claimed_value: &BigRational,
    certificate: &BlockAngularOptimalityCertificate,
    memory_budget: Option<usize>,
    work: &mut WorkMeter,
) -> Result<(), Decline> {
    work.checkpoint()?;
    if &certificate.value != claimed_value
        || !rational_within_cap(&certificate.value)
        || certificate.master_multipliers.len() > MAX_MASTER_ROWS
        || certificate.minimizers.len() > MAX_BLOCKS
    {
        return Err(Decline::Verification);
    }
    let plan = recognize_with_work(
        model,
        memory_budget,
        PricingPreparation::ExhaustiveReplay,
        work,
    )?;
    if certificate.master_multipliers.len() != plan.master_rows.len()
        || certificate.minimizers.len() != plan.blocks.len()
    {
        return Err(Decline::Verification);
    }
    let mut duals = Vec::with_capacity(plan.master_rows.len());
    for ((row, value), expected_row) in certificate.master_multipliers.iter().zip(&plan.master_rows)
    {
        work.charge_terms(1)?;
        if row != expected_row || value.is_negative() || !rational_within_cap(value) {
            return Err(Decline::Verification);
        }
        duals.push(value.clone());
    }
    let mut priced = Vec::with_capacity(plan.blocks.len());
    for block in &plan.blocks {
        priced.push(price_block_exhaustive(
            block,
            &duals,
            MasterPhase::Objective,
            work,
        )?);
    }
    for (actual, recorded) in priced.iter().zip(&certificate.minimizers) {
        work.charge_terms(1)?;
        let matches = match (&actual.pattern, recorded) {
            (
                Pattern::Source { amounts, exits },
                CertifiedBlockPattern::Source {
                    amounts: recorded_amounts,
                    exits: recorded_exits,
                },
            ) => amounts == recorded_amounts && exits == recorded_exits,
            (Pattern::Initial { exit }, CertifiedBlockPattern::Initial { exit: recorded }) => {
                exit == recorded
            }
            _ => false,
        };
        if !matches {
            return Err(Decline::Verification);
        }
    }
    let bound = lagrangian_bound(model, &plan, &duals, &priced, work)?;
    if &bound != claimed_value {
        return Err(Decline::Verification);
    }
    Ok(())
}

pub(crate) fn certificate_parts(
    certificate: &BlockAngularOptimalityCertificate,
) -> (
    &BigRational,
    &[(u32, BigRational)],
    &[CertifiedBlockPattern],
) {
    (
        &certificate.value,
        &certificate.master_multipliers,
        &certificate.minimizers,
    )
}

pub(crate) fn certificate_from_parts(
    value: BigRational,
    master_multipliers: Vec<(u32, BigRational)>,
    minimizers: Vec<CertifiedBlockPattern>,
) -> BlockAngularOptimalityCertificate {
    BlockAngularOptimalityCertificate {
        value,
        master_multipliers,
        minimizers,
    }
}

pub(crate) fn source_pattern_parts(pattern: &CertifiedBlockPattern) -> Option<(&[i64], &[u8])> {
    match pattern {
        CertifiedBlockPattern::Source { amounts, exits } => Some((amounts, exits)),
        CertifiedBlockPattern::Initial { .. } => None,
    }
}

pub(crate) fn initial_pattern_exit(pattern: &CertifiedBlockPattern) -> Option<u8> {
    match pattern {
        CertifiedBlockPattern::Initial { exit } => Some(*exit),
        CertifiedBlockPattern::Source { .. } => None,
    }
}

pub(crate) fn source_pattern(amounts: Vec<i64>, exits: Vec<u8>) -> CertifiedBlockPattern {
    CertifiedBlockPattern::Source { amounts, exits }
}

pub(crate) fn certified_initial_pattern(exit: u8) -> CertifiedBlockPattern {
    CertifiedBlockPattern::Initial { exit }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn first_primes(count: usize) -> Vec<i64> {
        let mut primes: Vec<i64> = Vec::with_capacity(count);
        let mut candidate = 2i64;
        while primes.len() < count {
            if primes
                .iter()
                .take_while(|&&prime| prime.saturating_mul(prime) <= candidate)
                .all(|&prime| candidate % prime != 0)
            {
                primes.push(candidate);
            }
            candidate += 1;
        }
        primes
    }

    fn denominator_stress_master(
        rows: usize,
        columns: usize,
        matrix_exact: bool,
        rhs_exact: bool,
        objective_exact: bool,
    ) -> Model {
        let primes = first_primes(rows.max(columns));
        let mut master = Model::new();
        let columns = (0..columns)
            .map(|_| master.add_col(0.0, 1.0))
            .collect::<Vec<_>>();
        let rounded_row = columns
            .iter()
            .copied()
            .map(|column| (column, 1.0))
            .collect::<Vec<_>>();
        for row_index in 0..rows {
            let row = master.add_row(0.0, f64::INFINITY, &rounded_row);
            if matrix_exact {
                for (column_index, column) in columns.iter().enumerate() {
                    master.record_inexact_row_coeff(
                        row,
                        column.0,
                        BigRational::new(BigInt::one(), BigInt::from(primes[column_index])),
                    );
                }
            }
            if rhs_exact {
                master.record_inexact_row_bound(
                    row,
                    true,
                    BigRational::new(BigInt::one(), BigInt::from(primes[row_index])),
                );
            }
        }
        let rounded_objective = columns
            .iter()
            .copied()
            .map(|column| (column, 1.0))
            .collect::<Vec<_>>();
        master.set_objective(&rounded_objective, Sense::Minimize);
        if objective_exact {
            for (column_index, column) in columns.iter().enumerate() {
                master.record_inexact_obj_coeff(
                    column.0,
                    BigRational::new(BigInt::one(), BigInt::from(primes[column_index])),
                );
            }
        }
        master
    }

    fn denominator_stress_plan(size: usize) -> (Plan, Vec<Vec<Pattern>>) {
        let primes = first_primes(size);
        let blocks = (0..size)
            .map(|column| {
                Block::Initial(InitialBlock {
                    chain: Chain {
                        root: None,
                        states: Vec::new(),
                        exits: Vec::new(),
                        quantity: Some(1),
                        choices: vec![ChainChoice {
                            columns: Vec::new(),
                            cost_per_unit: BigRational::new(
                                BigInt::one(),
                                BigInt::from(primes[column]),
                            ),
                            master_per_unit: (0..size)
                                .map(|row| {
                                    (
                                        row,
                                        BigRational::new(
                                            BigInt::one(),
                                            BigInt::from(primes[column]),
                                        ),
                                    )
                                })
                                .collect(),
                        }],
                    },
                })
            })
            .collect::<Vec<_>>();
        let plan = Plan {
            fixed_zero: Vec::new(),
            master_rows: (0..size)
                .map(|row| u32::try_from(row).expect("bounded master row"))
                .collect(),
            master_rhs: (0..size)
                .map(|row| BigRational::new(BigInt::one(), BigInt::from(primes[row])))
                .collect(),
            blocks,
        };
        let patterns = (0..size)
            .map(|_| vec![Pattern::Initial { exit: 0 }])
            .collect();
        (plan, patterns)
    }

    fn fixture_column(model: &mut Model, integral: bool) -> Col {
        if integral {
            model.add_int_col(0.0, 10.0)
        } else {
            model.add_col(0.0, 10.0)
        }
    }

    fn source_model_variant(integral: bool, block_count: usize, sense: Option<Sense>) -> Model {
        // Two source blocks, each with two chains of length two, linked by two
        // cover rows.  Capacity is y0 + y1 <= 2.  The unique cheapest optimum
        // sends both units through the appropriate first exits.
        let mut model = Model::new();
        let mut block_columns = Vec::new();
        for _ in 0..block_count {
            let roots = [
                fixture_column(&mut model, integral),
                fixture_column(&mut model, integral),
            ];
            let mut columns = Vec::new();
            for root in roots {
                let state0 = fixture_column(&mut model, integral);
                let state1 = fixture_column(&mut model, integral);
                let exit0 = fixture_column(&mut model, integral);
                let exit1 = fixture_column(&mut model, integral);
                model.add_row(0.0, 0.0, &[(root, 1.0), (state0, -1.0)]);
                model.add_row(0.0, 0.0, &[(state0, 1.0), (state1, -1.0), (exit0, -1.0)]);
                model.add_row(0.0, 0.0, &[(state1, 1.0), (exit1, -1.0)]);
                columns.push((root, state0, state1, exit0, exit1));
            }
            model.add_row(f64::NEG_INFINITY, 2.0, &[(roots[0], 1.0), (roots[1], 1.0)]);
            block_columns.push(columns);
        }
        for chain in 0..2 {
            let coefficients = block_columns
                .iter()
                .flat_map(|block| [(block[chain].1, 1.0), (block[chain].2, 1.0)])
                .collect::<Vec<_>>();
            model.add_row(2.0, f64::INFINITY, &coefficients);
        }
        let mut objective = Vec::new();
        for block in &block_columns {
            for (_, _, _, exit0, exit1) in block {
                objective.push((*exit0, 1.0));
                objective.push((*exit1, 3.0));
            }
        }
        if let Some(sense) = sense {
            model.set_objective(&objective, sense);
        }
        model
    }

    fn source_model() -> Model {
        source_model_variant(true, 2, Some(Sense::Minimize))
    }

    fn source_blocks(plan: &Plan) -> Vec<&SourceBlock> {
        plan.blocks
            .iter()
            .filter_map(|block| match block {
                Block::Source(source) => Some(source),
                Block::Initial(_) => None,
            })
            .collect()
    }

    fn exact_pricing_fixture(
        maxima: Vec<i64>,
        weights: Vec<i128>,
        rhs: i128,
    ) -> (ExactCapacityDomain, Vec<Vec<i64>>) {
        let signature = CapacityDomainSignature {
            maxima,
            weights,
            rhs,
        };
        let mut meter =
            MemoryMeter::new(Some(DEFAULT_ROUTE_MEMORY), false).expect("bounded fixture memory");
        meter
            .charge(ROUTE_METADATA_RESERVE)
            .expect("fixture metadata");
        let mut preparation_work = WorkMeter::new(None);
        let mitm = prepare_mitm_assignments(&signature, &mut meter, &mut preparation_work)
            .expect("bounded exact domain prepares");
        let mut tuples = Vec::new();
        let mut current = vec![0i64; signature.maxima.len()];
        let mut enumeration_work = WorkMeter::new(None);
        enumerate_capacity_tuples_i128(
            0,
            &signature.maxima,
            &signature.weights,
            signature.rhs,
            &mut current,
            0,
            &mut tuples,
            &mut enumeration_work,
        )
        .expect("bounded exact tuples enumerate");
        (
            ExactCapacityDomain {
                signature,
                mitm: Some(mitm),
            },
            tuples,
        )
    }

    fn assert_mitm_matches_exhaustive(
        maxima: Vec<i64>,
        weights: Vec<i128>,
        rhs: i128,
        costs: Vec<BigRational>,
    ) -> (BigRational, Vec<i64>) {
        let (domain, tuples) = exact_pricing_fixture(maxima, weights, rhs);
        let mut exhaustive_work = WorkMeter::new(None);
        let expected = price_source_amounts_exhaustive(&tuples, &costs, &mut exhaustive_work)
            .expect("exhaustive price");
        let mut meter =
            MemoryMeter::new(Some(DEFAULT_ROUTE_MEMORY), false).expect("bounded pricing memory");
        meter
            .charge(ROUTE_METADATA_RESERVE)
            .expect("pricing metadata");
        let mut mitm_work = WorkMeter::new(None);
        let actual = price_source_amounts_mitm(&domain, &costs, &mut meter, &mut mitm_work)
            .expect("MITM price");
        assert_eq!(actual, expected);
        actual
    }

    #[test]
    fn mitm_pricing_matches_exhaustive_across_all_supports_and_signed_rationals() {
        for support in 1..=MAX_CAPACITY_SUPPORT {
            let maxima = vec![if support <= 4 { 2 } else { 1 }; support];
            let weights = (0..support)
                .map(|index| i128::try_from(index + 1).expect("small support"))
                .collect::<Vec<_>>();
            let rhs = maxima
                .iter()
                .zip(&weights)
                .map(|(maximum, weight)| i128::from(*maximum) * *weight)
                .sum::<i128>()
                / 2;
            let costs = (0..support)
                .map(|index| match index % 3 {
                    0 => {
                        BigRational::new((-i64::try_from(index).unwrap_or(0) - 1).into(), 3.into())
                    }
                    1 => BigRational::zero(),
                    _ => BigRational::new((i64::try_from(index).unwrap_or(0) + 2).into(), 5.into()),
                })
                .collect();
            assert_mitm_matches_exhaustive(maxima, weights, rhs, costs);
        }
    }

    #[test]
    fn mitm_pricing_breaks_exact_cost_ties_by_the_full_tuple() {
        let (value, amounts) = assert_mitm_matches_exhaustive(
            vec![1, 1],
            vec![1, 1],
            1,
            vec![BigRational::from_integer((-1).into()); 2],
        );
        assert_eq!(value, BigRational::from_integer((-1).into()));
        assert_eq!(amounts, vec![0, 1], "[0,1] is lexicographically first");

        let (zero_value, zero_amounts) = assert_mitm_matches_exhaustive(
            vec![2, 2, 2, 2],
            vec![1, 2, 3, 4],
            7,
            vec![BigRational::zero(); 4],
        );
        assert!(zero_value.is_zero());
        assert_eq!(zero_amounts, vec![0, 0, 0, 0]);
    }

    #[test]
    fn mitm_pricing_handles_checked_i128_activity_boundaries() {
        let large = i128::MAX / 3;
        assert_mitm_matches_exhaustive(
            vec![1, 1, 1],
            vec![large, large - 1, 1],
            large.checked_mul(2).expect("bounded rhs"),
            vec![
                BigRational::new((-7).into(), 11.into()),
                BigRational::new((-5).into(), 13.into()),
                BigRational::new(1.into(), 17.into()),
            ],
        );
    }

    #[test]
    fn production_pricing_falls_back_exhaustively_without_an_i128_domain() {
        let huge = BigInt::one() << 200usize;
        let coefficients = vec![
            BigRational::from_integer(huge.clone()),
            BigRational::from_integer(&huge + BigInt::one()),
        ];
        let capacity = BigRational::from_integer(&huge + BigInt::from(3));
        assert_eq!(integral_capacity_row(&coefficients, &capacity), Ok(None));

        let chain = |cost: i64| Chain {
            root: Some(0),
            states: Vec::new(),
            exits: Vec::new(),
            quantity: None,
            choices: vec![ChainChoice {
                columns: Vec::new(),
                cost_per_unit: BigRational::from_integer(cost.into()),
                master_per_unit: Vec::new(),
            }],
        };
        let block = Block::Source(SourceBlock {
            chains: vec![chain(-1), chain(-1)],
            tuples: Arc::from([vec![0, 0], vec![0, 1], vec![1, 0]]),
            exact_domain: None,
        });
        MITM_SOURCE_PRICINGS.with(|count| count.set(0));
        EXHAUSTIVE_SOURCE_PRICINGS.with(|count| count.set(0));
        let mut meter = MemoryMeter::new(Some(DEFAULT_ROUTE_MEMORY), false)
            .expect("bounded production pricing memory");
        meter
            .charge(ROUTE_METADATA_RESERVE)
            .expect("pricing metadata");
        let mut work = WorkMeter::new(None);
        let priced =
            price_block_production(&block, &[], MasterPhase::Objective, &mut meter, &mut work)
                .expect("non-i128 source falls back");
        assert_eq!(
            priced.pattern,
            Pattern::Source {
                amounts: vec![0, 1],
                exits: vec![0, 0],
            }
        );
        MITM_SOURCE_PRICINGS.with(|count| assert_eq!(count.get(), 0));
        EXHAUSTIVE_SOURCE_PRICINGS.with(|count| assert_eq!(count.get(), 1));
    }

    #[test]
    fn local_mitm_capacity_pressure_preserves_exact_exhaustive_pricing() {
        let signature = CapacityDomainSignature {
            maxima: vec![1, 1],
            weights: vec![1, 1],
            rhs: 1,
        };
        let (_, left_box, right_box) =
            balanced_capacity_split(&signature.maxima).expect("bounded split");
        let required =
            mitm_assignments_storage_bytes(left_box, right_box).expect("bounded advice size");
        let outer_budget = required
            .checked_sub(1)
            .and_then(|bytes| bytes.checked_mul(ROUTE_MEMORY_PARTS))
            .expect("nonzero bounded test budget");
        let mut meter =
            MemoryMeter::new(Some(outer_budget), false).expect("positive local memory box");
        assert_eq!(meter.remaining(), required - 1);
        MITM_ASSIGNMENT_PREPARATIONS.with(|count| count.set(0));
        let mut work = WorkMeter::new(None);
        assert!(
            prepare_mitm_assignments_if_local_capacity(&signature, &mut meter, &mut work)
                .expect("local advice pressure is fail-soft")
                .is_none()
        );
        MITM_ASSIGNMENT_PREPARATIONS.with(|count| assert_eq!(count.get(), 0));

        let mut expired_meter =
            MemoryMeter::new(Some(outer_budget), false).expect("positive local memory box");
        let mut expired = WorkMeter::new(Some(Instant::now()));
        assert_eq!(
            prepare_mitm_assignments_if_local_capacity(
                &signature,
                &mut expired_meter,
                &mut expired,
            )
            .err(),
            Some(Decline::Deadline),
            "deadline failure must not be relabelled as local advice pressure"
        );

        let chain = || Chain {
            root: Some(0),
            states: Vec::new(),
            exits: Vec::new(),
            quantity: None,
            choices: vec![ChainChoice {
                columns: Vec::new(),
                cost_per_unit: BigRational::from_integer((-1).into()),
                master_per_unit: Vec::new(),
            }],
        };
        let block = Block::Source(SourceBlock {
            chains: vec![chain(), chain()],
            tuples: Arc::from([vec![0, 0], vec![0, 1], vec![1, 0]]),
            exact_domain: Some(Arc::new(ExactCapacityDomain {
                signature,
                mitm: None,
            })),
        });
        MITM_SOURCE_PRICINGS.with(|count| count.set(0));
        EXHAUSTIVE_SOURCE_PRICINGS.with(|count| count.set(0));
        let mut pricing_meter = MemoryMeter::new(Some(DEFAULT_ROUTE_MEMORY), false)
            .expect("bounded production pricing memory");
        let mut pricing_work = WorkMeter::new(None);
        let priced = price_block_production(
            &block,
            &[],
            MasterPhase::Objective,
            &mut pricing_meter,
            &mut pricing_work,
        )
        .expect("exact exhaustive fallback remains available");
        assert_eq!(
            priced.pattern,
            Pattern::Source {
                amounts: vec![0, 1],
                exits: vec![0, 0],
            }
        );
        MITM_SOURCE_PRICINGS.with(|count| assert_eq!(count.get(), 0));
        EXHAUSTIVE_SOURCE_PRICINGS.with(|count| assert_eq!(count.get(), 1));
    }

    #[test]
    fn recognition_caches_low_memory_exact_domain_without_mitm_advice() {
        const MAXIMUM: i64 = (1 << 14) - 1;
        let mut model = Model::new();
        let mut states = Vec::new();
        let mut exits = Vec::new();
        for _ in 0..2 {
            let root = model.add_int_col(0.0, MAXIMUM as f64);
            let state = model.add_int_col(0.0, MAXIMUM as f64);
            let exit = model.add_int_col(0.0, MAXIMUM as f64);
            model.add_row(0.0, 0.0, &[(root, 1.0), (state, -1.0)]);
            model.add_row(0.0, 0.0, &[(state, 1.0), (exit, -1.0)]);
            model.add_row(f64::NEG_INFINITY, MAXIMUM as f64, &[(root, 1.0)]);
            states.push(state);
            exits.push(exit);
        }
        model.add_row(1.0, f64::INFINITY, &[(states[0], 1.0), (states[1], 1.0)]);
        model.set_objective(&[(exits[0], 1.0), (exits[1], 1.0)], Sense::Minimize);

        MITM_ASSIGNMENT_PREPARATIONS.with(|count| count.set(0));
        let plan = recognize(&model, None, Some(6 << 20))
            .expect("tuple oracle fits even though retained MITM advice does not");
        let sources = source_blocks(&plan);
        assert_eq!(sources.len(), 2);
        assert_eq!(sources[0].tuples.len(), 1 << 14);
        assert!(Arc::ptr_eq(&sources[0].tuples, &sources[1].tuples));
        let first_domain = sources[0]
            .exact_domain
            .as_ref()
            .expect("primitive exact domain retained");
        let second_domain = sources[1]
            .exact_domain
            .as_ref()
            .expect("identical exact domain reused");
        assert!(Arc::ptr_eq(first_domain, second_domain));
        assert!(first_domain.mitm.is_none());
        MITM_ASSIGNMENT_PREPARATIONS.with(|count| {
            assert_eq!(
                count.get(),
                0,
                "the local preflight must skip allocation and cache the fallback"
            )
        });

        MITM_SOURCE_PRICINGS.with(|count| count.set(0));
        EXHAUSTIVE_SOURCE_PRICINGS.with(|count| count.set(0));
        let mut meter = MemoryMeter::new(Some(DEFAULT_ROUTE_MEMORY), false)
            .expect("bounded production pricing memory");
        let mut work = WorkMeter::new(None);
        let priced = price_block_production(
            &plan.blocks[0],
            &[BigRational::zero()],
            MasterPhase::Objective,
            &mut meter,
            &mut work,
        )
        .expect("cached exact domain retains the exhaustive production oracle");
        assert_eq!(
            priced.pattern,
            Pattern::Source {
                amounts: vec![0],
                exits: vec![0],
            }
        );
        MITM_SOURCE_PRICINGS.with(|count| assert_eq!(count.get(), 0));
        EXHAUSTIVE_SOURCE_PRICINGS.with(|count| assert_eq!(count.get(), 1));
    }

    #[test]
    fn mitm_pricing_observes_memory_and_work_limits() {
        let (domain, _) = exact_pricing_fixture(vec![2, 2, 2, 2], vec![1, 2, 3, 4], 7);
        let costs = vec![BigRational::one(); 4];
        let mut tiny_meter = MemoryMeter::new(Some(2), false).expect("one-byte phase cap");
        let mut work = WorkMeter::new(None);
        assert_eq!(
            price_source_amounts_mitm(&domain, &costs, &mut tiny_meter, &mut work),
            Err(Decline::Memory)
        );

        let mut meter =
            MemoryMeter::new(Some(DEFAULT_ROUTE_MEMORY), false).expect("bounded pricing memory");
        let mut stopped = WorkMeter::with_test_deadline_after(0);
        assert_eq!(
            price_source_amounts_mitm(&domain, &costs, &mut meter, &mut stopped),
            Err(Decline::Deadline)
        );
    }

    #[test]
    fn coarse_scout_has_no_fixture_false_negative_and_grants_no_authority() {
        let model = source_model();
        assert!(is_coarse_block_angular_candidate(&model));

        let mut false_positive = model;
        let (coefficients, _, _) = false_positive.row(Row(0));
        let coefficients = coefficients
            .iter()
            .map(|&(column, coefficient)| (Col(column), coefficient))
            .collect::<Vec<_>>();
        false_positive.set_row(Row(0), 1.0, 1.0, &coefficients);
        assert!(
            is_coarse_block_angular_candidate(&false_positive),
            "the cheap unit-row census intentionally admits this shape"
        );
        assert!(
            recognize(&false_positive, None, Some(DEFAULT_ROUTE_MEMORY)).is_err(),
            "exact recognition must still reject the nonzero source conservation row"
        );
    }

    #[test]
    fn diagnostic_reports_the_exact_production_stage() {
        let solved = diag_block_angular(&source_model(), 60.0, Some(64 << 20));
        assert!(solved.contains("candidate=true"), "{solved}");
        assert!(solved.contains("status=optimal"), "{solved}");
        assert!(solved.contains("stage=replay"), "{solved}");
        assert!(solved.contains("route_budget_bytes=67108864"), "{solved}");
        assert!(solved.contains("phase_cap_bytes=33554432"), "{solved}");

        let mut unsupported = Model::new();
        let x = unsupported.add_binary_col();
        unsupported.set_objective(&[(x, 1.0)], Sense::Minimize);
        let declined = diag_block_angular(&unsupported, 60.0, None);
        assert!(declined.contains("candidate=false"), "{declined}");
        assert!(declined.contains("status=declined"), "{declined}");
        assert!(declined.contains("stage=recognition"), "{declined}");
        assert!(declined.contains("reason=not-applicable"), "{declined}");
        assert!(
            declined.contains("route_budget_bytes=67108864"),
            "{declined}"
        );
        assert!(declined.contains("phase_cap_bytes=33554432"), "{declined}");
    }

    #[test]
    fn identical_capacity_domains_reuse_tuples_before_enumeration() {
        CAPACITY_TUPLE_ENUMERATIONS.with(|count| count.set(0));
        MITM_ASSIGNMENT_PREPARATIONS.with(|count| count.set(0));
        let plan = recognize(&source_model(), None, Some(DEFAULT_ROUTE_MEMORY))
            .expect("identical source domains recognize");
        let blocks = source_blocks(&plan);
        assert_eq!(blocks.len(), 2);
        assert!(Arc::ptr_eq(&blocks[0].tuples, &blocks[1].tuples));
        assert!(Arc::ptr_eq(
            blocks[0]
                .exact_domain
                .as_ref()
                .expect("primitive capacity domain"),
            blocks[1]
                .exact_domain
                .as_ref()
                .expect("shared primitive capacity domain")
        ));
        assert_eq!(
            blocks[0].tuples.as_ref(),
            &[
                vec![0, 0],
                vec![0, 1],
                vec![0, 2],
                vec![1, 0],
                vec![1, 1],
                vec![2, 0],
            ]
        );
        CAPACITY_TUPLE_ENUMERATIONS.with(|count| {
            assert_eq!(
                count.get(),
                1,
                "the second primitive-identical domain must skip enumeration"
            )
        });
        MITM_ASSIGNMENT_PREPARATIONS.with(|count| {
            assert_eq!(
                count.get(),
                1,
                "the second primitive-identical domain must share MITM assignments"
            )
        });
    }

    #[test]
    fn public_replay_recognition_allocates_no_mitm_assignments() {
        MITM_ASSIGNMENT_PREPARATIONS.with(|count| count.set(0));
        let mut work = WorkMeter::new(None);
        let plan = recognize_with_work(
            &source_model(),
            Some(DEFAULT_ROUTE_MEMORY),
            PricingPreparation::ExhaustiveReplay,
            &mut work,
        )
        .expect("replay recognition");
        for block in source_blocks(&plan) {
            assert!(
                block
                    .exact_domain
                    .as_ref()
                    .expect("primitive domain retained")
                    .mitm
                    .is_none(),
                "public replay must not construct production pricing advice"
            );
        }
        MITM_ASSIGNMENT_PREPARATIONS.with(|count| assert_eq!(count.get(), 0));
    }

    #[test]
    fn equivalent_nonidentical_capacity_domains_keep_tuple_fallback() {
        let mut model = source_model();
        let second_capacity = Row(13);
        let (coefficients, lower, _) = model.row(second_capacity);
        let doubled = coefficients
            .iter()
            .map(|&(column, coefficient)| (Col(column), coefficient * 2.0))
            .collect::<Vec<_>>();
        model.set_row(second_capacity, lower, 5.0, &doubled);

        CAPACITY_TUPLE_ENUMERATIONS.with(|count| count.set(0));
        let plan = recognize(&model, None, Some(DEFAULT_ROUTE_MEMORY))
            .expect("integer-equivalent source domains recognize");
        let blocks = source_blocks(&plan);
        assert_eq!(blocks.len(), 2);
        assert!(
            Arc::ptr_eq(&blocks[0].tuples, &blocks[1].tuples),
            "tuple comparison must canonicalize semantically equal domains"
        );
        CAPACITY_TUPLE_ENUMERATIONS.with(|count| {
            assert_eq!(
                count.get(),
                2,
                "2x+2y<=5 is not the same primitive inequality as x+y<=2"
            )
        });
    }

    #[test]
    fn batched_resource_polls_preserve_exact_hooks_and_local_limits() {
        let deadline = Instant::now()
            .checked_add(Duration::from_secs(60))
            .expect("near deadline");
        let mut work = WorkMeter::new(Some(deadline));
        work.charge_terms(WALL_TERM_POLL_STRIDE - 1)
            .expect("below term boundary");
        assert_eq!(work.wall_polls.get(), 0);
        work.charge_terms(1).expect("term boundary");
        assert_eq!(work.wall_polls.get(), 1);
        for _ in 0..WALL_ROUND_POLL_STRIDE - 1 {
            work.charge_round().expect("below round boundary");
        }
        assert_eq!(work.wall_polls.get(), 1);
        work.charge_round().expect("round boundary");
        assert_eq!(work.wall_polls.get(), 2);
        work.checkpoint().expect("explicit wall checkpoint");
        assert_eq!(work.wall_polls.get(), 3);

        let mut deterministic = WorkMeter::with_test_deadline_after(3);
        deterministic.charge_terms(2).expect("before exact hook");
        assert_eq!(deterministic.charge_round(), Err(Decline::Deadline));
        assert_eq!(deterministic.wall_polls.get(), 0);

        let mut memory = MemoryMeter::new(Some(DEFAULT_ROUTE_MEMORY), true)
            .expect("bounded process-aware meter");
        memory
            .charge(PROCESS_MEMORY_POLL_STRIDE - 1)
            .expect("below process boundary");
        assert_eq!(memory.full_process_polls, 0);
        memory.charge(1).expect("process boundary");
        assert_eq!(memory.full_process_polls, 1);

        let mut tiny = MemoryMeter::new(Some(2), true).expect("one-byte local meter");
        let polls_before = tiny.full_process_polls;
        assert_eq!(tiny.charge(2), Err(Decline::Memory));
        assert_eq!(tiny.used, 0, "a rejected allocation is never charged");
        assert_eq!(
            tiny.full_process_polls, polls_before,
            "the exact local cap rejects before a full process poll"
        );

        struct ClearForcedMemory;
        impl Drop for ClearForcedMemory {
            fn drop(&mut self) {
                ay_sys::force_process_memory_exceeded_for_testing(false);
            }
        }
        let _clear = ClearForcedMemory;
        let mut forced = MemoryMeter::new(Some(DEFAULT_ROUTE_MEMORY), true)
            .expect("meter before forcing the hook");
        ay_sys::force_process_memory_exceeded_for_testing(true);
        assert_eq!(forced.charge(1), Err(Decline::Memory));
    }

    fn source_plus_initial_model() -> Model {
        let mut model = Model::new();
        let root = model.add_int_col(0.0, 2.0);
        let source_state = model.add_int_col(0.0, 2.0);
        let source_exit = model.add_int_col(0.0, 2.0);
        model.add_row(0.0, 0.0, &[(root, 1.0), (source_state, -1.0)]);
        model.add_row(0.0, 0.0, &[(source_state, 1.0), (source_exit, -1.0)]);
        model.add_row(f64::NEG_INFINITY, 2.0, &[(root, 1.0)]);

        let initial_state = model.add_int_col(0.0, 1.0);
        let initial_exit0 = model.add_int_col(0.0, 1.0);
        let initial_exit1 = model.add_int_col(0.0, 1.0);
        model.add_row(-1.0, -1.0, &[(initial_state, -1.0), (initial_exit0, -1.0)]);
        model.add_row(0.0, 0.0, &[(initial_state, 1.0), (initial_exit1, -1.0)]);
        model.add_row(
            1.0,
            f64::INFINITY,
            &[(source_state, 1.0), (initial_state, 1.0)],
        );
        model.set_objective(&[(source_exit, 2.0), (initial_exit1, 1.0)], Sense::Minimize);
        model
    }

    #[derive(Clone, Copy, Debug)]
    struct TinyCase {
        seed: u64,
        source_blocks: usize,
        include_initial: bool,
        chains_per_source: usize,
        base_chain_length: usize,
        master_rows: usize,
        capacity: i64,
        flip_local_signs: bool,
        exact_decimals: bool,
        tied_exit_costs: bool,
        nonuniform_uppers: bool,
    }

    #[derive(Clone)]
    struct TinyChainColumns {
        root: Option<Col>,
        states: Vec<Col>,
        exits: Vec<Col>,
        quantity: i64,
    }

    #[derive(Clone)]
    struct TinySourceBlock {
        chains: Vec<TinyChainColumns>,
        capacity_weights: Vec<i64>,
        capacity: i64,
        capacity_row: Row,
    }

    #[derive(Clone)]
    enum TinyBlock {
        Source(TinySourceBlock),
        Initial(TinyChainColumns),
    }

    #[derive(Clone)]
    struct TinyFixture {
        model: Model,
        blocks: Vec<TinyBlock>,
        local_rows: Vec<Row>,
        master_rows: Vec<Row>,
    }

    struct TinyReference {
        value: BigRational,
        points: Vec<Vec<BigRational>>,
    }

    fn tiny_rat(numerator: i64, denominator: i64) -> BigRational {
        BigRational::new(numerator.into(), denominator.into())
    }

    fn tiny_scaled(value: i64, scale: &BigRational) -> BigRational {
        BigRational::from_integer(value.into()) * scale
    }

    fn add_tiny_equality(
        model: &mut Model,
        local_rows: &mut Vec<Row>,
        terms: &[(Col, f64)],
        rhs: f64,
        negate: bool,
    ) {
        let (terms, rhs) = if negate {
            (
                terms
                    .iter()
                    .map(|&(column, coefficient)| (column, -coefficient))
                    .collect::<Vec<_>>(),
                -rhs,
            )
        } else {
            (terms.to_vec(), rhs)
        };
        local_rows.push(model.add_row(rhs, rhs, &terms));
    }

    fn add_tiny_cost(costs: &mut Vec<(Col, BigRational)>, column: Col, value: BigRational) {
        costs.push((column, value));
    }

    fn build_tiny_fixture(case: TinyCase) -> TinyFixture {
        assert!(case.source_blocks >= 1);
        assert!(case.source_blocks + usize::from(case.include_initial) >= 2);
        assert!((1..=2).contains(&case.chains_per_source));
        assert!((1..=2).contains(&case.base_chain_length));
        assert!((1..=case.base_chain_length).contains(&case.master_rows));
        assert!((1..=2).contains(&case.capacity));

        let mut model = Model::new();
        let mut blocks = Vec::new();
        let mut local_rows = Vec::new();
        let mut costs = Vec::new();
        let scale = if case.exact_decimals {
            tiny_rat(1, 10)
        } else {
            BigRational::one()
        };
        let mut master_terms = vec![Vec::<(Col, BigRational)>::new(); case.master_rows];

        for block_index in 0..case.source_blocks {
            let mut chains = Vec::new();
            let mut capacity_terms = Vec::new();
            let mut capacity_weights = Vec::new();
            for chain_index in 0..case.chains_per_source {
                let length = case.base_chain_length
                    + usize::from(
                        case.base_chain_length < 2
                            && (case.seed + block_index as u64 + chain_index as u64) & 1 == 1,
                    );
                let upper = if case.nonuniform_uppers {
                    1 + ((case.seed + block_index as u64 + chain_index as u64) & 1) as i64
                } else {
                    2
                };
                let weight = if chain_index == 0 {
                    1
                } else {
                    1 + ((case.seed + block_index as u64 + chain_index as u64) & 1) as i64
                };
                let root = model.add_int_col(0.0, upper as f64);
                add_tiny_cost(
                    &mut costs,
                    root,
                    tiny_scaled(-(5 + block_index as i64 + chain_index as i64), &scale),
                );
                capacity_terms.push((root, weight as f64));
                capacity_weights.push(weight);

                let states = (0..length)
                    .map(|state_index| {
                        let state = model.add_int_col(0.0, upper as f64);
                        add_tiny_cost(&mut costs, state, tiny_scaled(-2, &scale));
                        let master = state_index % case.master_rows;
                        let coefficient = if case.exact_decimals {
                            tiny_rat(
                                1 + ((case.seed
                                    + block_index as u64
                                    + chain_index as u64
                                    + state_index as u64)
                                    % 3) as i64,
                                10,
                            )
                        } else {
                            BigRational::from_integer(
                                (1 + ((case.seed
                                    + block_index as u64
                                    + chain_index as u64
                                    + state_index as u64)
                                    & 1))
                                    .into(),
                            )
                        };
                        master_terms[master].push((state, coefficient));
                        state
                    })
                    .collect::<Vec<_>>();
                let exits = (0..length)
                    .map(|exit_index| {
                        let exit = model.add_int_col(0.0, upper as f64);
                        let slope = if case.tied_exit_costs { 2 } else { 1 };
                        add_tiny_cost(
                            &mut costs,
                            exit,
                            tiny_scaled(slope * exit_index as i64, &scale),
                        );
                        exit
                    })
                    .collect::<Vec<_>>();

                let negate = case.flip_local_signs && local_rows.len() & 1 == 1;
                add_tiny_equality(
                    &mut model,
                    &mut local_rows,
                    &[(root, 1.0), (states[0], -1.0)],
                    0.0,
                    negate,
                );
                for state_index in 0..length {
                    let mut terms = vec![(states[state_index], 1.0)];
                    if state_index + 1 < length {
                        terms.push((states[state_index + 1], -1.0));
                    }
                    terms.push((exits[state_index], -1.0));
                    let negate = case.flip_local_signs && local_rows.len() & 1 == 1;
                    add_tiny_equality(&mut model, &mut local_rows, &terms, 0.0, negate);
                }
                chains.push(TinyChainColumns {
                    root: Some(root),
                    states,
                    exits,
                    quantity: upper,
                });
            }
            let capacity_row =
                model.add_row(f64::NEG_INFINITY, case.capacity as f64, &capacity_terms);
            blocks.push(TinyBlock::Source(TinySourceBlock {
                chains,
                capacity_weights,
                capacity: case.capacity,
                capacity_row,
            }));
        }

        if case.include_initial {
            let length = case.base_chain_length
                + usize::from(case.base_chain_length < 2 && case.seed & 2 != 0);
            let quantity = 1 + ((case.seed >> 2) & 1) as i64;
            let states = (0..length)
                .map(|state_index| {
                    let upper =
                        quantity + i64::from(case.nonuniform_uppers && state_index & 1 == 1);
                    let state = model.add_int_col(0.0, upper as f64);
                    add_tiny_cost(&mut costs, state, tiny_scaled(-2, &scale));
                    let master = state_index % case.master_rows;
                    let coefficient = if case.exact_decimals {
                        tiny_rat(1 + ((case.seed + state_index as u64) % 3) as i64, 10)
                    } else {
                        BigRational::from_integer(
                            (1 + ((case.seed + state_index as u64) & 1)).into(),
                        )
                    };
                    master_terms[master].push((state, coefficient));
                    state
                })
                .collect::<Vec<_>>();
            let exits = (0..=length)
                .map(|exit_index| {
                    let upper = quantity + i64::from(case.nonuniform_uppers && exit_index & 1 == 0);
                    let exit = model.add_int_col(0.0, upper as f64);
                    let slope = if case.tied_exit_costs { 2 } else { 1 };
                    add_tiny_cost(
                        &mut costs,
                        exit,
                        tiny_scaled(slope * exit_index as i64, &scale),
                    );
                    exit
                })
                .collect::<Vec<_>>();
            let negate = case.flip_local_signs && local_rows.len() & 1 == 1;
            add_tiny_equality(
                &mut model,
                &mut local_rows,
                &[(states[0], 1.0), (exits[0], 1.0)],
                quantity as f64,
                negate,
            );
            for state_index in 0..length {
                let mut terms = vec![(states[state_index], 1.0)];
                if state_index + 1 < length {
                    terms.push((states[state_index + 1], -1.0));
                }
                terms.push((exits[state_index + 1], -1.0));
                let negate = case.flip_local_signs && local_rows.len() & 1 == 1;
                add_tiny_equality(&mut model, &mut local_rows, &terms, 0.0, negate);
            }
            blocks.push(TinyBlock::Initial(TinyChainColumns {
                root: None,
                states,
                exits,
                quantity,
            }));
        }

        let objective = costs
            .iter()
            .map(|(column, value)| {
                (
                    *column,
                    value.to_f64().expect("bounded tiny objective proxy"),
                )
            })
            .collect::<Vec<_>>();
        model.set_objective(&objective, Sense::Minimize);
        if case.exact_decimals {
            for (column, value) in &costs {
                model.record_inexact_obj_coeff(column.0, value.clone());
            }
        }
        let offset = if case.exact_decimals {
            tiny_rat(-7, 10)
        } else {
            BigRational::from_integer(((case.seed % 3) as i64 - 1).into())
        };
        model.set_objective_offset(offset.to_f64().expect("bounded tiny offset proxy"));
        if case.exact_decimals {
            model.record_inexact_obj_offset(offset);
        }

        let mut master_rows = Vec::new();
        for terms in master_terms {
            let rhs = if case.exact_decimals {
                tiny_rat(1, 10)
            } else {
                BigRational::one()
            };
            let rounded = terms
                .iter()
                .map(|(column, value)| {
                    (*column, value.to_f64().expect("bounded tiny master proxy"))
                })
                .collect::<Vec<_>>();
            let row = model.add_row(
                rhs.to_f64().expect("bounded tiny master rhs proxy"),
                f64::INFINITY,
                &rounded,
            );
            if case.exact_decimals {
                for (column, value) in terms {
                    model.record_inexact_row_coeff(row, column.0, value);
                }
                model.record_inexact_row_bound(row, true, rhs);
            }
            master_rows.push(row);
        }

        TinyFixture {
            model,
            blocks,
            local_rows,
            master_rows,
        }
    }

    fn weak_compositions(total: i64, parts: usize) -> Vec<Vec<i64>> {
        fn recurse(
            remaining: i64,
            parts: usize,
            current: &mut Vec<i64>,
            result: &mut Vec<Vec<i64>>,
        ) {
            if parts == 1 {
                current.push(remaining);
                result.push(current.clone());
                current.pop();
                return;
            }
            for value in 0..=remaining {
                current.push(value);
                recurse(remaining - value, parts - 1, current, result);
                current.pop();
            }
        }

        assert!(total >= 0 && parts > 0);
        let mut result = Vec::new();
        recurse(total, parts, &mut Vec::new(), &mut result);
        result
    }

    fn source_amount_tuples(block: &TinySourceBlock) -> Vec<Vec<i64>> {
        fn recurse(
            block: &TinySourceBlock,
            chain: usize,
            activity: i64,
            current: &mut Vec<i64>,
            result: &mut Vec<Vec<i64>>,
        ) {
            if chain == block.chains.len() {
                result.push(current.clone());
                return;
            }
            for amount in 0..=block.chains[chain].quantity {
                let next = activity + amount * block.capacity_weights[chain];
                if next > block.capacity {
                    break;
                }
                current.push(amount);
                recurse(block, chain + 1, next, current, result);
                current.pop();
            }
        }

        let mut result = Vec::new();
        recurse(block, 0, 0, &mut Vec::new(), &mut result);
        result
    }

    fn add_sparse_integer_point(target: &mut [i64], source: &[i64]) {
        for (target, source) in target.iter_mut().zip(source) {
            *target += source;
        }
    }

    fn source_chain_points(chain: &TinyChainColumns, amount: i64, columns: usize) -> Vec<Vec<i64>> {
        weak_compositions(amount, chain.exits.len())
            .into_iter()
            .map(|exit_values| {
                let mut point = vec![0; columns];
                point[chain.root.expect("source root").0 as usize] = amount;
                for (index, (&column, &value)) in chain.exits.iter().zip(&exit_values).enumerate() {
                    point[column.0 as usize] = value;
                    point[chain.states[index].0 as usize] = exit_values[index..].iter().sum();
                }
                point
            })
            .collect()
    }

    fn initial_chain_points(chain: &TinyChainColumns, columns: usize) -> Vec<Vec<i64>> {
        weak_compositions(chain.quantity, chain.exits.len())
            .into_iter()
            .map(|exit_values| {
                let mut point = vec![0; columns];
                for (column, value) in chain.exits.iter().zip(&exit_values) {
                    point[column.0 as usize] = *value;
                }
                for (index, state) in chain.states.iter().enumerate() {
                    point[state.0 as usize] = exit_values[index + 1..].iter().sum();
                }
                point
            })
            .collect()
    }

    fn combine_point_families(families: &[Vec<Vec<i64>>], columns: usize) -> Vec<Vec<i64>> {
        fn recurse(
            families: &[Vec<Vec<i64>>],
            family: usize,
            current: &mut Vec<i64>,
            result: &mut Vec<Vec<i64>>,
        ) {
            if family == families.len() {
                result.push(current.clone());
                return;
            }
            for point in &families[family] {
                add_sparse_integer_point(current, point);
                recurse(families, family + 1, current, result);
                for (current, value) in current.iter_mut().zip(point) {
                    *current -= value;
                }
            }
        }

        let mut result = Vec::new();
        recurse(families, 0, &mut vec![0; columns], &mut result);
        result
    }

    fn tiny_block_points(block: &TinyBlock, columns: usize) -> Vec<Vec<i64>> {
        match block {
            TinyBlock::Initial(chain) => initial_chain_points(chain, columns),
            TinyBlock::Source(block) => {
                let mut result = Vec::new();
                for amounts in source_amount_tuples(block) {
                    let families = block
                        .chains
                        .iter()
                        .zip(amounts)
                        .map(|(chain, amount)| source_chain_points(chain, amount, columns))
                        .collect::<Vec<_>>();
                    result.extend(combine_point_families(&families, columns));
                }
                result
            }
        }
    }

    fn exhaustive_tiny_reference(fixture: &TinyFixture) -> TinyReference {
        // This reference deliberately does not inspect `Plan`, patterns,
        // pricing, or duals.  It enumerates every bounded integral split of a
        // chain's flow across its exits, forms the Cartesian product of the
        // blocks, and asks only the native model checker/objective evaluator.
        // The tiny generator caps each amount at two, each source at two
        // chains, and each chain at two states, so this stays deterministic
        // and small while covering points that are convex combinations of DW
        // extreme patterns.
        let columns = fixture.model.num_cols();
        let families = fixture
            .blocks
            .iter()
            .map(|block| tiny_block_points(block, columns))
            .collect::<Vec<_>>();
        let mut best_value = None;
        let mut best_points = Vec::new();
        for integer_point in combine_point_families(&families, columns) {
            let point = integer_point
                .into_iter()
                .map(|value| BigRational::from_integer(value.into()))
                .collect::<Vec<_>>();
            if fixture.model.check_point(&point).is_err() {
                continue;
            }
            let value = fixture.model.objective_value_at(&point);
            match &best_value {
                None => {
                    best_value = Some(value);
                    best_points = vec![point];
                }
                Some(best) if &value < best => {
                    best_value = Some(value);
                    best_points = vec![point];
                }
                Some(best) if &value == best => best_points.push(point),
                Some(_) => {}
            }
        }
        TinyReference {
            value: best_value.expect("tiny admitted fixture is feasible"),
            points: best_points,
        }
    }

    fn assert_tiny_route_matches_reference(fixture: &TinyFixture, label: &str) {
        let plan = recognize(&fixture.model, None, Some(DEFAULT_ROUTE_MEMORY))
            .unwrap_or_else(|reason| panic!("{label}: admitted fixture declined: {reason:?}"));
        let reference = exhaustive_tiny_reference(fixture);
        let mut work = WorkMeter::new(None);
        let decision = solve(&fixture.model, &plan, Some(DEFAULT_ROUTE_MEMORY), &mut work)
            .unwrap_or_else(|reason| panic!("{label}: admitted fixture did not solve: {reason:?}"));
        assert_eq!(decision.value, reference.value, "{label}: objective");
        assert!(
            reference.points.contains(&decision.model_values),
            "{label}: returned point is not an exhaustively enumerated optimum"
        );
        fixture
            .model
            .check_point(&decision.model_values)
            .unwrap_or_else(|reason| panic!("{label}: returned point is invalid: {reason:?}"));
        verify_optimality_certificate(&fixture.model, &decision.value, &decision.certificate)
            .unwrap_or_else(|reason| {
                panic!("{label}: public verifier rejected artifact: {reason}")
            });
    }

    #[derive(Clone, Copy)]
    struct TinyRng(u64);

    impl TinyRng {
        fn next(&mut self) -> u64 {
            self.0 = self
                .0
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            self.0
        }

        fn bit(&mut self) -> bool {
            self.next() >> 63 != 0
        }
    }

    fn randomized_tiny_case(rng: &mut TinyRng, index: usize) -> TinyCase {
        let include_initial = rng.bit();
        let base_chain_length = 1 + usize::from(rng.bit());
        let master_rows = if base_chain_length == 2 && rng.bit() {
            2
        } else {
            1
        };
        let tied_exit_costs = rng.bit() && master_rows == 1;
        TinyCase {
            seed: rng.next() ^ index as u64,
            source_blocks: if include_initial { 1 } else { 2 },
            include_initial,
            chains_per_source: 1 + usize::from(rng.bit()),
            base_chain_length,
            master_rows,
            capacity: 1 + i64::from(rng.bit()),
            flip_local_signs: rng.bit(),
            exact_decimals: rng.bit(),
            tied_exit_costs,
            nonuniform_uppers: rng.bit(),
        }
    }

    fn systematic_tiny_case(index: usize) -> TinyCase {
        let include_initial = index & 1 != 0;
        let base_chain_length = 1 + ((index >> 1) & 1);
        let master_rows = if base_chain_length == 2 && index & 8 != 0 {
            2
        } else {
            1
        };
        TinyCase {
            seed: 0x9e37_79b9_u64.wrapping_mul(index as u64 + 1),
            source_blocks: if include_initial { 1 } else { 2 },
            include_initial,
            chains_per_source: 1 + ((index >> 2) & 1),
            base_chain_length,
            master_rows,
            capacity: 1 + ((index >> 3) & 1) as i64,
            flip_local_signs: index & 1 != 0,
            exact_decimals: index & 2 != 0,
            tied_exit_costs: index & 4 != 0 && master_rows == 1,
            nonuniform_uppers: index & 8 != 0,
        }
    }

    #[test]
    fn tiny_systematic_models_match_an_independent_exhaustive_reference() {
        for index in 0..16 {
            let case = systematic_tiny_case(index);
            let fixture = build_tiny_fixture(case);
            assert_tiny_route_matches_reference(&fixture, &format!("systematic {index}: {case:?}"));
            if case.exact_decimals {
                assert_ne!(
                    fixture.model.obj_offset_exact(),
                    exact(fixture.model.objective_offset()).expect("finite offset proxy"),
                    "case {index} must really exercise the exact decimal side store"
                );
            }
        }
    }

    #[test]
    fn tiny_seeded_random_models_match_an_independent_exhaustive_reference() {
        let mut rng = TinyRng(0xd1ff_e4e7_5eed_cafe);
        for index in 0..16 {
            let case = randomized_tiny_case(&mut rng, index);
            let fixture = build_tiny_fixture(case);
            assert_tiny_route_matches_reference(&fixture, &format!("seeded {index}: {case:?}"));
        }
    }

    #[test]
    fn recognized_capacity_tuples_are_complete_against_integer_census() {
        for index in 0..16 {
            let case = systematic_tiny_case(index);
            let fixture = build_tiny_fixture(case);
            let plan = recognize(&fixture.model, None, Some(DEFAULT_ROUTE_MEMORY))
                .unwrap_or_else(|reason| panic!("capacity case {index} declined: {reason:?}"));
            assert_eq!(plan.blocks.len(), fixture.blocks.len());
            for (recognized, native) in plan.blocks.iter().zip(&fixture.blocks) {
                match (recognized, native) {
                    (Block::Initial(recognized), TinyBlock::Initial(native)) => {
                        assert_eq!(recognized.chain.choices.len(), native.exits.len());
                    }
                    (Block::Source(recognized), TinyBlock::Source(native)) => {
                        let actual = recognized.tuples.iter().cloned().collect::<BTreeSet<_>>();
                        let expected = source_amount_tuples(native).into_iter().collect();
                        assert_eq!(
                            actual, expected,
                            "capacity case {index} omitted or invented a source tuple"
                        );
                        assert_eq!(recognized.chains.len(), native.chains.len());
                        for (chain, expected) in recognized.chains.iter().zip(&native.chains) {
                            assert_eq!(chain.choices.len(), expected.exits.len());
                        }
                    }
                    _ => panic!("capacity case {index} changed block kind or order"),
                }
            }
        }
    }

    #[test]
    fn production_wrapper_and_public_replay_match_the_exhaustive_reference() {
        for index in [0, 3, 10, 15] {
            let case = systematic_tiny_case(index);
            let fixture = build_tiny_fixture(case);
            let reference = exhaustive_tiny_reference(&fixture);
            MITM_SOURCE_PRICINGS.with(|count| count.set(0));
            let decision = try_solve_certified(&fixture.model, None, Some(DEFAULT_ROUTE_MEMORY))
                .unwrap_or_else(|| panic!("production case {index} declined"));
            MITM_SOURCE_PRICINGS
                .with(|count| assert!(count.get() > 0, "production must exercise MITM pricing"));
            assert_eq!(decision.value, reference.value, "production case {index}");
            assert!(reference.points.contains(&decision.model_values));
            MITM_SOURCE_PRICINGS.with(|count| count.set(0));
            EXHAUSTIVE_SOURCE_PRICINGS.with(|count| count.set(0));
            verify_optimality_certificate(&fixture.model, &decision.value, &decision.certificate)
                .unwrap_or_else(|reason| panic!("production case {index} replay failed: {reason}"));
            MITM_SOURCE_PRICINGS.with(|count| {
                assert_eq!(count.get(), 0, "public replay must not consult MITM advice")
            });
            EXHAUSTIVE_SOURCE_PRICINGS
                .with(|count| assert!(count.get() > 0, "public replay must exhaustively re-price"));

            let mut changed_claim = decision.value.clone();
            changed_claim += BigRational::one();
            assert!(verify_optimality_certificate(
                &fixture.model,
                &changed_claim,
                &decision.certificate,
            )
            .is_err());
        }
    }

    #[test]
    fn structural_mutations_decline_while_equivalent_forms_remain_exact() {
        let case = TinyCase {
            seed: 41,
            source_blocks: 2,
            include_initial: false,
            chains_per_source: 2,
            base_chain_length: 2,
            master_rows: 2,
            capacity: 2,
            flip_local_signs: false,
            exact_decimals: false,
            tied_exit_costs: false,
            nonuniform_uppers: true,
        };
        let fixture = build_tiny_fixture(case);
        assert_tiny_route_matches_reference(&fixture, "mutation baseline");

        let mut sign_reversed = fixture.clone();
        for &row in &sign_reversed.local_rows {
            let (coefficients, lower, upper) = sign_reversed.model.row(row);
            let negated = coefficients
                .iter()
                .map(|&(column, coefficient)| (Col(column), -coefficient))
                .collect::<Vec<_>>();
            sign_reversed.model.set_row(row, -upper, -lower, &negated);
        }
        assert_tiny_route_matches_reference(&sign_reversed, "all local signs reversed");

        let mut scaled_master = fixture.clone();
        let row = scaled_master.master_rows[0];
        let (coefficients, lower, upper) = scaled_master.model.row(row);
        let doubled = coefficients
            .iter()
            .map(|&(column, coefficient)| (Col(column), 2.0 * coefficient))
            .collect::<Vec<_>>();
        scaled_master
            .model
            .set_row(row, 2.0 * lower, upper, &doubled);
        assert_tiny_route_matches_reference(&scaled_master, "scaled master row");

        let mut inert_zero = fixture.clone();
        let zero = inert_zero.model.add_int_col(0.0, 0.0);
        inert_zero.model.add_row(0.0, 0.0, &[(zero, 1.0)]);
        assert_tiny_route_matches_reference(&inert_zero, "propagated fixed-zero noise");

        let mut nonunit = fixture.model.clone();
        let row = fixture.local_rows[0];
        let (coefficients, lower, upper) = nonunit.row(row);
        let mut rewritten = coefficients
            .iter()
            .map(|&(column, coefficient)| (Col(column), coefficient))
            .collect::<Vec<_>>();
        rewritten[0].1 *= 2.0;
        nonunit.set_row(row, lower, upper, &rewritten);
        assert!(recognize(&nonunit, None, Some(DEFAULT_ROUTE_MEMORY)).is_err());

        let mut duplicate_master = fixture.model.clone();
        let row = fixture.master_rows[0];
        let (coefficients, lower, _) = duplicate_master.row(row);
        let duplicate = coefficients
            .iter()
            .map(|&(column, coefficient)| (Col(column), coefficient))
            .collect::<Vec<_>>();
        duplicate_master.add_row(lower, f64::INFINITY, &duplicate);
        assert!(recognize(&duplicate_master, None, Some(DEFAULT_ROUTE_MEMORY)).is_err());

        let TinyBlock::Source(first_source) = &fixture.blocks[0] else {
            unreachable!()
        };
        let mut ranged_capacity = fixture.model.clone();
        let (coefficients, _, upper) = ranged_capacity.row(first_source.capacity_row);
        let coefficients = coefficients
            .iter()
            .map(|&(column, coefficient)| (Col(column), coefficient))
            .collect::<Vec<_>>();
        ranged_capacity.set_row(first_source.capacity_row, 0.0, upper, &coefficients);
        assert!(recognize(&ranged_capacity, None, Some(DEFAULT_ROUTE_MEMORY)).is_err());

        let mut negative_capacity = fixture.model.clone();
        let (coefficients, lower, upper) = negative_capacity.row(first_source.capacity_row);
        let mut coefficients = coefficients
            .iter()
            .map(|&(column, coefficient)| (Col(column), coefficient))
            .collect::<Vec<_>>();
        coefficients[0].1 = -coefficients[0].1;
        negative_capacity.set_row(first_source.capacity_row, lower, upper, &coefficients);
        assert!(recognize(&negative_capacity, None, Some(DEFAULT_ROUTE_MEMORY)).is_err());

        let mut forced_zero_flow = fixture.clone();
        forced_zero_flow
            .model
            .set_col_bounds(first_source.chains[0].states[0], 0.0, 0.0);
        assert_tiny_route_matches_reference(
            &forced_zero_flow,
            "fixed-zero flow is propagated before recognition",
        );
    }

    #[test]
    fn recognizes_and_prices_generic_source_blocks() {
        let model = source_model();
        let plan = recognize(&model, None, Some(DEFAULT_ROUTE_MEMORY)).expect("recognized");
        assert_eq!(plan.master_rows.len(), 2);
        assert_eq!(plan.blocks.len(), 2);
        for block in &plan.blocks {
            let Block::Source(block) = block else {
                panic!("source block expected")
            };
            assert_eq!(block.chains.len(), 2);
            assert_eq!(block.tuples.len(), 6);
        }
    }

    #[test]
    fn recognizer_is_name_independent_and_certificate_replays() {
        let model = source_model();
        let decision = try_solve_certified(&model, None, Some(DEFAULT_ROUTE_MEMORY))
            .expect("route proves optimum");
        assert_eq!(decision.value, BigRational::from_integer(4.into()));
        verify_optimality_certificate(&model, &decision.value, &decision.certificate)
            .expect("certificate replays");
        model
            .check_point(&decision.model_values)
            .expect("exact point");
    }

    #[test]
    fn conservation_row_signs_do_not_change_recognition_or_value() {
        let mut model = source_model();
        for row_index in 0..model.num_rows() {
            let row = Row(row_index as u32);
            let (coefficients, lower, upper) = model.row(row);
            if lower != 0.0 || upper != 0.0 {
                continue;
            }
            let negated = coefficients
                .iter()
                .map(|&(column, coefficient)| (Col(column), -coefficient))
                .collect::<Vec<_>>();
            model.set_row(row, 0.0, 0.0, &negated);
        }
        let decision = try_solve_certified(&model, None, Some(DEFAULT_ROUTE_MEMORY))
            .expect("sign-normalized chains solve");
        assert_eq!(decision.value, BigRational::from_integer(4.into()));
        verify_optimality_certificate(&model, &decision.value, &decision.certificate)
            .expect("sign-normalized certificate replays");
    }

    #[test]
    fn recognizes_fixed_initial_stock_chain_and_reconstructs_it() {
        let model = source_plus_initial_model();
        let plan = recognize(&model, None, Some(DEFAULT_ROUTE_MEMORY)).expect("recognized");
        assert_eq!(plan.blocks.len(), 2);
        let initial = plan
            .blocks
            .iter()
            .find_map(|block| match block {
                Block::Initial(initial) => Some(initial),
                Block::Source(_) => None,
            })
            .expect("initial block");
        assert_eq!(initial.chain.choices.len(), 2);

        let decision = try_solve_certified(&model, None, Some(DEFAULT_ROUTE_MEMORY))
            .expect("initial stock closes the cover at exact optimum");
        assert_eq!(decision.value, BigRational::from_integer(1.into()));
        model
            .check_point(&decision.model_values)
            .expect("exact point");
        verify_optimality_certificate(&model, &decision.value, &decision.certificate)
            .expect("initial-stock artifact replays");
    }

    #[test]
    fn declines_an_unaccounted_local_inequality() {
        let mut model = source_model();
        let first = model.col_at(0).expect("column");
        model.add_row(f64::NEG_INFINITY, 1.0, &[(first, -1.0)]);
        let mut work = WorkMeter::new(None);
        assert!(!coarse_candidate(&model, &mut work).expect("bounded coarse census"));
        assert!(recognize(&model, None, Some(DEFAULT_ROUTE_MEMORY)).is_err());
    }

    #[test]
    fn declines_a_nonunit_conservation_row() {
        let mut model = source_model();
        let (coefficients, lower, upper) = model.row(Row(0));
        let rewritten = coefficients
            .iter()
            .map(|&(column, coefficient)| {
                (
                    Col(column),
                    if coefficient > 0.0 { 2.0 } else { coefficient },
                )
            })
            .collect::<Vec<_>>();
        model.set_row(Row(0), lower, upper, &rewritten);
        assert!(recognize(&model, None, Some(DEFAULT_ROUTE_MEMORY)).is_err());
    }

    #[test]
    fn nonmatching_objective_domain_and_component_shapes_decline() {
        let cases = [
            source_model_variant(true, 2, Some(Sense::Maximize)),
            source_model_variant(true, 2, None),
            {
                let mut model = source_model();
                model.set_objective(&[], Sense::Minimize);
                model
            },
            source_model_variant(false, 2, Some(Sense::Minimize)),
            source_model_variant(true, 1, Some(Sense::Minimize)),
        ];
        for model in cases {
            assert!(recognize(&model, None, Some(DEFAULT_ROUTE_MEMORY)).is_err());
            assert!(try_solve_certified(&model, None, Some(DEFAULT_ROUTE_MEMORY)).is_none());
        }
    }

    #[test]
    fn oversized_exact_payload_declines_before_clone() {
        let mut model = source_model();
        let column = model.col_at(0).expect("first column");
        model.record_inexact_row_coeff(
            Row(0),
            column.0,
            BigRational::from_integer(BigInt::one() << (MAX_RATIONAL_BITS + 1)),
        );
        assert_eq!(
            recognize(&model, None, Some(DEFAULT_ROUTE_MEMORY)).err(),
            Some(Decline::Resource)
        );
    }

    #[test]
    fn maximum_i64_capacity_domain_declines_without_overflow() {
        let mut model = source_model();
        let root = model.col_at(0).expect("first root");
        model.set_col_bounds(root, 0.0, 2f64.powi(63));
        model.record_inexact_row_bound(
            Row(6),
            false,
            BigRational::from_integer(BigInt::from(i64::MAX)),
        );
        assert_eq!(
            recognize(&model, None, Some(DEFAULT_ROUTE_MEMORY)).err(),
            Some(Decline::Resource)
        );
    }

    #[test]
    fn declines_an_initial_chain_row_with_a_second_inflow() {
        let mut model = source_plus_initial_model();
        let initial_state = model.col_at(3).expect("initial state");
        let prior_exit = model.col_at(4).expect("initial first exit");
        let final_exit = model.col_at(5).expect("initial final exit");
        model.set_row(
            Row(4),
            0.0,
            0.0,
            &[(initial_state, 1.0), (prior_exit, 1.0), (final_exit, -1.0)],
        );
        assert!(recognize(&model, None, Some(DEFAULT_ROUTE_MEMORY)).is_err());
    }

    #[test]
    fn tampered_multiplier_or_minimizer_is_rejected() {
        let model = source_model();
        let decision = try_solve_certified(&model, None, Some(DEFAULT_ROUTE_MEMORY))
            .expect("route proves optimum");
        let mut bad_multiplier = decision.certificate.clone();
        bad_multiplier.master_multipliers[0].1 += BigRational::one();
        assert!(verify_optimality_certificate(&model, &decision.value, &bad_multiplier).is_err());

        let mut bad_pattern = decision.certificate;
        match &mut bad_pattern.minimizers[0] {
            CertifiedBlockPattern::Source { exits, .. } => exits[0] ^= 1,
            CertifiedBlockPattern::Initial { .. } => unreachable!(),
        }
        assert!(verify_optimality_certificate(&model, &decision.value, &bad_pattern).is_err());
    }

    #[test]
    fn expired_deadline_and_tiny_memory_decline() {
        let model = source_model();
        assert_eq!(
            recognize(&model, Some(Instant::now()), Some(DEFAULT_ROUTE_MEMORY)).err(),
            Some(Decline::Deadline)
        );
        assert_eq!(
            recognize(&model, None, Some(1)).err(),
            Some(Decline::Memory)
        );
    }

    #[test]
    fn cumulative_work_and_replay_memory_fail_closed() {
        let mut exhausted = WorkMeter::new(None);
        assert_eq!(
            exhausted.charge_terms(MAX_ROUTE_TERM_WORK.saturating_add(1)),
            Err(Decline::Resource)
        );
        let tuples = vec![vec![0, 1, 2, 3]; 8];
        let mut interrupted_dedup = WorkMeter::with_test_deadline_after(12);
        assert_eq!(
            tuple_sets_equal(&tuples, &tuples, &mut interrupted_dedup),
            Err(Decline::Deadline),
            "canonical tuple comparison must checkpoint inside the scan"
        );

        let model = source_model();
        let decision = try_solve_certified(&model, None, Some(DEFAULT_ROUTE_MEMORY))
            .expect("fixture route proves optimum");
        let mut expired_replay = WorkMeter::new(Some(Instant::now()));
        assert_eq!(
            verify_optimality_certificate_with_work(
                &model,
                &decision.value,
                &decision.certificate,
                Some(DEFAULT_ROUTE_MEMORY),
                &mut expired_replay,
            ),
            Err(Decline::Deadline),
            "certificate replay must observe its pinned absolute deadline",
        );
        let mut replay_work = WorkMeter::new(replay_deadline());
        assert_eq!(
            verify_optimality_certificate_with_work(
                &model,
                &decision.value,
                &decision.certificate,
                Some(1),
                &mut replay_work,
            ),
            Err(Decline::Memory),
            "public-style replay must enforce its own deterministic memory box",
        );
    }

    #[test]
    fn inner_materialization_and_duplicate_scans_are_preemptible() {
        let mut master = Model::new();
        let columns = (0..1_024)
            .map(|_| master.add_col(0.0, 1.0))
            .collect::<Vec<_>>();
        let row = columns
            .iter()
            .map(|column| (*column, 1.0))
            .collect::<Vec<_>>();
        master.add_row(0.0, f64::INFINITY, &row);
        master.set_objective(&[(columns[0], 1.0)], Sense::Minimize);
        let mut interrupted_materialization = WorkMeter::with_test_deadline_after(600);
        assert_eq!(
            rmp_materialization(&master, false, &mut interrupted_materialization).err(),
            Some(Decline::Deadline),
        );
        assert!(
            interrupted_materialization.terms < row.len(),
            "the deadline must fire inside the row rather than after a whole-row precharge"
        );

        let existing = Pattern::Source {
            amounts: vec![0; MAX_CHAINS_PER_BLOCK],
            exits: vec![0; MAX_CHAINS_PER_BLOCK],
        };
        let mut candidate = existing.clone();
        let Pattern::Source { amounts, .. } = &mut candidate else {
            unreachable!()
        };
        *amounts.last_mut().expect("nonempty fixture") = 1;
        let patterns = vec![existing; 64];
        let mut interrupted_lookup = WorkMeter::with_test_deadline_after(48);
        assert_eq!(
            contains_pattern_with_work(&patterns, &candidate, &mut interrupted_lookup),
            Err(Decline::Deadline),
            "quadratic duplicate lookup must share the cumulative envelope"
        );
    }

    #[test]
    fn rounded_rmp_row_filters_only_true_zero_coefficients() {
        let exact = vec![(Col(0), BigRational::zero()), (Col(1), BigRational::one())];
        let mut work = WorkMeter::new(None);
        assert_eq!(
            rounded_row_advice(&exact, &mut work).expect("exact row rounds"),
            vec![(1, 1.0)],
            "the bounded constructor must retain add_row's exact-zero filtering"
        );

        let true_nonzero = BigRational::new(BigInt::one(), BigInt::one() << 4_095usize);
        let mut work = WorkMeter::new(None);
        assert_eq!(
            rounded_row_advice(&[(Col(0), true_nonzero)], &mut work).err(),
            Some(Decline::Arithmetic),
            "a true nonzero may never disappear from the float advice row"
        );
    }

    #[test]
    fn exact_witness_conversion_checks_inside_the_point() {
        let mut model = Model::new();
        for _ in 0..1_024 {
            model.add_col(0.0, 1.0);
        }
        let values = vec![BigRational::zero(); model.num_cols()];
        let mut work = WorkMeter::with_test_deadline_after(600);
        let mut decline = None;
        let mut bounded = |units| match work.charge_terms(units) {
            Ok(()) => true,
            Err(reason) => {
                decline.get_or_insert(reason);
                false
            }
        };
        assert!(matches!(
            model.check_point_with_work(&values, &mut bounded),
            Err(crate::PointViolation::ResourceLimit)
        ));
        drop(bounded);
        assert_eq!(decline, Some(Decline::Deadline));
        assert!(
            work.terms < values.len(),
            "the deadline must fire before converting the entire exact point"
        );
    }

    #[test]
    fn deterministic_deadline_interrupts_rmp_construction() {
        let model = source_model();
        let plan = recognize(&model, None, Some(DEFAULT_ROUTE_MEMORY)).expect("recognized");
        let patterns = plan
            .blocks
            .iter()
            .map(|block| vec![initial_pattern(block)])
            .collect::<Vec<_>>();
        RMP_SESSION_MATERIALIZATIONS.with(|count| count.set(0));
        let mut work = WorkMeter::with_test_deadline_after(6);
        assert_eq!(
            solve_restricted_master(
                &plan,
                &patterns,
                MasterPhase::Feasibility,
                MasterArithmetic::Advice,
                Some(DEFAULT_ROUTE_MEMORY),
                &mut work,
            )
            .err(),
            Some(Decline::Deadline),
        );
        assert!(
            work.terms.saturating_add(work.rounds) >= 6,
            "the injected deadline fired only after RMP construction began"
        );
        RMP_SESSION_MATERIALIZATIONS.with(|count| {
            assert_eq!(
                count.get(),
                0,
                "deadline must fire before nested LP materialization"
            )
        });
    }

    #[test]
    fn advice_master_decline_retries_exact_once_inside_the_same_envelope() {
        let mut work = WorkMeter::new(None);
        work.charge_terms(17).expect("initial shared work");
        work.charge_round().expect("initial shared round");
        let before = (work.terms, work.rounds);
        assert!(
            adjudicate_master_attempt(MasterArithmetic::Advice, Err(Decline::Master), &work,)
                .expect("advice miss schedules exact attempt")
                .is_none()
        );
        assert_eq!(
            (work.terms, work.rounds),
            before,
            "the transition must not restart the cumulative work envelope"
        );
        assert_eq!(
            adjudicate_master_attempt(MasterArithmetic::Exact, Err(Decline::Master), &work,).err(),
            Some(Decline::Master),
            "an exact miss must not schedule a second exact attempt"
        );
        assert_eq!(
            adjudicate_master_attempt(MasterArithmetic::Advice, Err(Decline::Memory), &work,).err(),
            Some(Decline::Memory),
            "memory exhaustion must not be relabelled as a retry"
        );

        let expired = WorkMeter::new(Some(Instant::now()));
        assert_eq!(
            adjudicate_master_attempt(MasterArithmetic::Advice, Err(Decline::Master), &expired,)
                .err(),
            Some(Decline::Deadline),
            "the exact transition remains inside the pinned wall deadline"
        );
    }

    #[test]
    fn low_rmp_budget_declines_before_nested_materialization() {
        let model = source_model();
        let plan = recognize(&model, None, Some(DEFAULT_ROUTE_MEMORY)).expect("recognized");
        let patterns = plan
            .blocks
            .iter()
            .map(|block| vec![initial_pattern(block)])
            .collect::<Vec<_>>();
        RMP_SESSION_MATERIALIZATIONS.with(|count| count.set(0));
        let mut work = WorkMeter::new(None);
        assert_eq!(
            solve_restricted_master(
                &plan,
                &patterns,
                MasterPhase::Feasibility,
                MasterArithmetic::Advice,
                Some(4 << 20),
                &mut work,
            )
            .err(),
            Some(Decline::Memory),
        );
        RMP_SESSION_MATERIALIZATIONS.with(|count| {
            assert_eq!(
                count.get(),
                0,
                "preflight must reject before LpSession clones or lowers the master"
            )
        });
    }

    #[test]
    fn pricing_preflight_accounts_for_live_result_patterns_and_growth() {
        let model = source_model();
        let plan = recognize(&model, None, Some(DEFAULT_ROUTE_MEMORY)).expect("recognized");
        let mut patterns = plan
            .blocks
            .iter()
            .map(|block| vec![initial_pattern(block)])
            .collect::<Vec<_>>();
        let mut master_work = WorkMeter::new(None);
        let result = solve_restricted_master(
            &plan,
            &patterns,
            MasterPhase::Feasibility,
            MasterArithmetic::Advice,
            Some(DEFAULT_ROUTE_MEMORY),
            &mut master_work,
        )
        .expect("bounded restricted master");
        let mut census_work = WorkMeter::new(None);
        let required = pricing_pass_storage_bytes(&plan, &patterns, &result, &mut census_work)
            .expect("bounded aggregate pricing peak");
        assert!(required > ROUTE_METADATA_RESERVE);
        let outer_budget = required
            .checked_sub(1)
            .and_then(|bytes| bytes.checked_mul(ROUTE_MEMORY_PARTS))
            .expect("bounded test budget");
        let before = patterns.clone();
        MITM_SOURCE_PRICINGS.with(|count| count.set(0));
        EXHAUSTIVE_SOURCE_PRICINGS.with(|count| count.set(0));
        let mut pricing_work = WorkMeter::new(None);
        assert_eq!(
            add_priced_columns(
                &plan,
                &mut patterns,
                &result,
                MasterPhase::Feasibility,
                Some(outer_budget),
                &mut pricing_work,
            )
            .err(),
            Some(Decline::Memory),
        );
        assert_eq!(
            patterns, before,
            "the aggregate preflight must run before candidate cloning"
        );
        assert_eq!(
            pricing_work.rounds, 0,
            "the aggregate preflight must run before any pricing oracle"
        );
        MITM_SOURCE_PRICINGS.with(|count| assert_eq!(count.get(), 0));
        EXHAUSTIVE_SOURCE_PRICINGS.with(|count| assert_eq!(count.get(), 0));
    }

    #[test]
    fn pricing_preflight_reserves_old_and_complete_grown_pattern_buffers() {
        let model = source_model();
        let plan = recognize(&model, None, Some(DEFAULT_ROUTE_MEMORY)).expect("recognized");
        let patterns = plan
            .blocks
            .iter()
            .map(|block| vec![initial_pattern(block)])
            .collect::<Vec<_>>();
        let mut master_work = WorkMeter::new(None);
        let result = solve_restricted_master(
            &plan,
            &patterns,
            MasterPhase::Feasibility,
            MasterArithmetic::Advice,
            Some(DEFAULT_ROUTE_MEMORY),
            &mut master_work,
        )
        .expect("bounded restricted master");
        let mut census_work = WorkMeter::new(None);
        let required = pricing_pass_storage_bytes(&plan, &patterns, &result, &mut census_work)
            .expect("bounded aggregate pricing peak");
        let pattern_bytes =
            pattern_cache_storage_bytes(&patterns, &mut WorkMeter::new(None)).expect("patterns");
        let growth_frontier = MAX_RESTRICTED_COLUMNS
            .checked_mul(size_of::<Pattern>())
            .and_then(|bytes| bytes.checked_mul(2))
            .expect("bounded pattern growth frontier");
        assert!(
            required >= pattern_bytes + growth_frontier,
            "pricing preflight must retain the old pattern buffers and reserve a complete doubled allocation"
        );
    }

    #[test]
    fn capacity_tuple_membership_is_exact_logarithmic_and_preemptible() {
        let tuples = (0..MAX_FEASIBLE_TUPLES)
            .map(|value| vec![i64::try_from(value).expect("bounded tuple")])
            .collect::<Vec<_>>();

        let mut hit_work = WorkMeter::new(None);
        assert!(contains_capacity_tuple(
            &tuples,
            &[i64::try_from(MAX_FEASIBLE_TUPLES - 1).expect("bounded target")],
            &mut hit_work,
        )
        .expect("exact membership"));
        assert!(
            hit_work.terms <= 32,
            "20,000 tuples need at most 16 inspected one-coordinate entries"
        );

        let mut miss_work = WorkMeter::new(None);
        assert!(!contains_capacity_tuple(
            &tuples,
            &[i64::try_from(MAX_FEASIBLE_TUPLES).expect("bounded target")],
            &mut miss_work,
        )
        .expect("exact non-membership"));
        assert!(miss_work.terms <= 32);

        let mut interrupted = WorkMeter::with_test_deadline_after(1);
        assert_eq!(
            contains_capacity_tuple(&tuples, &[0], &mut interrupted),
            Err(Decline::Deadline),
            "binary membership must remain inside the cumulative envelope"
        );
    }

    #[test]
    fn capacity_tuple_construction_checks_lexicographic_order() {
        let mut tuples = Vec::new();
        let mut work = WorkMeter::new(None);
        for tuple in [[0, 0], [0, 1], [1, 0]] {
            push_capacity_tuple_in_order(&tuple, &mut tuples, &mut work)
                .expect("strictly increasing tuple");
        }
        let before = tuples.clone();
        assert_eq!(
            push_capacity_tuple_in_order(&[0, 1], &mut tuples, &mut work),
            Err(Decline::Structure),
        );
        assert_eq!(tuples, before, "an out-of-order tuple is never retained");

        let mut full = (0..MAX_FEASIBLE_TUPLES)
            .map(|value| vec![i64::try_from(value).expect("bounded tuple")])
            .collect::<Vec<_>>();
        assert_eq!(
            push_capacity_tuple_in_order(
                &[i64::try_from(MAX_FEASIBLE_TUPLES).expect("bounded tuple")],
                &mut full,
                &mut work,
            ),
            Err(Decline::Resource),
        );
        assert_eq!(
            full.len(),
            MAX_FEASIBLE_TUPLES,
            "the rejected tuple must not allocate or mutate the retained set"
        );
    }

    #[test]
    fn exact_rmp_preflight_accounts_for_distinct_denominator_families() {
        let estimate = |model: &Model| {
            let mut work = WorkMeter::new(None);
            rmp_materialization(model, true, &mut work).expect("bounded exact preflight")
        };
        let baseline = estimate(&denominator_stress_master(8, 8, false, false, false));
        let matrix = estimate(&denominator_stress_master(8, 8, true, false, false));
        let rhs = estimate(&denominator_stress_master(8, 8, false, true, false));
        let objective_baseline = estimate(&denominator_stress_master(1, 8, false, false, false));
        let objective = estimate(&denominator_stress_master(1, 8, false, false, true));
        assert!(matrix.exact_cell_bits > baseline.exact_cell_bits);
        assert!(rhs.exact_cell_bits > baseline.exact_cell_bits);
        assert!(objective.exact_cell_bits > objective_baseline.exact_cell_bits);
        assert!(matrix.exact_cell_bytes >= baseline.exact_cell_bytes);
        assert!(rhs.exact_cell_bytes >= baseline.exact_cell_bytes);
        assert!(objective.exact_cell_bytes >= objective_baseline.exact_cell_bytes);

        // Forty small pairwise-coprime denominators per matrix row still look
        // harmless under a max-entry census.  Their basis-wide product is not:
        // the complete restricted-master path must reject the dense ExactLp
        // peak inside an explicitly pinned 32 MiB half-envelope before
        // constructing a session.  This low-memory contract is deliberately
        // independent of the larger bounded production default.
        const ADVERSARIAL_OUTER_BUDGET: usize = 64 << 20;
        let meter = MemoryMeter::new(Some(ADVERSARIAL_OUTER_BUDGET), false)
            .expect("deterministic route memory box");
        assert_eq!(meter.limit, 32 << 20);
        let (plan, patterns) = denominator_stress_plan(40);
        RMP_SESSION_MATERIALIZATIONS.with(|count| count.set(0));
        let mut adversarial_work = WorkMeter::new(None);
        assert_eq!(
            solve_restricted_master(
                &plan,
                &patterns,
                MasterPhase::Objective,
                MasterArithmetic::Exact,
                Some(ADVERSARIAL_OUTER_BUDGET),
                &mut adversarial_work,
            )
            .err(),
            Some(Decline::Memory),
        );
        RMP_SESSION_MATERIALIZATIONS.with(|count| {
            assert_eq!(
                count.get(),
                0,
                "the exact preflight must decline before nested LP construction"
            )
        });

        // The LCM computation itself uses the same checkpoints as the wall
        // deadline.  A deterministic injected deadline proves that a single
        // wide row cannot finish its repeated gcd/product census unchecked.
        let primes = first_primes(1_024);
        let mut wide = Model::new();
        let columns = (0..primes.len())
            .map(|_| wide.add_col(0.0, 1.0))
            .collect::<Vec<_>>();
        let rounded = columns
            .iter()
            .copied()
            .map(|column| (column, 1.0))
            .collect::<Vec<_>>();
        let row = wide.add_row(0.0, f64::INFINITY, &rounded);
        for (column, prime) in columns.iter().zip(primes) {
            wide.record_inexact_row_coeff(
                row,
                column.0,
                BigRational::new(BigInt::one(), BigInt::from(prime)),
            );
        }
        wide.set_objective(&[(columns[0], 1.0)], Sense::Minimize);
        let mut interrupted = WorkMeter::with_test_deadline_after(600);
        assert_eq!(
            rmp_materialization(&wide, true, &mut interrupted).err(),
            Some(Decline::Deadline),
        );
        assert!(
            interrupted.terms < rounded.len(),
            "deadline must interrupt the denominator census inside the wide row"
        );
    }

    #[test]
    fn float_only_rmp_certifies_true_side_store_without_exact_fallback() {
        let mut model = Model::new();
        let x = model.add_col(0.0, 1.0);
        model.add_row(0.0, f64::INFINITY, &[(x, 1.0)]);
        model.set_objective(&[(x, 1.0 / 3.0)], Sense::Minimize);
        let expired = Instant::now()
            .checked_sub(Duration::from_secs(1))
            .expect("representable expired deadline");
        let mut expired_session = LpSession::new(&model, &SolveOpts::new().with_deadline(expired))
            .expect("continuous LP");
        let mut unlimited = |_| true;
        assert!(
            expired_session
                .optimize_model_objective_float_only(&mut unlimited)
                .expect("bounded entry")
                .is_none(),
            "expired lowering/certification must decline"
        );
        assert!(!expired_session.exact_rim_is_materialized());

        let mut exact_f64_work = WorkMeter::new(None);
        let exact_f64_box = rmp_materialization(&model, true, &mut exact_f64_work)
            .expect("exact-f64 RMP receives a finite exact-tableau preflight");
        assert!(exact_f64_box.engine == RmpEngine::BoundedExact);

        model.record_inexact_obj_coeff(x.0, BigRational::new(BigInt::one(), BigInt::from(3)));
        let mut certified_work = WorkMeter::new(None);
        let certified_box = rmp_materialization(&model, false, &mut certified_work)
            .expect("true-model basis certification has a bounded materialization");
        assert!(certified_box.bytes > 0);
        assert!(certified_box.engine == RmpEngine::CertifiedFloat);
        let mut exact_work = WorkMeter::new(None);
        let exact_box = rmp_materialization(&model, true, &mut exact_work)
            .expect("explicit exact RMP receives a finite tableau preflight");
        assert!(exact_box.bytes > 0);
        assert!(exact_box.engine == RmpEngine::BoundedExact);
        let mut session = LpSession::new(&model, &SolveOpts::new()).expect("continuous LP");
        let mut unlimited = |_| true;
        let outcome = session
            .optimize_model_objective_float_only(&mut unlimited)
            .expect("bounded entry")
            .expect("the rounded basis is certified against the exact objective");
        assert!(
            matches!(
                outcome,
                Outcome::Optimal {
                    ref value,
                    cert: Some(_),
                    ..
                } if value.is_zero()
            ),
            "the exact objective has optimum zero at the lower bound: {outcome:?}"
        );
        assert!(
            !session.exact_rim_is_materialized(),
            "true-model basis certification must not enter ExactLp"
        );

        let mut underflowed = Model::new();
        let x = underflowed.add_col(0.0, 1.0);
        underflowed.set_objective(&[], Sense::Minimize);
        let tiny = BigRational::new(BigInt::one(), BigInt::from(10u8).pow(400));
        underflowed.record_inexact_obj_coeff(x.0, tiny.clone());
        assert_eq!(
            underflowed.obj_coeff(x),
            0.0,
            "the exact nonzero objective has an underflowed search proxy"
        );
        let mut session = LpSession::new(&underflowed, &SolveOpts::new()).expect("continuous LP");
        let mut unlimited = |_| true;
        let outcome = session
            .optimize_model_objective_float_only(&mut unlimited)
            .expect("bounded entry")
            .expect("the lower-bound basis proves the underflowed exact objective");
        let Outcome::Optimal {
            value,
            cert: Some(cert),
            ..
        } = outcome
        else {
            panic!("expected a certified exact optimum, got {outcome:?}");
        };
        assert!(value.is_zero());
        assert_eq!(cert.objective, vec![(x.0, tiny)]);
        assert!(
            !session.exact_rim_is_materialized(),
            "the zero-proxy exact objective must still avoid ExactLp"
        );
    }

    #[test]
    fn speculative_deadline_reserves_native_time() {
        let outer = Instant::now() + Duration::from_secs(60);
        let (recognition, route) = route_deadlines(Some(outer)).expect("positive route slice");
        assert!(recognition <= route);
        assert!(recognition <= Instant::now() + RECOGNITION_WALL_CAP);
        assert!(route < outer);
        assert!(outer.saturating_duration_since(route) >= Duration::from_secs(50));
    }
}
