// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Shared exact-rational polynomial kernel for the strict pure-NRA
//! certificate kinds (`TheoryLemmaKind::NraIntervalUnsat`,
//! `TheoryLemmaKind::NraUnivariateUnsat`).
//!
//! This module owns the pieces both NRA validators share:
//!
//! * multivariate polynomials over `BigRational` ([`MPoly`]) with
//!   `BTreeMap`-only iteration (deterministic, no hash order anywhere);
//! * fail-closed constraint extraction from a lemma clause
//!   ([`extract_constraints`]): the NEGATION of the clause must normalize to
//!   a conjunction of polynomial sign constraints over Real/Int-sorted
//!   terms, else the whole extraction refuses;
//! * exact rational intervals with open/closed endpoint algebra
//!   ([`Ival`]/[`Bnd`]) used by the HC4 interval kernel;
//! * a global [`WorkMeter`] with the budget caps — every cap trip is a
//!   refusal (`Err`), never a panic and never an acceptance.
//!
//! INDEPENDENCE (house constraint): this kernel deliberately does NOT
//! depend on `ay-theories/nra`. The solver's `univariate.rs`/`icp.rs`
//! search heuristics stay solver-side; the checker re-implements a minimal
//! closed DECISION so classifier and validator cannot drift and a solver
//! bug cannot leak into the trusted base.
//!
//! Soundness of the abstractions used here:
//!
//! * OPAQUE LEAVES: any non-whitelisted Real/Int-sorted application is
//!   treated as a fresh universally-quantified variable keyed by its
//!   `TermId` (arguments not recursed). Refuting all real valuations
//!   refutes in particular the valuation induced by any model of the
//!   richer theory. Identical `TermId`s share a variable (hash-consing
//!   makes this the congruence-respecting direction); distinct `TermId`s
//!   are never merged — merging would be the unsound direction and there
//!   is no merging code.
//! * INT RELAXATION: Int-sorted variables range over R here; R-infeasible
//!   implies Z-infeasible. Integrality is never used to refute.

use std::collections::{BTreeMap, BTreeSet};
use std::mem::size_of;

use ay_core::{Constant, Sort, Symbol, TermData, TermId, TermStore};
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Pow, Signed, Zero};

// ============================================================================
// Budget caps (fail-closed: every trip is a refusal, never an acceptance)
// ============================================================================

/// Unique DAG nodes visited during extraction (boolean spine + arithmetic).
pub(crate) const MAX_DAG_NODES: usize = 100_000;
/// Total expanded monomials across the whole invocation.
pub(crate) const MAX_TOTAL_MONOMIALS: usize = 200_000;
/// Maximum total degree of any parsed/derived polynomial.
pub(crate) const MAX_POLY_DEGREE: u32 = 256;
/// Global `BigRational` operation budget per recognize/validate invocation.
pub(crate) const MAX_BIGRATIONAL_OPS: u64 = 8_000_000;
/// Maximum numerator-plus-denominator width of any polynomial coefficient.
///
/// Exact arithmetic is only a finite checker envelope when one operation
/// cannot hide an attacker-sized `BigInt`.  Keep this independent of the
/// operation counter: every input is checked before cloning/arithmetic and
/// every result is checked before it can feed another operation.
pub(crate) const MAX_POLY_COEFF_BITS: u64 = 4_096;
/// Maximum distinct variables for the interval kernel.
pub(crate) const MAX_INTERVAL_VARS: usize = 24;
/// Maximum HC4 propagation passes.
pub(crate) const MAX_INTERVAL_PASSES: usize = 32;
/// Cumulative Sturm-chain coefficient size cap (bits).
pub(crate) const MAX_STURM_CHAIN_BITS: u64 = 1_000_000;
/// Maximum bisection/refinement steps during root isolation.
pub(crate) const MAX_BISECTION_STEPS: usize = 4_096;
/// Maximum recursion depth for the arithmetic term walk (stack safety; a
/// deeper term is refused, never overflowed into).
pub(crate) const MAX_PARSE_DEPTH: usize = 2_000;
/// Maximum bit-size (numerator + denominator) of any interval endpoint the
/// HC4 loop may carry into the next pass. Backward narrowing composes
/// multiplications and root bounds whose exact rational endpoints can grow
/// multiplicatively pass over pass; past this cap the propagation REFUSES
/// (fail closed) instead of grinding in huge-integer arithmetic. All
/// measured reclaim targets (mbo/hong) refute within the first passes with
/// endpoints under a couple hundred bits, so 4096 is generous headroom.
pub(crate) const MAX_ENDPOINT_BITS: u64 = 4_096;

const fn ceil_log2(value: usize) -> usize {
    let mut power = 1_usize;
    let mut bits = 0_usize;
    while power < value {
        power = power.saturating_mul(2);
        bits += 1;
    }
    bits
}

/// Caller-envelope debit for one materialized monomial. This covers a
/// degree-maximal key through deterministic-tree insertion/comparison, key and
/// coefficient cloning, and conservative node/value overhead. The internal
/// 200k monomial counter remains the hard per-invocation cap; this debit makes
/// repeated private materialization visible to the proof-wide caller.
pub(crate) const GENERIC_MONOMIAL_WORK: usize = MAX_POLY_DEGREE as usize
    * (2 * ceil_log2(MAX_TOTAL_MONOMIALS) + 16)
    + (MAX_POLY_COEFF_BITS as usize).div_ceil(32)
    + 1;
pub(crate) const GENERIC_MONOMIAL_BYTES: usize = MAX_POLY_DEGREE as usize
    * size_of::<(TermId, u32)>()
    + (MAX_POLY_COEFF_BITS as usize).div_ceil(8)
    + size_of::<Monomial>()
    + size_of::<BigRational>()
    + 64;
const GENERIC_DAG_NODE_BYTES: usize = 128;
const GENERIC_VARIABLE_ENTRY_BYTES: usize = size_of::<TermId>() + 64;
const GENERIC_VARIABLE_INSERT_WORK: u64 = ceil_log2(MAX_DAG_NODES) as u64 + 1;
pub(crate) const GENERIC_MEMO_TREE_WORK: usize = 2 * ceil_log2(MAX_DAG_NODES) + 16;
const GENERIC_CONTAINER_SLOT_OVERHEAD: usize = 64;
const MAX_RATIONAL_TRANSIENT_BITS: u64 = 2 * MAX_POLY_COEFF_BITS + 1;
const RATIONAL_SCRATCH_HEADERS: usize = 16 * (size_of::<BigInt>() + size_of::<BigRational>());

// ============================================================================
// Work meter
// ============================================================================

/// Global work budget for one recognize/validate invocation. A fresh meter is
/// created per call so recognizer and validator are bit-identical.
pub(crate) struct WorkMeter<'a> {
    ops_remaining: u64,
    monomials_remaining: usize,
    nodes_remaining: usize,
    progress: Option<&'a mut dyn FnMut(usize, usize) -> bool>,
}

impl<'a> WorkMeter<'a> {
    const PROGRESS_POLL_INTERVAL: u64 = 1_024;

    pub(crate) fn new() -> Self {
        Self {
            ops_remaining: MAX_BIGRATIONAL_OPS,
            monomials_remaining: MAX_TOTAL_MONOMIALS,
            nodes_remaining: MAX_DAG_NODES,
            progress: None,
        }
    }

    /// Construct a meter that also polls a caller-owned cancellation/deadline
    /// callback. Resource deltas remain charged by the outer proof envelope;
    /// this borrowed callback carries control only.
    pub(crate) fn with_progress(progress: &'a mut dyn FnMut(usize, usize) -> bool) -> Self {
        Self {
            ops_remaining: MAX_BIGRATIONAL_OPS,
            monomials_remaining: MAX_TOTAL_MONOMIALS,
            nodes_remaining: MAX_DAG_NODES,
            progress: Some(progress),
        }
    }

    fn charge_progress(&mut self, work: usize, bytes: usize) -> Result<(), String> {
        if self
            .progress
            .as_mut()
            .is_some_and(|progress| !progress(work, bytes))
        {
            return Err(WORK_METER_RESOURCE_LIMIT.to_string());
        }
        Ok(())
    }

    /// Immediate zero-debit control poll at phase boundaries.
    pub(crate) fn poll(&mut self) -> Result<(), String> {
        self.charge_progress(0, 0)
    }

    /// Poll at a bounded interval inside loops whose work was precharged in
    /// bulk. The loop index is local to one operation, so index zero also
    /// checks cancellation before the first potentially expensive item.
    pub(crate) fn poll_loop(&mut self, index: usize) -> Result<(), String> {
        if index.is_multiple_of(Self::PROGRESS_POLL_INTERVAL as usize) {
            self.poll()?;
        }
        Ok(())
    }

    /// Charge `n` rational operations; `Err` when the budget is exhausted.
    pub(crate) fn charge_ops(&mut self, n: u64) -> Result<(), String> {
        let caller_work = usize::try_from(n).map_err(|_| WORK_METER_RESOURCE_LIMIT.to_string())?;
        self.charge_progress(caller_work, 0)?;
        if self.ops_remaining < n {
            self.ops_remaining = 0;
            return Err("nra work budget exceeded: rational op meter".to_string());
        }
        self.ops_remaining -= n;
        Ok(())
    }

    /// Charge `n` produced monomials; `Err` when the budget is exhausted.
    pub(crate) fn charge_monomials(&mut self, n: usize) -> Result<(), String> {
        self.charge_structural_monomials(n)?;
        if self.monomials_remaining < n {
            self.monomials_remaining = 0;
            return Err("nra work budget exceeded: monomial meter".to_string());
        }
        self.monomials_remaining -= n;
        Ok(())
    }

    /// Debit caller-visible structural work/allocation without consuming the
    /// extraction production counter. Used for explicit clones owned by the
    /// equality-span eliminator, which has its own tighter materialization cap.
    pub(crate) fn charge_structural_monomials(&mut self, n: usize) -> Result<(), String> {
        let work = n
            .checked_mul(GENERIC_MONOMIAL_WORK)
            .ok_or_else(|| WORK_METER_RESOURCE_LIMIT.to_string())?;
        let bytes = n
            .checked_mul(GENERIC_MONOMIAL_BYTES)
            .ok_or_else(|| WORK_METER_RESOURCE_LIMIT.to_string())?;
        self.charge_progress(work, bytes)
    }

    pub(crate) fn charge_private_allocation(
        &mut self,
        work: usize,
        bytes: usize,
    ) -> Result<(), String> {
        self.charge_progress(work, bytes)
    }

    /// Debit conservative `num-rational` scratch before an exact operation.
    /// The caller's byte ledger is cumulative by design: repeated temporary
    /// allocations remain visible even though each operation releases them.
    pub(crate) fn charge_rational_scratch(&mut self, transient_bits: u64) -> Result<(), String> {
        self.charge_progress(0, generic_rational_scratch_bytes(transient_bits)?)
    }

    pub(crate) fn charge_container_slot<T>(&mut self) -> Result<(), String> {
        self.charge_progress(1, generic_container_slot_bytes::<T>()?)
    }

    /// Charge one visited DAG node; `Err` when the budget is exhausted.
    pub(crate) fn charge_node(&mut self) -> Result<(), String> {
        self.charge_nodes(1)
    }

    /// Reserve `n` pending Boolean-spine visits before allocating/enqueuing
    /// them. Charging at pop time alone permits a wide nested conjunction to
    /// materialize an attacker-sized queue before the same cap can fire.
    pub(crate) fn charge_nodes(&mut self, n: usize) -> Result<(), String> {
        let bytes = n
            .checked_mul(GENERIC_DAG_NODE_BYTES)
            .ok_or_else(|| WORK_METER_RESOURCE_LIMIT.to_string())?;
        self.charge_progress(n, bytes)?;
        if self.nodes_remaining < n {
            self.nodes_remaining = 0;
            return Err("nra work budget exceeded: DAG node meter".to_string());
        }
        self.nodes_remaining -= n;
        Ok(())
    }
}

pub(crate) fn generic_rational_scratch_bytes(transient_bits: u64) -> Result<usize, String> {
    if transient_bits > MAX_RATIONAL_TRANSIENT_BITS {
        return Err(WORK_METER_RESOURCE_LIMIT.to_string());
    }
    let payload = usize::try_from(transient_bits.saturating_add(7) / 8)
        .map_err(|_| WORK_METER_RESOURCE_LIMIT.to_string())?;
    payload
        .checked_mul(32)
        .and_then(|bytes| bytes.checked_add(RATIONAL_SCRATCH_HEADERS))
        .ok_or_else(|| WORK_METER_RESOURCE_LIMIT.to_string())
}

pub(crate) fn generic_container_slot_bytes<T>() -> Result<usize, String> {
    size_of::<T>()
        .checked_mul(4)
        .and_then(|slots| slots.checked_add(GENERIC_CONTAINER_SLOT_OVERHEAD))
        .ok_or_else(|| WORK_METER_RESOURCE_LIMIT.to_string())
}

fn binary_rational_transient_bits(left: &BigRational, right: &BigRational) -> u64 {
    rat_bits(left)
        .saturating_add(rat_bits(right))
        .saturating_add(1)
}

/// Stable internal marker used to preserve caller cancellation as the typed
/// proof-level `ResourceLimit` error across the arithmetic checker's existing
/// string-error boundary.
pub(crate) const WORK_METER_RESOURCE_LIMIT: &str = "nra caller resource envelope exhausted";

// ============================================================================
// Multivariate polynomials
// ============================================================================

/// A monomial: sorted `(variable TermId, exponent)` pairs, exponents >= 1.
/// The empty vector is the constant monomial.
pub(crate) type Monomial = Vec<(TermId, u32)>;

/// Total degree of a monomial.
pub(crate) fn monomial_degree(m: &Monomial) -> u32 {
    m.iter().map(|&(_, e)| e).sum()
}

/// A multivariate polynomial over `BigRational`, keyed by monomial.
/// `BTreeMap` keeps every iteration deterministic.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct MPoly {
    pub(crate) terms: BTreeMap<Monomial, BigRational>,
}

impl MPoly {
    pub(crate) fn zero() -> Self {
        Self::default()
    }

    pub(crate) fn constant(c: BigRational) -> Self {
        let mut p = Self::default();
        if !c.is_zero() {
            p.terms.insert(Vec::new(), c);
        }
        p
    }

    pub(crate) fn var(v: TermId) -> Self {
        let mut p = Self::default();
        p.terms.insert(vec![(v, 1)], BigRational::one());
        p
    }

    /// `None` when the polynomial has a non-constant monomial.
    pub(crate) fn as_constant(
        &self,
        meter: &mut WorkMeter<'_>,
    ) -> Result<Option<BigRational>, String> {
        match self.terms.len() {
            0 => Ok(Some(BigRational::zero())),
            1 => {
                let Some((m, c)) = self.terms.iter().next() else {
                    return Ok(None);
                };
                if m.is_empty() {
                    ensure_coeff_width(c)?;
                    meter.charge_ops(bit_scaled(1, rat_bits(c)))?;
                    meter.charge_private_allocation(0, rational_clone_bytes(c)?)?;
                    Ok(Some(c.clone()))
                } else {
                    Ok(None)
                }
            }
            _ => Ok(None),
        }
    }

    pub(crate) fn max_total_degree(&self) -> u32 {
        self.terms.keys().map(monomial_degree).max().unwrap_or(0)
    }

    fn max_total_degree_metered(&self, meter: &mut WorkMeter<'_>) -> Result<u32, String> {
        let mut maximum = 0;
        for (index, monomial) in self.terms.keys().enumerate() {
            meter.poll_loop(index)?;
            maximum = maximum.max(monomial_degree(monomial));
        }
        Ok(maximum)
    }

    /// Distinct variables of this polynomial, merged into `out`.
    pub(crate) fn collect_vars(
        &self,
        out: &mut BTreeSet<TermId>,
        meter: &mut WorkMeter<'_>,
    ) -> Result<(), String> {
        for (index, m) in self.terms.keys().enumerate() {
            meter.poll_loop(index)?;
            for &(v, _) in m {
                meter.charge_ops(GENERIC_VARIABLE_INSERT_WORK)?;
                meter.charge_private_allocation(0, GENERIC_VARIABLE_ENTRY_BYTES)?;
                out.insert(v);
            }
        }
        Ok(())
    }

    fn add_monomial(
        &mut self,
        m: Monomial,
        c: BigRational,
        meter: &mut WorkMeter<'_>,
    ) -> Result<(), String> {
        ensure_coeff_width(&c)?;
        if c.is_zero() {
            return Ok(());
        }
        match self.terms.entry(m) {
            std::collections::btree_map::Entry::Vacant(e) => {
                e.insert(c);
            }
            std::collections::btree_map::Entry::Occupied(mut e) => {
                let bits = rat_bits(e.get()).max(rat_bits(&c));
                meter.charge_ops(bit_scaled(1, bits))?;
                meter.charge_rational_scratch(binary_rational_transient_bits(e.get(), &c))?;
                let sum = e.get() + &c;
                ensure_coeff_width(&sum)?;
                if sum.is_zero() {
                    e.remove();
                } else {
                    *e.get_mut() = sum;
                }
            }
        }
        Ok(())
    }

    /// In-place sum, charging only the ADDEND's size — the n-ary `+` of an
    /// mbo-scale polynomial (thousands of monomials) must accumulate in
    /// linear total work, not quadratically.
    pub(crate) fn add_assign_from(
        &mut self,
        other: &Self,
        meter: &mut WorkMeter<'_>,
    ) -> Result<(), String> {
        // Do not rescan `self` here. This is the accumulator used by n-ary
        // `+`; rescanning the growing result for every addend would turn the
        // linear fold into unmetered quadratic work. Existing coefficients
        // passed the width invariant when inserted, and `add_monomial` below
        // checks and charges the one accumulator entry an addend touches.
        meter.charge_ops(other.terms.len() as u64)?; // coefficient-width scan
        let bits = max_coeff_bits_metered(other.terms.values(), meter)?;
        if bits > MAX_POLY_COEFF_BITS {
            return Err(format!(
                "nra polynomial coefficient exceeds cap {MAX_POLY_COEFF_BITS} bits"
            ));
        }
        meter.charge_ops(bit_scaled(other.terms.len() as u64 + 1, bits))?;
        meter.charge_monomials(other.terms.len())?;
        for (index, (m, c)) in other.terms.iter().enumerate() {
            meter.poll_loop(index)?;
            ensure_coeff_width(c)?;
            self.add_monomial(m.clone(), c.clone(), meter)?;
        }
        Ok(())
    }

    /// In-place difference (adds the negation of `other`).
    pub(crate) fn sub_assign_from(
        &mut self,
        other: &Self,
        meter: &mut WorkMeter<'_>,
    ) -> Result<(), String> {
        // As above, validate/charge the addend plus the exact accumulator
        // entries touched by `add_monomial`; never rescan a growing n-ary
        // subtraction result.
        meter.charge_ops(other.terms.len() as u64)?; // coefficient-width scan
        let bits = max_coeff_bits_metered(other.terms.values(), meter)?;
        if bits > MAX_POLY_COEFF_BITS {
            return Err(format!(
                "nra polynomial coefficient exceeds cap {MAX_POLY_COEFF_BITS} bits"
            ));
        }
        meter.charge_ops(bit_scaled(other.terms.len() as u64 + 1, bits))?;
        meter.charge_monomials(other.terms.len())?;
        for (index, (m, c)) in other.terms.iter().enumerate() {
            meter.poll_loop(index)?;
            // Check before unary negation: `-c` owns a new BigInt allocation.
            ensure_coeff_width(c)?;
            meter.charge_rational_scratch(rat_bits(c).saturating_add(1))?;
            let negated = -c;
            self.add_monomial(m.clone(), negated, meter)?;
        }
        Ok(())
    }

    pub(crate) fn neg(&self, meter: &mut WorkMeter<'_>) -> Result<Self, String> {
        meter.charge_ops(self.terms.len() as u64)?; // coefficient-width scan
        let bits = max_coeff_bits_metered(self.terms.values(), meter)?;
        if bits > MAX_POLY_COEFF_BITS {
            return Err(format!(
                "nra polynomial coefficient exceeds cap {MAX_POLY_COEFF_BITS} bits"
            ));
        }
        meter.charge_ops(bit_scaled(self.terms.len() as u64, bits))?;
        meter.charge_monomials(self.terms.len())?;
        let mut out = Self::default();
        for (index, (m, c)) in self.terms.iter().enumerate() {
            meter.poll_loop(index)?;
            // Check before unary negation: `-c` owns a new BigInt allocation.
            ensure_coeff_width(c)?;
            meter.charge_rational_scratch(rat_bits(c).saturating_add(1))?;
            out.terms.insert(m.clone(), -c);
        }
        Ok(out)
    }

    pub(crate) fn sub(&self, other: &Self, meter: &mut WorkMeter<'_>) -> Result<Self, String> {
        meter.charge_ops(self.terms.len() as u64)?; // coefficient-width scan
        let bits = max_coeff_bits_metered(self.terms.values(), meter)?;
        if bits > MAX_POLY_COEFF_BITS {
            return Err(format!(
                "nra polynomial coefficient exceeds cap {MAX_POLY_COEFF_BITS} bits"
            ));
        }
        meter.charge_ops(bit_scaled(self.terms.len() as u64, bits))?;
        meter.charge_monomials(self.terms.len())?;
        let mut out = self.clone();
        out.sub_assign_from(other, meter)?;
        Ok(out)
    }

    pub(crate) fn scale(&self, c: &BigRational, meter: &mut WorkMeter<'_>) -> Result<Self, String> {
        ensure_coeff_width(c)?;
        meter.charge_ops(self.terms.len() as u64)?; // coefficient-width scan
        let bits = max_coeff_bits_metered(self.terms.values(), meter)?.max(rat_bits(c));
        if bits > MAX_POLY_COEFF_BITS {
            return Err(format!(
                "nra polynomial coefficient exceeds cap {MAX_POLY_COEFF_BITS} bits"
            ));
        }
        meter.charge_ops(bit_scaled(self.terms.len() as u64, bits))?;
        meter.charge_monomials(self.terms.len())?;
        if c.is_zero() {
            return Ok(Self::zero());
        }
        let mut out = Self::default();
        for (index, (m, k)) in self.terms.iter().enumerate() {
            meter.poll_loop(index)?;
            meter.charge_rational_scratch(binary_rational_transient_bits(k, c))?;
            let scaled = k * c;
            ensure_coeff_width(&scaled)?;
            out.terms.insert(m.clone(), scaled);
        }
        Ok(out)
    }

    pub(crate) fn mul(&self, other: &Self, meter: &mut WorkMeter<'_>) -> Result<Self, String> {
        let product_size = self.terms.len().saturating_mul(other.terms.len());
        meter.charge_ops(self.terms.len().saturating_add(other.terms.len()) as u64)?;
        let bits = max_coeff_bits_metered(self.terms.values(), meter)?
            .max(max_coeff_bits_metered(other.terms.values(), meter)?);
        if bits > MAX_POLY_COEFF_BITS {
            return Err(format!(
                "nra polynomial coefficient exceeds cap {MAX_POLY_COEFF_BITS} bits"
            ));
        }
        meter.charge_ops(bit_scaled(product_size as u64, bits))?;
        meter.charge_monomials(product_size)?;
        let mut out = Self::default();
        let mut product_index = 0_usize;
        for (ma, ca) in &self.terms {
            for (mb, cb) in &other.terms {
                meter.poll_loop(product_index)?;
                product_index = product_index.saturating_add(1);
                let m = merge_monomials(ma, mb)?;
                if monomial_degree(&m) > MAX_POLY_DEGREE {
                    return Err(format!(
                        "nra polynomial degree exceeds cap {MAX_POLY_DEGREE}"
                    ));
                }
                meter.charge_rational_scratch(binary_rational_transient_bits(ca, cb))?;
                let product = ca * cb;
                ensure_coeff_width(&product)?;
                out.add_monomial(m, product, meter)?;
            }
        }
        Ok(out)
    }
}

/// Merge two sorted monomials, adding exponents of shared variables.
fn merge_monomials(a: &Monomial, b: &Monomial) -> Result<Monomial, String> {
    // Refuse an over-degree product before reserving its merged key. Since
    // every exponent is positive, this also bounds the requested Vec capacity
    // by the accepted degree envelope.
    let combined_degree = monomial_degree(a)
        .checked_add(monomial_degree(b))
        .ok_or_else(|| "nra polynomial degree overflow".to_string())?;
    if combined_degree > MAX_POLY_DEGREE {
        return Err(format!(
            "nra polynomial degree exceeds cap {MAX_POLY_DEGREE}"
        ));
    }
    let capacity = a
        .len()
        .checked_add(b.len())
        .ok_or_else(|| "nra monomial key capacity overflow".to_string())?;
    let mut out = Vec::with_capacity(capacity);
    let (mut i, mut j) = (0, 0);
    while i < a.len() && j < b.len() {
        match a[i].0.cmp(&b[j].0) {
            std::cmp::Ordering::Less => {
                out.push(a[i]);
                i += 1;
            }
            std::cmp::Ordering::Greater => {
                out.push(b[j]);
                j += 1;
            }
            std::cmp::Ordering::Equal => {
                let e = a[i]
                    .1
                    .checked_add(b[j].1)
                    .ok_or_else(|| "nra monomial exponent overflow".to_string())?;
                out.push((a[i].0, e));
                i += 1;
                j += 1;
            }
        }
    }
    out.extend_from_slice(&a[i..]);
    out.extend_from_slice(&b[j..]);
    Ok(out)
}

// ============================================================================
// Constraints
// ============================================================================

/// Relation of a normalized constraint `poly REL 0`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Rel {
    /// `poly = 0`
    Eq,
    /// `poly != 0`
    Ne,
    /// `poly < 0`
    Lt,
    /// `poly <= 0`
    Le,
    /// `poly > 0`
    Gt,
    /// `poly >= 0`
    Ge,
}

impl Rel {
    /// Whether a value with the given exact sign (`-1`, `0`, `+1`) satisfies
    /// the relation against zero.
    pub(crate) fn satisfied_by_sign(self, sign: std::cmp::Ordering) -> bool {
        use std::cmp::Ordering::{Equal, Greater, Less};
        match self {
            Self::Eq => sign == Equal,
            Self::Ne => sign != Equal,
            Self::Lt => sign == Less,
            Self::Le => sign != Greater,
            Self::Gt => sign == Greater,
            Self::Ge => sign != Less,
        }
    }
}

/// One normalized sign constraint `poly REL 0`.
#[derive(Clone, Debug)]
pub(crate) struct Constraint {
    pub(crate) poly: MPoly,
    pub(crate) rel: Rel,
}

/// Result of [`extract_constraints`].
pub(crate) struct Extraction {
    /// Surviving non-constant constraints (constant conjuncts evaluated away).
    pub(crate) constraints: Vec<Constraint>,
    /// Distinct variables (opaque leaves included) of surviving constraints.
    pub(crate) vars: BTreeSet<TermId>,
    /// Whether any parsed relation SIDE contains a monomial of total
    /// degree 2 or more (this subsumes the difference polynomial, since
    /// `deg(a-b) <= max(deg a, deg b)`). Identity refutations with
    /// cancelling nonlinear sides count as nonlinear; all-linear-sides
    /// conflicts never do.
    pub(crate) has_nonlinear: bool,
    /// Whether some constant conjunct evaluated to FALSE (the conjunction is
    /// then infeasible outright).
    pub(crate) const_refuted: bool,
}

struct RelationExtraction {
    constraint: Option<Constraint>,
    has_nonlinear: bool,
    const_refuted: bool,
}

fn extract_polynomial_relation(
    terms: &TermStore,
    name: &str,
    args: &[TermId],
    asserted: bool,
    memo: &mut BTreeMap<TermId, MPoly>,
    meter: &mut WorkMeter<'_>,
) -> Result<RelationExtraction, String> {
    let (a, b) = (args[0], args[1]);
    if !matches!(terms.sort(a), Sort::Int | Sort::Real)
        || !matches!(terms.sort(b), Sort::Int | Sort::Real)
    {
        return Err(format!(
            "relation {name} over non-arithmetic sorts {:?}/{:?}",
            terms.sort(a),
            terms.sort(b)
        ));
    }
    if terms.sort(a) != terms.sort(b) {
        return Err(format!(
            "relation {name} has mismatched arithmetic sorts {:?}/{:?}",
            terms.sort(a),
            terms.sort(b)
        ));
    }
    let pa = parse_poly(terms, a, memo, meter, 0)?;
    let pb = parse_poly(terms, b, memo, meter, 0)?;
    // Nonlinearity is measured on the parsed SIDES: a polynomial identity
    // refutation can have nonlinear sides whose difference cancels.
    let has_nonlinear =
        pa.max_total_degree_metered(meter)? >= 2 || pb.max_total_degree_metered(meter)? >= 2;
    let poly = pa.sub(&pb, meter)?;
    let rel = match (name, asserted) {
        ("<", true) => Rel::Lt,
        ("<", false) => Rel::Ge,
        ("<=", true) => Rel::Le,
        ("<=", false) => Rel::Gt,
        (">", true) => Rel::Gt,
        (">", false) => Rel::Le,
        (">=", true) => Rel::Ge,
        (">=", false) => Rel::Lt,
        ("=", true) => Rel::Eq,
        ("=", false) => Rel::Ne,
        _ => return Err(format!("unsupported relation {name}")),
    };
    let constant = poly.as_constant(meter)?;
    let const_refuted = constant
        .as_ref()
        .is_some_and(|c| !rel.satisfied_by_sign(c.cmp(&BigRational::zero())));
    let constraint = constant.is_none().then_some(Constraint { poly, rel });
    Ok(RelationExtraction {
        constraint,
        has_nonlinear,
        const_refuted,
    })
}

/// Normalize the NEGATION of `clause` into a conjunction of polynomial sign
/// constraints, failing closed on ANY unsupported shape.
///
/// The negation of a clause is the conjunction of the negations of its
/// literals. Each literal contributes: `(not phi)` asserts `phi`; a bare atom
/// asserts its negation (relation flipped, equality becoming `!=`). An `and`
/// asserted positively flattens recursively (the mbo shape: one literal
/// `not(and (> h1 0) ... (= BIGPOLY 0))`). Any `or`, `=>`, `ite`, `let`,
/// quantifier, Boolean variable or constant, non-arithmetic sort, or `and`
/// under negation refuses the whole extraction.
pub(crate) fn extract_constraints(
    terms: &TermStore,
    clause: &[TermId],
    meter: &mut WorkMeter<'_>,
) -> Result<Extraction, String> {
    if clause.is_empty() {
        return Err("empty clause".to_string());
    }
    meter.charge_nodes(clause.len())?;
    for &lit in clause {
        if !matches!(terms.sort(lit), Sort::Bool) {
            return Err(format!(
                "literal has non-Bool sort {:?}; lemma clauses must be propositional",
                terms.sort(lit)
            ));
        }
    }

    // (formula, asserted): `asserted == true` asserts the formula itself,
    // `false` asserts its negation. The negated clause asserts the negation
    // of every literal.
    let mut pending: Vec<(TermId, bool)> = Vec::new();
    pending
        .try_reserve_exact(clause.len())
        .map_err(|_| "nra pending-clause allocation refused".to_string())?;
    pending.extend(clause.iter().rev().map(|&lit| (lit, false)));
    let mut memo: BTreeMap<TermId, MPoly> = BTreeMap::new();
    let mut constraints: Vec<Constraint> = Vec::new();
    let mut has_nonlinear = false;
    let mut const_refuted = false;

    while let Some((t, asserted)) = pending.pop() {
        meter.poll()?;
        match terms.get(t) {
            TermData::Not(inner) => {
                meter.charge_node()?;
                pending
                    .try_reserve(1)
                    .map_err(|_| "nra pending-negation allocation refused".to_string())?;
                pending.push((*inner, !asserted));
            }
            TermData::App(Symbol::Named(name), args) if name == "and" => {
                if !asserted {
                    return Err(
                        "negated conjunction is disjunctive; out of the conjunctive fragment"
                            .to_string(),
                    );
                }
                meter.charge_nodes(args.len())?;
                pending
                    .try_reserve(args.len())
                    .map_err(|_| "nra pending-conjunction allocation refused".to_string())?;
                for &arg in args.iter().rev() {
                    pending.push((arg, true));
                }
            }
            TermData::App(Symbol::Named(name), args)
                if args.len() == 2 && matches!(name.as_str(), "<" | "<=" | ">" | ">=" | "=") =>
            {
                let extracted =
                    extract_polynomial_relation(terms, name, args, asserted, &mut memo, meter)?;
                has_nonlinear |= extracted.has_nonlinear;
                const_refuted |= extracted.const_refuted;
                if let Some(constraint) = extracted.constraint {
                    meter.charge_container_slot::<Constraint>()?;
                    constraints
                        .try_reserve(1)
                        .map_err(|_| "nra constraint allocation refused".to_string())?;
                    constraints.push(constraint);
                }
            }
            _ => {
                return Err(
                    "literal is not a polynomial sign constraint over Real/Int terms; \
                     out of the pure-NRA fragment"
                        .to_string(),
                );
            }
        }
    }

    let mut vars = BTreeSet::new();
    for c in &constraints {
        c.poly.collect_vars(&mut vars, meter)?;
    }
    Ok(Extraction {
        constraints,
        vars,
        has_nonlinear,
        const_refuted,
    })
}

/// Parse an arithmetic term into an exact multivariate polynomial, walking
/// the same `TermData` surface as `ay-core`'s Farkas parser but into a
/// multivariate poly. Whitelist-only; any non-whitelisted Real/Int-sorted
/// APPLICATION becomes an opaque leaf (fresh variable keyed by its `TermId`,
/// arguments NOT recursed); anything else refuses.
fn parse_poly(
    terms: &TermStore,
    t: TermId,
    memo: &mut BTreeMap<TermId, MPoly>,
    meter: &mut WorkMeter<'_>,
    depth: usize,
) -> Result<MPoly, String> {
    if depth > MAX_PARSE_DEPTH {
        return Err("nra term nesting exceeds depth cap".to_string());
    }
    meter.charge_private_allocation(GENERIC_MEMO_TREE_WORK, 0)?;
    if let Some(p) = memo.get(&t) {
        charge_poly_result(p, meter)?;
        return Ok(p.clone());
    }
    meter.charge_node()?;
    let poly = parse_poly_uncached(terms, t, memo, meter, depth)?;
    if poly.max_total_degree_metered(meter)? > MAX_POLY_DEGREE {
        return Err(format!(
            "nra polynomial degree exceeds cap {MAX_POLY_DEGREE}"
        ));
    }
    charge_poly_result(&poly, meter)?;
    meter.charge_private_allocation(GENERIC_MEMO_TREE_WORK, 0)?;
    memo.insert(t, poly.clone());
    Ok(poly)
}

fn parse_poly_uncached(
    terms: &TermStore,
    t: TermId,
    memo: &mut BTreeMap<TermId, MPoly>,
    meter: &mut WorkMeter<'_>,
    depth: usize,
) -> Result<MPoly, String> {
    match terms.get(t) {
        TermData::Const(Constant::Int(n)) => {
            let bits = n.bits().saturating_add(1); // denominator is one
            if bits > MAX_POLY_COEFF_BITS {
                return Err(format!(
                    "nra polynomial coefficient exceeds cap {MAX_POLY_COEFF_BITS} bits"
                ));
            }
            meter.charge_ops(bit_scaled(1, bits))?;
            meter.charge_monomials(1)?;
            Ok(MPoly::constant(BigRational::from(n.clone())))
        }
        TermData::Const(Constant::Rational(r)) => {
            ensure_coeff_width(&r.0)?;
            meter.charge_ops(bit_scaled(1, rat_bits(&r.0)))?;
            meter.charge_monomials(1)?;
            Ok(MPoly::constant(r.0.clone()))
        }
        TermData::Var(_, _) if matches!(terms.sort(t), Sort::Int | Sort::Real) => {
            meter.charge_monomials(1)?;
            Ok(MPoly::var(t))
        }
        TermData::App(Symbol::Named(name), args) if name == "+" => {
            let result_sort = terms.sort(t);
            if !matches!(result_sort, Sort::Int | Sort::Real)
                || args.iter().any(|&arg| terms.sort(arg) != result_sort)
            {
                return Err("ill-sorted arithmetic addition".to_string());
            }
            let mut acc = MPoly::zero();
            for &arg in args {
                let sub = parse_poly(terms, arg, memo, meter, depth + 1)?;
                acc.add_assign_from(&sub, meter)?;
            }
            Ok(acc)
        }
        TermData::App(Symbol::Named(name), args) if name == "-" && args.len() == 1 => {
            if !matches!(terms.sort(t), Sort::Int | Sort::Real)
                || terms.sort(args[0]) != terms.sort(t)
            {
                return Err("ill-sorted arithmetic negation".to_string());
            }
            parse_poly(terms, args[0], memo, meter, depth + 1)?.neg(meter)
        }
        TermData::App(Symbol::Named(name), args) if name == "-" && args.len() >= 2 => {
            let result_sort = terms.sort(t);
            if !matches!(result_sort, Sort::Int | Sort::Real)
                || args.iter().any(|&arg| terms.sort(arg) != result_sort)
            {
                return Err("ill-sorted arithmetic subtraction".to_string());
            }
            let mut acc = parse_poly(terms, args[0], memo, meter, depth + 1)?;
            for &arg in &args[1..] {
                let sub = parse_poly(terms, arg, memo, meter, depth + 1)?;
                acc.sub_assign_from(&sub, meter)?;
            }
            Ok(acc)
        }
        TermData::App(Symbol::Named(name), args) if name == "*" => {
            let result_sort = terms.sort(t);
            if !matches!(result_sort, Sort::Int | Sort::Real)
                || args.iter().any(|&arg| terms.sort(arg) != result_sort)
            {
                return Err("ill-sorted arithmetic multiplication".to_string());
            }
            meter.charge_monomials(1)?;
            let mut acc = MPoly::constant(BigRational::one());
            for &arg in args {
                let sub = parse_poly(terms, arg, memo, meter, depth + 1)?;
                acc = acc.mul(&sub, meter)?;
            }
            Ok(acc)
        }
        TermData::App(Symbol::Named(name), args)
            if name == "/" && args.len() == 2 && matches!(terms.sort(t), Sort::Real) =>
        {
            parse_real_division(terms, t, args, memo, meter, depth)
        }
        TermData::App(_, _) if matches!(terms.sort(t), Sort::Int | Sort::Real) => {
            // Opaque leaf: fresh variable keyed by this TermId.
            meter.charge_monomials(1)?;
            Ok(MPoly::var(t))
        }
        _ => Err(
            "term outside the whitelisted arithmetic fragment (ite/let/quantifier/\
             non-arithmetic constant or variable)"
                .to_string(),
        ),
    }
}

fn parse_real_division(
    terms: &TermStore,
    term: TermId,
    args: &[TermId],
    memo: &mut BTreeMap<TermId, MPoly>,
    meter: &mut WorkMeter<'_>,
    depth: usize,
) -> Result<MPoly, String> {
    if args.iter().any(|&arg| *terms.sort(arg) != Sort::Real) {
        return Err("ill-sorted real division".to_string());
    }
    // Division ONLY by a subtree that evaluates to a nonzero rational
    // constant (exact scaling); otherwise the whole node is an opaque leaf
    // (universal abstraction, sound for refutation).
    let denom = parse_poly(terms, args[1], memo, meter, depth + 1)?;
    Ok(match denom.as_constant(meter)? {
        Some(c) if !c.is_zero() => {
            let numer = parse_poly(terms, args[0], memo, meter, depth + 1)?;
            ensure_coeff_width(&c)?;
            meter.charge_ops(bit_scaled(1, rat_bits(&c)))?;
            meter.charge_private_allocation(0, rational_clone_bytes(&c)?)?;
            meter.charge_rational_scratch(rat_bits(&c).saturating_add(3))?;
            let inverse = BigRational::one() / c;
            ensure_coeff_width(&inverse)?;
            numer.scale(&inverse, meter)?
        }
        _ => {
            meter.charge_monomials(1)?;
            MPoly::var(term)
        }
    })
}

fn charge_poly_result(poly: &MPoly, meter: &mut WorkMeter<'_>) -> Result<(), String> {
    meter.charge_ops(poly.terms.len() as u64)?; // coefficient-width scan
    let bits = max_coeff_bits_metered(poly.terms.values(), meter)?;
    if bits > MAX_POLY_COEFF_BITS {
        return Err(format!(
            "nra polynomial coefficient exceeds cap {MAX_POLY_COEFF_BITS} bits"
        ));
    }
    meter.charge_ops(bit_scaled(poly.terms.len() as u64, bits))?;
    meter.charge_monomials(poly.terms.len())?;
    Ok(())
}

// ============================================================================
// Exact rational intervals with open/closed endpoints
// ============================================================================

/// One interval endpoint. Finite endpoints carry openness (`true` = open,
/// the endpoint value is EXCLUDED). Infinite endpoints are inherently open.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Bnd {
    NegInf,
    Fin(BigRational, bool),
    PosInf,
}

impl Bnd {
    pub(crate) fn closed(v: BigRational) -> Self {
        Self::Fin(v, false)
    }
    pub(crate) fn open(v: BigRational) -> Self {
        Self::Fin(v, true)
    }

    fn bits(&self) -> u64 {
        match self {
            Self::NegInf | Self::PosInf => 1,
            Self::Fin(v, _) => rat_bits(v),
        }
    }
}

/// Bit-size of a rational (numerator + denominator): the honest cost unit
/// for exact arithmetic — one "operation" on n-bit operands costs O(n)
/// word operations, and the meter must account for that or a pathological
/// system could grind for minutes inside a nominally-bounded op count.
pub(crate) fn rat_bits(v: &BigRational) -> u64 {
    v.numer().bits().saturating_add(v.denom().bits())
}

/// Reject an attacker-sized exact coefficient before it can be cloned or used
/// by another polynomial operation.
pub(crate) fn ensure_coeff_width(v: &BigRational) -> Result<(), String> {
    if rat_bits(v) > MAX_POLY_COEFF_BITS {
        Err(format!(
            "nra polynomial coefficient exceeds cap {MAX_POLY_COEFF_BITS} bits"
        ))
    } else {
        Ok(())
    }
}

fn rational_clone_bytes(value: &BigRational) -> Result<usize, String> {
    let payload = usize::try_from(rat_bits(value).saturating_add(7) / 8)
        .map_err(|_| WORK_METER_RESOURCE_LIMIT.to_string())?;
    payload
        .checked_add(size_of::<BigRational>())
        .ok_or_else(|| WORK_METER_RESOURCE_LIMIT.to_string())
}

/// Largest coefficient bit-size in a coefficient slice, for bit-proportional
/// work charging: exact-arithmetic loops must charge by operand width, or a
/// clause with enormous rational literals could grind CPU inside a
/// nominally-bounded op count (the meter's unit is a WORD operation).
pub(crate) fn max_coeff_bits<'a, I: IntoIterator<Item = &'a BigRational>>(coeffs: I) -> u64 {
    coeffs.into_iter().map(rat_bits).max().unwrap_or(0)
}

fn max_coeff_bits_metered<'a, I: IntoIterator<Item = &'a BigRational>>(
    coeffs: I,
    meter: &mut WorkMeter<'_>,
) -> Result<u64, String> {
    let mut maximum = 0;
    for (index, coefficient) in coeffs.into_iter().enumerate() {
        meter.poll_loop(index)?;
        maximum = maximum.max(rat_bits(coefficient));
    }
    Ok(maximum)
}

/// Scale an op count by operand bit-width in 32-bit words (minimum 1).
pub(crate) fn bit_scaled(ops: u64, bits: u64) -> u64 {
    ops.saturating_mul(1 + bits / 32)
}

/// Compare two endpoints by VALUE only (openness ignored).
fn cmp_bnd_val(a: &Bnd, b: &Bnd) -> std::cmp::Ordering {
    use std::cmp::Ordering::{Equal, Greater, Less};
    match (a, b) {
        (Bnd::NegInf, Bnd::NegInf) | (Bnd::PosInf, Bnd::PosInf) => Equal,
        (Bnd::NegInf, _) | (_, Bnd::PosInf) => Less,
        (_, Bnd::NegInf) | (Bnd::PosInf, _) => Greater,
        (Bnd::Fin(x, _), Bnd::Fin(y, _)) => x.cmp(y),
    }
}

/// An interval over the extended reals. Invariant: `lo` is never `PosInf`
/// and `hi` is never `NegInf`. Emptiness is represented, not panicked on.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Ival {
    pub(crate) lo: Bnd,
    pub(crate) hi: Bnd,
}

impl Ival {
    pub(crate) fn full() -> Self {
        Self {
            lo: Bnd::NegInf,
            hi: Bnd::PosInf,
        }
    }

    pub(crate) fn point(v: BigRational) -> Self {
        Self {
            lo: Bnd::closed(v.clone()),
            hi: Bnd::closed(v),
        }
    }

    pub(crate) fn empty() -> Self {
        Self {
            lo: Bnd::open(BigRational::zero()),
            hi: Bnd::open(BigRational::zero()),
        }
    }

    pub(crate) fn is_empty(&self) -> bool {
        match (&self.lo, &self.hi) {
            (Bnd::NegInf, _) | (_, Bnd::PosInf) => false,
            (Bnd::Fin(a, ao), Bnd::Fin(b, bo)) => match a.cmp(b) {
                std::cmp::Ordering::Greater => true,
                std::cmp::Ordering::Equal => *ao || *bo,
                std::cmp::Ordering::Less => false,
            },
            // lo == PosInf or hi == NegInf: invariant breach (no constructor
            // here produces it — `add`/`mul` return Err instead). Emptiness
            // is the ACCEPTING direction in the interval kernel, so a
            // hypothetical breach must NOT be read as empty: answer false,
            // which can only lose refutations, never fabricate one.
            _ => false,
        }
    }

    /// Whether the value 0 is a MEMBER of the interval (openness respected).
    pub(crate) fn contains_zero(&self) -> bool {
        if self.is_empty() {
            return false;
        }
        let lo_ok = match &self.lo {
            Bnd::NegInf => true,
            Bnd::Fin(v, open) => match v.cmp(&BigRational::zero()) {
                std::cmp::Ordering::Less => true,
                std::cmp::Ordering::Equal => !*open,
                std::cmp::Ordering::Greater => false,
            },
            Bnd::PosInf => false,
        };
        let hi_ok = match &self.hi {
            Bnd::PosInf => true,
            Bnd::Fin(v, open) => match v.cmp(&BigRational::zero()) {
                std::cmp::Ordering::Greater => true,
                std::cmp::Ordering::Equal => !*open,
                std::cmp::Ordering::Less => false,
            },
            Bnd::NegInf => false,
        };
        lo_ok && hi_ok
    }

    /// Whether every member is `> 0` (0 itself excluded).
    pub(crate) fn strictly_positive(&self) -> bool {
        !self.is_empty()
            && match &self.lo {
                Bnd::Fin(v, open) => match v.cmp(&BigRational::zero()) {
                    std::cmp::Ordering::Greater => true,
                    std::cmp::Ordering::Equal => *open,
                    std::cmp::Ordering::Less => false,
                },
                _ => false,
            }
    }

    /// Whether every member is `< 0` (0 itself excluded).
    pub(crate) fn strictly_negative(&self) -> bool {
        !self.is_empty()
            && match &self.hi {
                Bnd::Fin(v, open) => match v.cmp(&BigRational::zero()) {
                    std::cmp::Ordering::Less => true,
                    std::cmp::Ordering::Equal => *open,
                    std::cmp::Ordering::Greater => false,
                },
                _ => false,
            }
    }

    /// Total endpoint bit-size — the work-meter cost driver for this
    /// interval's arithmetic.
    pub(crate) fn bits(&self) -> u64 {
        self.lo.bits() + self.hi.bits()
    }

    pub(crate) fn add(&self, other: &Self, meter: &mut WorkMeter<'_>) -> Result<Self, String> {
        meter.charge_ops(2 + (self.bits() + other.bits()) / 64)?;
        if self.is_empty() || other.is_empty() {
            return Ok(Self::empty());
        }
        let lo = match (&self.lo, &other.lo) {
            (Bnd::NegInf, _) | (_, Bnd::NegInf) => Bnd::NegInf,
            (Bnd::Fin(a, ao), Bnd::Fin(b, bo)) => Bnd::Fin(a + b, *ao || *bo),
            _ => return Err("internal interval invariant (lo)".to_string()),
        };
        let hi = match (&self.hi, &other.hi) {
            (Bnd::PosInf, _) | (_, Bnd::PosInf) => Bnd::PosInf,
            (Bnd::Fin(a, ao), Bnd::Fin(b, bo)) => Bnd::Fin(a + b, *ao || *bo),
            _ => return Err("internal interval invariant (hi)".to_string()),
        };
        Ok(Self { lo, hi })
    }

    pub(crate) fn neg(&self) -> Self {
        if self.is_empty() {
            return Self::empty();
        }
        let lo = match &self.hi {
            Bnd::PosInf => Bnd::NegInf,
            Bnd::Fin(v, o) => Bnd::Fin(-v, *o),
            Bnd::NegInf => Bnd::PosInf,
        };
        let hi = match &self.lo {
            Bnd::NegInf => Bnd::PosInf,
            Bnd::Fin(v, o) => Bnd::Fin(-v, *o),
            Bnd::PosInf => Bnd::NegInf,
        };
        Self { lo, hi }
    }

    /// Whether the interval attains the value 0 (0 is a member).
    fn attains_zero(&self) -> bool {
        self.contains_zero()
    }

    /// Interval multiplication with exact endpoint-openness accounting.
    ///
    /// Hull: min/max over the four endpoint-pair candidates with the sound
    /// `0 * inf = 0` corner convention. Openness: a finite nonzero extremum
    /// is attained iff some tying corner pair has both endpoints attained
    /// (bilinear extrema over a box occur at corners); the extremum 0 is
    /// additionally attained whenever EITHER factor attains 0 (0 times any
    /// member is 0). When uncertain the endpoint is CLOSED — enlarging the
    /// set is always sound.
    pub(crate) fn mul(&self, other: &Self, meter: &mut WorkMeter<'_>) -> Result<Self, String> {
        // Four endpoint products, each costing (and possibly gcd-reducing)
        // operand-bit-proportional work.
        meter.charge_ops(8 + (self.bits() + other.bits()) / 16)?;
        if self.is_empty() || other.is_empty() {
            return Ok(Self::empty());
        }
        #[derive(Clone, Debug, PartialEq, Eq)]
        enum Val {
            NegInf,
            Fin(BigRational),
            PosInf,
        }
        fn cmp_val(a: &Val, b: &Val) -> std::cmp::Ordering {
            use std::cmp::Ordering::{Equal, Greater, Less};
            match (a, b) {
                (Val::NegInf, Val::NegInf) | (Val::PosInf, Val::PosInf) => Equal,
                (Val::NegInf, _) | (_, Val::PosInf) => Less,
                (_, Val::NegInf) | (Val::PosInf, _) => Greater,
                (Val::Fin(x), Val::Fin(y)) => x.cmp(y),
            }
        }
        // (value, attained-by-this-pair)
        fn pair(x: &Bnd, y: &Bnd) -> (Val, bool) {
            match (x, y) {
                (Bnd::Fin(a, ao), Bnd::Fin(b, bo)) => (Val::Fin(a * b), !*ao && !*bo),
                (Bnd::Fin(a, _), Bnd::PosInf) | (Bnd::PosInf, Bnd::Fin(a, _)) => {
                    match a.cmp(&BigRational::zero()) {
                        std::cmp::Ordering::Greater => (Val::PosInf, false),
                        std::cmp::Ordering::Less => (Val::NegInf, false),
                        std::cmp::Ordering::Equal => (Val::Fin(BigRational::zero()), false),
                    }
                }
                (Bnd::Fin(a, _), Bnd::NegInf) | (Bnd::NegInf, Bnd::Fin(a, _)) => {
                    match a.cmp(&BigRational::zero()) {
                        std::cmp::Ordering::Greater => (Val::NegInf, false),
                        std::cmp::Ordering::Less => (Val::PosInf, false),
                        std::cmp::Ordering::Equal => (Val::Fin(BigRational::zero()), false),
                    }
                }
                (Bnd::PosInf, Bnd::PosInf) | (Bnd::NegInf, Bnd::NegInf) => (Val::PosInf, false),
                (Bnd::PosInf, Bnd::NegInf) | (Bnd::NegInf, Bnd::PosInf) => (Val::NegInf, false),
            }
        }
        let cands = [
            pair(&self.lo, &other.lo),
            pair(&self.lo, &other.hi),
            pair(&self.hi, &other.lo),
            pair(&self.hi, &other.hi),
        ];
        let mut lo_val = cands[0].0.clone();
        let mut hi_val = cands[0].0.clone();
        for (v, _) in &cands[1..] {
            if cmp_val(v, &lo_val) == std::cmp::Ordering::Less {
                lo_val = v.clone();
            }
            if cmp_val(v, &hi_val) == std::cmp::Ordering::Greater {
                hi_val = v.clone();
            }
        }
        let zero_attained = self.attains_zero() || other.attains_zero();
        let attained = |target: &Val| -> bool {
            let corner = cands
                .iter()
                .any(|(v, att)| *att && cmp_val(v, target) == std::cmp::Ordering::Equal);
            let via_zero = matches!(target, Val::Fin(z) if z.is_zero()) && zero_attained;
            corner || via_zero
        };
        let lo = match &lo_val {
            Val::NegInf => Bnd::NegInf,
            Val::PosInf => return Err("internal interval invariant (mul lo)".to_string()),
            Val::Fin(v) => Bnd::Fin(v.clone(), !attained(&lo_val)),
        };
        let hi = match &hi_val {
            Val::PosInf => Bnd::PosInf,
            Val::NegInf => return Err("internal interval invariant (mul hi)".to_string()),
            Val::Fin(v) => Bnd::Fin(v.clone(), !attained(&hi_val)),
        };
        Ok(Self { lo, hi })
    }

    /// Multiply by a nonzero rational scalar (openness preserved, ends
    /// swapped for negative scalars).
    pub(crate) fn scale(&self, c: &BigRational, meter: &mut WorkMeter<'_>) -> Result<Self, String> {
        meter.charge_ops(2 + (self.bits() + rat_bits(c)) / 32)?;
        if self.is_empty() {
            return Ok(Self::empty());
        }
        if c.is_zero() {
            return Ok(Self::point(BigRational::zero()));
        }
        let map = |b: &Bnd| -> Bnd {
            match b {
                Bnd::NegInf => Bnd::NegInf,
                Bnd::PosInf => Bnd::PosInf,
                Bnd::Fin(v, o) => Bnd::Fin(v * c, *o),
            }
        };
        if c.is_positive() {
            Ok(Self {
                lo: map(&self.lo),
                hi: map(&self.hi),
            })
        } else {
            // Negative scalar: ends swap AND infinities flip side.
            let (lo, hi) = (map(&self.hi), map(&self.lo));
            let lo = match lo {
                Bnd::PosInf => Bnd::NegInf,
                other => other,
            };
            let hi = match hi {
                Bnd::NegInf => Bnd::PosInf,
                other => other,
            };
            Ok(Self { lo, hi })
        }
    }

    /// Raise to a nonnegative integer power (exact; even powers fold across
    /// zero with the 0-attained special case).
    pub(crate) fn pow(&self, k: u32, meter: &mut WorkMeter<'_>) -> Result<Self, String> {
        // A k-th power multiplies endpoint bit-sizes by k.
        meter.charge_ops(u64::from(k).max(1) + self.bits() * u64::from(k) / 32)?;
        if self.is_empty() {
            return Ok(Self::empty());
        }
        if k == 0 {
            return Ok(Self::point(BigRational::one()));
        }
        if k == 1 {
            return Ok(self.clone());
        }
        let pow_bnd = |b: &Bnd| -> Bnd {
            match b {
                Bnd::NegInf => Bnd::NegInf,
                Bnd::PosInf => Bnd::PosInf,
                Bnd::Fin(v, o) => Bnd::Fin(rat_pow(v, k), *o),
            }
        };
        if k % 2 == 1 {
            // Odd: strictly monotone over all of R.
            return Ok(Self {
                lo: pow_bnd(&self.lo),
                hi: pow_bnd(&self.hi),
            });
        }
        // Even power. Magnitude bound of an endpoint, as a candidate hi.
        let mag = |b: &Bnd| -> Bnd {
            match b {
                Bnd::NegInf | Bnd::PosInf => Bnd::PosInf,
                Bnd::Fin(v, o) => Bnd::Fin(rat_pow(&v.abs(), k), *o),
            }
        };
        let (mlo, mhi) = (mag(&self.lo), mag(&self.hi));
        let hi = match cmp_bnd_val(&mlo, &mhi) {
            std::cmp::Ordering::Greater => mlo.clone(),
            std::cmp::Ordering::Less => mhi.clone(),
            std::cmp::Ordering::Equal => match (&mlo, &mhi) {
                // Tie: the max is attained iff either endpoint is attained.
                (Bnd::Fin(v, o1), Bnd::Fin(_, o2)) => Bnd::Fin(v.clone(), *o1 && *o2),
                _ => Bnd::PosInf,
            },
        };
        if self.attains_zero() {
            return Ok(Self {
                lo: Bnd::closed(BigRational::zero()),
                hi,
            });
        }
        // Zero not attained: the interval is entirely on one side of 0
        // (possibly with an open 0 endpoint).
        let entirely_nonneg = match &self.lo {
            Bnd::Fin(v, _) => !v.is_negative(),
            _ => false,
        };
        if entirely_nonneg {
            Ok(Self {
                lo: pow_bnd(&self.lo),
                hi,
            })
        } else {
            // Entirely nonpositive: x^k decreasing; lo comes from hi.
            let lo = match &self.hi {
                Bnd::Fin(v, o) => Bnd::Fin(rat_pow(&v.abs(), k), *o),
                _ => return Err("internal interval invariant (pow)".to_string()),
            };
            Ok(Self { lo, hi })
        }
    }

    /// Intersection; on tying endpoint values the OPEN endpoint wins
    /// (intersection is the tighter set).
    pub(crate) fn intersect(&self, other: &Self) -> Self {
        let lo = match cmp_bnd_val(&self.lo, &other.lo) {
            std::cmp::Ordering::Greater => self.lo.clone(),
            std::cmp::Ordering::Less => other.lo.clone(),
            std::cmp::Ordering::Equal => match (&self.lo, &other.lo) {
                (Bnd::Fin(v, o1), Bnd::Fin(_, o2)) => Bnd::Fin(v.clone(), *o1 || *o2),
                (a, _) => a.clone(),
            },
        };
        let hi = match cmp_bnd_val(&self.hi, &other.hi) {
            std::cmp::Ordering::Less => self.hi.clone(),
            std::cmp::Ordering::Greater => other.hi.clone(),
            std::cmp::Ordering::Equal => match (&self.hi, &other.hi) {
                (Bnd::Fin(v, o1), Bnd::Fin(_, o2)) => Bnd::Fin(v.clone(), *o1 || *o2),
                (a, _) => a.clone(),
            },
        };
        Self { lo, hi }
    }

    /// Reciprocal of a sign-definite interval (0 not a member); `None` when
    /// 0 is a member (division would be undefined — caller skips, sound).
    pub(crate) fn inv(&self, meter: &mut WorkMeter<'_>) -> Result<Option<Self>, String> {
        meter.charge_ops(2 + self.bits() / 32)?;
        if self.is_empty() || self.contains_zero() {
            return Ok(None);
        }
        if self.strictly_positive() {
            let lo = match &self.hi {
                Bnd::PosInf => Bnd::open(BigRational::zero()),
                Bnd::Fin(v, o) => {
                    if v.is_zero() {
                        return Ok(None);
                    }
                    Bnd::Fin(BigRational::one() / v, *o)
                }
                Bnd::NegInf => return Ok(None),
            };
            let hi = match &self.lo {
                Bnd::Fin(v, o) => {
                    if v.is_zero() {
                        if *o {
                            Bnd::PosInf
                        } else {
                            return Ok(None);
                        }
                    } else {
                        Bnd::Fin(BigRational::one() / v, *o)
                    }
                }
                _ => return Ok(None),
            };
            return Ok(Some(Self { lo, hi }));
        }
        if self.strictly_negative() {
            let pos = self.neg();
            let inv_pos = pos.inv(meter)?;
            return Ok(inv_pos.map(|iv| iv.neg()));
        }
        Ok(None)
    }
}

/// Exact rational power by BigInt exponentiation of numerator/denominator.
pub(crate) fn rat_pow(v: &BigRational, k: u32) -> BigRational {
    if k == 0 {
        return BigRational::one();
    }
    if k == 1 {
        return v.clone();
    }
    let n: BigInt = Pow::pow(v.numer(), k);
    let d: BigInt = Pow::pow(v.denom(), k);
    // Denominator of a reduced rational is nonzero; its power is nonzero.
    BigRational::new(n, d)
}

// ============================================================================
// Outward rational k-th roots
// ============================================================================

/// `floor(n^(1/k))` for `n >= 0`, by binary search (no external deps).
fn bigint_nth_root_floor(n: &BigInt, k: u32) -> BigInt {
    if n.is_zero() || n.is_one() || k == 1 {
        return n.clone();
    }
    let bits = n.bits();
    let mut hi: BigInt = BigInt::one() << (bits / u64::from(k) + 2);
    let mut lo = BigInt::zero();
    // Invariant: lo^k <= n < hi^k.
    while &lo + 1u32 < hi {
        let mid: BigInt = (&lo + &hi) >> 1;
        if Pow::pow(&mid, k) <= *n {
            lo = mid;
        } else {
            hi = mid;
        }
    }
    lo
}

/// Outward rational bounds `(lower, upper, exact)` for `q^(1/k)` with
/// `q >= 0`: `lower <= q^(1/k) <= upper`, and `exact` when
/// `lower == upper == q^(1/k)` is exactly rational.
pub(crate) fn rat_nth_root_bounds(
    q: &BigRational,
    k: u32,
    meter: &mut WorkMeter<'_>,
) -> Result<(BigRational, BigRational, bool), String> {
    if q.is_negative() {
        return Err("nth root of negative".to_string());
    }
    if k == 0 {
        return Err("zeroth root".to_string());
    }
    let a = q.numer().clone();
    let b = q.denom().clone();
    // Cost guard: b^(k-1) can be large; charge by bit growth.
    let bit_cost = (a.bits() + b.bits()).saturating_mul(u64::from(k)) / 32 + 1;
    meter.charge_ops(bit_cost)?;
    // q^(1/k) = (a * b^(k-1))^(1/k) / b.
    let n: BigInt = &a * Pow::pow(&b, k - 1);
    let s = bigint_nth_root_floor(&n, k);
    let exact = Pow::pow(&s, k) == n;
    let lower = BigRational::new(s.clone(), b.clone());
    let upper = if exact {
        lower.clone()
    } else {
        BigRational::new(s + 1u32, b)
    };
    Ok((lower, upper, exact))
}

#[cfg(test)]
mod resource_regression_tests {
    use super::*;

    fn int_equality(terms: &mut TermStore, name: &str) -> TermId {
        let variable = terms.mk_var(name, Sort::Int);
        let zero = terms.mk_int(0.into());
        terms.mk_eq(variable, zero)
    }

    #[test]
    fn normal_nested_conjunction_extracts_all_constraints() {
        let mut terms = TermStore::new();
        let a = int_equality(&mut terms, "nested_a");
        let b = int_equality(&mut terms, "nested_b");
        let c = int_equality(&mut terms, "nested_c");
        let inner = terms.mk_app(Symbol::named("and"), vec![a, b], Sort::Bool);
        let outer = terms.mk_app(Symbol::named("and"), vec![inner, c], Sort::Bool);
        let not_outer = terms.mk_not_raw(outer);
        let mut meter = WorkMeter::new();
        let extraction = extract_constraints(&terms, &[not_outer], &mut meter)
            .expect("ordinary nested conjunction must remain supported");
        assert_eq!(extraction.constraints.len(), 3);
    }

    /// Build a shared N-by-N Boolean spine directly in the term store. The
    /// second fanout must be charged before it can be appended, so rejection
    /// occurs with only the first wide layer resident in `pending` rather than
    /// after materializing the full shared expansion.
    #[test]
    fn shared_wide_nested_conjunction_refuses_before_queue_expansion() {
        const WIDTH: usize = 400;
        let mut terms = TermStore::new();
        let atom = int_equality(&mut terms, "shared_wide_atom");
        let shared = terms.mk_app(Symbol::named("and"), vec![atom; WIDTH], Sort::Bool);
        let outer = terms.mk_app(Symbol::named("and"), vec![shared; WIDTH], Sort::Bool);
        let not_outer = terms.mk_not_raw(outer);
        let mut meter = WorkMeter::new();
        meter.nodes_remaining = 1_000;
        let error = match extract_constraints(&terms, &[not_outer], &mut meter) {
            Err(error) => error,
            Ok(_) => panic!("N-by-N pending expansion must hit the pre-enqueue node cap"),
        };
        assert!(error.contains("DAG node meter"), "{error}");
    }

    #[test]
    fn scratch_refusal_precedes_occupied_coefficient_addition() {
        let mut terms = TermStore::new();
        let variable = terms.mk_var("scratch_order_x", Sort::Int);
        let mut left = MPoly::var(variable);
        let right = left.clone();
        let before = left.clone();
        let one = BigRational::one();
        let scratch = generic_rational_scratch_bytes(binary_rational_transient_bits(&one, &one))
            .expect("tiny rational scratch bound fits usize");
        let mut refused = false;
        let mut progress = |work: usize, bytes: usize| {
            if (work, bytes) == (0, scratch) {
                refused = true;
                return false;
            }
            true
        };
        let mut meter = WorkMeter::with_progress(&mut progress);

        let error = left
            .add_assign_from(&right, &mut meter)
            .expect_err("caller refusal must stop before exact addition");
        assert_eq!(error, WORK_METER_RESOURCE_LIMIT);
        assert!(refused, "fixture must reach the scratch precharge");
        assert_eq!(left, before, "coefficient changed before scratch approval");
    }

    /// The n-ary accumulator must touch each existing coefficient only when
    /// the current addend shares its monomial. A whole-result scan per addend
    /// makes this 8k-wide source quadratic even though the published work
    /// meter describes a linear fold.
    #[test]
    fn wide_nary_addition_accumulates_with_linear_accounting() {
        const WIDTH: usize = 8_192;
        let mut terms = TermStore::new();
        let args: Vec<TermId> = (0..WIDTH)
            .map(|i| terms.mk_var(format!("wide_nary_{i}"), Sort::Int))
            .collect();
        let sum = terms.mk_add(args);
        let mut memo = BTreeMap::new();
        let mut meter = WorkMeter::new();
        let poly = parse_poly(&terms, sum, &mut memo, &mut meter, 0)
            .expect("a wide linear sum must stay inside the linear work envelope");
        assert_eq!(poly.terms.len(), WIDTH, "every distinct addend survives");
        assert!(
            meter.ops_remaining > MAX_BIGRATIONAL_OPS / 2,
            "fixture must leave ample work headroom, got {}",
            meter.ops_remaining
        );
    }
}
