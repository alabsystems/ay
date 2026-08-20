// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Strict semantic validation for `Generic` theory lemmas whose refutation
//! needs ORDER reasoning: exact-rational Fourier–Motzkin elimination over the
//! negated clause, with every distinct MONOMIAL abstracted to an independent
//! variable.
//!
//! # The obligation
//!
//! [`super::nia_linear_ideal`] decides ONE shape: a disequality polynomial
//! lying in the rational SPAN of the equality polynomials. That settles
//! arithmetic-IDENTITY lemmas (loop-invariant consecution) and nothing else —
//! it deliberately ignores every `<`/`<=` conjunct. The `Generic` lemmas that
//! survive are dominated by ORDER conflicts: length/index side conditions from
//! the string and set theories, antisymmetry (`x <= y`, `y <= x`, `x != y`),
//! transitivity chains, and bound contradictions after scaling.
//!
//! # The decision
//!
//! Normalize the NEGATION of the clause into polynomial sign constraints (the
//! shared, fail-closed [`extract_constraints`]). Assign every distinct
//! non-constant MONOMIAL its own coordinate, so each constraint becomes a
//! LINEAR form `sum_j a_j * v_j + c` compared against zero. Then run
//! Fourier–Motzkin elimination over the rationals with strictness tracking. The
//! lemma is accepted exactly when the elimination derives a variable-free row
//! that its own relation refutes (`c <= 0` with `c > 0`, or `c < 0` with
//! `c >= 0`).
//!
//! Disequalities (`p != 0`) are handled by a BOUNDED case split: `p < 0` or
//! `p > 0`. Every branch must be infeasible.
//!
//! # Why this is sound
//!
//! Three independent claims, each in the safe direction.
//!
//! 1. MONOMIAL ABSTRACTION IS A RELAXATION. Any assignment `sigma` to the
//!    original terms induces an assignment to the coordinates (evaluate each
//!    monomial). By construction the linear form evaluates to exactly the same
//!    rational as the polynomial did, so a model of the original conjunction
//!    yields a model of the linear system. Contrapositive: refuting the linear
//!    system refutes the original. Nothing here uses `x * x >= 0`, or that
//!    `x * y` and `y * x` denote one product, or integrality — the abstraction
//!    is strictly WEAKER than nonlinear reasoning, which is the direction that
//!    cannot fabricate a proof.
//! 2. FOURIER–MOTZKIN OVER Q PROVES REAL INFEASIBILITY. One elimination step
//!    takes `a*t + P REL 0` with `a > 0` and `b*t + N REL 0` with `b < 0`,
//!    scales them by the POSITIVE rationals `1/a` and `-1/b` (which preserves
//!    both the direction and the strictness of a relation) and adds. Summing
//!    two facts of the form `X <= 0` gives `X <= 0`; if either summand is
//!    `< 0`, so is the sum. Every derived row is therefore a logical
//!    CONSEQUENCE of the two it came from, so a refuted derived row refutes the
//!    original system. Int-sorted terms are relaxed to R exactly as elsewhere
//!    in this kernel: R-infeasible implies Z-infeasible, never the converse
//!    (`x > 0 AND x < 1` is Z-infeasible and must NOT be reported infeasible
//!    here — the test suite pins that).
//! 3. DROPPING CONJUNCTS IS CONSERVATIVE. Beyond the disequality-split cap the
//!    surplus disequalities are dropped rather than split. Refuting a SUBSET of
//!    a conjunction refutes the conjunction, so this can only lose acceptances.
//!
//! The one non-error "no" answer — elimination completing with no refuted row —
//! means the relaxation genuinely has a rational model, and is reported as a
//! refusal. Every cap trip is likewise a refusal. There is no path on which an
//! exhausted budget, an unmodelled shape, or an arithmetic surprise ACCEPTS.
//!
//! There is no payload to forge: the checker re-derives the elimination itself.

use std::collections::{btree_map::Entry, BTreeMap, BTreeSet};
use std::mem::size_of;

use ay_core::TermId;
use num_rational::BigRational;
use num_traits::{Signed, Zero};

use super::nra_poly::{
    bit_scaled, ensure_coeff_width, generic_container_slot_bytes, rat_bits, Constraint, MPoly,
    Monomial, Rel, WorkMeter, MAX_POLY_COEFF_BITS, WORK_METER_RESOURCE_LIMIT,
};

// Production callers reach this lane through
// `nia_linear_ideal::validate_generic_arithmetic_refutation_with_progress`,
// which owns the extraction. These names exist so the unit tests can exercise
// the order lane in isolation, from a raw clause.
#[cfg(test)]
use super::nra_poly::extract_constraints;
#[cfg(test)]
use super::ProofCheckError;
#[cfg(test)]
use ay_core::{ProofId, TermStore};

/// Maximum distinct monomials admitted as elimination coordinates. Each round
/// removes one, so this also bounds the number of rounds.
const MAX_FM_VARIABLES: usize = 48;
/// Maximum rows alive at any point (Fourier–Motzkin is doubly exponential in
/// the worst case; this is the primary structural brake). It also bounds one
/// round's pair count, so at most `MAX_FM_ROWS * MAX_FM_VARIABLES` combinations
/// can be produced per branch.
const MAX_FM_ROWS: usize = 512;
/// Cumulative pair combinations across every round of every branch.
const MAX_FM_COMBINATIONS: u64 = 30_000;
/// Cumulative rows materialized across every round of every branch.
const MAX_FM_MATERIALIZED_ROWS: u64 = 200_000;
/// Maximum disequalities admitted to the case split (`2^k` branches). Surplus
/// disequalities are DROPPED, which is conservative — see the module note.
const MAX_NE_CASE_SPLIT: usize = 3;

/// One normalized linear row: `sum_j coeffs[j] * v_j + constant REL 0`, where
/// `REL` is `<` when `strict` and `<=` otherwise.
///
/// Invariant: `coeffs` never stores a zero coefficient, so `coeffs.is_empty()`
/// is exactly "this row is variable-free".
#[derive(Clone, Debug)]
struct Row {
    coeffs: BTreeMap<usize, BigRational>,
    constant: BigRational,
    strict: bool,
}

impl Row {
    fn is_variable_free(&self) -> bool {
        self.coeffs.is_empty()
    }

    /// Whether a variable-free row refutes itself.
    ///
    /// `c <= 0` is false exactly when `c > 0`; `c < 0` is false exactly when
    /// `c >= 0`. A row that still mentions a variable is never a refutation.
    fn is_refuted(&self) -> bool {
        self.coeffs.is_empty()
            && if self.strict {
                !self.constant.is_negative()
            } else {
                self.constant.is_positive()
            }
    }
}

/// Cumulative finite envelope for the elimination.
///
/// Every counter uses checked arithmetic and every cap trip is a refusal,
/// never an acceptance. The shared [`WorkMeter`] additionally charges the
/// caller's proof-wide work/byte envelope for each row and each rational
/// operation, so an adversarial lemma cannot spend unbounded work here even
/// while staying under these local caps.
#[derive(Default)]
struct FmBudget {
    combinations: u64,
    materialized_rows: u64,
}

impl FmBudget {
    fn charge_combination(&mut self, meter: &mut WorkMeter<'_>) -> Result<(), String> {
        self.combinations = self
            .combinations
            .checked_add(1)
            .ok_or_else(|| "fourier-motzkin combination accounting overflow".to_string())?;
        if self.combinations > MAX_FM_COMBINATIONS {
            return Err(format!(
                "fourier-motzkin combination cap {MAX_FM_COMBINATIONS} exceeded"
            ));
        }
        meter.charge_ops(1)
    }

    /// Account one materialized row, validating every coefficient width before
    /// it can feed another exact operation.
    fn charge_row(&mut self, row: &Row, meter: &mut WorkMeter<'_>) -> Result<(), String> {
        self.materialized_rows = self
            .materialized_rows
            .checked_add(1)
            .ok_or_else(|| "fourier-motzkin row accounting overflow".to_string())?;
        if self.materialized_rows > MAX_FM_MATERIALIZED_ROWS {
            return Err(format!(
                "fourier-motzkin materialized-row cap {MAX_FM_MATERIALIZED_ROWS} exceeded"
            ));
        }
        ensure_coeff_width(&row.constant)?;
        let mut bits = rat_bits(&row.constant);
        for (index, coeff) in row.coeffs.values().enumerate() {
            meter.poll_loop(index)?;
            ensure_coeff_width(coeff)?;
            bits = bits.max(rat_bits(coeff));
        }
        let width = u64::try_from(row.coeffs.len().saturating_add(1))
            .map_err(|_| WORK_METER_RESOURCE_LIMIT.to_string())?;
        meter.charge_ops(bit_scaled(width, bits))?;
        meter.charge_private_allocation(0, row_bytes(row)?)
    }
}

/// Deterministic logical byte accounting for one row: a full-width coefficient
/// per entry plus conservative tree-node overhead.
fn row_bytes(row: &Row) -> Result<usize, String> {
    let entries = row
        .coeffs
        .len()
        .checked_add(1)
        .ok_or_else(|| "fourier-motzkin row byte accounting overflow".to_string())?;
    let per_entry = size_of::<(usize, BigRational)>()
        .checked_add((MAX_POLY_COEFF_BITS as usize).div_ceil(8))
        .and_then(|bytes| bytes.checked_add(64))
        .ok_or_else(|| "fourier-motzkin row byte accounting overflow".to_string())?;
    entries
        .checked_mul(per_entry)
        .and_then(|bytes| bytes.checked_add(size_of::<Row>()))
        .ok_or_else(|| "fourier-motzkin row byte accounting overflow".to_string())
}

fn push_row(rows: &mut Vec<Row>, row: Row, meter: &mut WorkMeter<'_>) -> Result<(), String> {
    if rows.len() >= MAX_FM_ROWS {
        return Err(format!("fourier-motzkin row cap {MAX_FM_ROWS} exceeded"));
    }
    meter.charge_container_slot::<Row>()?;
    rows.try_reserve(1)
        .map_err(|_| "fourier-motzkin row allocation refused".to_string())?;
    rows.push(row);
    Ok(())
}

/// Assign each distinct non-constant monomial its own coordinate.
///
/// Indices come from the `BTreeSet` order, so they depend only on the monomial
/// keys and never on constraint order or any hash.
fn collect_atoms(
    constraints: &[Constraint],
    meter: &mut WorkMeter<'_>,
) -> Result<BTreeMap<Monomial, usize>, String> {
    let mut monomials: BTreeSet<Monomial> = BTreeSet::new();
    for constraint in constraints {
        meter.poll()?;
        for (index, monomial) in constraint.poly.terms.keys().enumerate() {
            meter.poll_loop(index)?;
            if monomial.is_empty() {
                continue;
            }
            let key_width = u64::try_from(monomial.len().saturating_add(1))
                .map_err(|_| WORK_METER_RESOURCE_LIMIT.to_string())?;
            meter.charge_ops(key_width)?;
            if monomials.contains(monomial) {
                continue;
            }
            if monomials.len() >= MAX_FM_VARIABLES {
                return Err(format!(
                    "fourier-motzkin coordinate cap {MAX_FM_VARIABLES} exceeded"
                ));
            }
            let entry_bytes = monomial
                .len()
                .checked_mul(size_of::<(TermId, u32)>())
                .and_then(|bytes| bytes.checked_add(64))
                .ok_or_else(|| "fourier-motzkin atom byte accounting overflow".to_string())?;
            meter.charge_private_allocation(0, entry_bytes)?;
            monomials.insert(monomial.clone());
        }
    }
    let mut atoms = BTreeMap::new();
    for (index, monomial) in monomials.into_iter().enumerate() {
        meter.poll_loop(index)?;
        meter.charge_private_allocation(0, generic_container_slot_bytes::<usize>()?)?;
        atoms.insert(monomial, index);
    }
    Ok(atoms)
}

/// Build `poly REL 0` (or `-poly REL 0` when `negate`) as a linear row over the
/// coordinate table.
fn row_from_poly(
    poly: &MPoly,
    negate: bool,
    strict: bool,
    atoms: &BTreeMap<Monomial, usize>,
    meter: &mut WorkMeter<'_>,
) -> Result<Row, String> {
    let mut coeffs: BTreeMap<usize, BigRational> = BTreeMap::new();
    let mut constant = BigRational::zero();
    for (index, (monomial, coeff)) in poly.terms.iter().enumerate() {
        meter.poll_loop(index)?;
        ensure_coeff_width(coeff)?;
        meter.charge_ops(bit_scaled(1, rat_bits(coeff)))?;
        meter.charge_rational_scratch(rat_bits(coeff).saturating_add(1))?;
        let value = if negate { -coeff } else { coeff.clone() };
        ensure_coeff_width(&value)?;
        if value.is_zero() {
            // `MPoly` prunes zero coefficients; keep the row invariant anyway.
            continue;
        }
        if monomial.is_empty() {
            constant = value;
            continue;
        }
        let Some(&slot) = atoms.get(monomial) else {
            return Err("fourier-motzkin monomial missing from the coordinate table".to_string());
        };
        meter.charge_container_slot::<(usize, BigRational)>()?;
        if coeffs.insert(slot, value).is_some() {
            return Err("duplicate monomial in a normalized polynomial".to_string());
        }
    }
    Ok(Row {
        coeffs,
        constant,
        strict,
    })
}

/// Pick the coordinate whose elimination produces the fewest rows.
///
/// Ties break to the smallest index, so the choice is a pure function of the
/// row set. A coordinate with no negative (or no positive) occurrence has cost
/// zero and is eliminated by simply dropping its rows — that is the sound
/// unbounded-direction case, not a shortcut.
fn choose_coordinate(rows: &[Row], meter: &mut WorkMeter<'_>) -> Result<Option<usize>, String> {
    let mut counts: BTreeMap<usize, (u64, u64)> = BTreeMap::new();
    for (index, row) in rows.iter().enumerate() {
        meter.poll_loop(index)?;
        for (slot, coeff) in &row.coeffs {
            meter.charge_ops(1)?;
            meter.charge_private_allocation(0, generic_container_slot_bytes::<(u64, u64)>()?)?;
            let entry = counts.entry(*slot).or_insert((0, 0));
            if coeff.is_positive() {
                entry.0 = entry.0.saturating_add(1);
            } else {
                entry.1 = entry.1.saturating_add(1);
            }
        }
    }
    let mut best: Option<(u64, usize)> = None;
    for (slot, (positive, negative)) in counts {
        meter.charge_ops(1)?;
        let cost = positive.saturating_mul(negative);
        if best.is_none_or(|(best_cost, _)| cost < best_cost) {
            best = Some((cost, slot));
        }
    }
    Ok(best.map(|(_, slot)| slot))
}

/// Eliminate `target` from the pair, producing their positive combination.
///
/// `positive` is `a*t + P REL 0` with `a > 0`; `negative` is `b*t + N REL 0`
/// with `b < 0`. Scaling by `1/a > 0` and `-1/b > 0` preserves direction and
/// strictness and makes the two `t` coefficients `+1` and `-1`, so their sum is
/// `t`-free:
///
/// ```text
///   P/a + N/(-b)  REL  0,   strict iff EITHER input was strict
/// ```
///
/// Nothing else about the two rows is used, so the result holds under every
/// assignment satisfying both — this is the step whose strictness rule decides
/// whether the validator can fabricate a proof, and it is the ONLY place a
/// strict flag is introduced.
fn combine(
    positive: &Row,
    negative: &Row,
    target: usize,
    meter: &mut WorkMeter<'_>,
    budget: &mut FmBudget,
) -> Result<Row, String> {
    let pivot_positive = positive
        .coeffs
        .get(&target)
        .ok_or_else(|| "fourier-motzkin positive pivot vanished".to_string())?;
    let pivot_negative = negative
        .coeffs
        .get(&target)
        .ok_or_else(|| "fourier-motzkin negative pivot vanished".to_string())?;
    if !pivot_positive.is_positive() || !pivot_negative.is_negative() {
        return Err("fourier-motzkin pivot sign invariant violated".to_string());
    }
    ensure_coeff_width(pivot_positive)?;
    ensure_coeff_width(pivot_negative)?;
    meter.charge_ops(bit_scaled(
        2,
        rat_bits(pivot_positive).max(rat_bits(pivot_negative)),
    ))?;
    meter.charge_rational_scratch(rat_bits(pivot_positive).saturating_add(1))?;
    let positive_factor = pivot_positive.recip();
    ensure_coeff_width(&positive_factor)?;
    meter.charge_rational_scratch(rat_bits(pivot_negative).saturating_add(2))?;
    let negative_factor = -pivot_negative.recip();
    ensure_coeff_width(&negative_factor)?;
    // Both multipliers MUST be strictly positive; a negative one would flip a
    // relation and could manufacture a contradiction out of a satisfiable
    // system. Re-check rather than assume.
    if !positive_factor.is_positive() || !negative_factor.is_positive() {
        return Err("fourier-motzkin scaling factor is not strictly positive".to_string());
    }

    let mut coeffs: BTreeMap<usize, BigRational> = BTreeMap::new();
    accumulate(&mut coeffs, positive, &positive_factor, target, meter)?;
    accumulate(&mut coeffs, negative, &negative_factor, target, meter)?;

    ensure_coeff_width(&positive.constant)?;
    ensure_coeff_width(&negative.constant)?;
    meter.charge_rational_scratch(
        rat_bits(&positive.constant).saturating_add(rat_bits(&positive_factor)),
    )?;
    let left = &positive.constant * &positive_factor;
    ensure_coeff_width(&left)?;
    meter.charge_rational_scratch(
        rat_bits(&negative.constant).saturating_add(rat_bits(&negative_factor)),
    )?;
    let right = &negative.constant * &negative_factor;
    ensure_coeff_width(&right)?;
    meter.charge_rational_scratch(
        rat_bits(&left)
            .saturating_add(rat_bits(&right))
            .saturating_add(1),
    )?;
    let constant = left + right;
    ensure_coeff_width(&constant)?;

    let row = Row {
        coeffs,
        constant,
        // A strict premise makes the consequence strict; two non-strict
        // premises can only yield a non-strict consequence.
        strict: positive.strict || negative.strict,
    };
    budget.charge_row(&row, meter)?;
    Ok(row)
}

/// Add `factor * row` into `out`, skipping the eliminated coordinate.
fn accumulate(
    out: &mut BTreeMap<usize, BigRational>,
    row: &Row,
    factor: &BigRational,
    target: usize,
    meter: &mut WorkMeter<'_>,
) -> Result<(), String> {
    for (index, (slot, coeff)) in row.coeffs.iter().enumerate() {
        meter.poll_loop(index)?;
        if *slot == target {
            continue;
        }
        ensure_coeff_width(coeff)?;
        meter.charge_ops(bit_scaled(2, rat_bits(coeff).max(rat_bits(factor))))?;
        meter.charge_rational_scratch(rat_bits(coeff).saturating_add(rat_bits(factor)))?;
        let scaled = coeff * factor;
        ensure_coeff_width(&scaled)?;
        match out.entry(*slot) {
            Entry::Vacant(vacant) => {
                if !scaled.is_zero() {
                    meter.charge_container_slot::<(usize, BigRational)>()?;
                    vacant.insert(scaled);
                }
            }
            Entry::Occupied(mut occupied) => {
                meter.charge_rational_scratch(
                    rat_bits(occupied.get())
                        .saturating_add(rat_bits(&scaled))
                        .saturating_add(1),
                )?;
                let sum = occupied.get() + &scaled;
                ensure_coeff_width(&sum)?;
                if sum.is_zero() {
                    occupied.remove();
                } else {
                    *occupied.get_mut() = sum;
                }
            }
        }
    }
    Ok(())
}

/// Eliminate `target` from every row, returning the next round's row set.
fn eliminate_coordinate(
    rows: Vec<Row>,
    target: usize,
    meter: &mut WorkMeter<'_>,
    budget: &mut FmBudget,
) -> Result<Vec<Row>, String> {
    let mut positive: Vec<Row> = Vec::new();
    let mut negative: Vec<Row> = Vec::new();
    let mut next: Vec<Row> = Vec::new();
    for (index, row) in rows.into_iter().enumerate() {
        meter.poll_loop(index)?;
        match row.coeffs.get(&target).map(|coeff| coeff.is_positive()) {
            None => push_row(&mut next, row, meter)?,
            Some(true) => push_row(&mut positive, row, meter)?,
            Some(false) => push_row(&mut negative, row, meter)?,
        }
    }

    // Refuse the round before materializing an oversized product.
    let projected = next
        .len()
        .checked_add(positive.len().saturating_mul(negative.len()))
        .ok_or_else(|| "fourier-motzkin row projection overflow".to_string())?;
    if projected > MAX_FM_ROWS {
        return Err(format!("fourier-motzkin row cap {MAX_FM_ROWS} exceeded"));
    }

    let mut pair_index = 0_usize;
    for upper in &positive {
        for lower in &negative {
            meter.poll_loop(pair_index)?;
            pair_index = pair_index.saturating_add(1);
            budget.charge_combination(meter)?;
            let combined = combine(upper, lower, target, meter, budget)?;
            if combined.is_variable_free() && !combined.is_refuted() {
                // A satisfied variable-free row carries no information.
                continue;
            }
            push_row(&mut next, combined, meter)?;
        }
    }
    Ok(next)
}

/// Decide whether the linear relaxation is infeasible over the RATIONALS.
///
/// `Ok(true)` — a variable-free row refutes itself, so the system has no
/// rational model and the lemma may be accepted. `Ok(false)` — elimination
/// completed with every remaining row satisfiable, so the relaxation HAS a
/// rational model and the lemma must be refused. `Err` — a cap or the caller's
/// envelope stopped the search, which is likewise a refusal.
fn fourier_motzkin_infeasible(
    mut rows: Vec<Row>,
    meter: &mut WorkMeter<'_>,
    budget: &mut FmBudget,
) -> Result<bool, String> {
    // Each round eliminates one coordinate and never reintroduces it, so
    // `MAX_FM_VARIABLES` rounds suffice; the extra iteration performs the final
    // variable-free scan.
    for _round in 0..=MAX_FM_VARIABLES {
        meter.poll()?;
        let mut open: Vec<Row> = Vec::new();
        for (index, row) in rows.drain(..).enumerate() {
            meter.poll_loop(index)?;
            if row.is_variable_free() {
                if row.is_refuted() {
                    return Ok(true);
                }
                continue;
            }
            push_row(&mut open, row, meter)?;
        }
        let Some(target) = choose_coordinate(&open, meter)? else {
            // No coordinate left and nothing refuted: the relaxation is
            // satisfiable. This is the only non-error "no".
            return Ok(false);
        };
        rows = eliminate_coordinate(open, target, meter, budget)?;
    }
    Err("fourier-motzkin round budget exhausted".to_string())
}

/// Decide the ORDER lane for an ALREADY-EXTRACTED negated clause.
///
/// The caller ([`super::nia_linear_ideal`]) owns the single
/// [`extract_constraints`] pass and the single [`WorkMeter`], so this lane adds
/// only its own elimination work to the proof-wide resource envelope. That
/// sharing is not cosmetic: this arm runs on EVERY trust-kind theory lemma of
/// every proof, and a second full clause parse would double the `Generic` arm's
/// charge against the caller's envelope.
///
/// Returns `Ok(())` only when the elimination itself derived the refutation;
/// every other outcome — including "the relaxation has a rational model" and
/// every cap trip — is an error, so the caller keeps its fail-closed behaviour.
pub(crate) fn fourier_motzkin_refutes(
    constraints: &[Constraint],
    meter: &mut WorkMeter<'_>,
) -> Result<(), String> {
    meter.poll()?;
    if constraints.is_empty() {
        return Err("no arithmetic conjunct to refute".to_string());
    }

    let atoms = collect_atoms(constraints, meter)?;
    let mut budget = FmBudget::default();
    let mut base: Vec<Row> = Vec::new();
    let mut disequalities: Vec<&MPoly> = Vec::new();

    for constraint in constraints {
        meter.poll()?;
        // `poly REL 0` becomes one or two rows of the canonical `. <= 0` /
        // `. < 0` form: `>=`/`>` are the negations of `<=`/`<`.
        let rows: &[(bool, bool)] = match constraint.rel {
            Rel::Le => &[(false, false)],
            Rel::Lt => &[(false, true)],
            Rel::Ge => &[(true, false)],
            Rel::Gt => &[(true, true)],
            // `p = 0` is `p <= 0` AND `-p <= 0`.
            Rel::Eq => &[(false, false), (true, false)],
            Rel::Ne => {
                // Bounded case split below. Beyond the cap the surplus
                // disequalities are simply dropped: refuting a SUBSET of the
                // conjunction refutes the conjunction, so this only ever loses
                // acceptances.
                if disequalities.len() < MAX_NE_CASE_SPLIT {
                    meter.charge_container_slot::<&MPoly>()?;
                    disequalities.try_reserve(1).map_err(|_| {
                        "fourier-motzkin disequality allocation refused".to_string()
                    })?;
                    disequalities.push(&constraint.poly);
                }
                &[]
            }
        };
        for &(negate, strict) in rows {
            let row = row_from_poly(&constraint.poly, negate, strict, &atoms, meter)?;
            budget.charge_row(&row, meter)?;
            push_row(&mut base, row, meter)?;
        }
    }

    if base.is_empty() && disequalities.is_empty() {
        return Err("no order or equality conjunct survived normalization".to_string());
    }

    // Every branch of the disequality case split must be infeasible; a single
    // satisfiable branch means the negated clause has a model.
    let branches = 1_usize
        .checked_shl(
            u32::try_from(disequalities.len())
                .map_err(|_| "fourier-motzkin split accounting overflow".to_string())?,
        )
        .ok_or_else(|| "fourier-motzkin split accounting overflow".to_string())?;
    for branch in 0..branches {
        meter.poll()?;
        let mut rows: Vec<Row> = Vec::new();
        for (index, row) in base.iter().enumerate() {
            meter.poll_loop(index)?;
            budget.charge_row(row, meter)?;
            push_row(&mut rows, row.clone(), meter)?;
        }
        for (index, poly) in disequalities.iter().enumerate() {
            meter.poll_loop(index)?;
            // Bit set: take the `p > 0` side (`-p < 0`); clear: the `p < 0`
            // side. Both sides are STRICT — that is what `p != 0` means.
            let negate = (branch >> index) & 1 == 1;
            let row = row_from_poly(poly, negate, true, &atoms, meter)?;
            budget.charge_row(&row, meter)?;
            push_row(&mut rows, row, meter)?;
        }
        if !fourier_motzkin_infeasible(rows, meter, &mut budget)? {
            return Err(format!(
                "the negated clause has a rational model (branch {branch} of \
                 {branches} in the disequality split)"
            ));
        }
    }
    Ok(())
}

/// Test-only harness: extract a raw clause and decide the ORDER lane alone.
///
/// Production goes through the shared entry point in
/// [`super::nia_linear_ideal`]; this exists so the adversarial suite can pin
/// Fourier–Motzkin's own verdicts without the equality-span fast path in front
/// of them.
#[cfg(test)]
fn decide_fourier_motzkin_refutation_with_progress(
    terms: &TermStore,
    clause: &[TermId],
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Result<(), String> {
    let mut meter = WorkMeter::with_progress(progress);
    meter.poll()?;
    let extraction = extract_constraints(terms, clause, &mut meter)?;
    meter.poll()?;
    if extraction.const_refuted {
        return Ok(());
    }
    fourier_motzkin_refutes(&extraction.constraints, &mut meter)
}

#[cfg(test)]
fn decide_fourier_motzkin_refutation(terms: &TermStore, clause: &[TermId]) -> Result<(), String> {
    let mut unbounded = |_: usize, _: usize| true;
    decide_fourier_motzkin_refutation_with_progress(terms, clause, &mut unbounded)
}

#[cfg(test)]
fn validate_fourier_motzkin_refutation_with_progress(
    terms: &TermStore,
    step_id: ProofId,
    clause: &[TermId],
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Result<(), ProofCheckError> {
    decide_fourier_motzkin_refutation_with_progress(terms, clause, progress).map_err(|reason| {
        if reason == WORK_METER_RESOURCE_LIMIT {
            ProofCheckError::ResourceLimit
        } else {
            ProofCheckError::InvalidTheoryLemma {
                step: step_id,
                reason: format!("fourier_motzkin_refutation: {reason}"),
            }
        }
    })
}

#[cfg(test)]
fn validate_fourier_motzkin_refutation(
    terms: &TermStore,
    step_id: ProofId,
    clause: &[TermId],
) -> Result<(), ProofCheckError> {
    let mut unbounded = |_: usize, _: usize| true;
    validate_fourier_motzkin_refutation_with_progress(terms, step_id, clause, &mut unbounded)
}

#[cfg(test)]
#[path = "nia_fourier_motzkin_tests.rs"]
mod tests;
