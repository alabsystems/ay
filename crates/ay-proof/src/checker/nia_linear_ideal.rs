// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Strict semantic validation for arithmetic lemmas whose refutation is a
//! LINEAR COMBINATION OF EQUALITIES over the monomial basis.
//!
//! # The obligation
//!
//! `TheoryLemmaKind::Generic` carries no payload and had no strict validator,
//! so a correctly-computed UNSAT whose refutation used one of these lemmas was
//! refused by mandatory certification and degraded to `unknown`. The dominant
//! shape in practice is a loop-invariant CONSECUTION step: "the invariant holds
//! after the body, given that it held before", e.g.
//!
//! ```smt2
//! (assert (= (+ sum (* counter n)) (* n n)))                       ; invariant
//! (assert (not (= (+ (+ sum n) (* (- counter 1) n)) (* n n))))     ; negated goal
//! ```
//!
//! which is UNSAT but NOT Farkas-refutable as written, because `counter * n`
//! and `n * n` are nonlinear. It is refutable the moment each distinct MONOMIAL
//! is treated as its own basis element: the goal polynomial normalizes to
//! exactly the invariant polynomial, so the two constraints are `P = 0` and
//! `P != 0`.
//!
//! # The decision
//!
//! Normalize the NEGATION of the clause into polynomial sign constraints (the
//! shared, fail-closed [`extract_constraints`]). Then, treating each distinct
//! monomial as an independent coordinate, decide whether some disequality
//! polynomial lies in the RATIONAL LINEAR SPAN of the equality polynomials by
//! Gaussian elimination over exact `BigRational` coefficients.
//!
//! # Why this is sound
//!
//! Suppose the negated clause contains conjuncts `P_1 = 0, …, P_k = 0` and
//! `G != 0`, and `G = sum_i c_i * P_i` as polynomials (an IDENTITY, so it holds
//! under every assignment). Any assignment satisfying every `P_i = 0` gives
//! `G = sum_i c_i * 0 = 0`, contradicting `G != 0`. So the conjunction is
//! infeasible and the clause is therefore VALID.
//!
//! Note what is NOT assumed: the span test is over the monomial basis, i.e. it
//! ignores every algebraic relation between monomials (it never uses
//! `n * n >= 0`, nor that `counter * n` and `n * counter` denote a product).
//! That makes it strictly WEAKER than real nonlinear reasoning, which is the
//! safe direction — a polynomial identity is valid over any commutative ring,
//! so nothing here depends on the sort being `Int` rather than `Real`.
//!
//! Three further conservative points:
//!
//! * Ignoring the non-equality conjuncts (`<`, `<=`, …) only makes infeasibility
//!   HARDER to establish, never easier: dropping conjuncts weakens the
//!   hypothesis, so a refutation of the retained subset refutes the whole.
//! * [`extract_constraints`] fails closed on any shape it does not model, and
//!   drops only constant conjuncts that evaluate to TRUE (a FALSE one sets
//!   `const_refuted`, which is infeasibility outright).
//! * The elimination is exact rational arithmetic — no floating point, no
//!   pseudo-remainders — and is metered, so an adversarial lemma cannot spend
//!   unbounded work here.
//!
//! There is no payload to forge: the checker re-derives the combination itself
//! and accepts only what it can reconstruct.

use std::collections::BTreeMap;
use std::mem::size_of;

use ay_core::{ProofId, TermId, TermStore};
use num_traits::Zero;

use super::nra_poly::{
    bit_scaled, ensure_coeff_width, extract_constraints, rat_bits, MPoly, Monomial, Rel, WorkMeter,
    WORK_METER_RESOURCE_LIMIT,
};
use super::ProofCheckError;

/// Bound on elimination steps, so a wide lemma cannot spend unbounded work.
const MAX_ELIMINATION_STEPS: u64 = 100_000;
/// Maximum equality constraints admitted to the span calculation.
const MAX_EQUALITY_ROWS: usize = 2_048;
/// Maximum disequalities inspected for membership in the equality span.
const MAX_DISEQUALITY_ROWS: usize = 1_024;
/// Maximum nonzero rows retained by the echelon basis.
const MAX_BASIS_ROWS: usize = 1_024;
/// Cumulative polynomial terms materialized by extraction and elimination.
const MAX_MATERIALIZED_TERMS: usize = 200_000;
/// Cumulative logical accounting limit for polynomial/key/coefficient state.
///
/// This is deliberately not advertised as allocator-exact peak RSS: BTree node
/// layouts and Vec spare capacity are implementation details. The hard
/// pre-allocation envelope instead comes from the shared 200k produced-
/// monomial meter, degree-256 key bound, and 4096-bit coefficient cap. This
/// tighter logical counter limits how much of that finite envelope elimination
/// may cumulatively copy/materialize.
const MAX_MATERIALIZED_BYTES: u64 = 64 * 1024 * 1024;

type PivotBasis = BTreeMap<Monomial, MPoly>;

/// Private finite envelope for equality-span bookkeeping.
///
/// The shared [`WorkMeter`] bounds rational word operations and monomial/DAG
/// production before extraction allocates it; degree and coefficient caps bound
/// each key/value. This companion meter is cumulative *logical* accounting,
/// not an allocator-exact peak-memory claim. Elimination clone/scale/subtract
/// outputs are charged by a deterministic logical upper bound before their
/// allocation, while already-extracted polynomials are accounted immediately
/// afterward under the shared hard pre-allocation bounds. Every counter uses
/// checked arithmetic and a cap trip is a refusal, never an acceptance.
#[derive(Default)]
struct IdealEnvelope {
    materialized_terms: usize,
    materialized_bytes: u64,
}

impl IdealEnvelope {
    fn charge_allocation(&mut self, terms: usize, bytes: u64, what: &str) -> Result<(), String> {
        self.materialized_terms = self
            .materialized_terms
            .checked_add(terms)
            .ok_or_else(|| "linear-ideal term accounting overflow".to_string())?;
        if self.materialized_terms > MAX_MATERIALIZED_TERMS {
            return Err(format!(
                "linear-ideal materialized-term cap exceeded while {what}"
            ));
        }
        self.materialized_bytes = self
            .materialized_bytes
            .checked_add(bytes)
            .ok_or_else(|| "linear-ideal byte accounting overflow".to_string())?;
        if self.materialized_bytes > MAX_MATERIALIZED_BYTES {
            return Err(format!(
                "linear-ideal materialized-byte cap exceeded while {what}"
            ));
        }
        Ok(())
    }

    fn charge_poly(
        &mut self,
        poly: &MPoly,
        meter: &mut WorkMeter<'_>,
        what: &str,
    ) -> Result<(), String> {
        let mut bytes = u64::try_from(size_of::<MPoly>())
            .map_err(|_| "linear-ideal size accounting overflow".to_string())?;
        precharge_poly_scan(poly, meter)?;
        for (index, (monomial, coeff)) in poly.terms.iter().enumerate() {
            meter.poll_loop(index)?;
            ensure_coeff_width(coeff)?;
            let key_items = u64::try_from(monomial.len())
                .map_err(|_| "linear-ideal key accounting overflow".to_string())?;
            let key_item_bytes = u64::try_from(size_of::<(TermId, u32)>())
                .map_err(|_| "linear-ideal key accounting overflow".to_string())?;
            let key_bytes = key_items
                .checked_mul(key_item_bytes)
                .ok_or_else(|| "linear-ideal key accounting overflow".to_string())?;
            let coeff_bytes = rat_bits(coeff).saturating_add(7) / 8;
            bytes = bytes
                .checked_add(key_bytes)
                .and_then(|n| n.checked_add(coeff_bytes))
                .and_then(|n| n.checked_add(64)) // deterministic logical node/value overhead
                .ok_or_else(|| "linear-ideal byte accounting overflow".to_string())?;
        }
        self.charge_allocation(poly.terms.len(), bytes, what)
    }

    /// Precharge one output whose monomial keys are a subset of `shape` and
    /// whose coefficients may grow up to the global width cap.
    fn charge_poly_upper(
        &mut self,
        shape: &MPoly,
        meter: &mut WorkMeter<'_>,
        what: &str,
    ) -> Result<(), String> {
        let mut bytes = u64::try_from(size_of::<MPoly>())
            .map_err(|_| "linear-ideal size accounting overflow".to_string())?;
        precharge_poly_scan(shape, meter)?;
        for (index, (monomial, coeff)) in shape.terms.iter().enumerate() {
            meter.poll_loop(index)?;
            ensure_coeff_width(coeff)?;
            let key_items = u64::try_from(monomial.len())
                .map_err(|_| "linear-ideal key accounting overflow".to_string())?;
            let key_item_bytes = u64::try_from(size_of::<(TermId, u32)>())
                .map_err(|_| "linear-ideal key accounting overflow".to_string())?;
            let key_bytes = key_items
                .checked_mul(key_item_bytes)
                .ok_or_else(|| "linear-ideal key accounting overflow".to_string())?;
            let max_coeff_bytes = super::nra_poly::MAX_POLY_COEFF_BITS.saturating_add(7) / 8;
            bytes = bytes
                .checked_add(key_bytes)
                .and_then(|n| n.checked_add(max_coeff_bytes))
                .and_then(|n| n.checked_add(64))
                .ok_or_else(|| "linear-ideal byte accounting overflow".to_string())?;
        }
        self.charge_allocation(shape.terms.len(), bytes, what)
    }

    fn charge_pivot_lookup(
        &mut self,
        basis_len: usize,
        pivot: &Monomial,
        meter: &mut WorkMeter<'_>,
    ) -> Result<(), String> {
        // `BTreeMap` gives indexed deterministic lookup. Charge the stronger
        // full-row/key-width bound, so implementation details of its node
        // fanout cannot make the accounting optimistic.
        let rows = u64::try_from(basis_len.saturating_add(1))
            .map_err(|_| "linear-ideal pivot accounting overflow".to_string())?;
        let key_width = u64::try_from(pivot.len().saturating_add(1))
            .map_err(|_| "linear-ideal pivot accounting overflow".to_string())?;
        let work = rows
            .checked_mul(key_width)
            .ok_or_else(|| "linear-ideal pivot accounting overflow".to_string())?;
        meter.charge_ops(work)
    }

    fn charge_leading_lookup(
        &mut self,
        poly_len: usize,
        meter: &mut WorkMeter<'_>,
    ) -> Result<(), String> {
        // Charge a full deterministic map scan although `next_back` is
        // logarithmic/constant-amortized. This covers traversal plus every
        // possible monomial-key comparison with room to spare.
        let rows = u64::try_from(poly_len.saturating_add(1))
            .map_err(|_| "linear-ideal leading accounting overflow".to_string())?;
        let key_width = u64::from(super::nra_poly::MAX_POLY_DEGREE).saturating_add(1);
        meter.charge_ops(
            rows.checked_mul(key_width)
                .ok_or_else(|| "linear-ideal leading accounting overflow".to_string())?,
        )
    }

    fn leading_term<'poly>(
        &mut self,
        poly: &'poly MPoly,
        meter: &mut WorkMeter<'_>,
    ) -> Result<Option<(&'poly Monomial, &'poly num_rational::BigRational)>, String> {
        self.charge_leading_lookup(poly.terms.len(), meter)?;
        Ok(poly.terms.iter().next_back())
    }

    fn clone_leading(
        &mut self,
        monomial: &Monomial,
        coeff: &num_rational::BigRational,
        meter: &mut WorkMeter<'_>,
    ) -> Result<(Monomial, num_rational::BigRational), String> {
        ensure_coeff_width(coeff)?;
        let key_items = u64::try_from(monomial.len())
            .map_err(|_| "linear-ideal leading-key accounting overflow".to_string())?;
        let work = key_items
            .checked_add(bit_scaled(1, rat_bits(coeff)))
            .ok_or_else(|| "linear-ideal leading-clone accounting overflow".to_string())?;
        meter.charge_ops(work)?;
        let key_bytes = key_items
            .checked_mul(
                u64::try_from(size_of::<(TermId, u32)>())
                    .map_err(|_| "linear-ideal leading-key accounting overflow".to_string())?,
            )
            .ok_or_else(|| "linear-ideal leading-key accounting overflow".to_string())?;
        let bytes = key_bytes
            .checked_add(rat_bits(coeff).saturating_add(7) / 8)
            .ok_or_else(|| "linear-ideal leading-clone accounting overflow".to_string())?;
        self.charge_allocation(1, bytes, "cloning a leading pivot and coefficient")?;
        meter.charge_structural_monomials(1)?;
        let clone = (monomial.clone(), coeff.clone());
        ensure_coeff_width(&clone.1)?;
        Ok(clone)
    }

    fn reciprocal(
        &mut self,
        coeff: &num_rational::BigRational,
        meter: &mut WorkMeter<'_>,
    ) -> Result<num_rational::BigRational, String> {
        ensure_coeff_width(coeff)?;
        meter.charge_ops(bit_scaled(1, rat_bits(coeff)))?;
        if coeff.is_zero() {
            return Err("zero leading coefficient in linear-ideal basis".to_string());
        }
        let bytes = rat_bits(coeff)
            .saturating_add(7)
            .checked_div(8)
            .and_then(|payload| {
                payload.checked_add(u64::try_from(size_of::<num_rational::BigRational>()).ok()?)
            })
            .ok_or_else(|| "linear-ideal reciprocal accounting overflow".to_string())?;
        let caller_bytes =
            usize::try_from(bytes).map_err(|_| WORK_METER_RESOURCE_LIMIT.to_string())?;
        meter.charge_private_allocation(0, caller_bytes)?;
        self.charge_allocation(0, bytes, "materializing a leading-coefficient reciprocal")?;
        meter.charge_rational_scratch(rat_bits(coeff).saturating_add(1))?;
        let inverse = coeff.recip();
        ensure_coeff_width(&inverse)?;
        Ok(inverse)
    }
}

fn precharge_poly_scan(poly: &MPoly, meter: &mut WorkMeter<'_>) -> Result<(), String> {
    let terms = u64::try_from(poly.terms.len())
        .map_err(|_| "linear-ideal scan accounting overflow".to_string())?;
    let per_term = u64::from(super::nra_poly::MAX_POLY_DEGREE)
        .checked_add(bit_scaled(1, super::nra_poly::MAX_POLY_COEFF_BITS))
        .ok_or_else(|| "linear-ideal scan accounting overflow".to_string())?;
    meter.charge_ops(
        terms
            .checked_mul(per_term)
            .ok_or_else(|| "linear-ideal scan accounting overflow".to_string())?,
    )
}

/// Validate a `Generic` arithmetic lemma whose refutation is a linear
/// combination of equalities over the monomial basis.
///
/// Returns `Ok(())` only when the checker has itself reconstructed the
/// combination; every other outcome — including "outside this fragment" — is an
/// error, so the caller keeps its existing fail-closed behaviour.
#[cfg(test)]
pub(crate) fn validate_linear_ideal_refutation(
    terms: &TermStore,
    step_id: ProofId,
    clause: &[TermId],
) -> Result<(), ProofCheckError> {
    let mut unbounded = |_: usize, _: usize| true;
    validate_linear_ideal_refutation_with_progress(terms, step_id, clause, &mut unbounded)
}

#[cfg(test)]
fn decide_linear_ideal_refutation(terms: &TermStore, clause: &[TermId]) -> Result<(), String> {
    let mut unbounded = |_: usize, _: usize| true;
    decide_linear_ideal_refutation_with_progress(terms, clause, &mut unbounded)
}

#[cfg(test)]
pub(crate) fn validate_linear_ideal_refutation_with_progress(
    terms: &TermStore,
    step_id: ProofId,
    clause: &[TermId],
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Result<(), ProofCheckError> {
    decide_linear_ideal_refutation_with_progress(terms, clause, progress).map_err(|reason| {
        if reason == WORK_METER_RESOURCE_LIMIT {
            ProofCheckError::ResourceLimit
        } else {
            ProofCheckError::InvalidTheoryLemma {
                step: step_id,
                reason: format!("linear_ideal_refutation: {reason}"),
            }
        }
    })
}

/// Validate a `Generic` arithmetic lemma on EITHER arithmetic lane.
///
/// The negated clause is normalized ONCE and then offered to two rules:
///
/// 1. the equality-span FAST PATH of this module, which decides polynomial
///    IDENTITY refutations (loop-invariant consecution) and ignores order;
/// 2. `super::nia_fourier_motzkin`, which decides the ORDER lane by
///    exact-rational Fourier–Motzkin elimination over the same constraints.
///
/// Sharing one extraction and one `WorkMeter` matters: this runs on every
/// trust-kind theory lemma of every proof, and re-parsing each clause would
/// double the caller's proof-wide resource charge for the whole `Generic` arm.
/// Declaration-free recognizer used by proof producers: `true` exactly when
/// the strict `crate::checker` `ArithClauseTautology` arm accepts the
/// clause (recognizer IS the validator, so classifier and checker cannot
/// drift). Runs under the validator's own work meter with an unbounded
/// progress callback.
#[must_use]
pub fn recognize_arith_clause_tautology(terms: &TermStore, clause: &[TermId]) -> bool {
    validate_generic_arithmetic_refutation_with_progress(terms, ProofId(0), clause, &mut |_, _| {
        true
    })
    .is_ok()
}

pub(crate) fn validate_generic_arithmetic_refutation_with_progress(
    terms: &TermStore,
    step_id: ProofId,
    clause: &[TermId],
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Result<(), ProofCheckError> {
    decide_generic_arithmetic_refutation_with_progress(terms, clause, progress).map_err(|reason| {
        if reason == WORK_METER_RESOURCE_LIMIT {
            ProofCheckError::ResourceLimit
        } else {
            ProofCheckError::InvalidTheoryLemma {
                step: step_id,
                reason: format!("generic_arithmetic_refutation: {reason}"),
            }
        }
    })
}

fn decide_generic_arithmetic_refutation_with_progress(
    terms: &TermStore,
    clause: &[TermId],
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Result<(), String> {
    let mut meter = WorkMeter::with_progress(progress);
    meter.poll()?;
    let extraction = extract_constraints(terms, clause, &mut meter)?;
    meter.poll()?;
    let mut envelope = IdealEnvelope::default();
    account_extracted_constraints(&extraction.constraints, &mut meter, &mut envelope)?;

    // A conjunct that evaluated to FALSE refutes the negation outright.
    if extraction.const_refuted {
        return Ok(());
    }

    match decide_span_refutation(&extraction.constraints, &mut meter, &mut envelope) {
        Ok(()) => return Ok(()),
        // A caller-envelope refusal is a resource event, not a verdict: do not
        // spend more of the same envelope on the second lane.
        Err(reason) if reason == WORK_METER_RESOURCE_LIMIT => return Err(reason),
        Err(_) => {}
    }
    super::nia_fourier_motzkin::fourier_motzkin_refutes(&extraction.constraints, &mut meter)
}

#[cfg(test)]
fn decide_linear_ideal_refutation_with_progress(
    terms: &TermStore,
    clause: &[TermId],
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Result<(), String> {
    let mut meter = WorkMeter::with_progress(progress);
    meter.poll()?;
    let extraction = extract_constraints(terms, clause, &mut meter)?;
    meter.poll()?;
    let mut envelope = IdealEnvelope::default();
    account_extracted_constraints(&extraction.constraints, &mut meter, &mut envelope)?;

    // A conjunct that evaluated to FALSE refutes the negation outright.
    if extraction.const_refuted {
        return Ok(());
    }
    decide_span_refutation(&extraction.constraints, &mut meter, &mut envelope)
}

/// The equality-span rule proper: is some disequality polynomial in the
/// rational span of the equality polynomials?
fn decide_span_refutation(
    constraints: &[super::nra_poly::Constraint],
    meter: &mut WorkMeter<'_>,
    envelope: &mut IdealEnvelope,
) -> Result<(), String> {
    let mut equalities: Vec<&MPoly> = Vec::new();
    let mut disequalities: Vec<&MPoly> = Vec::new();
    for constraint in constraints {
        meter.poll()?;
        match constraint.rel {
            Rel::Eq => {
                if equalities.len() == MAX_EQUALITY_ROWS {
                    return Err(format!(
                        "linear-ideal equality-row cap {MAX_EQUALITY_ROWS} exceeded"
                    ));
                }
                meter.charge_container_slot::<&MPoly>()?;
                equalities
                    .try_reserve(1)
                    .map_err(|_| "linear-ideal equality-row allocation refused".to_string())?;
                equalities.push(&constraint.poly);
            }
            Rel::Ne => {
                if disequalities.len() == MAX_DISEQUALITY_ROWS {
                    return Err(format!(
                        "linear-ideal disequality-row cap {MAX_DISEQUALITY_ROWS} exceeded"
                    ));
                }
                meter.charge_container_slot::<&MPoly>()?;
                disequalities
                    .try_reserve(1)
                    .map_err(|_| "linear-ideal disequality-row allocation refused".to_string())?;
                disequalities.push(&constraint.poly);
            }
            // Order constraints carry no equational content for this rule.
            // Ignoring them is conservative (see the module note).
            _ => {}
        }
    }

    if disequalities.is_empty() {
        return Err("no disequality conjunct to refute".to_string());
    }

    // Row-echelon basis of the equality span, each row normalized to leading
    // coefficient 1 so reduction is a single scale-and-subtract.
    let mut basis = PivotBasis::new();
    for poly in &equalities {
        meter.poll()?;
        let residual = reduce(poly, &basis, meter, envelope)?;
        if let Some((lead_ref, coeff_ref)) = envelope.leading_term(&residual, meter)? {
            if basis.len() == MAX_BASIS_ROWS {
                return Err(format!(
                    "linear-ideal basis-row cap {MAX_BASIS_ROWS} exceeded"
                ));
            }
            let (lead, coeff) = envelope.clone_leading(lead_ref, coeff_ref, meter)?;
            envelope.charge_pivot_lookup(basis.len(), &lead, meter)?;
            let inverse = envelope.reciprocal(&coeff, meter)?;
            envelope.charge_poly_upper(&residual, meter, "precharging a normalized basis row")?;
            let normalized = residual.scale(&inverse, meter)?;
            if basis.insert(lead, normalized).is_some() {
                return Err("duplicate pivot survived linear-ideal reduction".to_string());
            }
        }
    }

    // `G` is in the span iff it reduces to the zero polynomial.
    for poly in &disequalities {
        meter.poll()?;
        let residual = reduce(poly, &basis, meter, envelope)?;
        if residual.terms.is_empty() {
            return Ok(());
        }
    }

    Err(format!(
        "no disequality lies in the rational span of the {} equality conjunct(s)",
        equalities.len()
    ))
}

fn account_extracted_constraints(
    constraints: &[super::nra_poly::Constraint],
    meter: &mut WorkMeter<'_>,
    envelope: &mut IdealEnvelope,
) -> Result<(), String> {
    for constraint in constraints {
        meter.poll()?;
        envelope.charge_poly(&constraint.poly, meter, "accounting extracted constraints")?;
    }
    Ok(())
}

/// Reduce `poly` against the echelon `basis`, cancelling leading monomials.
///
/// Terminates: each step cancels the current leading monomial and introduces
/// only strictly smaller ones, so the leading monomial strictly decreases in a
/// well-founded order. The meter bounds the work regardless.
fn reduce(
    poly: &MPoly,
    basis: &PivotBasis,
    meter: &mut WorkMeter<'_>,
    envelope: &mut IdealEnvelope,
) -> Result<MPoly, String> {
    envelope.charge_poly(poly, meter, "precharging an elimination-residual clone")?;
    meter.charge_structural_monomials(poly.terms.len())?;
    let mut residual = poly.clone();
    let mut steps: u64 = 0;
    loop {
        meter.poll()?;
        let Some((lead, coeff)) = envelope.leading_term(&residual, meter)? else {
            return Ok(residual);
        };
        envelope.charge_pivot_lookup(basis.len(), lead, meter)?;
        let Some(row) = basis.get(lead) else {
            return Ok(residual);
        };
        steps += 1;
        if steps > MAX_ELIMINATION_STEPS {
            return Err("elimination step budget exhausted".to_string());
        }
        meter.charge_ops(1)?;
        debug_assert!(!coeff.is_zero(), "MPoly prunes zero coefficients");
        let (_, coeff) = envelope.clone_leading(lead, coeff, meter)?;
        // `row` has leading coefficient 1 at `lead`, so this cancels it exactly.
        envelope.charge_poly_upper(row, meter, "precharging a scaled basis row")?;
        let scaled = row.scale(&coeff, meter)?;
        // `sub` starts by cloning `residual` and can then insert every key from
        // `scaled`; charging both shapes is a conservative upper bound on the
        // one result map, including coefficient growth to the global cap.
        envelope.charge_poly_upper(&residual, meter, "precharging a reduced residual (left)")?;
        envelope.charge_poly_upper(&scaled, meter, "precharging a reduced residual (right)")?;
        let next = residual.sub(&scaled, meter)?;
        residual = next;
    }
}

#[cfg(test)]
#[path = "nia_linear_ideal_tests.rs"]
mod tests;
