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

use ay_core::{ProofId, TermId, TermStore};
use num_traits::Zero;

use super::nra_poly::{extract_constraints, MPoly, Monomial, Rel, WorkMeter};
use super::ProofCheckError;

/// Bound on elimination steps, so a wide lemma cannot spend unbounded work.
const MAX_ELIMINATION_STEPS: u64 = 100_000;

/// Validate a `Generic` arithmetic lemma whose refutation is a linear
/// combination of equalities over the monomial basis.
///
/// Returns `Ok(())` only when the checker has itself reconstructed the
/// combination; every other outcome — including "outside this fragment" — is an
/// error, so the caller keeps its existing fail-closed behaviour.
pub(crate) fn validate_linear_ideal_refutation(
    terms: &TermStore,
    step_id: ProofId,
    clause: &[TermId],
) -> Result<(), ProofCheckError> {
    decide_linear_ideal_refutation(terms, clause).map_err(|reason| {
        ProofCheckError::InvalidTheoryLemma {
            step: step_id,
            reason: format!("linear_ideal_refutation: {reason}"),
        }
    })
}

fn decide_linear_ideal_refutation(terms: &TermStore, clause: &[TermId]) -> Result<(), String> {
    let mut meter = WorkMeter::new();
    let extraction = extract_constraints(terms, clause, &mut meter)?;

    // A conjunct that evaluated to FALSE refutes the negation outright.
    if extraction.const_refuted {
        return Ok(());
    }

    let mut equalities: Vec<&MPoly> = Vec::new();
    let mut disequalities: Vec<&MPoly> = Vec::new();
    for constraint in &extraction.constraints {
        match constraint.rel {
            Rel::Eq => equalities.push(&constraint.poly),
            Rel::Ne => disequalities.push(&constraint.poly),
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
    let mut basis: Vec<(Monomial, MPoly)> = Vec::new();
    for poly in &equalities {
        let residual = reduce(poly, &basis, &mut meter)?;
        if let Some((lead, coeff)) = leading(&residual) {
            let inverse = coeff.recip();
            let normalized = residual.scale(&inverse, &mut meter)?;
            basis.push((lead, normalized));
        }
    }

    // `G` is in the span iff it reduces to the zero polynomial.
    for poly in &disequalities {
        let residual = reduce(poly, &basis, &mut meter)?;
        if residual.terms.is_empty() {
            return Ok(());
        }
    }

    Err(format!(
        "no disequality lies in the rational span of the {} equality conjunct(s)",
        equalities.len()
    ))
}

/// Leading (monomial, coefficient) under the shared monomial order.
///
/// `MPoly` prunes zero coefficients on every update, so a non-empty `terms` map
/// always has a genuinely non-zero leading entry.
fn leading(poly: &MPoly) -> Option<(Monomial, num_rational::BigRational)> {
    poly.terms
        .iter()
        .next_back()
        .map(|(monomial, coeff)| (monomial.clone(), coeff.clone()))
}

/// Reduce `poly` against the echelon `basis`, cancelling leading monomials.
///
/// Terminates: each step cancels the current leading monomial and introduces
/// only strictly smaller ones, so the leading monomial strictly decreases in a
/// well-founded order. The meter bounds the work regardless.
fn reduce(
    poly: &MPoly,
    basis: &[(Monomial, MPoly)],
    meter: &mut WorkMeter,
) -> Result<MPoly, String> {
    let mut residual = poly.clone();
    let mut steps: u64 = 0;
    loop {
        let Some((lead, coeff)) = leading(&residual) else {
            return Ok(residual);
        };
        let Some((_, row)) = basis.iter().find(|(monomial, _)| *monomial == lead) else {
            return Ok(residual);
        };
        steps += 1;
        if steps > MAX_ELIMINATION_STEPS {
            return Err("elimination step budget exhausted".to_string());
        }
        meter.charge_ops(1)?;
        debug_assert!(!coeff.is_zero(), "MPoly prunes zero coefficients");
        // `row` has leading coefficient 1 at `lead`, so this cancels it exactly.
        let scaled = row.scale(&coeff, meter)?;
        residual = residual.sub(&scaled, meter)?;
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ay_core::Sort;

    fn int_var(terms: &mut TermStore, name: &str) -> TermId {
        terms.mk_var(name, Sort::Int)
    }

    fn int_const(terms: &mut TermStore, n: i64) -> TermId {
        terms.mk_int(n.into())
    }

    /// The motivating shape: loop-invariant consecution, where the nonlinear
    /// monomials cancel. Clause is `(or (not INV) INV_NEXT)`.
    #[test]
    fn accepts_invariant_consecution() {
        let mut terms = TermStore::new();
        let n = int_var(&mut terms, "n");
        let sum = int_var(&mut terms, "sum");
        let counter = int_var(&mut terms, "counter");
        let one = int_const(&mut terms, 1);

        // sum + counter*n = n*n
        let counter_n = terms.mk_mul(vec![counter, n]);
        let n_n = terms.mk_mul(vec![n, n]);
        let inv_lhs = terms.mk_add(vec![sum, counter_n]);
        let inv = terms.mk_eq(inv_lhs, n_n);

        // (sum + n) + (counter - 1)*n = n*n
        let sum_next = terms.mk_add(vec![sum, n]);
        let counter_next = terms.mk_sub(vec![counter, one]);
        let counter_next_n = terms.mk_mul(vec![counter_next, n]);
        let inv_next_lhs = terms.mk_add(vec![sum_next, counter_next_n]);
        let inv_next = terms.mk_eq(inv_next_lhs, n_n);

        let clause = vec![terms.mk_not_raw(inv), inv_next];
        validate_linear_ideal_refutation(&terms, ProofId(0), &clause)
            .expect("consecution clause is a polynomial identity and must validate");
    }

    /// A clause that is NOT valid must be refused: the goal equality is not a
    /// combination of the premise equality (an off-by-one in the update).
    #[test]
    fn rejects_non_identity() {
        let mut terms = TermStore::new();
        let n = int_var(&mut terms, "n");
        let sum = int_var(&mut terms, "sum");
        let counter = int_var(&mut terms, "counter");
        let one = int_const(&mut terms, 1);

        let counter_n = terms.mk_mul(vec![counter, n]);
        let n_n = terms.mk_mul(vec![n, n]);
        let inv_lhs = terms.mk_add(vec![sum, counter_n]);
        let inv = terms.mk_eq(inv_lhs, n_n);

        // WRONG update: sum + 1 instead of sum + n.
        let sum_next = terms.mk_add(vec![sum, one]);
        let counter_next = terms.mk_sub(vec![counter, one]);
        let counter_next_n = terms.mk_mul(vec![counter_next, n]);
        let inv_next_lhs = terms.mk_add(vec![sum_next, counter_next_n]);
        let inv_next = terms.mk_eq(inv_next_lhs, n_n);

        let clause = vec![terms.mk_not_raw(inv), inv_next];
        validate_linear_ideal_refutation(&terms, ProofId(0), &clause)
            .expect_err("a non-identity must NOT validate");
    }

    /// The rule must not accept a clause with no disequality to refute, even
    /// when the equalities themselves are consistent.
    #[test]
    fn rejects_without_disequality() {
        let mut terms = TermStore::new();
        let x = int_var(&mut terms, "x");
        let zero = int_const(&mut terms, 0);
        let ge = terms.mk_ge(x, zero);
        let clause = vec![ge];
        validate_linear_ideal_refutation(&terms, ProofId(0), &clause)
            .expect_err("no disequality conjunct means nothing is refuted");
    }

    /// Order constraints alone must never suffice: `x > 0` does not refute
    /// `x >= 0`. This pins the "ignoring inequalities is conservative" claim —
    /// the rule must decline rather than infer from them.
    #[test]
    fn rejects_order_only_conflict() {
        let mut terms = TermStore::new();
        let x = int_var(&mut terms, "x");
        let zero = int_const(&mut terms, 0);
        let gt = terms.mk_gt(x, zero);
        let lt = terms.mk_lt(x, zero);
        let clause = vec![terms.mk_not_raw(gt), terms.mk_not_raw(lt)];
        validate_linear_ideal_refutation(&terms, ProofId(0), &clause)
            .expect_err("this rule decides equalities only; order conflicts belong to Farkas");
    }
}
