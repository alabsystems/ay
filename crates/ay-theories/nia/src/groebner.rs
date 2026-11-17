// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bounded Groebner-basis consequences of the asserted equality atoms
//! (#nia-groebner), mirroring z3's `arith-grobner` use inside its
//! nonlinear arithmetic solver (`nla_grobner.cpp`).
//!
//! The linearized relaxation treats every product as an opaque aux
//! variable, so ideal consequences that mix products — the VeryMax
//! Farkas shape `Nl * lam + linear = 0` rows whose shared bilinear lead
//! cancels into a purely linear fact — are invisible to it. This pass
//! extracts a polynomial over the base variables from every true
//! equality atom, runs a budget-capped Buchberger completion over
//! `BigRational` coefficients (grlex order), and asserts each derived
//! polynomial that is linear over the *tracked* monomials into the
//! inner LIA solver as a pair of reason-carrying cuts (`>=` and `<=`).
//! Every derived polynomial carries the exact provenance set of
//! asserted equality literals it was combined from; those literals are
//! the cut reasons, so a conflict the cuts join explains itself. A
//! derived nonzero constant is a direct conflict on its provenance.
//!
//! Soundness: S-polynomial combination and reduction only form
//! `Q`-linear combinations of input polynomials with monomial
//! multipliers, i.e. ideal members — every common zero of the asserted
//! equalities is a zero of each derived polynomial. Caps (input count,
//! degree, terms, pairs, basis size) only ever *drop* derived facts,
//! degrading to the previous behavior; nothing outside the supported
//! term shapes (`+`, `-`, `*`, constants, variables, monomial auxes)
//! is extracted.

use std::cmp::Ordering;
use std::collections::{BTreeMap, VecDeque};

use num_traits::{One, Signed, Zero};

use super::*;

/// Most equality polynomials admitted to one Buchberger run.
pub(crate) const MAX_INPUT_POLYS: usize = 96;
/// Highest total degree kept during extraction and completion.
pub(crate) const MAX_DEGREE: usize = 6;
/// Most monomials in any single polynomial.
pub(crate) const MAX_TERMS: usize = 96;
/// Most S-polynomial pairs formed per run.
const MAX_PAIRS: usize = 1024;
/// Largest basis retained per run.
const MAX_BASIS: usize = 160;
/// Deepest term walk during polynomial extraction.
pub(crate) const MAX_EXTRACT_DEPTH: usize = 48;
/// Most single-term reduction steps applied to one polynomial.
const MAX_REDUCE_STEPS: usize = 4096;

/// A monomial: sorted multiset of base variables (`[]` is the constant).
pub(crate) type Mono = Vec<TermId>;
/// Sparse polynomial terms keyed by monomial.
pub(crate) type PolyTerms = BTreeMap<Mono, BigRational>;

/// A polynomial plus the asserted equality literals it derives from.
#[derive(Clone)]
pub(crate) struct GPoly {
    pub(crate) terms: PolyTerms,
    pub(crate) provenance: Vec<(TermId, bool)>,
}

/// Graded lexicographic order on monomials (degree first, then the
/// sorted factor list compared by term id): an admissible order.
fn mono_cmp(a: &Mono, b: &Mono) -> Ordering {
    a.len()
        .cmp(&b.len())
        .then_with(|| a.iter().map(|t| t.0).cmp(b.iter().map(|t| t.0)))
}

/// Multiset inclusion: every factor of `divisor` occurs in `mono`.
fn mono_divides(divisor: &Mono, mono: &Mono) -> bool {
    let (mut i, mut j) = (0, 0);
    while i < divisor.len() && j < mono.len() {
        match divisor[i].0.cmp(&mono[j].0) {
            Ordering::Equal => {
                i += 1;
                j += 1;
            }
            Ordering::Greater => j += 1,
            Ordering::Less => return false,
        }
    }
    i == divisor.len()
}

/// Multiset difference `mono - divisor` (caller checked divisibility).
fn mono_quotient(mono: &Mono, divisor: &Mono) -> Mono {
    let mut out = Vec::with_capacity(mono.len() - divisor.len());
    let (mut i, mut j) = (0, 0);
    while j < mono.len() {
        if i < divisor.len() && divisor[i] == mono[j] {
            i += 1;
        } else {
            out.push(mono[j]);
        }
        j += 1;
    }
    out
}

/// Least common multiple of two monomials (per-factor max multiplicity).
fn mono_lcm(a: &Mono, b: &Mono) -> Mono {
    let mut out = Vec::with_capacity(a.len().max(b.len()));
    let (mut i, mut j) = (0, 0);
    while i < a.len() || j < b.len() {
        if i < a.len() && (j == b.len() || a[i].0 < b[j].0) {
            out.push(a[i]);
            i += 1;
        } else if j < b.len() && (i == a.len() || b[j].0 < a[i].0) {
            out.push(b[j]);
            j += 1;
        } else {
            out.push(a[i]);
            i += 1;
            j += 1;
        }
    }
    out
}

/// Product of two monomials (sorted merge of the factor multisets).
pub(crate) fn mono_mul(a: &Mono, b: &Mono) -> Mono {
    let mut out: Mono = a.iter().chain(b.iter()).copied().collect();
    out.sort_unstable_by_key(|t| t.0);
    out
}

impl GPoly {
    fn leading(&self) -> Option<(&Mono, &BigRational)> {
        self.terms.iter().max_by(|(a, _), (b, _)| mono_cmp(a, b))
    }

    fn is_zero(&self) -> bool {
        self.terms.is_empty()
    }

    pub(crate) fn is_constant(&self) -> bool {
        self.terms.len() == 1 && self.terms.contains_key(&Vec::new())
    }

    /// Divide through by the leading coefficient (provenance unchanged).
    fn make_monic(&mut self) {
        let Some((_, lc)) = self.leading() else {
            return;
        };
        if lc.is_one() {
            return;
        }
        let lc = lc.clone();
        for coeff in self.terms.values_mut() {
            *coeff /= &lc;
        }
    }

    /// `self += scale * shift * other`, merging provenance. Returns
    /// `false` when a size cap is exceeded (caller drops the result).
    fn add_scaled(&mut self, other: &GPoly, shift: &Mono, scale: &BigRational) -> bool {
        for (mono, coeff) in &other.terms {
            let shifted = mono_mul(mono, shift);
            if shifted.len() > MAX_DEGREE {
                return false;
            }
            let entry = self.terms.entry(shifted).or_insert_with(BigRational::zero);
            *entry += scale * coeff;
        }
        self.terms.retain(|_, c| !c.is_zero());
        if self.terms.len() > MAX_TERMS {
            return false;
        }
        merge_provenance(&mut self.provenance, &other.provenance);
        true
    }
}

fn merge_provenance(into: &mut Vec<(TermId, bool)>, from: &[(TermId, bool)]) {
    for lit in from {
        if !into.contains(lit) {
            into.push(*lit);
        }
    }
}

/// S-polynomial of two monic polynomials: the lead-canceling combination
/// `(lcm/lt_f) * f - (lcm/lt_g) * g`.
fn s_polynomial(f: &GPoly, g: &GPoly) -> Option<GPoly> {
    let (lf, _) = f.leading()?;
    let (lg, _) = g.leading()?;
    let lcm = mono_lcm(lf, lg);
    if lcm.len() > MAX_DEGREE {
        return None;
    }
    let mut out = GPoly {
        terms: PolyTerms::new(),
        provenance: Vec::new(),
    };
    let shift_f = mono_quotient(&lcm, lf);
    let shift_g = mono_quotient(&lcm, lg);
    if !out.add_scaled(f, &shift_f, &BigRational::one()) {
        return None;
    }
    if !out.add_scaled(g, &shift_g, &-BigRational::one()) {
        return None;
    }
    Some(out)
}

/// Reduce `poly` by the (monic) basis until no term is divisible by a
/// basis lead. `None` when a cap is hit — the polynomial is dropped,
/// which loses only completeness.
fn reduce(mut poly: GPoly, basis: &[GPoly]) -> Option<GPoly> {
    for _ in 0..MAX_REDUCE_STEPS {
        // Largest reducible monomial first (canonical reduction order).
        let mut target: Option<(Mono, BigRational, usize)> = None;
        for (mono, coeff) in &poly.terms {
            for (bi, g) in basis.iter().enumerate() {
                let (lead, _) = g.leading()?;
                if mono_divides(lead, mono) {
                    let better = target
                        .as_ref()
                        .is_none_or(|(best, _, _)| mono_cmp(mono, best) == Ordering::Greater);
                    if better {
                        target = Some((mono.clone(), coeff.clone(), bi));
                    }
                    break;
                }
            }
        }
        let Some((mono, coeff, bi)) = target else {
            return Some(poly);
        };
        let (lead, _) = basis[bi].leading()?;
        let shift = mono_quotient(&mono, lead);
        let neg = -coeff;
        let g = basis[bi].clone();
        if !poly.add_scaled(&g, &shift, &neg) {
            return None;
        }
    }
    None
}

/// Budget-capped Buchberger completion. The result includes the inputs
/// (reduced, monic) and every derived polynomial the budgets allowed.
pub(crate) fn buchberger(inputs: Vec<GPoly>) -> Vec<GPoly> {
    let mut basis: Vec<GPoly> = Vec::new();
    let mut queue: VecDeque<GPoly> = inputs.into_iter().collect();
    let mut pairs = 0usize;
    while let Some(candidate) = queue.pop_front() {
        let Some(mut reduced) = reduce(candidate, &basis) else {
            continue;
        };
        if reduced.is_zero() {
            continue;
        }
        reduced.make_monic();
        if reduced.is_constant() {
            basis.push(reduced);
            return basis;
        }
        for g in &basis {
            if pairs >= MAX_PAIRS {
                break;
            }
            pairs += 1;
            if let Some(sp) = s_polynomial(&reduced, g) {
                if !sp.is_zero() {
                    queue.push_back(sp);
                }
            }
        }
        basis.push(reduced);
        if basis.len() >= MAX_BASIS {
            break;
        }
    }
    basis
}

/// Canonical integer signature of a polynomial: coefficients scaled to
/// coprime integers with a positive leading coefficient. Two
/// polynomials that are nonzero rational multiples share a signature,
/// which is what input/derived dedup needs; the signature doubles as
/// the integer coefficients of the emitted cut.
pub(crate) fn integer_signature(terms: &PolyTerms) -> Option<Vec<(Mono, BigInt)>> {
    if terms.is_empty() {
        return None;
    }
    let mut scale = BigInt::one();
    for coeff in terms.values() {
        scale = num_integer_lcm(&scale, coeff.denom());
    }
    let mut signed: Vec<(Mono, BigInt)> = terms
        .iter()
        .map(|(mono, coeff)| (mono.clone(), coeff.numer() * (&scale / coeff.denom())))
        .collect();
    let mut gcd = BigInt::zero();
    for (_, coeff) in &signed {
        gcd = num_integer_gcd(&gcd, coeff);
    }
    if gcd > BigInt::one() {
        for (_, coeff) in &mut signed {
            *coeff /= &gcd;
        }
    }
    signed.sort_by(|(a, _), (b, _)| mono_cmp(a, b));
    if signed.last().is_some_and(|(_, c)| c.is_negative()) {
        for (_, coeff) in &mut signed {
            *coeff = -coeff.clone();
        }
    }
    Some(signed)
}

fn num_integer_gcd(a: &BigInt, b: &BigInt) -> BigInt {
    use num_integer::Integer;
    a.gcd(b)
}

fn num_integer_lcm(a: &BigInt, b: &BigInt) -> BigInt {
    use num_integer::Integer;
    a.lcm(b)
}
