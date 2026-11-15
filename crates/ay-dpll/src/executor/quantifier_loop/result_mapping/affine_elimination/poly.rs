// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The binder's coefficient read as an integer polynomial over the `Int`
//! atoms it multiplies, for the affine elimination's numeral and gcd tests.

use std::collections::BTreeMap;

use ay_core::kani_compat::DetHashSet;
use ay_core::{Sort, TermData, TermId};
use num_bigint::BigInt;
use num_integer::Integer;
use num_traits::{One, Zero};

use crate::executor::Executor;

/// An integer polynomial over `Int`-valued atoms: each monomial is the sorted
/// list of the atoms it multiplies (the empty list is the constant), mapped
/// to its nonzero coefficient.
pub(super) type IntPoly = BTreeMap<Vec<TermId>, BigInt>;

/// A polynomial with more monomials than this is not expanded; the
/// coefficient is then read as symbolic (no numeral, may vanish).
const MAX_POLY_MONOMIALS: usize = 64;

/// Arithmetic nesting past this depth is not expanded (same fallback).
const MAX_POLY_DEPTH: usize = 128;

impl Executor {
    /// The coefficient of `binder` in an affine `t`
    /// ([`Self::binder_affine_in`]) as a polynomial over `Int` atoms; `None`
    /// past the size or depth bound.
    pub(super) fn binder_coefficient_poly(
        &self,
        t: TermId,
        binder: TermId,
        mentioning: &DetHashSet<TermId>,
        depth: usize,
    ) -> Option<IntPoly> {
        if t == binder {
            return Some(poly_constant(BigInt::one()));
        }
        if !mentioning.contains(&t) {
            return Some(IntPoly::new());
        }
        if depth > MAX_POLY_DEPTH {
            return None;
        }
        let TermData::App(sym, args) = self.ctx.terms.get(t) else {
            return None;
        };
        match sym.name() {
            "+" => args.iter().try_fold(IntPoly::new(), |acc, &a| {
                poly_add(
                    acc,
                    &self.binder_coefficient_poly(a, binder, mentioning, depth + 1)?,
                )
            }),
            "-" => {
                let (&first, rest) = args.split_first()?;
                let first = self.binder_coefficient_poly(first, binder, mentioning, depth + 1)?;
                if rest.is_empty() {
                    return Some(poly_neg(first));
                }
                rest.iter().try_fold(first, |acc, &a| {
                    poly_sub(
                        acc,
                        &self.binder_coefficient_poly(a, binder, mentioning, depth + 1)?,
                    )
                })
            }
            "*" => {
                let mut product = poly_constant(BigInt::one());
                for &a in args {
                    let factor = if mentioning.contains(&a) {
                        self.binder_coefficient_poly(a, binder, mentioning, depth + 1)?
                    } else {
                        self.integer_poly(a, depth + 1)?
                    };
                    product = poly_mul(&product, &factor)?;
                }
                Some(product)
            }
            _ => None,
        }
    }

    /// The value of an affine `t` ([`Self::binder_affine_in`]) at `binder = 0`
    /// — the `r` of `t = c·v + r` — as a polynomial over `Int` atoms; `None`
    /// past the size or depth bound.
    pub(super) fn binder_rest_poly(
        &self,
        t: TermId,
        binder: TermId,
        mentioning: &DetHashSet<TermId>,
        depth: usize,
    ) -> Option<IntPoly> {
        if t == binder {
            return Some(IntPoly::new());
        }
        if !mentioning.contains(&t) {
            return self.integer_poly(t, depth);
        }
        if depth > MAX_POLY_DEPTH {
            return None;
        }
        let TermData::App(sym, args) = self.ctx.terms.get(t) else {
            return None;
        };
        match sym.name() {
            "+" => args.iter().try_fold(IntPoly::new(), |acc, &a| {
                poly_add(
                    acc,
                    &self.binder_rest_poly(a, binder, mentioning, depth + 1)?,
                )
            }),
            "-" => {
                let (&first, rest) = args.split_first()?;
                let first = self.binder_rest_poly(first, binder, mentioning, depth + 1)?;
                if rest.is_empty() {
                    return Some(poly_neg(first));
                }
                rest.iter().try_fold(first, |acc, &a| {
                    poly_sub(
                        acc,
                        &self.binder_rest_poly(a, binder, mentioning, depth + 1)?,
                    )
                })
            }
            "*" => args
                .iter()
                .try_fold(poly_constant(BigInt::one()), |acc, &a| {
                    poly_mul(
                        &acc,
                        &self.binder_rest_poly(a, binder, mentioning, depth + 1)?,
                    )
                }),
            _ => None,
        }
    }

    /// `t` expanded as a polynomial over its maximal `Int` subterms that are
    /// not `+`, `-`, `*` or an integer numeral; `None` for a non-`Int` atom
    /// or past the size or depth bound.
    fn integer_poly(&self, t: TermId, depth: usize) -> Option<IntPoly> {
        if !matches!(self.ctx.terms.sort(t), Sort::Int) || depth > MAX_POLY_DEPTH {
            return None;
        }
        match self.ctx.terms.get(t) {
            TermData::Const(ay_core::Constant::Int(n)) => Some(poly_constant(n.clone())),
            TermData::App(sym, args) if sym.name() == "+" => {
                args.iter().try_fold(IntPoly::new(), |acc, &a| {
                    poly_add(acc, &self.integer_poly(a, depth + 1)?)
                })
            }
            TermData::App(sym, args) if sym.name() == "-" && !args.is_empty() => {
                let first = self.integer_poly(args[0], depth + 1)?;
                if args.len() == 1 {
                    return Some(poly_neg(first));
                }
                args[1..].iter().try_fold(first, |acc, &a| {
                    poly_sub(acc, &self.integer_poly(a, depth + 1)?)
                })
            }
            TermData::App(sym, args) if sym.name() == "*" => args
                .iter()
                .try_fold(poly_constant(BigInt::one()), |acc, &a| {
                    poly_mul(&acc, &self.integer_poly(a, depth + 1)?)
                }),
            _ => Some(IntPoly::from([(vec![t], BigInt::one())])),
        }
    }
}

fn poly_constant(k: BigInt) -> IntPoly {
    let mut poly = IntPoly::new();
    if !k.is_zero() {
        poly.insert(Vec::new(), k);
    }
    poly
}

fn poly_add(mut acc: IntPoly, other: &IntPoly) -> Option<IntPoly> {
    for (monomial, k) in other {
        let entry = acc.entry(monomial.clone()).or_insert_with(BigInt::zero);
        *entry += k;
        if entry.is_zero() {
            acc.remove(monomial);
        }
    }
    (acc.len() <= MAX_POLY_MONOMIALS).then_some(acc)
}

fn poly_neg(poly: IntPoly) -> IntPoly {
    poly.into_iter()
        .map(|(monomial, k)| (monomial, -k))
        .collect()
}

pub(super) fn poly_sub(acc: IntPoly, other: &IntPoly) -> Option<IntPoly> {
    poly_add(acc, &poly_neg(other.clone()))
}

fn poly_mul(a: &IntPoly, b: &IntPoly) -> Option<IntPoly> {
    let mut product = IntPoly::new();
    for (ma, ka) in a {
        for (mb, kb) in b {
            let mut monomial: Vec<TermId> = ma.iter().chain(mb.iter()).copied().collect();
            monomial.sort_unstable();
            let term = IntPoly::from([(monomial, ka * kb)]);
            product = poly_add(product, &term)?;
        }
    }
    Some(product)
}

/// The polynomial's value when it is a constant.
pub(super) fn poly_numeral(poly: &IntPoly) -> Option<BigInt> {
    match poly.len() {
        0 => Some(BigInt::zero()),
        1 => poly.get(&Vec::new()).cloned(),
        _ => None,
    }
}

/// Whether `c = 0` makes `(REL r 0)` false whatever integers the atoms
/// denote, read as a polynomial identity: for a monomial `m` of `c` with
/// coefficient `cₘ` (and `rₘ` in `r`), `cₘ·r − rₘ·c` is a constant `K`, so
/// `c = 0` forces `cₘ·r = K` — no integer `r` when `cₘ ∤ K` (then `c` never
/// vanishes), else `r = K/cₘ`, and `(REL K/cₘ 0)` is false. Then `(and (= c
/// 0) (REL r 0))`, the exact elimination of `∀v. (c·v + r REL 0)`, is false:
/// `∀v. (v·f(a) + f(a) < 0)` (`c = r = f(a)`) and `∀v. (v·(w + 3) + w − 4 =
/// 0)` (`c = 0` forces `r = −7`) are refuted like a never-vanishing
/// coefficient. `false` when `c` has no symbolic monomial or the difference
/// is not a constant.
pub(super) fn vanishing_falsifies_rest(c: &IntPoly, r: &IntPoly, relation: &str) -> bool {
    let Some((monomial, c_m)) = c.iter().find(|(monomial, _)| !monomial.is_empty()) else {
        return false;
    };
    let r_m = r.get(monomial).cloned().unwrap_or_else(BigInt::zero);
    let difference = poly_mul(&poly_constant(c_m.clone()), r)
        .zip(poly_mul(&poly_constant(r_m), c))
        .and_then(|(scaled_r, scaled_c)| poly_sub(scaled_r, &scaled_c));
    let Some(k) = difference.as_ref().and_then(poly_numeral) else {
        return false;
    };
    if !(&k % c_m).is_zero() {
        return true;
    }
    let r_at_vanishing = k / c_m;
    let holds = match relation {
        "=" => r_at_vanishing.is_zero(),
        "<" => r_at_vanishing < BigInt::zero(),
        "<=" => r_at_vanishing <= BigInt::zero(),
        ">" => r_at_vanishing > BigInt::zero(),
        ">=" => r_at_vanishing >= BigInt::zero(),
        _ => return false,
    };
    !holds
}

/// Whether `k0 + Σ kₘ·m` has no integer zero: the gcd of the `kₘ` does not
/// divide `k0` (or there is no `m` and `k0 ≠ 0`). Every monomial is a
/// product of `Int`-valued atoms, so whatever integers they denote the sum
/// is then never 0 — `2w − 1` and `4wz + 1` never vanish.
pub(super) fn poly_never_vanishes(poly: &IntPoly) -> bool {
    let constant = poly.get(&Vec::new()).cloned().unwrap_or_else(BigInt::zero);
    let divisor = poly
        .iter()
        .filter(|(monomial, _)| !monomial.is_empty())
        .fold(BigInt::zero(), |g, (_, k)| g.gcd(k));
    if divisor.is_zero() {
        return !constant.is_zero();
    }
    !(constant % divisor).is_zero()
}

#[cfg(test)]
mod tests {
    use ay_core::TermId;
    use num_bigint::BigInt;

    use super::{vanishing_falsifies_rest, IntPoly};

    fn poly(terms: &[(&[u32], i64)]) -> IntPoly {
        terms
            .iter()
            .map(|(monomial, k)| {
                let monomial = monomial.iter().map(|&id| TermId::new(id)).collect();
                (monomial, BigInt::from(*k))
            })
            .collect()
    }

    /// `c = 2m − 2`, `r = m`: `2r − c = 2`, so `c = 0` forces `r = 1`. With
    /// `c = 2m + 1` the identity `2r − c = −1` has no integer solution at `c =
    /// 0` (`2 ∤ −1`): `c` never vanishes and every relation refutes.
    #[test]
    fn the_polynomial_identity_decides_the_rest_at_a_vanishing_coefficient() {
        let c = poly(&[(&[7], 2), (&[], -2)]);
        let r = poly(&[(&[7], 1)]);
        assert!(vanishing_falsifies_rest(&c, &r, "="), "c = 0 forces r = 1");
        assert!(!vanishing_falsifies_rest(&c, &r, ">"), "r = 1 > 0 holds");
        let c = poly(&[(&[7], 2), (&[], 1)]);
        for relation in ["=", "<", "<=", ">", ">="] {
            assert!(
                vanishing_falsifies_rest(&c, &r, relation),
                "2m + 1 never vanishes over the integers ({relation})"
            );
        }
        // A rest that does not follow the coefficient: undecided.
        let r = poly(&[(&[7], 1), (&[9], 1)]);
        assert!(!vanishing_falsifies_rest(&c, &r, "="));
    }
}
