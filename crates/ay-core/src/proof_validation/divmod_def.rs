// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Shape and validity of one atom of a FRESH div/mod PURIFICATION definition.
//!
//! The executor eliminates `(div x k)` / `(mod x k)` for a non-zero integer
//! literal `k` by minting a quotient `q` and a remainder `r` the problem never
//! mentions and asserting the SMT-LIB definition of the pair:
//!
//! ```text
//! x = k*q + r      0 <= r      r < |k|
//! ```
//!
//! None of the three atoms is authored and none is a tautology (`x = 2*q + r`
//! is false at `q = r = 0, x = 1`), so before this rule each one reached a
//! published proof as a premiseless `trust` step that strict certification
//! refuses. They are sound for the same reason `fresh_def_eq` is: `q` and `r`
//! are FRESH, so any model of the problem extends to one that also satisfies
//! the atoms, here by `q := (div x k)` and `r := (mod x k)`. That is exactly
//! the SMT-LIB `Ints` definition of `div` and `mod` for a non-zero divisor.
//!
//! The step is `(cl atom)` with `:args (q D r M)`, where `D` and `M` are the
//! TERMS `q` and `r` are defined by. This module decides the LOCAL half: that
//! `atom` is VALID once `q` and `r` are replaced by `D` and `M`. It knows
//! nothing about freshness, one definiens per symbol, or independence; those
//! are whole-proof properties `ay_proof`'s `FreshDefRegistry` decides, over the
//! same map as `fresh_def_bound` and `fresh_def_eq`.
//!
//! # What VALID means here, and why each case is sound
//!
//! Both sides of the atom are read as integer linear forms over opaque atoms
//! (`farkas::parse_linear_expr`), and `q`/`r` are replaced by the linear forms
//! of `D`/`M`. A `div`/`mod` application is one opaque atom. The atom is
//! accepted only in these cases:
//!
//! * an EQUALITY whose difference is identically zero — an identity over
//!   arbitrary values of every opaque atom, hence true under any assignment;
//! * an EQUALITY whose difference is a non-zero multiple of
//!   `x - k*(div x k) - (mod x k)`, when `D` is `(div x k)` and `M` is
//!   `(mod x k)` over the SAME `x` and literal `k != 0`: the SMT-LIB
//!   definition makes that form zero;
//! * a COMPARISON whose slack is a constant meeting the bound, or is
//!   `a*(mod x k) + c` alone (with `M` that application, `a` and `c`
//!   integers) and meets the bound at both ends of `0 <= (mod x k) <= |k|-1` —
//!   it is linear in the remainder, so its minimum is at an end.
//!
//! Folded definientia need no special case. `mk_intdiv`/`mk_mod` fold a
//! literal dividend to the Euclidean literals, and a divisor `1` to `x`/`0`;
//! the substituted atom is then an identity or a constant comparison, which
//! the first and third cases decide by arithmetic alone.
//!
//! Everything else fails closed: a `(div x k)` under a comparison (a quotient
//! has no range), a symbolic or zero divisor, a dividend that differs between
//! `D` and `M`, a non-integer coefficient, an atom mentioning neither symbol.

use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};

use super::farkas::{parse_linear_expr, LinearExpr};
use crate::term::{Constant, Symbol, TermData};
use crate::{Sort, TermId, TermStore};

/// A well-formed div/mod purification step, decomposed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DivModDefShape {
    /// The fresh quotient symbol.
    pub quotient: TermId,
    /// The term the quotient is defined by.
    pub quotient_definiens: TermId,
    /// The fresh remainder symbol.
    pub remainder: TermId,
    /// The term the remainder is defined by.
    pub remainder_definiens: TermId,
    /// The step's single clause literal.
    pub atom: TermId,
}

/// Why a candidate step is not a valid div/mod purification atom.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DivModDefShapeError {
    /// The step carries premises; a definition is derived from nothing.
    HasPremises,
    /// The step does not carry exactly the four `:args` `(q D r M)`.
    ArgArity(usize),
    /// The clause is not exactly one literal.
    ClauseArity(usize),
    /// `q` or `r` is not an atomic `Int` variable, or they are one symbol.
    NotTwoIntSymbols,
    /// A definiens is not `Int`-sorted.
    DefiniensSort,
    /// The atom mentions neither defined symbol.
    MentionsNeitherSymbol,
    /// The atom is not valid once `q := D` and `r := M`.
    NotValid,
}

impl std::fmt::Display for DivModDefShapeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::HasPremises => write!(f, "a div/mod definition must have no premises"),
            Self::ArgArity(n) => write!(
                f,
                "a div/mod definition must carry `:args (q D r M)`, got {n} terms"
            ),
            Self::ClauseArity(n) => write!(
                f,
                "a div/mod definition must conclude exactly one literal, got {n}"
            ),
            Self::NotTwoIntSymbols => write!(
                f,
                "a div/mod definition must define two distinct atomic `Int` symbols"
            ),
            Self::DefiniensSort => write!(f, "a div/mod definiens must be `Int`-sorted"),
            Self::MentionsNeitherSymbol => write!(
                f,
                "a div/mod definition's atom must mention its quotient or remainder"
            ),
            Self::NotValid => write!(
                f,
                "the atom is not valid with the quotient and remainder replaced by their \
                 definientia"
            ),
        }
    }
}

/// Decompose and validate one candidate `divmod_def` step.
///
/// # Errors
///
/// Returns the first local condition the step fails. Freshness, one definiens
/// per symbol and independence are whole-proof properties and are NOT decided
/// here.
pub fn recognize_divmod_def(
    terms: &TermStore,
    clause: &[TermId],
    premise_count: usize,
    args: &[TermId],
) -> Result<DivModDefShape, DivModDefShapeError> {
    if premise_count != 0 {
        return Err(DivModDefShapeError::HasPremises);
    }
    let &[quotient, quotient_definiens, remainder, remainder_definiens] = args else {
        return Err(DivModDefShapeError::ArgArity(args.len()));
    };
    let &[atom] = clause else {
        return Err(DivModDefShapeError::ClauseArity(clause.len()));
    };
    let int_symbol = |term: TermId| match terms.get(term) {
        TermData::Var(name, _) if matches!(terms.sort(term), Sort::Int) => Some(name),
        _ => None,
    };
    match (int_symbol(quotient), int_symbol(remainder)) {
        (Some(q), Some(r)) if q != r => {}
        _ => return Err(DivModDefShapeError::NotTwoIntSymbols),
    }
    if !matches!(terms.sort(quotient_definiens), Sort::Int)
        || !matches!(terms.sort(remainder_definiens), Sort::Int)
    {
        return Err(DivModDefShapeError::DefiniensSort);
    }
    let definition = Definition {
        quotient,
        quotient_form: parse_linear_expr(terms, quotient_definiens),
        remainder,
        remainder_form: parse_linear_expr(terms, remainder_definiens),
        euclid: euclidean_pair(terms, quotient_definiens, remainder_definiens),
    };
    definition.decide(terms, atom)?;
    Ok(DivModDefShape {
        quotient,
        quotient_definiens,
        remainder,
        remainder_definiens,
        atom,
    })
}

/// `(div x k)` and `(mod x k)` over one dividend and one non-zero literal.
struct EuclideanPair {
    /// The opaque remainder atom `(mod x k)`.
    remainder: TermId,
    /// `|k| - 1`, the largest remainder.
    top: BigInt,
    /// The linear form of `x - k*(div x k) - (mod x k)`, zero by definition.
    definition: LinearExpr,
}

fn euclidean_pair(terms: &TermStore, quotient: TermId, remainder: TermId) -> Option<EuclideanPair> {
    let operands = |term: TermId, head: &str| match terms.get(term) {
        TermData::App(Symbol::Named(name), args) if name == head && args.len() == 2 => {
            Some((args[0], args[1]))
        }
        _ => None,
    };
    let (dividend, divisor) = operands(quotient, "div")?;
    if operands(remainder, "mod")? != (dividend, divisor) {
        return None;
    }
    if !matches!(terms.sort(dividend), Sort::Int) {
        return None;
    }
    let TermData::Const(Constant::Int(divisor)) = terms.get(divisor) else {
        return None;
    };
    if divisor.is_zero() {
        return None;
    }
    let mut definition = parse_linear_expr(terms, dividend);
    definition.add_scaled(
        &atom_form(quotient),
        &BigRational::from_integer(-divisor.clone()),
    );
    definition.add_scaled(&atom_form(remainder), &-BigRational::one());
    Some(EuclideanPair {
        remainder,
        top: divisor.abs() - BigInt::one(),
        definition,
    })
}

/// The linear form of one opaque atom.
fn atom_form(atom: TermId) -> LinearExpr {
    LinearExpr {
        coeffs: std::collections::BTreeMap::from([(atom, BigRational::one())]),
        constant: BigRational::zero(),
    }
}

struct Definition {
    quotient: TermId,
    quotient_form: LinearExpr,
    remainder: TermId,
    remainder_form: LinearExpr,
    euclid: Option<EuclideanPair>,
}

impl Definition {
    fn decide(&self, terms: &TermStore, atom: TermId) -> Result<(), DivModDefShapeError> {
        let TermData::App(Symbol::Named(op), operands) = terms.get(atom) else {
            return Err(DivModDefShapeError::NotValid);
        };
        let &[lhs, rhs] = operands.as_slice() else {
            return Err(DivModDefShapeError::NotValid);
        };
        if !matches!(terms.sort(lhs), Sort::Int) || !matches!(terms.sort(rhs), Sort::Int) {
            return Err(DivModDefShapeError::NotValid);
        }
        let (high, low, need) = match op.as_str() {
            "=" => (lhs, rhs, None),
            "<=" => (rhs, lhs, Some(0)),
            "<" => (rhs, lhs, Some(1)),
            ">=" => (lhs, rhs, Some(0)),
            ">" => (lhs, rhs, Some(1)),
            _ => return Err(DivModDefShapeError::NotValid),
        };
        let mut slack = parse_linear_expr(terms, high);
        let mut low = parse_linear_expr(terms, low);
        low.negate();
        slack.add_scaled(&low, &BigRational::one());
        if !slack.coeffs.contains_key(&self.quotient) && !slack.coeffs.contains_key(&self.remainder)
        {
            return Err(DivModDefShapeError::MentionsNeitherSymbol);
        }
        let slack = self.substitute(slack);
        let valid = match need {
            None => self.is_valid_equality(&slack),
            Some(need) => self.is_valid_lower_bound(&slack, &BigInt::from(need)),
        };
        valid.then_some(()).ok_or(DivModDefShapeError::NotValid)
    }

    /// `form` with each defined symbol replaced by its definiens' form.
    fn substitute(&self, mut form: LinearExpr) -> LinearExpr {
        for (symbol, definiens) in [
            (self.quotient, &self.quotient_form),
            (self.remainder, &self.remainder_form),
        ] {
            if let Some(coeff) = form.coeffs.remove(&symbol) {
                form.add_scaled(definiens, &coeff);
            }
        }
        form
    }

    /// `slack = 0` is valid: an identity, or a multiple of the SMT-LIB
    /// definition `x - k*(div x k) - (mod x k) = 0`.
    fn is_valid_equality(&self, slack: &LinearExpr) -> bool {
        if is_zero_form(slack) {
            return true;
        }
        let Some(euclid) = &self.euclid else {
            return false;
        };
        // The definition's remainder coefficient is -1, so the only multiple
        // `c` that can cancel the slack's is `c = -slack[mod]`, and
        // `slack - c * definition` must vanish.
        let Some(remainder_coeff) = slack.coeffs.get(&euclid.remainder).cloned() else {
            return false;
        };
        let mut residue = slack.clone();
        residue.add_scaled(&euclid.definition, &remainder_coeff);
        is_zero_form(&residue)
    }

    /// `slack >= need` holds for every value of every atom it mentions.
    fn is_valid_lower_bound(&self, slack: &LinearExpr, need: &BigInt) -> bool {
        let Some(constant) = integer(&slack.constant) else {
            return false;
        };
        match slack.coeffs.len() {
            0 => &constant >= need,
            1 => {
                let Some(euclid) = &self.euclid else {
                    return false;
                };
                let Some(coeff) = slack.coeffs.get(&euclid.remainder).and_then(integer) else {
                    return false;
                };
                let at_top = &coeff * &euclid.top + &constant;
                &constant >= need && &at_top >= need
            }
            _ => false,
        }
    }
}

fn integer(value: &BigRational) -> Option<BigInt> {
    value.is_integer().then(|| value.to_integer())
}

fn is_zero_form(form: &LinearExpr) -> bool {
    form.constant.is_zero() && form.coeffs.values().all(Zero::is_zero)
}
