// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Semantic verification of mixed Int/Real arithmetic conflicts.
//!
//! No fresh single-sort solver is FAITHFUL on a conflict that mixes the two
//! numeric sorts: the LIA verifier leaves Real atoms uninterpreted and the LRA
//! verifier drops integrality, so a `Sat` from either may be a false positive
//! on a valid bridged conflict (#6853: the AUFLIRA archimedean_nat regression,
//! where rejecting such a conflict degraded a decidable query to `unknown`).
//! That is why these conflicts used to be accepted with no check at all, and
//! that is how the LIA lane's dropped-constant conflict
//! `{ not (= (to_real c) (+ (to_real c) 1/2)) }` — the negation of a VALID
//! literal — was learned and turned a satisfiable QSAT kernel query UNSAT.
//!
//! The check here is faithful in each direction it answers, and answers
//! nothing else:
//!
//! 1. A fresh LRA solve over the literals is a RELAXATION of them: LRA reads
//!    `to_real x` as `x`, abstracts what it cannot interpret as free columns,
//!    and drops only integrality, so every model of the literals is a model of
//!    the relaxation. Relaxation UNSAT is therefore UNSAT: `Reproved`.
//! 2. When the relaxation is SAT, its model is only a CANDIDATE. It refutes
//!    the conflict only after an exact re-evaluation shows it is a genuine
//!    model: every Int-sorted leaf integral and every literal, evaluated
//!    exactly with `to_real`/`to_int`/`is_int` interpreted, at its asserted
//!    polarity. That is a satisfying assignment of the literal set, so the
//!    conflict is spurious: `ConflictIsSat`.
//! 3. Anything else — a fractional Int value (an integer-gap conflict), a term
//!    the evaluator does not interpret, a split request — stays
//!    `AcceptedUnchecked`, exactly as before. A VALID conflict has no model,
//!    so step 2 can never reject one: the #6853 completeness is kept.

use ay_core::kani_compat::DetHashMap;
use ay_core::{Constant, Sort, Symbol, TermData, TermId, TermStore, TheoryLit};
use ay_lra::LraSolver;
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{Signed, Zero};

use super::dispatch::ConflictSemanticVerdict;
use super::VerificationError;

/// Verify a mixed Int/Real arithmetic literal set (see the module docs).
pub(super) fn verify_int_real_mix_conflict(
    context: &[TheoryLit],
    terms: &TermStore,
) -> Result<ConflictSemanticVerdict, VerificationError> {
    use ay_core::{TheoryResult, TheorySolver};

    ay_lia::instrument::bump_verify_fresh_lra_solve();
    let mut relaxation = LraSolver::new(terms);
    // #8257: verification mode skips post-simplex propagation.
    relaxation.set_verification_mode();
    for lit in context {
        relaxation.register_atom(lit.term);
    }
    for lit in context {
        relaxation.assert_literal(lit.term, lit.value);
    }

    match relaxation.check() {
        TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_) => {
            Ok(ConflictSemanticVerdict::Reproved)
        }
        TheoryResult::Sat => {
            let mut witness = Witness {
                terms,
                relaxation: &relaxation,
                memo: DetHashMap::default(),
            };
            if context
                .iter()
                .all(|lit| witness.eval_bool(lit.term, EVAL_FUEL) == Some(lit.value))
            {
                tracing::debug!(
                    lit_count = context.len(),
                    "mixed int/real conflict refuted: the LRA relaxation's model is an \
                     exact, integral model of every literal"
                );
                Err(VerificationError::ConflictIsSat)
            } else {
                tracing::debug!(
                    lit_count = context.len(),
                    "mixed int/real conflict accepted unchecked: the LRA relaxation is SAT \
                     but its model is not an exact integral witness (#6853 completeness)"
                );
                Ok(ConflictSemanticVerdict::AcceptedUnchecked)
            }
        }
        _ => Ok(ConflictSemanticVerdict::AcceptedUnchecked),
    }
}

/// Recursion budget for one literal: conflict atoms are shallow linear terms.
const EVAL_FUEL: u32 = 64;

/// Exact evaluation of arithmetic literals under the relaxation's model.
/// `None` means "not interpreted here", never a guess.
struct Witness<'a> {
    terms: &'a TermStore,
    relaxation: &'a LraSolver,
    memo: DetHashMap<TermId, Option<BigRational>>,
}

impl Witness<'_> {
    /// The candidate value of a numeric leaf. A leaf the relaxation never
    /// saw is unconstrained by it; zero is as good a candidate as any (the
    /// exact re-evaluation is what decides). An Int-sorted leaf must be
    /// integral, or the candidate is no model at all.
    fn leaf(&mut self, term: TermId) -> Option<BigRational> {
        if let Some(value) = self.memo.get(&term) {
            return value.clone();
        }
        let value = match self.terms.sort(term) {
            Sort::Int | Sort::Real => {
                let value = self
                    .relaxation
                    .get_value(term)
                    .unwrap_or_else(BigRational::zero);
                (!matches!(self.terms.sort(term), Sort::Int) || value.is_integer()).then_some(value)
            }
            _ => None,
        };
        self.memo.insert(term, value.clone());
        value
    }

    fn eval_num(&mut self, term: TermId, fuel: u32) -> Option<BigRational> {
        let fuel = fuel.checked_sub(1)?;
        let terms = self.terms;
        match terms.get(term) {
            TermData::Const(Constant::Int(n)) => Some(BigRational::from_integer(n.clone())),
            TermData::Const(Constant::Rational(r)) => Some(r.0.clone()),
            TermData::Var(..) => self.leaf(term),
            TermData::Ite(cond, then_t, else_t) => {
                let (cond, then_t, else_t) = (*cond, *then_t, *else_t);
                if self.eval_bool(cond, fuel)? {
                    self.eval_num(then_t, fuel)
                } else {
                    self.eval_num(else_t, fuel)
                }
            }
            TermData::App(Symbol::Named(name), args) => {
                let args = args.clone();
                match (name.as_str(), args.as_slice()) {
                    ("+", _) => args.iter().try_fold(BigRational::zero(), |acc, &a| {
                        Some(acc + self.eval_num(a, fuel)?)
                    }),
                    ("-", [a]) => Some(-self.eval_num(*a, fuel)?),
                    ("-", [first, rest @ ..]) => {
                        let mut acc = self.eval_num(*first, fuel)?;
                        for &a in rest {
                            acc -= self.eval_num(a, fuel)?;
                        }
                        Some(acc)
                    }
                    ("*", _) => args
                        .iter()
                        .try_fold(BigRational::from_integer(BigInt::from(1)), |acc, &a| {
                            Some(acc * self.eval_num(a, fuel)?)
                        }),
                    ("/", [first, rest @ ..]) if !rest.is_empty() => {
                        let mut acc = self.eval_num(*first, fuel)?;
                        for &a in rest {
                            let divisor = self.eval_num(a, fuel)?;
                            // Division by zero is an uninterpreted value in
                            // SMT-LIB: not something to evaluate here.
                            if divisor.is_zero() {
                                return None;
                            }
                            acc /= divisor;
                        }
                        Some(acc)
                    }
                    ("to_real", [a]) => self.eval_num(*a, fuel),
                    ("to_int", [a]) => Some(BigRational::from_integer(
                        self.eval_num(*a, fuel)?.floor().to_integer(),
                    )),
                    ("abs", [a]) => Some(self.eval_num(*a, fuel)?.abs()),
                    _ => None,
                }
            }
            _ => None,
        }
    }

    fn eval_bool(&mut self, term: TermId, fuel: u32) -> Option<bool> {
        let fuel = fuel.checked_sub(1)?;
        let terms = self.terms;
        match terms.get(term) {
            TermData::Const(Constant::Bool(b)) => Some(*b),
            TermData::Not(inner) => {
                let inner = *inner;
                Some(!self.eval_bool(inner, fuel)?)
            }
            TermData::App(Symbol::Named(name), args) => {
                let args = args.clone();
                match (name.as_str(), args.as_slice()) {
                    ("<" | "<=" | ">" | ">=", [_, _, ..]) => {
                        let op = name.clone();
                        let values = self.eval_all(&args, fuel)?;
                        Some(values.windows(2).all(|pair| match op.as_str() {
                            "<" => pair[0] < pair[1],
                            "<=" => pair[0] <= pair[1],
                            ">" => pair[0] > pair[1],
                            _ => pair[0] >= pair[1],
                        }))
                    }
                    ("=", [first, _, ..]) if is_numeric(terms.sort(*first)) => {
                        let values = self.eval_all(&args, fuel)?;
                        Some(values.windows(2).all(|pair| pair[0] == pair[1]))
                    }
                    ("distinct", [first, _, ..]) if is_numeric(terms.sort(*first)) => {
                        let values = self.eval_all(&args, fuel)?;
                        Some(
                            values
                                .iter()
                                .enumerate()
                                .all(|(i, v)| values[i + 1..].iter().all(|w| v != w)),
                        )
                    }
                    ("is_int", [a]) => Some(self.eval_num(*a, fuel)?.is_integer()),
                    _ => None,
                }
            }
            _ => None,
        }
    }

    fn eval_all(&mut self, args: &[TermId], fuel: u32) -> Option<Vec<BigRational>> {
        args.iter().map(|&a| self.eval_num(a, fuel)).collect()
    }
}

fn is_numeric(sort: &Sort) -> bool {
    matches!(sort, Sort::Int | Sort::Real)
}
