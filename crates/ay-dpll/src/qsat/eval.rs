// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact evaluation of the engine's quantifier-free terms under a model.
//!
//! Rationals throughout; SMT-LIB Euclidean `div`/`mod` with a non-zero
//! integral divisor. Anything outside the fragment evaluates to `None`.

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::term::{Constant, TermData};
use ay_core::{Sort, TermId, TermStore};
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};

use super::lin::{euclid_div, euclid_rem, Model, Val};

/// Exact evaluator with a per-walk memo.
pub(crate) struct Eval<'a> {
    pub(crate) terms: &'a TermStore,
    pub(crate) model: &'a Model,
    memo: HashMap<TermId, Val>,
    work: usize,
}

/// Evaluation work bound per walk (distinct nodes).
const MAX_EVAL_WORK: usize = 4_000_000;

impl<'a> Eval<'a> {
    pub(crate) fn new(terms: &'a TermStore, model: &'a Model) -> Self {
        Self {
            terms,
            model,
            memo: HashMap::default(),
            work: 0,
        }
    }

    pub(crate) fn boolean(&mut self, t: TermId) -> Option<bool> {
        self.value(t)?.boolean()
    }

    pub(crate) fn number(&mut self, t: TermId) -> Option<BigRational> {
        self.value(t)?.num().cloned()
    }

    pub(crate) fn value(&mut self, t: TermId) -> Option<Val> {
        if let Some(v) = self.memo.get(&t) {
            return Some(v.clone());
        }
        self.work += 1;
        if self.work > MAX_EVAL_WORK {
            return None;
        }
        let v = stacker::maybe_grow(64 * 1024, 4 * 1024 * 1024, || self.compute(t))?;
        self.memo.insert(t, v.clone());
        Some(v)
    }

    fn compute(&mut self, t: TermId) -> Option<Val> {
        let terms = self.terms;
        match terms.get(t) {
            TermData::Const(Constant::Bool(b)) => Some(Val::Bool(*b)),
            TermData::Const(Constant::Int(n)) => {
                Some(Val::Num(BigRational::from_integer(n.clone())))
            }
            TermData::Const(Constant::Rational(r)) => Some(Val::Num(r.0.clone())),
            TermData::Const(_) => None,
            TermData::Var(..) => self.model.vals.get(&t).cloned(),
            TermData::Not(inner) => Some(Val::Bool(!self.boolean(*inner)?)),
            TermData::Ite(c, a, b) => {
                let (c, a, b) = (*c, *a, *b);
                if self.boolean(c)? {
                    self.value(a)
                } else {
                    self.value(b)
                }
            }
            TermData::App(sym, args) => {
                let args = args.clone();
                let name = sym.name().to_string();
                if args.is_empty() {
                    // A declared constant spelled as a nullary application.
                    return self.model.vals.get(&t).cloned();
                }
                self.app(&name, &args, terms.sort(t).clone())
            }
            _ => None,
        }
    }

    fn nums(&mut self, args: &[TermId]) -> Option<Vec<BigRational>> {
        args.iter().map(|&a| self.number(a)).collect()
    }

    fn app(&mut self, name: &str, args: &[TermId], sort: Sort) -> Option<Val> {
        let _ = sort;
        match name {
            "and" | "or" | "not" | "=>" | "xor" | "=" | "distinct" | "ite" => {
                self.bool_app(name, args)
            }
            _ => self.arith_app(name, args),
        }
    }

    /// Connectives, equality and `ite`.
    fn bool_app(&mut self, name: &str, args: &[TermId]) -> Option<Val> {
        let b = |v: bool| Some(Val::Bool(v));
        match name {
            "and" => {
                for &a in args {
                    if !self.boolean(a)? {
                        return b(false);
                    }
                }
                b(true)
            }
            "or" => {
                for &a in args {
                    if self.boolean(a)? {
                        return b(true);
                    }
                }
                b(false)
            }
            "not" if args.len() == 1 => b(!self.boolean(args[0])?),
            "=>" => {
                let (last, prem) = args.split_last()?;
                for &p in prem {
                    if !self.boolean(p)? {
                        return b(true);
                    }
                }
                b(self.boolean(*last)?)
            }
            "xor" => {
                let mut acc = false;
                for &a in args {
                    acc ^= self.boolean(a)?;
                }
                b(acc)
            }
            "=" | "distinct" => {
                let vals: Vec<Val> = args.iter().map(|&a| self.value(a)).collect::<Option<_>>()?;
                if name == "=" {
                    b(vals.windows(2).all(|w| w[0] == w[1]))
                } else {
                    b(vals
                        .iter()
                        .enumerate()
                        .all(|(i, x)| vals[i + 1..].iter().all(|y| x != y)))
                }
            }
            "ite" if args.len() == 3 => {
                if self.boolean(args[0])? {
                    self.value(args[1])
                } else {
                    self.value(args[2])
                }
            }
            _ => None,
        }
    }

    /// Comparisons and arithmetic.
    fn arith_app(&mut self, name: &str, args: &[TermId]) -> Option<Val> {
        let b = |v: bool| Some(Val::Bool(v));
        match name {
            "<" | "<=" | ">" | ">=" => {
                let v = self.nums(args)?;
                if v.len() < 2 {
                    return None;
                }
                b(v.windows(2).all(|w| match name {
                    "<" => w[0] < w[1],
                    "<=" => w[0] <= w[1],
                    ">" => w[0] > w[1],
                    _ => w[0] >= w[1],
                }))
            }
            "+" => {
                let v = self.nums(args)?;
                Some(Val::Num(
                    v.into_iter().fold(BigRational::zero(), |a, x| a + x),
                ))
            }
            "-" => {
                let v = self.nums(args)?;
                if v.len() == 1 {
                    return Some(Val::Num(-v[0].clone()));
                }
                let mut it = v.into_iter();
                let first = it.next()?;
                Some(Val::Num(it.fold(first, |a, x| a - x)))
            }
            "*" => {
                let v = self.nums(args)?;
                Some(Val::Num(
                    v.into_iter().fold(BigRational::one(), |a, x| a * x),
                ))
            }
            "/" => {
                let v = self.nums(args)?;
                let mut it = v.into_iter();
                let mut acc = it.next()?;
                for x in it {
                    if x.is_zero() {
                        return None;
                    }
                    acc /= x;
                }
                Some(Val::Num(acc))
            }
            "div" | "mod" if args.len() == 2 => {
                let v = self.nums(args)?;
                if !v[0].is_integer() || !v[1].is_integer() || v[1].is_zero() {
                    return None;
                }
                let (n, d) = (v[0].to_integer(), v[1].to_integer());
                let r = if name == "div" {
                    euclid_div(&n, &d)
                } else {
                    euclid_rem(&n, &d)
                };
                Some(Val::Num(BigRational::from_integer(r)))
            }
            "abs" if args.len() == 1 => Some(Val::Num(self.number(args[0])?.abs())),
            "to_real" if args.len() == 1 => Some(Val::Num(self.number(args[0])?)),
            "to_int" if args.len() == 1 => Some(Val::Num(BigRational::from_integer(
                self.number(args[0])?.floor().to_integer(),
            ))),
            "is_int" if args.len() == 1 => b(self.number(args[0])?.is_integer()),
            _ => None,
        }
    }
}
