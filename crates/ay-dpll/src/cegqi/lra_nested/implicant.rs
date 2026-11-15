// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Model evaluation and implicant extraction (plan §3.4 step 1).
//!
//! `implicant(t, want, I)` returns linear literals, each TRUE in `I`, whose
//! conjunction implies `t = want` under the Boolean structure of `t`. Every
//! arithmetic atom is normalized with the shared [`LinRat`] form. Anything
//! outside linear real arithmetic over Bool connectives answers `None`, which
//! the caller turns into a decline (Risk R8).

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::term::{Constant, TermData};
use ay_core::{Sort, TermId, TermStore};
use num_rational::BigRational;
use num_traits::Zero;

use crate::qe::cooper::Rel;
use crate::qe::linrat::{parse_lin, LinRat};

/// A model restricted to the variables the search asked for.
#[derive(Clone, Debug, Default)]
pub(crate) struct Assignment {
    pub(crate) reals: HashMap<TermId, BigRational>,
    pub(crate) bools: HashMap<TermId, bool>,
}

/// A normalized arithmetic literal `lin ⋈ 0`.
pub(crate) type LinLit = (Rel, LinRat);

/// Whether `lit` holds under `reals`; `None` if a variable is unassigned.
pub(crate) fn lit_holds(lit: &LinLit, reals: &HashMap<TermId, BigRational>) -> Option<bool> {
    let assign: std::collections::HashMap<TermId, BigRational> = lit
        .1
        .coeffs
        .keys()
        .filter_map(|v| Some((*v, reals.get(v)?.clone())))
        .collect();
    let value = lit.1.eval(&assign)?;
    Some(match lit.0 {
        Rel::Le => value <= BigRational::zero(),
        Rel::Lt => value < BigRational::zero(),
        Rel::Eq => value.is_zero(),
        Rel::Ne => !value.is_zero(),
    })
}

/// Evaluates and extracts under one assignment, with a work budget.
pub(crate) struct Walker<'a> {
    pub(crate) terms: &'a TermStore,
    pub(crate) model: &'a Assignment,
    /// Counterexample constants: implicant choices prefer children that
    /// mention fewer of them.
    pub(crate) ce_vars: &'a [TermId],
    pub(crate) work: usize,
    pub(crate) max_work: usize,
}

impl Walker<'_> {
    fn tick(&mut self) -> Option<()> {
        self.work += 1;
        (self.work <= self.max_work).then_some(())
    }

    fn real(&mut self, term: TermId) -> Option<BigRational> {
        self.tick()?;
        let lin = parse_lin(self.terms, term)?;
        let assign: std::collections::HashMap<TermId, BigRational> = lin
            .coeffs
            .keys()
            .filter_map(|v| Some((*v, self.model.reals.get(v)?.clone())))
            .collect();
        lin.eval(&assign)
    }

    /// Whether an `=`/`distinct` over `args` is arithmetic (any Real side;
    /// numerals may be Int-sorted).
    fn is_real_eq(&self, args: &[TermId]) -> bool {
        args.iter()
            .any(|&a| matches!(self.terms.sort(a), Sort::Real))
    }

    /// Truth value of a Bool-sorted `term`.
    pub(crate) fn eval(&mut self, term: TermId) -> Option<bool> {
        self.tick()?;
        match self.terms.get(term).clone() {
            TermData::Const(Constant::Bool(b)) => Some(b),
            TermData::Var(..) => self.model.bools.get(&term).copied(),
            TermData::Not(inner) => Some(!self.eval(inner)?),
            TermData::Ite(c, a, b) => {
                let branch = if self.eval(c)? { a } else { b };
                self.eval(branch)
            }
            TermData::App(symbol, args) => self.eval_app(symbol.name(), &args),
            _ => None,
        }
    }

    fn eval_app(&mut self, name: &str, args: &[TermId]) -> Option<bool> {
        match name {
            "and" => {
                for &arg in args {
                    if !self.eval(arg)? {
                        return Some(false);
                    }
                }
                Some(true)
            }
            "or" => {
                for &arg in args {
                    if self.eval(arg)? {
                        return Some(true);
                    }
                }
                Some(false)
            }
            "=>" => {
                let (last, premises) = args.split_last()?;
                for &premise in premises {
                    if !self.eval(premise)? {
                        return Some(true);
                    }
                }
                self.eval(*last)
            }
            "xor" => {
                let mut acc = false;
                for &arg in args {
                    acc ^= self.eval(arg)?;
                }
                Some(acc)
            }
            "=" | "distinct" if self.is_real_eq(args) => {
                let values: Vec<BigRational> =
                    args.iter().map(|&a| self.real(a)).collect::<Option<_>>()?;
                if name == "=" {
                    Some(values.windows(2).all(|w| w[0] == w[1]))
                } else {
                    Some(all_distinct(&values))
                }
            }
            "=" | "distinct" => {
                let values: Vec<bool> =
                    args.iter().map(|&a| self.eval(a)).collect::<Option<_>>()?;
                if name == "=" {
                    Some(values.windows(2).all(|w| w[0] == w[1]))
                } else {
                    Some(all_distinct(&values))
                }
            }
            "<" | "<=" | ">" | ">=" => {
                let values: Vec<BigRational> =
                    args.iter().map(|&a| self.real(a)).collect::<Option<_>>()?;
                if values.len() < 2 {
                    return None;
                }
                Some(values.windows(2).all(|w| compare(name, &w[0], &w[1])))
            }
            _ => None,
        }
    }

    /// Number of counterexample constants syntactically below `term`
    /// (bounded; saturates at the work cap).
    fn ce_weight(&mut self, term: TermId) -> usize {
        let mut count = 0;
        let mut stack = vec![term];
        let mut seen = ay_core::kani_compat::DetHashSet::default();
        while let Some(t) = stack.pop() {
            if !seen.insert(t) || self.tick().is_none() {
                continue;
            }
            if self.ce_vars.contains(&t) {
                count += 1;
            }
            match self.terms.get(t) {
                TermData::App(_, args) => stack.extend(args.iter().copied()),
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(c, a, b) => stack.extend([*c, *a, *b]),
                _ => {}
            }
        }
        count
    }

    /// Append literals true under the model that force `term = want`.
    pub(crate) fn implicant(
        &mut self,
        term: TermId,
        want: bool,
        out: &mut Vec<LinLit>,
    ) -> Option<()> {
        self.tick()?;
        if self.eval(term)? != want {
            return None;
        }
        match self.terms.get(term).clone() {
            TermData::Const(Constant::Bool(_)) | TermData::Var(..) => Some(()),
            TermData::Not(inner) => self.implicant(inner, !want, out),
            TermData::Ite(c, a, b) => {
                let cond = self.eval(c)?;
                self.implicant(c, cond, out)?;
                self.implicant(if cond { a } else { b }, want, out)
            }
            TermData::App(symbol, args) => self.implicant_app(symbol.name(), &args, want, out),
            _ => None,
        }
    }

    fn implicant_app(
        &mut self,
        name: &str,
        args: &[TermId],
        want: bool,
        out: &mut Vec<LinLit>,
    ) -> Option<()> {
        match name {
            // `and` true / `or` false: every child is forced.
            "and" | "or" if want == (name == "and") => {
                for &arg in args {
                    self.implicant(arg, want, out)?;
                }
                Some(())
            }
            // `and` false / `or` true: one witnessing child suffices.
            "and" | "or" => {
                let child = self.cheapest_child(args, want)?;
                self.implicant(child, want, out)
            }
            "=>" => {
                let (last, premises) = args.split_last()?;
                if !want {
                    for &premise in premises {
                        self.implicant(premise, true, out)?;
                    }
                    return self.implicant(*last, false, out);
                }
                // True: a false premise or the true conclusion.
                let mut options: Vec<(TermId, bool)> =
                    premises.iter().map(|&p| (p, false)).collect();
                options.push((*last, true));
                let mut best: Option<(usize, TermId, bool)> = None;
                for (child, value) in options {
                    if self.eval(child)? == value {
                        let weight = self.ce_weight(child);
                        if best.is_none_or(|(w, _, _)| weight < w) {
                            best = Some((weight, child, value));
                        }
                    }
                }
                let (_, child, value) = best?;
                self.implicant(child, value, out)
            }
            "xor" => self.implicant_at_values(args, out),
            "=" | "distinct" if self.is_real_eq(args) => {
                self.implicant_real_eq(name, args, want, out)
            }
            "=" | "distinct" => self.implicant_at_values(args, out),
            "<" | "<=" | ">" | ">=" => self.implicant_chain(name, args, want, out),
            _ => None,
        }
    }

    /// Among `args`, the child evaluating to `value` with the fewest
    /// counterexample constants below it.
    fn cheapest_child(&mut self, args: &[TermId], value: bool) -> Option<TermId> {
        let mut best: Option<(usize, TermId)> = None;
        for &arg in args {
            if self.eval(arg)? == value {
                let weight = self.ce_weight(arg);
                if best.is_none_or(|(w, _)| weight < w) {
                    best = Some((weight, arg));
                }
            }
        }
        best.map(|(_, arg)| arg)
    }

    /// Iff/xor/Bool-distinct: every argument is forced at its model value.
    fn implicant_at_values(&mut self, args: &[TermId], out: &mut Vec<LinLit>) -> Option<()> {
        for &arg in args {
            let value = self.eval(arg)?;
            self.implicant(arg, value, out)?;
        }
        Some(())
    }

    fn implicant_real_eq(
        &mut self,
        name: &str,
        args: &[TermId],
        want: bool,
        out: &mut Vec<LinLit>,
    ) -> Option<()> {
        let pairs: Vec<(TermId, TermId)> = if name == "=" {
            args.windows(2).map(|w| (w[0], w[1])).collect()
        } else {
            let mut all = Vec::new();
            for (i, &a) in args.iter().enumerate() {
                for &b in &args[i + 1..] {
                    all.push((a, b));
                }
            }
            all
        };
        // `=` true or `distinct` true: every pair is forced.
        let forced_all = want;
        let pair_rel = if name == "=" { Rel::Eq } else { Rel::Ne };
        let pair_negated = if name == "=" { Rel::Ne } else { Rel::Eq };
        for (a, b) in pairs {
            let mut lin = parse_lin(self.terms, a)?;
            lin.sub(&parse_lin(self.terms, b)?);
            let lit = (if forced_all { pair_rel } else { pair_negated }, lin);
            let holds = lit_holds(&lit, &self.model.reals)?;
            if forced_all {
                if !holds {
                    return None;
                }
                out.push(lit);
            } else if holds {
                out.push(lit);
                return Some(());
            }
        }
        forced_all.then_some(())
    }

    fn implicant_chain(
        &mut self,
        name: &str,
        args: &[TermId],
        want: bool,
        out: &mut Vec<LinLit>,
    ) -> Option<()> {
        if args.len() < 2 {
            return None;
        }
        for w in args.windows(2) {
            let lit = atom_literal(self.terms, name, w[0], w[1], want)?;
            let holds = lit_holds(&lit, &self.model.reals)?;
            if want {
                if !holds {
                    return None;
                }
                out.push(lit);
            } else if holds {
                out.push(lit);
                return Some(());
            }
        }
        want.then_some(())
    }
}

/// `lhs ⋈ rhs` (or its negation when `!want`) as `lin ⋈' 0`.
pub(crate) fn atom_literal(
    terms: &TermStore,
    name: &str,
    lhs: TermId,
    rhs: TermId,
    want: bool,
) -> Option<LinLit> {
    let l = parse_lin(terms, lhs)?;
    let r = parse_lin(terms, rhs)?;
    let diff = |a: &LinRat, b: &LinRat| {
        let mut d = a.clone();
        d.sub(b);
        d
    };
    Some(match (name, want) {
        ("<=", true) => (Rel::Le, diff(&l, &r)),
        ("<=", false) => (Rel::Lt, diff(&r, &l)),
        ("<", true) => (Rel::Lt, diff(&l, &r)),
        ("<", false) => (Rel::Le, diff(&r, &l)),
        (">=", true) => (Rel::Le, diff(&r, &l)),
        (">=", false) => (Rel::Lt, diff(&l, &r)),
        (">", true) => (Rel::Lt, diff(&r, &l)),
        (">", false) => (Rel::Le, diff(&l, &r)),
        _ => return None,
    })
}

fn compare(name: &str, a: &BigRational, b: &BigRational) -> bool {
    match name {
        "<" => a < b,
        "<=" => a <= b,
        ">" => a > b,
        _ => a >= b,
    }
}

fn all_distinct<T: PartialEq>(values: &[T]) -> bool {
    values
        .iter()
        .enumerate()
        .all(|(i, a)| values[i + 1..].iter().all(|b| a != b))
}
