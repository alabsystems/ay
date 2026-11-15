// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The quantifier-free rewrite of the prenex normalizer: binders renamed,
//! `div`/`mod` purified, `abs` expanded, arithmetic `ite` lifted out of atoms.

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::{Constant, Symbol, TermData};
use ay_core::{Sort, TermId};
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{Signed, Zero};

use super::super::lin::{int_numeral, lin_of, numeral};
use super::{is_arith, Builder, Purified, ShapeDecline, MAX_ITES_PER_ATOM};

impl Builder<'_> {
    /// Quantifier-free rewrite under `env`: binders renamed, `div`/`mod`
    /// purified, `abs` expanded, arithmetic `ite` lifted out of atoms.
    pub(super) fn qf(&mut self, t: TermId, env: usize) -> Result<TermId, ShapeDecline> {
        if let Some(&r) = self.qf_memo.get(&(t, env)) {
            return Ok(r);
        }
        self.tick()?;
        let r = stacker::maybe_grow(64 * 1024, 8 * 1024 * 1024, || self.qf_uncached(t, env))?;
        self.qf_memo.insert((t, env), r);
        Ok(r)
    }

    fn qf_uncached(&mut self, t: TermId, env: usize) -> Result<TermId, ShapeDecline> {
        let data = self.terms.get(t).clone();
        let sort = self.terms.sort(t).clone();
        match data {
            TermData::Const(Constant::Bool(_) | Constant::Int(_) | Constant::Rational(_)) => Ok(t),
            TermData::Const(_) => Err(ShapeDecline::Sort),
            TermData::Var(name, _) => match self.lookup(env, &name) {
                Some(v) => Ok(v),
                None => self.free_constant(t),
            },
            TermData::Not(inner) => {
                let i = self.qf(inner, env)?;
                Ok(self.terms.mk_not_raw(i))
            }
            TermData::Ite(c, a, b) => {
                let c = self.qf(c, env)?;
                let a = self.qf(a, env)?;
                let b = self.qf(b, env)?;
                Ok(self.terms.mk_ite_raw(c, a, b))
            }
            TermData::App(sym, args) => self.qf_app(t, sym, args, sort, env),
            TermData::Forall(..) | TermData::Exists(..) => Err(ShapeDecline::QuantifierInTerm),
            _ => Err(ShapeDecline::Operator),
        }
    }

    fn qf_args(&mut self, args: &[TermId], env: usize) -> Result<Vec<TermId>, ShapeDecline> {
        args.iter().map(|&a| self.qf(a, env)).collect()
    }

    /// `q = (div num k)` as a fresh `Int` at the level of `num`.
    fn purify_div(&mut self, num: TermId, k: &BigInt) -> Result<TermId, ShapeDecline> {
        if !matches!(self.terms.sort(num), Sort::Int) {
            return Err(ShapeDecline::Sort);
        }
        if let Some(&q) = self.div_memo.get(&(num, k.clone())) {
            return Ok(q);
        }
        let level = self.level_of_term(num);
        let q = self.terms.mk_fresh_var("qsat!div", Sort::Int);
        self.register(q, level);
        let kt = self.terms.mk_int(k.clone());
        let def = self
            .terms
            .mk_app(Symbol::named("div"), vec![num, kt], Sort::Int);
        self.game.purified.push(Purified { var: q, def, level });
        // 0 ≤ num − k·q ≤ |k| − 1, built through `atom` like every other
        // atom: an arithmetic `ite` in `num` (`(mod (ite c a b) 2)`, or `abs`
        // after its expansion) is lifted out, so the definition's atoms stay
        // linear for MBP (it declined with `mbp-parse` otherwise).
        let kq = self
            .terms
            .mk_app(Symbol::named("*"), vec![kt, q], Sort::Int);
        let rem = self
            .terms
            .mk_app(Symbol::named("-"), vec![num, kq], Sort::Int);
        let zero = self.terms.mk_int(BigInt::zero());
        let hi = self.terms.mk_int(k.abs() - 1);
        let lo_atom = self.atom(Symbol::named("<="), vec![zero, rem], 0)?;
        let hi_atom = self.atom(Symbol::named("<="), vec![rem, hi], 0)?;
        let def_formula =
            self.terms
                .mk_app(Symbol::named("and"), vec![lo_atom, hi_atom], Sort::Bool);
        if level % 2 == 0 {
            self.exists_defs.push(def_formula);
        } else {
            self.forall_defs.push(def_formula);
        }
        self.div_memo.insert((num, k.clone()), q);
        Ok(q)
    }

    /// An arithmetic atom over rewritten arguments, with `ite` lifted out.
    /// Chains become conjunctions of binary atoms and `distinct` becomes
    /// negated equalities, so every atom the game sees is binary.
    fn atom(
        &mut self,
        sym: Symbol,
        args: Vec<TermId>,
        depth: usize,
    ) -> Result<TermId, ShapeDecline> {
        if args.len() < 2 {
            return Err(ShapeDecline::Operator);
        }
        if sym.name() == "distinct" {
            let mut parts = Vec::new();
            for i in 0..args.len() {
                for j in i + 1..args.len() {
                    let eq = self.atom(Symbol::named("="), vec![args[i], args[j]], depth)?;
                    parts.push(self.terms.mk_not_raw(eq));
                }
            }
            return Ok(self.connective(true, parts));
        }
        if args.len() > 2 {
            let mut parts = Vec::new();
            for w in args.windows(2) {
                parts.push(self.atom(sym.clone(), w.to_vec(), depth)?);
            }
            return Ok(self.connective(true, parts));
        }
        if let Some((ite, c, a, b)) = self.find_arith_ite(&args) {
            if depth >= MAX_ITES_PER_ATOM {
                return Err(ShapeDecline::Size);
            }
            let then_args = self.replace_all(&args, ite, a)?;
            let else_args = self.replace_all(&args, ite, b)?;
            let then_atom = self.atom(sym.clone(), then_args, depth + 1)?;
            let else_atom = self.atom(sym, else_args, depth + 1)?;
            let not_c = self.terms.mk_not_raw(c);
            let left = self
                .terms
                .mk_app(Symbol::named("and"), vec![c, then_atom], Sort::Bool);
            let right = self
                .terms
                .mk_app(Symbol::named("and"), vec![not_c, else_atom], Sort::Bool);
            return Ok(self
                .terms
                .mk_app(Symbol::named("or"), vec![left, right], Sort::Bool));
        }
        for &a in &args {
            if lin_of(self.terms, a).is_none() {
                return Err(ShapeDecline::Nonlinear);
            }
        }
        Ok(self.terms.mk_app(sym, args, Sort::Bool))
    }

    /// The first arithmetic `ite` below `args`, looking only through
    /// arithmetic operators.
    fn find_arith_ite(&self, args: &[TermId]) -> Option<(TermId, TermId, TermId, TermId)> {
        let mut stack: Vec<TermId> = args.to_vec();
        let mut seen = HashSet::default();
        while let Some(t) = stack.pop() {
            if !seen.insert(t) {
                continue;
            }
            match self.terms.get(t) {
                TermData::Ite(c, a, b) if is_arith(self.terms.sort(t)) => {
                    return Some((t, *c, *a, *b));
                }
                TermData::App(sym, args)
                    if matches!(sym.name(), "+" | "-" | "*" | "/" | "to_real") =>
                {
                    stack.extend(args.iter().copied());
                }
                _ => {}
            }
        }
        None
    }

    fn replace_all(
        &mut self,
        args: &[TermId],
        from: TermId,
        to: TermId,
    ) -> Result<Vec<TermId>, ShapeDecline> {
        let mut memo = HashMap::default();
        args.iter()
            .map(|&a| self.replace(a, from, to, &mut memo))
            .collect()
    }

    fn replace(
        &mut self,
        t: TermId,
        from: TermId,
        to: TermId,
        memo: &mut HashMap<TermId, TermId>,
    ) -> Result<TermId, ShapeDecline> {
        if t == from {
            return Ok(to);
        }
        if let Some(&r) = memo.get(&t) {
            return Ok(r);
        }
        self.tick()?;
        let r = match self.terms.get(t).clone() {
            TermData::App(sym, args) if matches!(sym.name(), "+" | "-" | "*" | "/" | "to_real") => {
                let sort = self.terms.sort(t).clone();
                let new: Vec<TermId> = args
                    .iter()
                    .map(|&a| self.replace(a, from, to, memo))
                    .collect::<Result<_, _>>()?;
                self.terms.mk_app(sym, new, sort)
            }
            _ => t,
        };
        memo.insert(t, r);
        Ok(r)
    }

    fn qf_app(
        &mut self,
        t: TermId,
        sym: Symbol,
        args: Vec<TermId>,
        sort: Sort,
        env: usize,
    ) -> Result<TermId, ShapeDecline> {
        if args.is_empty() {
            return match sym.name() {
                "true" | "false" => Ok(t),
                _ => self.free_constant(t),
            };
        }
        let name = sym.name().to_string();
        match name.as_str() {
            "and" | "or" | "not" | "=>" | "xor" => {
                let args = self.qf_args(&args, env)?;
                Ok(self.terms.mk_app(sym, args, Sort::Bool))
            }
            "=" | "distinct" | "<" | "<=" | ">" | ">=" => {
                if !args.iter().all(|&a| {
                    let s = self.terms.sort(a);
                    is_arith(s) || matches!(s, Sort::Bool)
                }) {
                    return Err(ShapeDecline::Sort);
                }
                let new_args = self.qf_args(&args, env)?;
                if args
                    .iter()
                    .any(|&a| matches!(self.terms.sort(a), Sort::Bool))
                {
                    // Boolean `=`/`distinct`: a connective.
                    return Ok(self.terms.mk_app(sym, new_args, Sort::Bool));
                }
                self.atom(sym, new_args, 0)
            }
            _ => self.qf_arith(&name, sym, &args, sort, env),
        }
    }

    /// Arithmetic operators: linear products and quotients by numerals,
    /// `abs` as an `ite`, `div`/`mod` purified.
    fn qf_arith(
        &mut self,
        name: &str,
        sym: Symbol,
        args: &[TermId],
        sort: Sort,
        env: usize,
    ) -> Result<TermId, ShapeDecline> {
        match name {
            "+" | "-" | "to_real" => {
                let args = self.qf_args(args, env)?;
                Ok(self.terms.mk_app(sym, args, sort))
            }
            "*" => {
                let new_args = self.qf_args(args, env)?;
                let nonconst = new_args
                    .iter()
                    .filter(|&&a| numeral(self.terms, a).is_none())
                    .count();
                if nonconst > 1 {
                    return Err(ShapeDecline::Nonlinear);
                }
                Ok(self.terms.mk_app(sym, new_args, sort))
            }
            "/" => {
                if args.len() != 2 {
                    return Err(ShapeDecline::Operator);
                }
                match numeral(self.terms, args[1]) {
                    Some(d) if !d.is_zero() => {}
                    _ => return Err(ShapeDecline::Nonlinear),
                }
                let new_args = self.qf_args(args, env)?;
                Ok(self.terms.mk_app(sym, new_args, sort))
            }
            "abs" if args.len() == 1 => {
                let a = self.qf(args[0], env)?;
                let zero = if matches!(sort, Sort::Int) {
                    self.terms.mk_int(BigInt::zero())
                } else {
                    self.terms.mk_rational(BigRational::zero())
                };
                // Through `atom`, like the `div` definition: an `ite` in `a`
                // is lifted out of the condition.
                let ge = self.atom(Symbol::named(">="), vec![a, zero], 0)?;
                let neg = self.terms.mk_app(Symbol::named("-"), vec![a], sort);
                Ok(self.terms.mk_ite_raw(ge, a, neg))
            }
            "div" | "mod" if args.len() == 2 => {
                let Some(k) = int_numeral(self.terms, args[1]) else {
                    return Err(ShapeDecline::Nonlinear);
                };
                if k.is_zero() {
                    return Err(ShapeDecline::Nonlinear);
                }
                let num = self.qf(args[0], env)?;
                let q = self.purify_div(num, &k)?;
                if name == "div" {
                    Ok(q)
                } else {
                    // mod = t − k·q
                    let kt = self.terms.mk_int(k);
                    let kq = self
                        .terms
                        .mk_app(Symbol::named("*"), vec![kt, q], Sort::Int);
                    Ok(self
                        .terms
                        .mk_app(Symbol::named("-"), vec![num, kq], Sort::Int))
                }
            }
            _ => Err(ShapeDecline::Operator),
        }
    }
}
