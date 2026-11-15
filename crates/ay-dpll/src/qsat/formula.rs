// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Atoms, levels and implicants of the game's quantifier-free formulas.
//!
//! The formulas are Boolean combinations (`and`, `or`, `not`, `=>`, `xor`,
//! Boolean `=`/`distinct`, Boolean `ite`) of ATOMS: Boolean variables and
//! binary arithmetic comparisons. Everything here is read-only on the store.

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::{Constant, TermData};
use ay_core::{Sort, TermId, TermStore};

use super::lin::{Eval, Val};

/// Whether `t` is an atom (a Boolean variable or an arithmetic comparison).
pub(crate) fn is_atom(terms: &TermStore, t: TermId) -> bool {
    match terms.get(t) {
        TermData::Var(..) => matches!(terms.sort(t), Sort::Bool),
        TermData::App(sym, args) => {
            if args.is_empty() {
                return matches!(terms.sort(t), Sort::Bool)
                    && !matches!(sym.name(), "true" | "false");
            }
            match sym.name() {
                "<" | "<=" | ">" | ">=" => true,
                "=" | "distinct" => args
                    .iter()
                    .all(|&a| matches!(terms.sort(a), Sort::Int | Sort::Real)),
                _ => false,
            }
        }
        _ => false,
    }
}

/// Append the atoms of `t` not yet in `seen`.
pub(crate) fn collect_atoms(
    terms: &TermStore,
    t: TermId,
    seen: &mut HashSet<TermId>,
    out: &mut Vec<TermId>,
) {
    let mut stack = vec![t];
    let mut visited: HashSet<TermId> = HashSet::default();
    while let Some(x) = stack.pop() {
        if !visited.insert(x) {
            continue;
        }
        if is_atom(terms, x) {
            if seen.insert(x) {
                out.push(x);
            }
            continue;
        }
        match terms.get(x) {
            TermData::Not(i) => stack.push(*i),
            TermData::Ite(c, a, b) => stack.extend([*c, *a, *b]),
            TermData::App(_, args) => stack.extend(args.iter().copied()),
            _ => {}
        }
    }
}

/// Memoized max variable level below a term.
pub(crate) struct Levels<'a> {
    pub(crate) level_of: &'a HashMap<TermId, usize>,
    memo: HashMap<TermId, usize>,
}

impl<'a> Levels<'a> {
    pub(crate) fn new(level_of: &'a HashMap<TermId, usize>) -> Self {
        Self {
            level_of,
            memo: HashMap::default(),
        }
    }

    pub(crate) fn of(&mut self, terms: &TermStore, t: TermId) -> usize {
        if let Some(&l) = self.memo.get(&t) {
            return l;
        }
        let l = if let Some(&l) = self.level_of.get(&t) {
            l
        } else {
            let children: Vec<TermId> = match terms.get(t) {
                TermData::Not(i) => vec![*i],
                TermData::Ite(c, a, b) => vec![*c, *a, *b],
                TermData::App(_, args) => args.clone(),
                _ => Vec::new(),
            };
            let mut best = 0;
            for c in children {
                best = best.max(stacker::maybe_grow(64 * 1024, 4 * 1024 * 1024, || {
                    self.of(terms, c)
                }));
            }
            best
        };
        self.memo.insert(t, l);
        l
    }
}

/// Extracts implicants: atom literals, true under the model, that force a
/// formula to its model value.
pub(crate) struct Implicant<'e, 'a> {
    pub(crate) eval: &'e mut Eval<'a>,
    pub(crate) levels: &'e mut Levels<'a>,
    pub(crate) out: Vec<(TermId, bool)>,
    seen: HashSet<(TermId, bool)>,
}

impl<'e, 'a> Implicant<'e, 'a> {
    pub(crate) fn new(eval: &'e mut Eval<'a>, levels: &'e mut Levels<'a>) -> Self {
        Self {
            eval,
            levels,
            out: Vec::new(),
            seen: HashSet::default(),
        }
    }

    fn terms(&self) -> &'a TermStore {
        self.eval.terms
    }

    /// Among `options` (child, wanted value) that hold, the one with the
    /// lowest variable level.
    fn best(&mut self, options: &[(TermId, bool)]) -> Option<(TermId, bool)> {
        let mut best: Option<(usize, TermId, bool)> = None;
        for &(c, v) in options {
            if self.eval.boolean(c)? == v {
                let l = self.levels.of(self.terms(), c);
                if best.is_none_or(|(bl, _, _)| l < bl) {
                    best = Some((l, c, v));
                }
            }
        }
        best.map(|(_, c, v)| (c, v))
    }

    /// Record literals forcing `t = want`; `None` when `t` does not evaluate
    /// to `want` or leaves the fragment.
    pub(crate) fn run(&mut self, t: TermId, want: bool) -> Option<()> {
        if !self.seen.insert((t, want)) {
            return Some(());
        }
        let terms = self.terms();
        if self.eval.boolean(t)? != want {
            return None;
        }
        if is_atom(terms, t) {
            self.out.push((t, want));
            return Some(());
        }
        stacker::maybe_grow(64 * 1024, 4 * 1024 * 1024, || match terms.get(t) {
            TermData::Const(Constant::Bool(_)) => Some(()),
            TermData::Not(i) => self.run(*i, !want),
            TermData::Ite(c, a, b) => {
                let (c, a, b) = (*c, *a, *b);
                let cv = self.eval.boolean(c)?;
                self.run(c, cv)?;
                self.run(if cv { a } else { b }, want)
            }
            TermData::App(sym, args) => {
                let args = args.clone();
                match sym.name() {
                    "true" | "false" => Some(()),
                    "not" => self.run(args[0], !want),
                    "and" | "or" if want == (sym.name() == "and") => {
                        for a in args {
                            self.run(a, want)?;
                        }
                        Some(())
                    }
                    "and" | "or" => {
                        let options: Vec<(TermId, bool)> =
                            args.iter().map(|&a| (a, want)).collect();
                        let (c, v) = self.best(&options)?;
                        self.run(c, v)
                    }
                    "=>" => {
                        let (last, prem) = args.split_last()?;
                        if !want {
                            for &p in prem {
                                self.run(p, true)?;
                            }
                            return self.run(*last, false);
                        }
                        let mut options: Vec<(TermId, bool)> =
                            prem.iter().map(|&p| (p, false)).collect();
                        options.push((*last, true));
                        let (c, v) = self.best(&options)?;
                        self.run(c, v)
                    }
                    "xor" | "=" | "distinct" => {
                        for a in args {
                            let v = self.eval.boolean(a)?;
                            self.run(a, v)?;
                        }
                        Some(())
                    }
                    _ => None,
                }
            }
            _ => None,
        })
    }
}

/// The two sides of an arithmetic equality atom `(= s t)`. A divisibility
/// atom `(= (mod e d) 0)` is not one: it is a literal of its own to the
/// projection, whose negation is a residue, not an order.
pub(crate) fn arith_eq_sides(terms: &TermStore, atom: TermId) -> Option<(TermId, TermId)> {
    let is_mod = |t: TermId| matches!(terms.get(t), TermData::App(sym, _) if sym.name() == "mod");
    match terms.get(atom) {
        TermData::App(sym, args)
            if sym.name() == "="
                && args.len() == 2
                && matches!(terms.sort(args[0]), Sort::Int | Sort::Real)
                && !is_mod(args[0])
                && !is_mod(args[1]) =>
        {
            Some((args[0], args[1]))
        }
        _ => None,
    }
}

/// `t` (or `¬t` when `!pol`) with every arithmetic equality that occurs only
/// NEGATIVELY replaced by the conjunction of its two inequalities: an
/// equivalence that turns theory disequalities into Boolean splits. Atoms
/// under a mixed-polarity connective (`=`, `xor`, `distinct`, an `ite`
/// condition) are kept.
pub(crate) fn split_negative_equalities(
    terms: &mut TermStore,
    t: TermId,
    pol: bool,
    memo: &mut HashMap<(TermId, bool), TermId>,
) -> TermId {
    use ay_core::term::Symbol;
    if let Some(&r) = memo.get(&(t, pol)) {
        return r;
    }
    let r = match terms.get(t).clone() {
        TermData::Not(i) => {
            let n = split_negative_equalities(terms, i, !pol, memo);
            if n == i {
                t
            } else {
                terms.mk_not_raw(n)
            }
        }
        TermData::App(sym, args) if matches!(sym.name(), "and" | "or") => {
            let new: Vec<TermId> = args
                .iter()
                .map(|&a| split_negative_equalities(terms, a, pol, memo))
                .collect();
            if new == args {
                t
            } else {
                terms.mk_app(sym, new, Sort::Bool)
            }
        }
        TermData::App(sym, args) if sym.name() == "=>" && !args.is_empty() => {
            let last = args.len() - 1;
            let new: Vec<TermId> = args
                .iter()
                .enumerate()
                .map(|(i, &a)| {
                    split_negative_equalities(terms, a, if i == last { pol } else { !pol }, memo)
                })
                .collect();
            if new == args {
                t
            } else {
                terms.mk_app(sym, new, Sort::Bool)
            }
        }
        _ if !pol => match arith_eq_sides(terms, t) {
            Some((a, b)) => {
                let le1 = terms.mk_app(Symbol::named("<="), vec![a, b], Sort::Bool);
                let le2 = terms.mk_app(Symbol::named("<="), vec![b, a], Sort::Bool);
                terms.mk_app(Symbol::named("and"), vec![le1, le2], Sort::Bool)
            }
            None => t,
        },
        _ => t,
    };
    memo.insert((t, pol), r);
    r
}

pub(crate) fn default_value(terms: &TermStore, t: TermId) -> Val {
    match terms.sort(t) {
        Sort::Bool => Val::Bool(false),
        _ => Val::Num(num_rational::BigRational::from_integer(0.into())),
    }
}
