// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The sequence equalities the SAT model actually relies on.
//!
//! The decomposition axioms are one-directional: `contains(s, t) =>
//! s = l ++ t ++ r`. With `contains(s, t)` false the implication already holds,
//! and the SAT solver may still set the equality atom true: nothing in the
//! Boolean structure reads it, and EUF and LIA accept it because the skolems
//! `l` and `r` are free. Reading that atom as a committed equality makes `s`
//! contain `t` — exactly what the false `contains` denies. Measured on the
//! replace shape with `dst = [5]`: the tightest-prefix atom
//! `x ++ src[0..len-1] = l ++ src ++ r`, whose `contains` is false, forced
//! every cell of `u` equal, so `src` occurred at offset 0 before the
//! committed first occurrence at offset 1.
//!
//! An equality counts only when it is RELEVANT: reached from a root that must
//! hold through connectives whose model values need it (every conjunct of a
//! true `and`, one true disjunct of a true `or`, the chosen branch of an
//! `ite`, ...). This is the relevancy notion CDCL(T) solvers use to keep
//! don't-care atoms away from theories. A true `or` is justified by a disjunct
//! other than a sequence equality whenever one is true, so `(or (not
//! contains) decomposition)` never commits the decomposition while
//! `contains` is false, whatever order the term store gives the disjuncts.

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::{Constant, TermData};
use ay_core::{Sort, TermId};

use super::{Model, MAX_WITNESS_ARITH_DEPTH};
use crate::executor::Executor;

/// Upper bound on the (term, polarity) pairs one relevancy walk visits.
const MAX_RELEVANCY_VISITS: usize = 1 << 20;

struct Relevancy<'a> {
    exec: &'a Executor,
    model: &'a Model,
    memo: HashMap<TermId, Option<bool>>,
}

impl Relevancy<'_> {
    /// Three-valued Boolean value of `t` under the SAT model.
    fn value(&mut self, t: TermId, depth: usize) -> Option<bool> {
        if let Some(&v) = self.memo.get(&t) {
            return v;
        }
        let model = self.model;
        let direct = self
            .exec
            .term_value(&model.sat_model, &model.term_to_var, t)
            .or_else(|| model.bool_overrides.get(&t).copied());
        let v = match (direct, self.exec.ctx.terms.get(t)) {
            (Some(v), _) => Some(v),
            (None, _) if depth >= MAX_WITNESS_ARITH_DEPTH => None,
            (None, TermData::Const(Constant::Bool(b))) => Some(*b),
            (None, TermData::Not(x)) => self.value(*x, depth + 1).map(|v| !v),
            (None, TermData::App(sym, args)) => match sym.name() {
                "and" => self.fold(args, depth, false),
                "or" => self.fold(args, depth, true),
                _ => None,
            },
            _ => None,
        };
        self.memo.insert(t, v);
        v
    }

    /// The child that justifies a true `or` (`want == true`) or a false
    /// `and`: one with that value, preferring any child other than a sequence
    /// equality so a disjunction commits no word equation it does not need.
    /// Argument order is the term store's canonical order, so the choice is
    /// deterministic.
    fn justifying_child(&mut self, args: &[TermId], want: bool) -> Option<TermId> {
        let exec = self.exec;
        let terms = &exec.ctx.terms;
        let is_seq_eq = |t: TermId| {
            matches!(terms.get(t), TermData::App(sym, a)
                if sym.name() == "=" && a.len() == 2 && matches!(terms.sort(a[0]), Sort::Seq(_)))
        };
        let mut fallback = None;
        for &a in args {
            if self.value(a, 0) != Some(want) {
                continue;
            }
            if !is_seq_eq(a) {
                return Some(a);
            }
            fallback.get_or_insert(a);
        }
        fallback
    }

    /// `or` (`absorbing == true`) or `and` over `args`, three-valued.
    fn fold(&mut self, args: &[TermId], depth: usize, absorbing: bool) -> Option<bool> {
        let mut all_known = true;
        for &a in args {
            match self.value(a, depth + 1) {
                Some(v) if v == absorbing => return Some(absorbing),
                Some(_) => {}
                None => all_known = false,
            }
        }
        all_known.then_some(!absorbing)
    }
}

impl Executor {
    /// `(a, b)` for every relevant sequence equality `(= a b)` the model makes
    /// true. `None` when the walk exceeds its visit budget.
    pub(super) fn relevant_seq_equalities(
        &self,
        model: &Model,
        roots: &[TermId],
    ) -> Option<Vec<(TermId, TermId)>> {
        let mut rel = Relevancy {
            exec: self,
            model,
            memo: HashMap::default(),
        };
        let terms = &self.ctx.terms;
        let mut out = Vec::new();
        let mut seen: HashSet<(TermId, bool)> = HashSet::default();
        let mut stack: Vec<(TermId, bool)> = roots.iter().map(|&r| (r, true)).collect();
        while let Some((t, want)) = stack.pop() {
            if !seen.insert((t, want)) {
                continue;
            }
            if seen.len() > MAX_RELEVANCY_VISITS {
                return None;
            }
            match terms.get(t) {
                TermData::Not(x) => stack.push((*x, !want)),
                TermData::Ite(c, a, b) if matches!(terms.sort(t), Sort::Bool) => {
                    if let Some(vc) = rel.value(*c, 0) {
                        stack.push((*c, vc));
                        stack.push((if vc { *a } else { *b }, want));
                    }
                }
                TermData::App(sym, args) => match (sym.name(), args.as_slice(), want) {
                    ("and", _, true) | ("or", _, false) => {
                        stack.extend(args.iter().map(|&a| (a, want)));
                    }
                    ("and", _, false) | ("or", _, true) => {
                        if let Some(a) = rel.justifying_child(args, want) {
                            stack.push((a, want));
                        }
                    }
                    ("=>", [a, b], true) => match (rel.value(*a, 0), rel.value(*b, 0)) {
                        (Some(false), _) => stack.push((*a, false)),
                        (_, Some(true)) => stack.push((*b, true)),
                        _ => {}
                    },
                    ("=>", [a, b], false) => stack.extend([(*a, true), (*b, false)]),
                    ("=" | "xor", [a, b], _) if matches!(terms.sort(*a), Sort::Bool) => {
                        for x in [*a, *b] {
                            if let Some(v) = rel.value(x, 0) {
                                stack.push((x, v));
                            }
                        }
                    }
                    ("=", [a, b], true) if matches!(terms.sort(*a), Sort::Seq(_)) => {
                        out.push((*a, *b));
                    }
                    _ => {}
                },
                _ => {}
            }
        }
        Some(out)
    }
}
