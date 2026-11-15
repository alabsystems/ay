// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The quantifier-free Herbrand expansion of a NEGATED quantified conjunct
//! (#qlra-nested-cegqi, plan §4.2).
//!
//! [`negated_expansion`] walks `¬R` in negation-normal polarity:
//!
//! * a quantifier occurrence that is UNIVERSAL in `¬R` (an effective
//!   existential of `R`) becomes the conjunction of its instances at the
//!   hinted tuples (none: `true`);
//! * a quantifier occurrence that is EXISTENTIAL in `¬R` is Skolemized with
//!   fresh constants, one per binder and per enclosing instance path;
//! * Boolean connectives keep their polarity (`=>`, Bool `ite`, Bool `=`,
//!   `xor` and binary Bool `distinct` are unfolded into `and`/`or`/`not`, so
//!   every quantifier occurrence has a single polarity). The frontend already
//!   desugars `=>` to `or`; its arm here is defensive and tested directly.
//!
//! SOUNDNESS. Instantiating a universal at ANY terms weakens it, and
//! Skolemizing an existential preserves satisfiability, so every model of
//! `pins ∧ ¬R` extends (by choosing the Skolem constants) to a model of
//! `pins ∧ E`. Hence `pins ∧ E` UNSAT ⇒ `pins ∧ ¬R` UNSAT ⇒ every model
//! agreeing with the pins satisfies `R`. That holds for every choice of
//! instance tuples — the hints are untrusted — and memoizing a subformula
//! per (term, polarity, environment) only shares a Skolem witness between
//! occurrences that are the same obligation in the same environment.
//!
//! Instance terms are read in the scope of the quantifier occurrence: a name
//! bound by an enclosing binder denotes that binder's current value.
//! Anything the walk does not treat (a `let`, a quantifier under a
//! non-connective operator) declines, and so do the caps.

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::term::TermData;
use ay_core::{Sort, TermId, TermStore};

use super::InstanceHints;

/// Instances one expansion may create, over every expansion site.
pub(in crate::executor) const MAX_EXPANSION_INSTANCES: usize = 2048;
/// Walk steps (memo misses) one expansion may take.
pub(in crate::executor) const MAX_EXPANSION_WORK: usize = 1 << 20;

/// Why no expansion was built.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(in crate::executor) enum ExpansionDecline {
    /// A construct the walk does not treat.
    Shape,
    /// The instance or work cap.
    Cap,
}

/// The expansion of `¬R`.
#[derive(Clone, Debug)]
pub(in crate::executor) struct NegatedExpansion {
    /// Quantifier-free; UNSAT (with the model pins) confirms `R`.
    pub(in crate::executor) formula: TermId,
    /// The fresh Skolem constants: they must stay FREE (never pinned).
    pub(in crate::executor) skolems: Vec<TermId>,
    /// Instances created at universal (in `¬R`) occurrences.
    pub(in crate::executor) instances: usize,
}

/// The maximal chain of directly nested same-kind quantifiers opened by `q`,
/// stopping before a binder name would repeat (the nested-CEGQI tree merges
/// blocks by the same rule): `(is_forall, binders, body)`.
pub(in crate::executor) fn binder_chain(
    terms: &TermStore,
    q: TermId,
) -> Option<(bool, Vec<(String, Sort)>, TermId)> {
    let (forall, mut binders, mut body) = match terms.get(q) {
        TermData::Forall(b, body, _) => (true, b.clone(), *body),
        TermData::Exists(b, body, _) => (false, b.clone(), *body),
        _ => return None,
    };
    loop {
        let (next, inner) = match (forall, terms.get(body)) {
            (true, TermData::Forall(b, inner, _)) | (false, TermData::Exists(b, inner, _)) => {
                (b, *inner)
            }
            _ => break,
        };
        if next
            .iter()
            .any(|(n, _)| binders.iter().any(|(m, _)| m == n))
        {
            break;
        }
        binders.extend(next.iter().cloned());
        body = inner;
    }
    Some((forall, binders, body))
}

/// Build the expansion of `¬conjunct` over `hints`.
pub(in crate::executor) fn negated_expansion(
    terms: &mut TermStore,
    conjunct: TermId,
    hints: &InstanceHints,
) -> Result<NegatedExpansion, ExpansionDecline> {
    let mut walker = Walker {
        terms,
        hints,
        envs: Vec::new(),
        env_ids: HashMap::default(),
        memo: HashMap::default(),
        subst_memo: HashMap::default(),
        quantified: HashMap::default(),
        skolems: Vec::new(),
        instances: 0,
        work: 0,
    };
    let root_env = walker.intern(HashMap::default());
    let formula = walker.walk(conjunct, false, root_env)?;
    Ok(NegatedExpansion {
        formula,
        skolems: walker.skolems,
        instances: walker.instances,
    })
}

type Env = HashMap<String, TermId>;

struct Walker<'a> {
    terms: &'a mut TermStore,
    hints: &'a InstanceHints,
    envs: Vec<Env>,
    env_ids: HashMap<Vec<(String, TermId)>, usize>,
    memo: HashMap<(TermId, bool, usize), TermId>,
    subst_memo: HashMap<(TermId, usize), TermId>,
    quantified: HashMap<TermId, bool>,
    skolems: Vec<TermId>,
    instances: usize,
    work: usize,
}

impl Walker<'_> {
    fn tick(&mut self) -> Result<(), ExpansionDecline> {
        self.work += 1;
        if self.work > MAX_EXPANSION_WORK {
            return Err(ExpansionDecline::Cap);
        }
        Ok(())
    }

    fn intern(&mut self, env: Env) -> usize {
        let mut key: Vec<(String, TermId)> = env.iter().map(|(n, &t)| (n.clone(), t)).collect();
        key.sort();
        if let Some(&id) = self.env_ids.get(&key) {
            return id;
        }
        self.envs.push(env);
        let id = self.envs.len() - 1;
        self.env_ids.insert(key, id);
        id
    }

    fn extend(&mut self, env: usize, names: &[(String, Sort)], values: &[TermId]) -> usize {
        let mut next = self.envs[env].clone();
        for ((name, _), &value) in names.iter().zip(values) {
            next.insert(name.clone(), value);
        }
        self.intern(next)
    }

    /// Memoized "contains a quantifier or a `let`" (a `let` then declines).
    fn has_quantifier(&mut self, term: TermId) -> bool {
        if let Some(&known) = self.quantified.get(&term) {
            return known;
        }
        let children: Vec<TermId> = match self.terms.get(term) {
            TermData::App(_, args) => args.clone(),
            TermData::Not(inner) => vec![*inner],
            TermData::Ite(c, a, b) => vec![*c, *a, *b],
            TermData::Var(..) | TermData::Const(..) => Vec::new(),
            _ => {
                self.quantified.insert(term, true);
                return true;
            }
        };
        let known = stacker::maybe_grow(64 * 1024, 2 * 1024 * 1024, || {
            children.into_iter().any(|c| self.has_quantifier(c))
        });
        self.quantified.insert(term, known);
        known
    }

    /// `term` (quantifier-free) with every in-scope name replaced by its
    /// environment value.
    fn subst(&mut self, term: TermId, env: usize) -> Result<TermId, ExpansionDecline> {
        if self.envs[env].is_empty() {
            return Ok(term);
        }
        if let Some(&done) = self.subst_memo.get(&(term, env)) {
            return Ok(done);
        }
        self.tick()?;
        let out = stacker::maybe_grow(64 * 1024, 2 * 1024 * 1024, || {
            Ok(match self.terms.get(term).clone() {
                TermData::Var(name, _) => match self.envs[env].get(&name) {
                    Some(&value) if self.terms.sort(value) == self.terms.sort(term) => value,
                    _ => term,
                },
                TermData::Const(_) => term,
                TermData::App(symbol, args) => {
                    let mut rewritten = Vec::with_capacity(args.len());
                    for &arg in &args {
                        rewritten.push(self.subst(arg, env)?);
                    }
                    if rewritten == args {
                        term
                    } else {
                        let sort = self.terms.sort(term).clone();
                        self.terms.mk_app(symbol, rewritten, sort)
                    }
                }
                TermData::Not(inner) => {
                    let rewritten = self.subst(inner, env)?;
                    self.terms.mk_not_raw(rewritten)
                }
                TermData::Ite(c, a, b) => {
                    let (c, a, b) = (
                        self.subst(c, env)?,
                        self.subst(a, env)?,
                        self.subst(b, env)?,
                    );
                    self.terms.mk_ite_raw(c, a, b)
                }
                _ => return Err(ExpansionDecline::Shape),
            })
        })?;
        self.subst_memo.insert((term, env), out);
        Ok(out)
    }

    /// `term` if `pos`, else `¬term`, expanded.
    fn walk(&mut self, term: TermId, pos: bool, env: usize) -> Result<TermId, ExpansionDecline> {
        if !self.has_quantifier(term) {
            let plain = self.subst(term, env)?;
            return Ok(if pos { plain } else { self.terms.mk_not(plain) });
        }
        if let Some(&done) = self.memo.get(&(term, pos, env)) {
            return Ok(done);
        }
        self.tick()?;
        let out = stacker::maybe_grow(64 * 1024, 2 * 1024 * 1024, || {
            match self.terms.get(term).clone() {
                TermData::Not(inner) => self.walk(inner, !pos, env),
                TermData::Ite(c, a, b) if matches!(self.terms.sort(term), Sort::Bool) => {
                    let (c1, a1) = (self.walk(c, true, env)?, self.walk(a, pos, env)?);
                    let (c0, b1) = (self.walk(c, false, env)?, self.walk(b, pos, env)?);
                    let then_arm = self.terms.mk_and(vec![c1, a1]);
                    let else_arm = self.terms.mk_and(vec![c0, b1]);
                    Ok(self.terms.mk_or(vec![then_arm, else_arm]))
                }
                TermData::App(symbol, args) => self.connective(symbol.name(), &args, pos, env),
                TermData::Forall(..) | TermData::Exists(..) => self.quantifier(term, pos, env),
                _ => Err(ExpansionDecline::Shape),
            }
        })?;
        self.memo.insert((term, pos, env), out);
        Ok(out)
    }

    fn connective(
        &mut self,
        name: &str,
        args: &[TermId],
        pos: bool,
        env: usize,
    ) -> Result<TermId, ExpansionDecline> {
        let bool_args = args
            .iter()
            .all(|&a| matches!(self.terms.sort(a), Sort::Bool));
        match (name, args.len()) {
            ("and" | "or", _) => {
                let mut parts = Vec::with_capacity(args.len());
                for &arg in args {
                    parts.push(self.walk(arg, pos, env)?);
                }
                Ok(if (name == "and") == pos {
                    self.terms.mk_and(parts)
                } else {
                    self.terms.mk_or(parts)
                })
            }
            ("=>", n) if n >= 1 => {
                // (or ¬a1 … ¬a(n-1) b), at polarity `pos`.
                let mut parts = Vec::with_capacity(n);
                for (i, &arg) in args.iter().enumerate() {
                    let last = i + 1 == n;
                    parts.push(self.walk(arg, if last { pos } else { !pos }, env)?);
                }
                Ok(if pos {
                    self.terms.mk_or(parts)
                } else {
                    self.terms.mk_and(parts)
                })
            }
            ("xor", 2) => self.equiv(args[0], args[1], !pos, env),
            ("distinct", 2) if bool_args => self.equiv(args[0], args[1], !pos, env),
            ("=", n) if n >= 2 && bool_args => {
                let mut parts = Vec::with_capacity(n - 1);
                for pair in args.windows(2) {
                    parts.push(self.equiv(pair[0], pair[1], pos, env)?);
                }
                Ok(if pos {
                    self.terms.mk_and(parts)
                } else {
                    self.terms.mk_or(parts)
                })
            }
            _ => Err(ExpansionDecline::Shape),
        }
    }

    /// `a ⟺ b` when `equal`, else `a ⊕ b`, with single-polarity operands.
    fn equiv(
        &mut self,
        a: TermId,
        b: TermId,
        equal: bool,
        env: usize,
    ) -> Result<TermId, ExpansionDecline> {
        let (a1, a0) = (self.walk(a, true, env)?, self.walk(a, false, env)?);
        let (b1, b0) = (self.walk(b, true, env)?, self.walk(b, false, env)?);
        let (left, right) = if equal {
            (vec![a1, b1], vec![a0, b0])
        } else {
            (vec![a1, b0], vec![a0, b1])
        };
        let left = self.terms.mk_and(left);
        let right = self.terms.mk_and(right);
        Ok(self.terms.mk_or(vec![left, right]))
    }

    fn quantifier(&mut self, q: TermId, pos: bool, env: usize) -> Result<TermId, ExpansionDecline> {
        let (forall, binders, body) = binder_chain(self.terms, q).ok_or(ExpansionDecline::Shape)?;
        if forall != pos {
            // Existential in the expanded formula: Skolemize.
            let fresh: Vec<TermId> = binders
                .iter()
                .map(|(name, sort)| {
                    self.terms
                        .mk_fresh_var(&format!("qmg!xp!{name}"), sort.clone())
                })
                .collect();
            self.skolems.extend(fresh.iter().copied());
            let inner = self.extend(env, &binders, &fresh);
            return self.walk(body, pos, inner);
        }
        // Universal in the expanded formula: the hinted instances.
        let tuples = self.hints.get(&q).cloned().unwrap_or_default();
        let mut parts = Vec::with_capacity(tuples.len());
        for tuple in tuples {
            if !self.tuple_fits(&binders, &tuple) {
                continue;
            }
            self.instances += 1;
            if self.instances > MAX_EXPANSION_INSTANCES {
                return Err(ExpansionDecline::Cap);
            }
            let mut values = Vec::with_capacity(tuple.len());
            for &component in &tuple {
                values.push(self.subst(component, env)?);
            }
            let inner = self.extend(env, &binders, &values);
            parts.push(self.walk(body, pos, inner)?);
        }
        Ok(self.terms.mk_and(parts))
    }

    /// A usable tuple: one quantifier-free term of the binder's sort per
    /// binder.
    fn tuple_fits(&mut self, binders: &[(String, Sort)], tuple: &[TermId]) -> bool {
        tuple.len() == binders.len()
            && binders.iter().zip(tuple).all(|((_, sort), &value)| {
                value.index() < self.terms.len()
                    && self.terms.sort(value) == sort
                    && !self.has_quantifier(value)
            })
    }
}
