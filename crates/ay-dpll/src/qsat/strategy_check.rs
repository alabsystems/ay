// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The quantified model gate's side of the strategy certificate: an
//! INDEPENDENT re-walk of one authored conjunct that Skolemizes it with the
//! certificate's terms.
//!
//! The walk computes the negation normal form of the conjunct and replaces
//! every quantifier occurrence by its body: a universal occurrence binds its
//! binders to the certificate's fresh engine variables (the Skolem
//! constants of the check), an existential occurrence binds them to the
//! certificate's strategy terms after substituting the bindings of the
//! enclosing existential occurrences. A strategy term may mention only
//! authored constants and the Skolem constants of ENCLOSING universal
//! occurrences; anything else refuses. The result `F` is quantifier-free and
//!
//! ```text
//!   ⊨ ∀ sk. F(sk)   implies   the conjunct holds (in the pinned model),
//! ```
//!
//! which is ordinary Skolemization read backwards: every existential is
//! witnessed by a term over the universals in its scope. The gate confirms
//! by a checked refutation of `pins ∧ ¬F`.
//!
//! A quantifier occurring at mixed polarity (under `=`, `xor`, `distinct`
//! or an `ite` condition) is expanded into both polarities first, exactly as
//! the negation normal form requires. The same occurrence visited twice must
//! produce the same instantiated body, so no Skolem constant is shared by
//! two different subformulas.

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::{Symbol, TermData};
use ay_core::{Sort, TermId, TermStore};

use num_traits::Zero;

use super::strategy::StrategyCert;

/// Distinct walk nodes before the check refuses.
const MAX_WORK: usize = 1_000_000;

struct Walker<'a> {
    terms: &'a mut TermStore,
    cert: &'a StrategyCert,
    engine_vars: HashSet<TermId>,
    universal_vars: HashSet<TermId>,
    /// First instantiated body per occurrence key.
    visited: HashMap<(TermId, bool), TermId>,
    work: usize,
}

#[derive(Clone, Default)]
struct Scope {
    /// Binder name -> bound term.
    names: HashMap<String, TermId>,
    /// Engine variables of enclosing existential occurrences -> binding.
    exists: Vec<(TermId, TermId)>,
    /// Skolem constants of enclosing universal occurrences.
    universals: HashSet<TermId>,
}

impl Walker<'_> {
    fn tick(&mut self) -> Result<(), &'static str> {
        self.work += 1;
        if self.work > MAX_WORK {
            Err("strategy-check-work")
        } else {
            Ok(())
        }
    }

    fn connective(&mut self, and: bool, parts: Vec<TermId>) -> TermId {
        match parts.as_slice() {
            [one] => *one,
            _ => self.terms.mk_app(
                Symbol::named(if and { "and" } else { "or" }),
                parts,
                Sort::Bool,
            ),
        }
    }

    fn not(&mut self, t: TermId) -> TermId {
        self.terms.mk_not_raw(t)
    }

    /// Substitute the scope's binder names in a quantifier-free term.
    fn qf(&mut self, t: TermId, scope: &Scope) -> Result<TermId, &'static str> {
        if scope.names.is_empty() {
            return Ok(t);
        }
        crate::ematching::subst_vars_exact_qf(self.terms, t, &scope.names)
            .ok_or("strategy-check-substitution")
    }

    /// Free variables of a term that are engine variables.
    fn engine_vars_in(&self, t: TermId) -> Vec<TermId> {
        let mut out = Vec::new();
        let mut stack = vec![t];
        let mut seen = HashSet::default();
        while let Some(x) = stack.pop() {
            if !seen.insert(x) {
                continue;
            }
            if self.engine_vars.contains(&x) {
                out.push(x);
                continue;
            }
            match self.terms.get(x) {
                TermData::App(_, args) => stack.extend(args.iter().copied()),
                TermData::Not(i) => stack.push(*i),
                TermData::Ite(c, a, b) => stack.extend([*c, *a, *b]),
                _ => {}
            }
        }
        out
    }

    /// One quantifier occurrence: bind its binders (Skolem constants for a
    /// universal, checked strategy terms for an existential) and walk on.
    fn walk_quantifier(
        &mut self,
        t: TermId,
        binders: &[(String, Sort)],
        body: TermId,
        pol: bool,
        scope: &Scope,
    ) -> Result<TermId, &'static str> {
        let is_forall = matches!(self.terms.get(t), TermData::Forall(..));
        let universal = is_forall == pol;
        let key = (t, pol);
        let occ = self
            .cert
            .occurrences
            .get(&key)
            .ok_or("strategy-check-unknown-occurrence")?;
        if occ.universal != universal || occ.vars.len() != binders.len() {
            return Err("strategy-check-occurrence-shape");
        }
        let mut inner = scope.clone();
        if universal {
            for ((name, sort), &v) in binders.iter().zip(&occ.vars) {
                if self.terms.sort(v) != sort {
                    return Err("strategy-check-sort");
                }
                inner.names.insert(name.clone(), v);
                inner.universals.insert(v);
            }
        } else {
            if occ.strategy.len() != binders.len() {
                return Err("strategy-check-occurrence-shape");
            }
            let mut bound = Vec::with_capacity(binders.len());
            for (((name, sort), &v), &s) in binders.iter().zip(&occ.vars).zip(&occ.strategy) {
                if self.terms.sort(s) != sort {
                    return Err("strategy-check-sort");
                }
                if crate::ematching::contains_quantifier(self.terms, s) {
                    return Err("strategy-check-quantified-term");
                }
                let s = super::mbp::substitute(self.terms, s, &scope.exists);
                for x in self.engine_vars_in(s) {
                    if !scope.universals.contains(&x) {
                        return Err("strategy-check-out-of-scope");
                    }
                }
                inner.names.insert(name.clone(), s);
                bound.push((v, s));
            }
            inner.exists.extend(bound);
        }
        let result = self.walk(body, pol, &inner)?;
        match self.visited.get(&key) {
            Some(&first) if first != result => Err("strategy-check-shared-occurrence"),
            Some(_) => Ok(result),
            None => {
                self.visited.insert(key, result);
                Ok(result)
            }
        }
    }

    fn walk(&mut self, t: TermId, pol: bool, scope: &Scope) -> Result<TermId, &'static str> {
        self.tick()?;
        if !crate::ematching::contains_quantifier(self.terms, t) {
            let r = self.qf(t, scope)?;
            return Ok(if pol { r } else { self.not(r) });
        }
        match self.terms.get(t).clone() {
            TermData::Not(inner) => self.walk(inner, !pol, scope),
            TermData::Forall(binders, body, _) | TermData::Exists(binders, body, _) => {
                self.walk_quantifier(t, &binders, body, pol, scope)
            }
            TermData::App(sym, args) => {
                let name = sym.name().to_string();
                match name.as_str() {
                    "and" | "or" => {
                        let is_and = (name == "and") == pol;
                        let parts = args
                            .iter()
                            .map(|&a| self.walk(a, pol, scope))
                            .collect::<Result<Vec<_>, _>>()?;
                        Ok(self.connective(is_and, parts))
                    }
                    "=>" => {
                        let (last, prem) = args.split_last().ok_or("strategy-check-shape")?;
                        let mut parts = Vec::new();
                        for &p in prem {
                            parts.push(self.walk(p, !pol, scope)?);
                        }
                        parts.push(self.walk(*last, pol, scope)?);
                        Ok(self.connective(pol, parts))
                    }
                    "=" | "xor" | "distinct"
                        if args.len() == 2
                            && args
                                .iter()
                                .all(|&a| matches!(self.terms.sort(a), Sort::Bool)) =>
                    {
                        let equal = (name == "=") == pol;
                        let (a, b) = (args[0], args[1]);
                        let a_t = self.walk(a, true, scope)?;
                        let a_f = self.walk(a, false, scope)?;
                        let b_t = self.walk(b, true, scope)?;
                        let b_f = self.walk(b, false, scope)?;
                        let (l, r) = if equal {
                            (
                                self.connective(true, vec![a_t, b_t]),
                                self.connective(true, vec![a_f, b_f]),
                            )
                        } else {
                            (
                                self.connective(true, vec![a_t, b_f]),
                                self.connective(true, vec![a_f, b_t]),
                            )
                        };
                        Ok(self.connective(false, vec![l, r]))
                    }
                    _ => Err("strategy-check-quantifier-in-term"),
                }
            }
            TermData::Ite(c, a, b) if matches!(self.terms.sort(t), Sort::Bool) => {
                let c_t = self.walk(c, true, scope)?;
                let c_f = self.walk(c, false, scope)?;
                let a_p = self.walk(a, pol, scope)?;
                let b_p = self.walk(b, pol, scope)?;
                let l = self.connective(true, vec![c_t, a_p]);
                let r = self.connective(true, vec![c_f, b_p]);
                Ok(self.connective(false, vec![l, r]))
            }
            _ => Err("strategy-check-quantifier-in-term"),
        }
    }
}

/// Skolemize `conjunct` with the certificate. Returns the quantifier-free
/// `F` and the Skolem constants the check must leave unpinned.
pub(crate) fn instantiate(
    terms: &mut TermStore,
    conjunct: TermId,
    cert: &StrategyCert,
) -> Result<(TermId, Vec<TermId>), &'static str> {
    let mut engine_vars = HashSet::default();
    let mut universal_vars = HashSet::default();
    for occ in cert.occurrences.values() {
        for &v in &occ.vars {
            if !engine_vars.insert(v) {
                return Err("strategy-check-shared-variable");
            }
            if occ.universal {
                universal_vars.insert(v);
            }
        }
    }
    let mut w = Walker {
        terms,
        cert,
        engine_vars,
        universal_vars,
        visited: HashMap::default(),
        work: 0,
    };
    let f = w.walk(conjunct, true, &Scope::default())?;
    if crate::ematching::contains_quantifier(w.terms, f) {
        return Err("strategy-check-residual-quantifier");
    }
    // Every engine variable left in F must be a universal Skolem constant.
    for x in w.engine_vars_in(f) {
        if !w.universal_vars.contains(&x) {
            return Err("strategy-check-residual-engine-variable");
        }
    }
    let skolems: Vec<TermId> = w.universal_vars.iter().copied().collect();
    Ok((f, skolems))
}

/// Whether some quantifier below `conjunct` is an EXISTENTIAL occurrence of
/// the certificate (at either polarity key).
pub(crate) fn has_existential_occurrence(
    terms: &TermStore,
    conjunct: TermId,
    cert: &StrategyCert,
) -> bool {
    let mut stack = vec![conjunct];
    let mut seen = HashSet::default();
    while let Some(t) = stack.pop() {
        if !seen.insert(t) {
            continue;
        }
        match terms.get(t) {
            TermData::Forall(_, body, _) | TermData::Exists(_, body, _) => {
                for pol in [true, false] {
                    if cert
                        .occurrences
                        .get(&(t, pol))
                        .is_some_and(|o| !o.universal)
                    {
                        return true;
                    }
                }
                stack.push(*body);
            }
            TermData::App(_, args) => stack.extend(args.iter().copied()),
            TermData::Not(i) => stack.push(*i),
            TermData::Ite(c, a, b) => stack.extend([*c, *a, *b]),
            _ => {}
        }
    }
    false
}

/// A quantifier-free `f` with every `(div n k)` / `(mod n k)` by a nonzero
/// integer numeral replaced by a fresh `q` (and `n − k·q`), together with
/// the definitions `0 ≤ n − k·q ≤ |k| − 1` and the fresh constants.
///
/// `q` is determined by its definition (Euclidean division), so
/// `pins ∧ ¬f` is satisfiable exactly when `pins ∧ ¬f' ∧ defs` is: a model
/// of the first extends by `q := div(n, k)`, and a model of the second
/// restricts to one of the first. Strategies of an Int MBP with a non-unit
/// coefficient are `div` terms, and the checked ground lane certifies the
/// purified bound form where it cannot certify the `div` itself (measured:
/// `2·div(2x, 2) ≠ 2x` undecided at the gate's cap, the bound form refuted).
pub(crate) fn purify_divmod(
    terms: &mut TermStore,
    f: TermId,
) -> (TermId, Vec<TermId>, Vec<TermId>) {
    let mut p = DivPurifier {
        terms,
        memo: HashMap::default(),
        quotients: HashMap::default(),
        defs: Vec::new(),
        fresh: Vec::new(),
    };
    let g = p.rewrite(f);
    (g, p.defs, p.fresh)
}

struct DivPurifier<'a> {
    terms: &'a mut TermStore,
    memo: HashMap<TermId, TermId>,
    quotients: HashMap<(TermId, num_bigint::BigInt), TermId>,
    defs: Vec<TermId>,
    fresh: Vec<TermId>,
}

impl DivPurifier<'_> {
    fn rewrite(&mut self, t: TermId) -> TermId {
        if let Some(&r) = self.memo.get(&t) {
            return r;
        }
        let r = stacker::maybe_grow(64 * 1024, 8 * 1024 * 1024, || self.rewrite_uncached(t));
        self.memo.insert(t, r);
        r
    }

    fn rewrite_uncached(&mut self, t: TermId) -> TermId {
        match self.terms.get(t).clone() {
            TermData::Not(inner) => {
                let i = self.rewrite(inner);
                if i == inner {
                    t
                } else {
                    self.terms.mk_not_raw(i)
                }
            }
            TermData::Ite(c, a, b) => {
                let (c2, a2, b2) = (self.rewrite(c), self.rewrite(a), self.rewrite(b));
                if (c2, a2, b2) == (c, a, b) {
                    t
                } else {
                    self.terms.mk_ite_raw(c2, a2, b2)
                }
            }
            TermData::App(sym, args) => {
                let new: Vec<TermId> = args.iter().map(|&a| self.rewrite(a)).collect();
                if matches!(sym.name(), "div" | "mod") && new.len() == 2 {
                    if let Some(k) =
                        super::lin::int_numeral(self.terms, new[1]).filter(|k| !k.is_zero())
                    {
                        let q = self.quotient(new[0], k.clone());
                        if sym.name() == "div" {
                            return q;
                        }
                        let kt = self.terms.mk_int(k);
                        let kq = self
                            .terms
                            .mk_app(Symbol::named("*"), vec![kt, q], Sort::Int);
                        return self
                            .terms
                            .mk_app(Symbol::named("-"), vec![new[0], kq], Sort::Int);
                    }
                }
                if new == args {
                    t
                } else {
                    let sort = self.terms.sort(t).clone();
                    self.terms.mk_app(sym, new, sort)
                }
            }
            _ => t,
        }
    }

    /// The fresh quotient of `n` by `k`, with its definition recorded once.
    fn quotient(&mut self, n: TermId, k: num_bigint::BigInt) -> TermId {
        if let Some(&q) = self.quotients.get(&(n, k.clone())) {
            return q;
        }
        let q = self.terms.mk_fresh_var("qsat!gate_div", Sort::Int);
        let kt = self.terms.mk_int(k.clone());
        let kq = self
            .terms
            .mk_app(Symbol::named("*"), vec![kt, q], Sort::Int);
        let rem = self
            .terms
            .mk_app(Symbol::named("-"), vec![n, kq], Sort::Int);
        let zero = self.terms.mk_int(num_bigint::BigInt::from(0));
        let hi = self.terms.mk_int(num_traits::Signed::abs(&k) - 1);
        let lo_atom = self
            .terms
            .mk_app(Symbol::named("<="), vec![zero, rem], Sort::Bool);
        let hi_atom = self
            .terms
            .mk_app(Symbol::named("<="), vec![rem, hi], Sort::Bool);
        self.defs.push(lo_atom);
        self.defs.push(hi_atom);
        self.fresh.push(q);
        self.quotients.insert((n, k), q);
        q
    }
}
