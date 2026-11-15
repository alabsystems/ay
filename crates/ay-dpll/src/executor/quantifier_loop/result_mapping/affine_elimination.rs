// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact elimination of an `Int` binder from the affine (in)equalities of a
//! universal's body, for the proof-free infeasible-universal rewrite
//! (`simplify_infeasible_forall_eq`). 2026-09-23 hunt, D11: the rewrite used
//! to read a symbolic coefficient with its other atoms set to 0.
//!
//! Every decision is read from the term DAG first, without minting a term
//! ([`Executor::affine_binder_probe`]); terms are built only for a rewrite
//! that changes the formula, plus the fixed footprint of the probe this
//! replaced ([`Executor::intern_replaced_probe_footprint`]). The term store
//! is append-only and term ids feed hash orders downstream, so a pass that
//! mints a different set of terms than its predecessor moves CDCL searches
//! it leaves unchanged (2026-09-25 verify, B2: `fold_26096_00078` lost its
//! `unsat`, `inc_26093_00136` ran 2.5x slower).

#[cfg(test)]
mod footprint_tests;
mod poly;
#[cfg(test)]
mod probe_tests;

use ay_core::kani_compat::DetHashSet;
use ay_core::{Sort, TermData, TermId};
use num_bigint::BigInt;
use num_traits::{One, Zero};

use super::super::super::Executor;
use super::super::collect_and_conjuncts;
use poly::{poly_never_vanishes, poly_numeral, poly_sub, vanishing_falsifies_rest};

/// The shape of an `Int` (in)equality `(REL L R)` affine in one `Int` binder
/// `v`, read without minting a term: `L − R = c·v + r` with `c` and `r` free
/// of `v`.
pub(super) struct AffineBinderProbe {
    relation: String,
    lhs: TermId,
    rhs: TermId,
    /// The binder's `Var` term.
    binder: TermId,
    /// The binder's name (the one `vars` lists).
    binder_name: String,
    /// `c` when it is a numeral.
    numeral: Option<BigInt>,
    /// `c` cannot vanish over the integers: a numeral other than 0, or a
    /// polynomial whose constant the gcd of its other coefficients does not
    /// divide ([`poly_never_vanishes`]).
    never_vanishes: bool,
    /// A symbolic `c` whose vanishing makes `(REL r 0)` false
    /// ([`vanishing_falsifies_rest`]): the elimination `(and (= c 0) (REL r 0))` is
    /// then false, and the conjunct refutes like a `c` that never vanishes.
    vanishing_refutes: bool,
}

/// What the dropped-disjunct path does with one operand of the `or`.
enum DisjunctFate {
    /// Mentions no binder: kept as it is.
    Keep,
    /// An affine equality whose coefficient never vanishes: holds at no more
    /// than one binder value per line, so it drops.
    Drop,
    /// An affine equality with a symbolic coefficient: contributes the case
    /// where it holds identically, `(and (= c 0) (= r 0))`.
    Vanishing(AffineBinderProbe),
}

impl Executor {
    /// Replace every conjunct of a universal's `body` that is an `Int`
    /// (in)equality affine in an `Int` binder of `vars` by that binder's exact
    /// elimination ([`Self::affine_binder_probe`]): with `L − R = c·v + r`,
    /// `c` and `r` free of `v`,
    ///
    /// ```text
    /// ∀v. (REL L R)  ≡  (= c 0) ∧ (REL r 0)      REL ∈ {=, <, <=, >, >=}
    /// ```
    ///
    /// because `c·v + r` with `c ≠ 0` takes every sign and misses every value
    /// but one as `v` ranges over the integers, and with `c = 0` it is `r`.
    /// `∀` distributes over `∧`, so the eliminated conjunct may stay under the
    /// other binders it mentions; a conjunct affine in several binders loses
    /// them one pass at a time. A coefficient that never vanishes makes the
    /// universal `false` (the historical numeral rewrite), and so does one
    /// whose vanishing falsifies the rest (`∀v. (v·f(a) + f(a) < 0)`: `f(a) =
    /// 0` leaves `0 < 0`; [`poly::vanishing_falsifies_rest`]); a symbolic one
    /// keeps the case where it vanishes, which the earlier probe erased by
    /// reading `1 + w` with `w` set to 0 (D11 wrong UNSAT: `(forall v. (= (+ v
    /// (* v w)) 0))` holds at `w = −1`).
    ///
    /// A pass that splits nothing mints only the replaced probe's footprint,
    /// and a refuting pass mints nothing more than `false`.
    pub(super) fn eliminate_affine_binder_conjuncts(
        &mut self,
        body: TermId,
        vars: &[(String, Sort)],
    ) -> TermId {
        let mut current = body;
        for pass in 0..=vars.len() {
            // The conjuncts in the order the replaced probe visited them
            // (`collect_and_conjuncts`: a nested `and` before its leaves).
            let mut conjuncts = Vec::new();
            collect_and_conjuncts(&self.ctx.terms, current, &mut conjuncts);
            if conjuncts.is_empty() {
                conjuncts.push(current);
            }
            let mut leaves = Vec::with_capacity(conjuncts.len());
            for conjunct in conjuncts {
                if pass == 0 {
                    self.intern_replaced_probe_footprint(conjunct, &["=", "<", "<=", ">", ">="]);
                }
                if self.is_and(conjunct) {
                    continue;
                }
                let probe = self.affine_binder_probe(conjunct, vars);
                // `forall vars.(... and C and ...)` is false when `forall v.C`
                // is: a coefficient that never vanishes leaves `C` false at
                // some value of `v`, and one whose vanishing falsifies the rest
                // leaves no case where `C` holds identically.
                if probe
                    .as_ref()
                    .is_some_and(|probe| probe.never_vanishes || probe.vanishing_refutes)
                {
                    return self.ctx.terms.mk_bool(false);
                }
                leaves.push((conjunct, probe));
            }
            if leaves.iter().all(|(_, probe)| probe.is_none()) {
                break;
            }
            let mut eliminated = Vec::with_capacity(leaves.len());
            for (conjunct, probe) in leaves {
                eliminated.push(match probe {
                    Some(probe) => self.affine_conjunct_elimination(&probe),
                    None => conjunct,
                });
            }
            current = self.ctx.terms.mk_and(eliminated);
        }
        current
    }

    /// The terms the probe this module replaced (main f399eca07a's
    /// `atom_is_binder_infeasible`) interned for every relation it inspected:
    /// `0`, `1` and `L - R`, for an `Int` relation in `relations`. Interning
    /// them here keeps the term store of a formula this pass does not rewrite
    /// what it was before the elimination existed. Measured on
    /// `inc_26093_00136` (`--z3-mode`, the plain query after a quantified
    /// `check-sat-assuming`): with this footprint the search counters equal
    /// main's (conflicts 95, decisions 6,489, propagations 15,386, 2.9 s);
    /// minting nothing gives 370 / 41,169 / 104,479 and 7.3 s, and the first
    /// exact split, which minted `L - R` alone, was 2.5x slower too.
    fn intern_replaced_probe_footprint(&mut self, atom: TermId, relations: &[&str]) {
        let TermData::App(sym, args) = self.ctx.terms.get(atom) else {
            return;
        };
        if !relations.contains(&sym.name()) || args.len() != 2 {
            return;
        }
        let (lhs, rhs) = (args[0], args[1]);
        if !matches!(self.ctx.terms.sort(lhs), Sort::Int) {
            return;
        }
        // Interned for their term ids only.
        let _ = self.ctx.terms.mk_int(BigInt::zero());
        let _ = self.ctx.terms.mk_int(BigInt::one());
        let _ = self.ctx.terms.mk_sub(vec![lhs, rhs]);
    }

    fn is_and(&self, term: TermId) -> bool {
        matches!(self.ctx.terms.get(term), TermData::App(sym, _) if sym.name() == "and")
    }

    /// `(and (= c 0) (REL r 0))` for a probe whose coefficient may vanish
    /// (`(REL r 0)` alone when `c` is the numeral 0).
    fn affine_conjunct_elimination(&mut self, probe: &AffineBinderProbe) -> TermId {
        let (coefficient, rest) = self.affine_split_terms(probe);
        let zero = self.ctx.terms.mk_int(BigInt::zero());
        let rest_relation = match probe.relation.as_str() {
            "<" => self.ctx.terms.mk_lt(rest, zero),
            "<=" => self.ctx.terms.mk_le(rest, zero),
            ">" => self.ctx.terms.mk_gt(rest, zero),
            ">=" => self.ctx.terms.mk_ge(rest, zero),
            _ => self.ctx.terms.mk_eq(rest, zero),
        };
        match coefficient {
            None => rest_relation,
            Some(coefficient) => {
                let vanishes = self.ctx.terms.mk_eq(coefficient, zero);
                self.ctx.terms.mk_and(vec![vanishes, rest_relation])
            }
        }
    }

    /// Build `c` (`None` when it is the numeral 0) and `r` of a probe:
    /// `r = (L − R)[v:=0]`, `c = (L − R)[v:=1] − r`. Exact because the probe
    /// admitted `L` and `R` only when every occurrence of the binder is the
    /// binder's own `Var` reached through `+`, `-` and `*` — the positions
    /// [`Self::subst_term`] rewrites.
    fn affine_split_terms(&mut self, probe: &AffineBinderProbe) -> (Option<TermId>, TermId) {
        let d = self.ctx.terms.mk_sub(vec![probe.lhs, probe.rhs]);
        let zero = self.ctx.terms.mk_int(BigInt::zero());
        let rest = self.subst_term(d, probe.binder, zero);
        match &probe.numeral {
            Some(k) if k.is_zero() => (None, rest),
            Some(k) => (Some(self.ctx.terms.mk_int(k.clone())), rest),
            None => {
                let one = self.ctx.terms.mk_int(BigInt::one());
                let at_one = self.subst_term(d, probe.binder, one);
                (Some(self.ctx.terms.mk_sub(vec![at_one, rest])), rest)
            }
        }
    }

    /// For `(forall vars. (or operands))`: when EVERY binder-dependent operand
    /// is an `Int` equality affine in a binder ([`Self::affine_binder_probe`]),
    /// return `(or <binder-independent operands> <vanishing cases>)`.
    ///
    /// An affine equality `c·v + r = 0` with `c ≠ 0` holds at no more than one
    /// value of `v`, and a finite union of such single-point exceptions (in any
    /// binders) cannot cover the infinite Int domain; with `c = 0` it is
    /// `r = 0`, true for every value or for none. So a coefficient that never
    /// vanishes drops the operand, and any other contributes its vanishing
    /// case `(and (= c 0) (= r 0))` — admitted only when the operand mentions
    /// no binder of `vars` but the one eliminated, since the case must be a
    /// fact about the free symbols. Returns `None` (keep the forall) if the
    /// body is not an `or`, nothing changes, or a binder-dependent operand is
    /// anything else; the decision is read before a term is minted.
    ///
    /// Computing the result here — rather than hoisting `(∀v.(or Ai))` into a
    /// disjunction — avoids leaving a forall in a non-conjunctive position,
    /// where the instantiation loop conjoins instances unsoundly
    /// (#quant-or-infeasible).
    ///
    /// INEQUALITY operands are never dropped: one is true on a half-line, so
    /// `(forall z. (or (> z 5) (<= z 6)))` is TRUE.
    pub(super) fn forall_or_drop_infeasible_disjuncts(
        &mut self,
        body: TermId,
        vars: &[(String, Sort)],
    ) -> Option<TermId> {
        let TermData::App(sym, args) = self.ctx.terms.get(body).clone() else {
            return None;
        };
        if sym.name() != "or" || args.len() < 2 {
            return None;
        }
        let mut fates = Vec::with_capacity(args.len());
        for &op in &args {
            if !vars.iter().any(|(n, _)| self.term_mentions_name(op, n)) {
                fates.push(DisjunctFate::Keep);
                continue;
            }
            self.intern_replaced_probe_footprint(op, &["="]);
            let probe = self.affine_binder_probe(op, vars)?;
            if probe.relation != "=" {
                return None;
            }
            if probe.never_vanishes {
                fates.push(DisjunctFate::Drop);
                continue;
            }
            if probe.numeral.is_some() {
                return None;
            }
            let other_binder = vars
                .iter()
                .any(|(n, _)| *n != probe.binder_name && self.term_mentions_name(op, n));
            if other_binder {
                return None;
            }
            fates.push(DisjunctFate::Vanishing(probe));
        }
        if fates.iter().all(|fate| matches!(fate, DisjunctFate::Keep)) {
            return None;
        }
        let mut kept: Vec<TermId> = Vec::new();
        for (op, fate) in args.into_iter().zip(fates) {
            match fate {
                DisjunctFate::Keep => kept.push(op),
                DisjunctFate::Drop => {}
                DisjunctFate::Vanishing(probe) => {
                    let (coefficient, rest) = self.affine_split_terms(&probe);
                    let coefficient = coefficient?;
                    let zero = self.ctx.terms.mk_int(BigInt::zero());
                    let vanishes = self.ctx.terms.mk_eq(coefficient, zero);
                    let rest = self.ctx.terms.mk_eq(rest, zero);
                    kept.push(self.ctx.terms.mk_and(vec![vanishes, rest]));
                }
            }
        }
        Some(match kept.as_slice() {
            [] => self.ctx.terms.mk_bool(false),
            [single] => *single,
            _ => self.ctx.terms.mk_or(kept),
        })
    }

    /// Read an `Int` (in)equality `(REL L R)` (`REL ∈ {=,<,<=,>,>=}`) as
    /// `L − R = c·v + r` for the first `Int` binder `v` of `vars` it is affine
    /// in, without minting a term.
    ///
    /// Affine means: every occurrence of the binder's NAME in `L` and `R` is
    /// the binder's own `Var`, reached from the root through `Int` `+`, `-`
    /// and a `*` with the binder in one factor ([`Self::binder_affine_in`]).
    /// An occurrence anywhere else — under an uninterpreted or other
    /// application, an `ite` (condition or branch), a `not`, a `let`, or a
    /// NESTED QUANTIFIER — is not affine, and the binder is skipped. The
    /// nested quantifier is the 2026-09-25 B1 wrong UNSAT: `v·(1 + 2·ite(∃u.
    /// u ≥ 0 ∧ u = v, 1, −1)) ≥ 0` is `3v` for `v ≥ 0` and `−v` below, valid,
    /// and was refuted because the `v` under `∃u` was read as a constant.
    /// Declining an inner binder that merely shadows the name is conservative.
    ///
    /// `c` and `r` are then free of `v` exactly; `c` is read as a polynomial
    /// over the `Int` atoms it multiplies ([`Self::binder_coefficient_poly`]).
    pub(super) fn affine_binder_probe(
        &self,
        atom: TermId,
        vars: &[(String, Sort)],
    ) -> Option<AffineBinderProbe> {
        let TermData::App(sym, args) = self.ctx.terms.get(atom) else {
            return None;
        };
        let relation = sym.name();
        if !matches!(relation, "=" | "<" | "<=" | ">" | ">=") || args.len() != 2 {
            return None;
        }
        let (lhs, rhs) = (args[0], args[1]);
        if !matches!(self.ctx.terms.sort(lhs), Sort::Int)
            || !matches!(self.ctx.terms.sort(rhs), Sort::Int)
        {
            return None;
        }
        for (name, sort) in vars {
            if !matches!(sort, Sort::Int) {
                continue;
            }
            // The parser creates fresh per-scope bound vars, so `mk_var(name)`
            // does NOT recover the body's binder; find its actual hash-consed
            // `Var(name, _)` term instead.
            let Some(binder) = self
                .find_bound_var_id(lhs, name)
                .or_else(|| self.find_bound_var_id(rhs, name))
            else {
                continue;
            };
            let mentioning = self.subterms_mentioning_name(atom, name);
            if !self.binder_affine_in(lhs, binder, &mentioning)
                || !self.binder_affine_in(rhs, binder, &mentioning)
            {
                continue;
            }
            let coefficient = match (
                self.binder_coefficient_poly(lhs, binder, &mentioning, 0),
                self.binder_coefficient_poly(rhs, binder, &mentioning, 0),
            ) {
                (Some(l), Some(r)) => poly_sub(l, &r),
                _ => None,
            };
            let (numeral, never_vanishes) = match &coefficient {
                Some(poly) => {
                    let numeral = poly_numeral(poly);
                    let never_vanishes = match &numeral {
                        Some(k) => !k.is_zero(),
                        None => poly_never_vanishes(poly),
                    };
                    (numeral, never_vanishes)
                }
                None => (None, false),
            };
            let vanishing_refutes = match &coefficient {
                Some(c) if numeral.is_none() && !never_vanishes => {
                    let rest = match (
                        self.binder_rest_poly(lhs, binder, &mentioning, 0),
                        self.binder_rest_poly(rhs, binder, &mentioning, 0),
                    ) {
                        (Some(l), Some(r)) => poly_sub(l, &r),
                        _ => None,
                    };
                    rest.is_some_and(|r| vanishing_falsifies_rest(c, &r, relation))
                }
                _ => false,
            };
            return Some(AffineBinderProbe {
                relation: relation.to_string(),
                lhs,
                rhs,
                binder,
                binder_name: name.clone(),
                numeral,
                never_vanishes,
                vanishing_refutes,
            });
        }
        None
    }

    /// Every subterm of `root` that mentions a `Var` named `name`, descending
    /// every node kind — applications, `not`, `ite`, `let` bindings and body,
    /// and quantifier bodies (an inner binder of the same name counts: the
    /// callers only decline on it).
    fn subterms_mentioning_name(&self, root: TermId, name: &str) -> DetHashSet<TermId> {
        let mut mentioning: DetHashSet<TermId> = DetHashSet::default();
        let mut visited: DetHashSet<TermId> = DetHashSet::default();
        // (term, children already pushed)
        let mut stack = vec![(root, false)];
        while let Some((t, expanded)) = stack.pop() {
            let children = self.term_children(t);
            if expanded {
                let direct = matches!(self.ctx.terms.get(t), TermData::Var(n, _) if n == name);
                if direct || children.iter().any(|c| mentioning.contains(c)) {
                    mentioning.insert(t);
                }
                continue;
            }
            if !visited.insert(t) {
                continue;
            }
            stack.push((t, true));
            stack.extend(
                children
                    .into_iter()
                    .filter(|c| !visited.contains(c))
                    .map(|c| (c, false)),
            );
        }
        mentioning
    }

    /// The direct subterms of `t`, of every node kind.
    fn term_children(&self, t: TermId) -> Vec<TermId> {
        match self.ctx.terms.get(t) {
            TermData::App(_, args) => args.clone(),
            TermData::Not(inner) => vec![*inner],
            TermData::Ite(c, a, b) => vec![*c, *a, *b],
            TermData::Let(bindings, body) => bindings
                .iter()
                .map(|(_, value)| *value)
                .chain(std::iter::once(*body))
                .collect(),
            TermData::Forall(_, body, _) | TermData::Exists(_, body, _) => vec![*body],
            _ => Vec::new(),
        }
    }

    /// Whether `t` is affine in `binder`: `t` is the binder, or mentions its
    /// name nowhere (`mentioning` is [`Self::subterms_mentioning_name`]), or
    /// is an `Int` `+` / `-` of affine terms, or an `Int` `*` with the name in
    /// at most one factor, that factor affine. Anything else that mentions the
    /// name is not affine.
    fn binder_affine_in(&self, t: TermId, binder: TermId, mentioning: &DetHashSet<TermId>) -> bool {
        if t == binder || !mentioning.contains(&t) {
            return true;
        }
        let TermData::App(sym, args) = self.ctx.terms.get(t) else {
            return false;
        };
        if !matches!(self.ctx.terms.sort(t), Sort::Int) {
            return false;
        }
        match sym.name() {
            "+" | "-" => args
                .iter()
                .all(|&a| self.binder_affine_in(a, binder, mentioning)),
            "*" => {
                let mut with_binder = args.iter().filter(|&a| mentioning.contains(a));
                match (with_binder.next(), with_binder.next()) {
                    (Some(&factor), None) => self.binder_affine_in(factor, binder, mentioning),
                    _ => false,
                }
            }
            _ => false,
        }
    }
}
