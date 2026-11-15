// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The approximation `⌊φ⌋Γ` (plan §3.2; FMSD'17 §6).
//!
//! Every instance a node logs is FROZEN at the moment it is generated: the
//! logged formula is `⌊ψ_N[k, t]⌋Γ` as it stood then, a quantifier-free term
//! over the node's environment `k`. A node occurrence is approximated by the
//! conjunction (authored `forall`) or disjunction (authored `exists`) of its
//! frozen instances, with the environment substituted by the occurrence's
//! context `ρ`. Because instances are generated only when every child of the
//! node is exact (Lemma 10.1), each frozen instance is EQUIVALENT to the true
//! instance `ψ_N[k, t]`, whatever the children log afterwards.
//!
//! Every construction here is a plain quantifier-free term rebuild: no
//! simplification beyond the store's `and`/`or` flattening, and caps that
//! DECLINE (never truncate).

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::term::{Constant, Symbol, TermData};
use ay_core::{Sort, TermId, TermStore};
use num_bigint::BigInt;
use num_integer::Integer;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};

use super::caps::MAX_APPROX_NODES;
use super::ntree::{Kind, NestedTree};
use super::QlraDecline;
use crate::qe::linrat::{parse_lin, rat_const};

/// Stack red zone / growth for the recursive rebuilds (deep let-expanded
/// bodies).
const STACK_RED_ZONE: usize = 64 * 1024;
const STACK_SIZE: usize = 2 * 1024 * 1024;

/// One frozen instance of a node.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct NInstance {
    /// Positional binder values over the node's environment.
    pub(crate) tuple: Vec<TermId>,
    /// `⌊ψ_N[k, tuple]⌋Γ` at generation time.
    pub(crate) frozen: TermId,
    pub(crate) round: usize,
}

/// A substitution of counterexample constants, sorted by key.
pub(crate) type Rho = Vec<(TermId, TermId)>;

/// Memoized builder of approximations and substitutions.
#[derive(Default)]
pub(crate) struct Approximator {
    rho_ids: HashMap<Rho, u32>,
    subst_memo: HashMap<(TermId, u32), TermId>,
    approx_memo: HashMap<(TermId, u32), TermId>,
    has_node: HashMap<TermId, bool>,
    work: usize,
    /// Largest per-build work seen (for `--stats`).
    pub(crate) max_work: usize,
}

fn cap() -> QlraDecline {
    QlraDecline::Cap("cap-approx")
}

impl Approximator {
    /// Γ changed: approximations (not substitutions) are stale.
    pub(crate) fn gamma_changed(&mut self) {
        self.approx_memo.clear();
    }

    fn rho_id(&mut self, rho: &[(TermId, TermId)]) -> u32 {
        if let Some(&id) = self.rho_ids.get(rho) {
            return id;
        }
        let id = u32::try_from(self.rho_ids.len()).unwrap_or(u32::MAX);
        self.rho_ids.insert(rho.to_vec(), id);
        id
    }

    fn tick(&mut self) -> Result<(), QlraDecline> {
        self.work += 1;
        self.max_work = self.max_work.max(self.work);
        if self.work > MAX_APPROX_NODES {
            return Err(cap());
        }
        Ok(())
    }

    fn subst_rec(
        &mut self,
        terms: &mut TermStore,
        term: TermId,
        rho: &[(TermId, TermId)],
        id: u32,
    ) -> Result<TermId, QlraDecline> {
        if let Some(&done) = self.subst_memo.get(&(term, id)) {
            return Ok(done);
        }
        self.tick()?;
        let out = stacker::maybe_grow(STACK_RED_ZONE, STACK_SIZE, || {
            Ok::<TermId, QlraDecline>(match terms.get(term).clone() {
                TermData::Var(..) => match rho.binary_search_by_key(&term, |(k, _)| *k) {
                    Ok(at) => rho[at].1,
                    Err(_) => term,
                },
                TermData::App(symbol, args) => {
                    let mut rewritten = Vec::with_capacity(args.len());
                    for &arg in &args {
                        rewritten.push(self.subst_rec(terms, arg, rho, id)?);
                    }
                    if rewritten == args {
                        term
                    } else {
                        let sort = terms.sort(term).clone();
                        rebuild_app(terms, symbol, rewritten, sort)
                    }
                }
                TermData::Not(inner) => {
                    let rewritten = self.subst_rec(terms, inner, rho, id)?;
                    if rewritten == inner {
                        term
                    } else {
                        rebuild_not(terms, rewritten)
                    }
                }
                TermData::Ite(c, a, b) => {
                    let c2 = self.subst_rec(terms, c, rho, id)?;
                    let a2 = self.subst_rec(terms, a, rho, id)?;
                    let b2 = self.subst_rec(terms, b, rho, id)?;
                    if (c2, a2, b2) == (c, a, b) {
                        term
                    } else {
                        rebuild_ite(terms, c2, a2, b2)
                    }
                }
                TermData::Const(_) => term,
                // Quantified terms never reach a substitution: the caller
                // approximates them first.
                _ => return Err(QlraDecline::Substitution),
            })
        })?;
        self.subst_memo.insert((term, id), out);
        Ok(out)
    }

    /// Whether `term` contains a node's quantifier subterm.
    fn contains_node(&mut self, terms: &TermStore, tree: &NestedTree, term: TermId) -> bool {
        if let Some(&known) = self.has_node.get(&term) {
            return known;
        }
        let known = tree.node_of.contains_key(&term)
            || match terms.get(term) {
                TermData::App(_, args) => args
                    .clone()
                    .iter()
                    .any(|&a| self.contains_node(terms, tree, a)),
                TermData::Not(inner) => self.contains_node(terms, tree, *inner),
                TermData::Ite(c, a, b) => {
                    let (c, a, b) = (*c, *a, *b);
                    self.contains_node(terms, tree, c)
                        || self.contains_node(terms, tree, a)
                        || self.contains_node(terms, tree, b)
                }
                _ => false,
            };
        self.has_node.insert(term, known);
        known
    }

    /// `⌊term⌋Γ[ρ]`: every node occurrence replaced by its frozen instances.
    pub(crate) fn approx(
        &mut self,
        terms: &mut TermStore,
        tree: &NestedTree,
        gamma: &[Vec<NInstance>],
        term: TermId,
        rho: &[(TermId, TermId)],
    ) -> Result<TermId, QlraDecline> {
        let id = self.rho_id(rho);
        self.work = 0;
        self.approx_rec(terms, tree, gamma, term, rho, id)
    }

    fn approx_rec(
        &mut self,
        terms: &mut TermStore,
        tree: &NestedTree,
        gamma: &[Vec<NInstance>],
        term: TermId,
        rho: &[(TermId, TermId)],
        id: u32,
    ) -> Result<TermId, QlraDecline> {
        if let Some(&done) = self.approx_memo.get(&(term, id)) {
            return Ok(done);
        }
        let out = if let Some(&node) = tree.node_of.get(&term) {
            self.node_rec(terms, tree, gamma, node, rho, id)?
        } else if !self.contains_node(terms, tree, term) {
            self.subst_rec(terms, term, rho, id)?
        } else {
            self.tick()?;
            stacker::maybe_grow(STACK_RED_ZONE, STACK_SIZE, || {
                self.rebuild(terms, tree, gamma, term, rho, id)
            })?
        };
        self.approx_memo.insert((term, id), out);
        Ok(out)
    }

    fn rebuild(
        &mut self,
        terms: &mut TermStore,
        tree: &NestedTree,
        gamma: &[Vec<NInstance>],
        term: TermId,
        rho: &[(TermId, TermId)],
        id: u32,
    ) -> Result<TermId, QlraDecline> {
        Ok(match terms.get(term).clone() {
            TermData::App(symbol, args) => {
                let mut rewritten = Vec::with_capacity(args.len());
                for &arg in &args {
                    rewritten.push(self.approx_rec(terms, tree, gamma, arg, rho, id)?);
                }
                let sort = terms.sort(term).clone();
                rebuild_app(terms, symbol, rewritten, sort)
            }
            TermData::Not(inner) => {
                let rewritten = self.approx_rec(terms, tree, gamma, inner, rho, id)?;
                rebuild_not(terms, rewritten)
            }
            TermData::Ite(c, a, b) => {
                let c2 = self.approx_rec(terms, tree, gamma, c, rho, id)?;
                let a2 = self.approx_rec(terms, tree, gamma, a, rho, id)?;
                let b2 = self.approx_rec(terms, tree, gamma, b, rho, id)?;
                rebuild_ite(terms, c2, a2, b2)
            }
            _ => return Err(QlraDecline::Substitution),
        })
    }

    /// `⌊N⌋Γ[ρ]` for node `node`.
    pub(crate) fn node(
        &mut self,
        terms: &mut TermStore,
        tree: &NestedTree,
        gamma: &[Vec<NInstance>],
        node: usize,
        rho: &[(TermId, TermId)],
    ) -> Result<TermId, QlraDecline> {
        let id = self.rho_id(rho);
        self.work = 0;
        self.node_rec(terms, tree, gamma, node, rho, id)
    }

    fn node_rec(
        &mut self,
        terms: &mut TermStore,
        tree: &NestedTree,
        gamma: &[Vec<NInstance>],
        node: usize,
        rho: &[(TermId, TermId)],
        id: u32,
    ) -> Result<TermId, QlraDecline> {
        let mut parts = Vec::with_capacity(gamma[node].len());
        for instance in &gamma[node] {
            parts.push(self.subst_rec(terms, instance.frozen, rho, id)?);
        }
        Ok(combine(terms, tree.nodes[node].kind, parts))
    }
}

fn bool_const(terms: &TermStore, term: TermId) -> Option<bool> {
    match terms.get(term) {
        TermData::Const(Constant::Bool(b)) => Some(*b),
        _ => None,
    }
}

/// Rebuild an application after substitution. The search only needs an
/// EQUIVALENT formula, so it normalizes: Boolean `and`/`or` go through the
/// store's folding constructors, and a linear arithmetic atom becomes
/// `Σ aᵢ·xᵢ ⋈ c` (`⋈ ∈ {<, <=, =}`, coprime integers) or folds to a
/// constant when no variable is left. Normalizing keeps substituted
/// templates from piling up nested products the probe's LRA solver must
/// re-normalize, and lets equal atoms hash-cons to one term.
fn rebuild_app(terms: &mut TermStore, symbol: Symbol, args: Vec<TermId>, sort: Sort) -> TermId {
    match symbol.name() {
        "and" if matches!(sort, Sort::Bool) => return terms.mk_and(args),
        "or" if matches!(sort, Sort::Bool) => return terms.mk_or(args),
        name => {
            if let Some(atom) = normalize_atom(terms, name, &args) {
                return atom;
            }
        }
    }
    terms.mk_app(symbol, args, sort)
}

fn rebuild_not(terms: &mut TermStore, inner: TermId) -> TermId {
    match bool_const(terms, inner) {
        Some(b) => terms.mk_bool(!b),
        None => terms.mk_not_raw(inner),
    }
}

fn rebuild_ite(terms: &mut TermStore, c: TermId, a: TermId, b: TermId) -> TermId {
    match bool_const(terms, c) {
        Some(true) => a,
        Some(false) => b,
        None => terms.mk_ite_raw(c, a, b),
    }
}

fn is_real_side(terms: &TermStore, t: TermId) -> bool {
    matches!(terms.sort(t), Sort::Real) || rat_const(terms, t).is_some()
}

/// `lhs ⋈ rhs` as a canonical linear atom (see [`rebuild_app`]).
fn normalize_atom(terms: &mut TermStore, name: &str, args: &[TermId]) -> Option<TermId> {
    let [lhs, rhs] = args else {
        return None;
    };
    let (op, flip) = match name {
        "<" => ("<", false),
        "<=" => ("<=", false),
        ">" => ("<", true),
        ">=" => ("<=", true),
        "=" if is_real_side(terms, *lhs) && is_real_side(terms, *rhs) => ("=", false),
        _ => return None,
    };
    let l = parse_lin(terms, *lhs)?;
    let r = parse_lin(terms, *rhs)?;
    let mut diff = if flip { r.clone() } else { l.clone() };
    diff.sub(if flip { &l } else { &r });
    if diff.coeffs.is_empty() {
        let v = &diff.constant;
        let holds = match op {
            "<" => v.is_negative(),
            "<=" => !v.is_positive(),
            _ => v.is_zero(),
        };
        return Some(terms.mk_bool(holds));
    }
    // Scale to coprime INTEGER coefficients (positively, so the relation is
    // kept; an equation also fixes the sign of its first coefficient):
    // integral rows keep the probe's simplex away from big-rational growth.
    let mut lcm = BigInt::one();
    let mut gcd = BigInt::zero();
    for c in diff.coeffs.values().chain(std::iter::once(&diff.constant)) {
        lcm = lcm.lcm(c.denom());
        gcd = gcd.gcd(c.numer());
    }
    let mut factor = BigRational::new(lcm, gcd.abs().max(BigInt::one()));
    if op == "=" && diff.coeffs.values().next()?.is_negative() {
        factor = -factor;
    }
    diff.scale(&factor);
    let bound = -diff.constant.clone();
    diff.constant = BigRational::zero();
    let left = diff.to_term(terms);
    let right = terms.mk_rational(bound);
    Some(terms.mk_app(Symbol::named(op), vec![left, right], Sort::Bool))
}

/// `∧ parts` for a universal, `∨ parts` for an existential (empty: ⊤ / ⊥).
pub(crate) fn combine(terms: &mut TermStore, kind: Kind, parts: Vec<TermId>) -> TermId {
    match (kind, parts.is_empty()) {
        (Kind::Forall, true) => terms.mk_bool(true),
        (Kind::Exists, true) => terms.mk_bool(false),
        (Kind::Forall, false) => terms.mk_and(parts),
        (Kind::Exists, false) => terms.mk_or(parts),
    }
}

/// DAG size of a query (for `--stats`), bounded by `limit`.
pub(crate) fn dag_size(terms: &TermStore, roots: &[TermId], limit: usize) -> usize {
    let mut seen = ay_core::kani_compat::DetHashSet::default();
    let mut stack: Vec<TermId> = roots.to_vec();
    while let Some(t) = stack.pop() {
        if seen.len() >= limit || !seen.insert(t) {
            continue;
        }
        match terms.get(t) {
            TermData::App(_, args) => stack.extend(args.iter().copied()),
            TermData::Not(inner) => stack.push(*inner),
            TermData::Ite(c, a, b) => stack.extend([*c, *a, *b]),
            _ => {}
        }
    }
    seen.len()
}
