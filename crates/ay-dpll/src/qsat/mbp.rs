// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Model-based projection of a cube (Bjørner–Janota, LPAR-20).
//!
//! Input: a conjunction `C` of atom literals, true in the model `M`, and the
//! variables `V` of one level. Output: a conjunction `P` over the remaining
//! variables with `M ⊨ P` and `P ⇒ ∃V. C`, plus, for every eliminated
//! arithmetic variable, the TERM it was replaced by. The image is finite
//! over all models, which is what terminates the game.
//!
//! * `Real` (Loos–Weispfenning under the model): a true equality solves the
//!   variable; otherwise the substitution is the greatest lower bound, the
//!   least upper bound, their midpoint, or a bound `± 1`, chosen so that every
//!   literal keeps its truth value in `M` (model preservation). Every choice
//!   is a linear term, so `P = C[v := t]` is an INSTANCE, not a virtual term.
//! * `Int` (Cooper under the model): a true equality `a·v + r = 0` resolves
//!   (adding `|a| ∣ r` when `|a| ≠ 1`); otherwise coefficients are normalized
//!   to `±1` over `w = L·v` (adding `L ∣ w`), and `w := ℓ* + ((M(w) − M(ℓ*))
//!   mod D)` for the largest lower bound `ℓ*` and `D` the lcm of the
//!   divisors (symmetrically from the least upper bound, or a residue when
//!   there are no bounds). The term for `v` is `w`'s term divided by `L`,
//!   exact inside `P`, which carries `L ∣ w`.
//! * `Bool`: literals over the variable are dropped.
//!
//! Every output literal is re-evaluated in `M`; any failure declines.

use ay_core::kani_compat::DetHashSet as HashSet;
use ay_core::term::{Symbol, TermData};
use ay_core::{Sort, TermId, TermStore};
use num_bigint::BigInt;
use num_integer::Integer;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};

use super::lin::{int_numeral, lin_of, Eval, Lin, Model, Val};

mod build;
mod int;

pub(crate) use super::subst::substitute;
use build::build;
use int::{eliminate_int, IntSubst};

/// `lin ⋈ 0`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Rel {
    Le,
    Lt,
    Eq,
    Ne,
}

#[derive(Clone, Debug)]
enum Lit {
    Arith(Rel, Lin),
    /// `d ∣ lin` (or its negation when `!pos`).
    Div(BigInt, Lin, bool),
    /// An atom literal that mentions no eliminated variable.
    Keep(TermId, bool),
}

/// Why a projection declined.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum MbpDecline {
    Parse,
    MixedIntReal,
    Model,
    Preservation,
    Build,
}

impl MbpDecline {
    pub(crate) fn label(self) -> &'static str {
        match self {
            Self::Parse => "mbp-parse",
            Self::MixedIntReal => "mbp-mixed-int-real",
            Self::Model => "mbp-model",
            Self::Preservation => "mbp-preservation",
            Self::Build => "mbp-build",
        }
    }
}

/// The projection result.
#[derive(Clone, Debug, Default)]
pub(crate) struct Projection {
    /// Projected literals `(atom, value)`.
    pub(crate) lits: Vec<(TermId, bool)>,
    /// `(eliminated variable, replacement term)` for arithmetic variables,
    /// each over the non-eliminated variables only.
    pub(crate) subst: Vec<(TermId, TermId)>,
}

fn diff(a: &Lin, b: &Lin) -> Lin {
    let mut d = a.clone();
    d.sub(b);
    d
}

/// Parse `(atom = value)` into a literal over `lin ⋈ 0`.
fn parse(terms: &TermStore, atom: TermId, value: bool) -> Option<Lit> {
    let TermData::App(sym, args) = terms.get(atom) else {
        return None;
    };
    if args.len() != 2 {
        return None;
    }
    let (a, b) = (args[0], args[1]);
    let name = sym.name();
    if name == "=" {
        // Divisibility `(= (mod e d) k)`, `0 <= k < |d|`, in either
        // orientation: `|d|` divides `e - k`.
        for (m, z) in [(a, b), (b, a)] {
            let (Some(k), TermData::App(ms, margs)) = (int_numeral(terms, z), terms.get(m)) else {
                continue;
            };
            if ms.name() != "mod" || margs.len() != 2 {
                continue;
            }
            let d = int_numeral(terms, margs[1])?.abs();
            if d.is_zero() {
                return None;
            }
            if k.is_negative() || k >= d {
                return None;
            }
            let mut e = lin_of(terms, margs[0])?;
            e.constant -= BigRational::from_integer(k);
            return Some(Lit::Div(d, e, value));
        }
    }
    let la = lin_of(terms, a)?;
    let lb = lin_of(terms, b)?;
    Some(match (name, value) {
        ("<=", true) => Lit::Arith(Rel::Le, diff(&la, &lb)),
        ("<=", false) => Lit::Arith(Rel::Lt, diff(&lb, &la)),
        ("<", true) => Lit::Arith(Rel::Lt, diff(&la, &lb)),
        ("<", false) => Lit::Arith(Rel::Le, diff(&lb, &la)),
        (">=", true) => Lit::Arith(Rel::Le, diff(&lb, &la)),
        (">=", false) => Lit::Arith(Rel::Lt, diff(&la, &lb)),
        (">", true) => Lit::Arith(Rel::Lt, diff(&lb, &la)),
        (">", false) => Lit::Arith(Rel::Le, diff(&la, &lb)),
        ("=", true) => Lit::Arith(Rel::Eq, diff(&la, &lb)),
        ("=", false) => Lit::Arith(Rel::Ne, diff(&la, &lb)),
        _ => return None,
    })
}

fn mentions_any(terms: &TermStore, t: TermId, vars: &HashSet<TermId>) -> bool {
    let mut stack = vec![t];
    let mut seen = HashSet::default();
    while let Some(x) = stack.pop() {
        if !seen.insert(x) {
            continue;
        }
        if vars.contains(&x) {
            return true;
        }
        match terms.get(x) {
            TermData::App(_, args) => stack.extend(args.iter().copied()),
            TermData::Not(i) => stack.push(*i),
            TermData::Ite(c, a, b) => stack.extend([*c, *a, *b]),
            _ => {}
        }
    }
    false
}

fn holds(lit: &Lit, m: &Model) -> Option<bool> {
    Some(match lit {
        Lit::Arith(rel, lin) => {
            let v = lin.eval(m)?;
            match rel {
                Rel::Le => v <= BigRational::zero(),
                Rel::Lt => v < BigRational::zero(),
                Rel::Eq => v.is_zero(),
                Rel::Ne => !v.is_zero(),
            }
        }
        Lit::Div(d, lin, pos) => {
            let v = lin.eval(m)?;
            if !v.is_integer() {
                return None;
            }
            (v.to_integer().mod_floor(d).is_zero()) == *pos
        }
        Lit::Keep(..) => true,
    })
}

fn int_lcm(a: &BigInt, b: &BigInt) -> BigInt {
    a.lcm(b)
}

/// Scale an integer literal to integral coefficients (positive factor).
fn integralize(lit: Lit) -> Lit {
    match lit {
        Lit::Arith(rel, lin) => {
            let s = BigRational::from_integer(lin.denom_lcm());
            Lit::Arith(rel, lin.scaled(&s))
        }
        Lit::Div(d, lin, pos) => {
            let s = lin.denom_lcm();
            Lit::Div(d * &s, lin.scaled(&BigRational::from_integer(s)), pos)
        }
        keep => keep,
    }
}

/// Eliminate one `Real` variable by model-preserving substitution.
fn eliminate_real(v: TermId, lits: &mut [Lit], m: &Model) -> Result<Lin, MbpDecline> {
    let mv = m.num(v).cloned().unwrap_or_else(BigRational::zero);
    // (term, value, strict)
    let mut lower: Option<(Lin, BigRational, bool)> = None;
    let mut upper: Option<(Lin, BigRational, bool)> = None;
    let mut solved: Option<Lin> = None;
    for lit in lits.iter() {
        let Lit::Arith(rel, lin) = lit else {
            continue;
        };
        let a = lin.coeff(v);
        if a.is_zero() {
            continue;
        }
        // a·v + r ⋈ 0  ⇒  v ⋈' −r/a
        let mut bound = lin.without(v);
        bound.scale(&(-a.recip()));
        let value = bound.eval(m).ok_or(MbpDecline::Model)?;
        let (is_lower, strict) = match rel {
            Rel::Eq => {
                if solved.is_none() {
                    solved = Some(bound);
                }
                continue;
            }
            Rel::Le => (a.is_negative(), false),
            Rel::Lt => (a.is_negative(), true),
            Rel::Ne => (mv > value, true),
        };
        let slot = if is_lower { &mut lower } else { &mut upper };
        let better = match slot {
            None => true,
            Some((_, bv, bs)) if is_lower => value > *bv || (value == *bv && strict && !*bs),
            Some((_, bv, bs)) => value < *bv || (value == *bv && strict && !*bs),
        };
        if better {
            *slot = Some((bound, value, strict));
        }
    }
    let t = if let Some(t) = solved {
        t
    } else {
        match (lower, upper) {
            (Some((l, lv, _)), Some((_, uv, _))) if lv == uv => l,
            (Some((l, _, _)), Some((u, _, _))) => {
                let mut mid = l;
                mid.add(&u);
                mid.scale(&BigRational::new(1.into(), 2.into()));
                mid
            }
            (Some((l, _, _)), None) => {
                let mut t = l;
                t.constant += BigRational::one();
                t
            }
            (None, Some((u, _, _))) => {
                let mut t = u;
                t.constant -= BigRational::one();
                t
            }
            (None, None) => Lin::zero(),
        }
    };
    for lit in lits.iter_mut() {
        if let Lit::Arith(_, lin) = lit {
            if lin.mentions(v) {
                *lin = lin.subst(v, &t);
            }
        }
    }
    Ok(t)
}

/// Parse the cube: literals over eliminated variables become arithmetic or
/// divisibility literals (each re-checked in the model); the rest are kept.
fn parse_cube(
    terms: &TermStore,
    cube: &[(TermId, bool)],
    elim: &HashSet<TermId>,
    model: &Model,
) -> Result<Vec<Lit>, MbpDecline> {
    let mut lits: Vec<Lit> = Vec::with_capacity(cube.len());
    for &(atom, value) in cube {
        if !mentions_any(terms, atom, elim) {
            lits.push(Lit::Keep(atom, value));
            continue;
        }
        if elim.contains(&atom) {
            // A Boolean variable being eliminated.
            continue;
        }
        let lit = parse(terms, atom, value).ok_or(MbpDecline::Parse)?;
        if holds(&lit, model) != Some(true) {
            return Err(MbpDecline::Model);
        }
        lits.push(lit);
    }
    Ok(lits)
}

/// Eliminate one `Int` variable from the literals that mention it.
fn eliminate_int_var(
    terms: &TermStore,
    v: TermId,
    lits: &mut Vec<Lit>,
    model: &Model,
) -> Result<IntSubst, MbpDecline> {
    let mut rest: Vec<Lit> = Vec::with_capacity(lits.len());
    let mut with_v: Vec<Lit> = Vec::new();
    for lit in lits.drain(..) {
        match &lit {
            Lit::Arith(_, lin) | Lit::Div(_, lin, _) if lin.mentions(v) => {
                // Every literal over an integer variable must be purely integer.
                if !lin.all_int(terms) {
                    return Err(MbpDecline::MixedIntReal);
                }
                with_v.push(integralize(lit));
            }
            _ => rest.push(lit),
        }
    }
    let s = eliminate_int(v, &mut with_v, model)?;
    rest.extend(with_v);
    *lits = rest;
    Ok(s)
}

/// The replacement terms, back-substituted so each is over surviving
/// variables only (later eliminations may appear in earlier terms).
fn replacement_terms(
    terms: &mut TermStore,
    pending: &[(TermId, Replacement)],
) -> Result<Vec<(TermId, TermId)>, MbpDecline> {
    let mut built: Vec<(TermId, TermId)> = Vec::with_capacity(pending.len());
    for (v, r) in pending.iter().rev() {
        let t = match r {
            Replacement::Bool(b) => terms.mk_bool(*b),
            Replacement::Real(lin) => lin.to_term(terms, &Sort::Real).ok_or(MbpDecline::Build)?,
            Replacement::Int(IntSubst::Term(lin)) => {
                lin.to_term(terms, &Sort::Int).ok_or(MbpDecline::Build)?
            }
            Replacement::Int(IntSubst::Div(lin, k)) => {
                let n = lin.to_term(terms, &Sort::Int).ok_or(MbpDecline::Build)?;
                let kt = terms.mk_int(k.clone());
                terms.mk_app(Symbol::named("div"), vec![n, kt], Sort::Int)
            }
        };
        let t = substitute(terms, t, &built);
        built.push((*v, t));
    }
    built.reverse();
    Ok(built)
}

/// Project `vars` out of `cube` under `model`.
pub(crate) fn project(
    terms: &mut TermStore,
    cube: &[(TermId, bool)],
    vars: &[TermId],
    model: &Model,
) -> Result<Projection, MbpDecline> {
    let elim: HashSet<TermId> = vars.iter().copied().collect();
    let mut lits = parse_cube(terms, cube, &elim, model)?;
    // Replacement per variable, in elimination order, before back-substitution.
    let mut pending: Vec<(TermId, Replacement)> = Vec::new();
    for &v in vars {
        let r = match terms.sort(v).clone() {
            // Literals over `v` were dropped; the model value is the move.
            Sort::Bool => {
                Replacement::Bool(model.vals.get(&v).and_then(Val::boolean).unwrap_or(false))
            }
            Sort::Real => Replacement::Real(eliminate_real(v, &mut lits, model)?),
            Sort::Int => Replacement::Int(eliminate_int_var(terms, v, &mut lits, model)?),
            _ => return Err(MbpDecline::Parse),
        };
        pending.push((v, r));
    }
    // Every projected literal must still hold in the model.
    if lits.iter().any(|lit| holds(lit, model) != Some(true)) {
        return Err(MbpDecline::Preservation);
    }
    let mut out = Vec::with_capacity(lits.len());
    let mut seen: HashSet<(TermId, bool)> = HashSet::default();
    for lit in &lits {
        if let Some(pair) = build(terms, lit)? {
            if seen.insert(pair) {
                out.push(pair);
            }
        }
    }
    let subst = replacement_terms(terms, &pending)?;
    // Defensive: each projected atom evaluates as recorded.
    let mut ev = Eval::new(terms, model);
    if out.iter().any(|&(a, v)| ev.boolean(a) != Some(v)) {
        return Err(MbpDecline::Preservation);
    }
    Ok(Projection { lits: out, subst })
}

/// What one eliminated variable was replaced by, before term building.
enum Replacement {
    Bool(bool),
    Real(Lin),
    Int(IntSubst),
}

/// `t` with every arithmetic atom replaced by its canonical form (the atom
/// [`build`] makes from its parsed literal): constant atoms folded to
/// `true`/`false`, `to_real` and like terms merged, integer bounds and
/// divisibility normalized. An exact equivalence: each rewrite is the one
/// projection itself relies on. Atoms outside the fragment are kept.
pub(crate) fn canonical_atoms(
    terms: &mut TermStore,
    t: TermId,
    memo: &mut ay_core::kani_compat::DetHashMap<TermId, TermId>,
) -> TermId {
    if let Some(&r) = memo.get(&t) {
        return r;
    }
    let r = match terms.get(t).clone() {
        TermData::Not(i) => {
            let n = canonical_atoms(terms, i, memo);
            terms.mk_not_raw(n)
        }
        TermData::Ite(c, a, b) if matches!(terms.sort(t), Sort::Bool) => {
            let (c, a, b) = (
                canonical_atoms(terms, c, memo),
                canonical_atoms(terms, a, memo),
                canonical_atoms(terms, b, memo),
            );
            terms.mk_ite_raw(c, a, b)
        }
        TermData::App(sym, args)
            if matches!(sym.name(), "and" | "or" | "=>" | "xor")
                || (matches!(sym.name(), "=" | "distinct")
                    && args
                        .first()
                        .is_some_and(|&a| matches!(terms.sort(a), Sort::Bool))) =>
        {
            let new: Vec<TermId> = args
                .iter()
                .map(|&a| canonical_atoms(terms, a, memo))
                .collect();
            terms.mk_app(sym, new, Sort::Bool)
        }
        TermData::App(..) => match parse(terms, t, true) {
            Some(lit @ (Lit::Arith(..) | Lit::Div(..))) => match build(terms, &lit) {
                Ok(Some((atom, true))) => atom,
                Ok(Some((atom, false))) => terms.mk_not_raw(atom),
                Ok(None) => terms.mk_bool(true),
                Err(MbpDecline::Preservation) => terms.mk_bool(false),
                Err(_) => t,
            },
            _ => t,
        },
        _ => t,
    };
    memo.insert(t, r);
    r
}

#[cfg(test)]
#[path = "mbp_tests.rs"]
mod tests;
