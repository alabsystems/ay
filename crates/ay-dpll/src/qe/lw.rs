// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Loos-Weispfenning virtual substitution for linear real arithmetic (LRA).
//!
//! Eliminates a single existential quantifier from a conjunction of linear
//! real literals:
//!
//! ```text
//! ∃x. φ      where φ = L₁ ∧ L₂ ∧ … ∧ Lₙ
//! ```
//!
//! and each `Lᵢ` normalizes to `t ⋈ 0` with `⋈ ∈ {=, ≠, ≤, <}` and `t` a
//! linear term `Σ aⱼ·yⱼ + c` over Real variables with rational coefficients.
//!
//! # Fragment (hard boundary)
//!
//! Anything outside the fragment is **refused**: the procedure returns
//! [`QeResult::NotSupported`] and the caller must keep the original formula.
//! Refused inputs include non-Real bound variables, Int-sorted free variables
//! (an emitted mixed-sort term would not be well-sorted), non-linear terms,
//! division by a non-constant, boolean structure inside literals, and any
//! literal whose head is not one of the supported relations. One mixed-sort
//! bridge IS supported: `(to_real t)` applications over Int-sorted `t` are
//! purified into fresh Real variables before parsing and substituted back
//! into the verified output (see [`purify_to_real`]), which is what lets
//! mixed-sort `∀n:Int ∃r:Real` blocks eliminate.
//!
//! # Algorithm (Loos-Weispfenning, −∞ / lower-endpoint form)
//!
//! Reference: R. Loos & V. Weispfenning, "Applying Linear Quantifier
//! Elimination" (1993); Nipkow, "Linear Quantifier Elimination" (IJCAR 2008).
//!
//! ```text
//! ∃x.φ  ≡  φ[x := −∞]  ∨  ⋁_{e ∈ E} φ[x := e]  ∨  ⋁_{e ∈ E} φ[x := e + ε]
//! ```
//!
//! where `E` collects the boundary point `e = −rest/a` of EVERY literal whose
//! `x`-coefficient `a` is nonzero. Taking both the exact point and the `+ε`
//! point for every literal is a SUPERSET of the minimal LW test set (which
//! distinguishes `=`/`≤` endpoints from `<`/`≠` endpoints): a superset is
//! sound — each virtual substitution exactly characterizes satisfaction at
//! that point / on a right-neighborhood, so each disjunct implies `∃x.φ` —
//! and remains complete, sidestepping the classic endpoint-classification
//! pitfalls (e.g. a `≤` lower endpoint punctured by a `≠` needs `+ε`).
//!
//! The `−∞` and `ε` cases evaluate symbolically per literal from the sign of
//! `x`'s coefficient (a rational constant, so the sign is resolved at build
//! time): under `−∞`, `a·x + r < 0` is `true` iff `a > 0`, an equality is
//! `false`, a disequality `true`; under `e + ε`, an equality is `false`, a
//! disequality `true`, and `a·x + r < 0` (or `≤`) becomes `v < 0` when
//! `a > 0` and `v ≤ 0` when `a < 0`, where `v = a·e + r`.
//!
//! # Soundness gate
//!
//! Mirroring [`super::cooper::selfcheck`]: the output is verified against the
//! input on a battery of ground rational assignments before being returned.
//! For each sampled assignment `σ`, `∃x.φ[σ]` is decided EXACTLY by interval
//! intersection over the one-variable bounds (complete for a one-variable
//! linear real conjunction, including strict/nonstrict endpoints and `≠`
//! punctures — finitely many punctures cannot empty an interval with
//! interior over the dense reals), and compared with an independent
//! evaluation of the LW output. ANY disagreement or unknown evaluation
//! refuses the elimination (fail-closed).

use ay_core::term::{Constant, Symbol, TermData};
use ay_core::{Sort, TermId, TermStore};
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};
use std::collections::{BTreeMap, HashMap, HashSet};

use super::cooper::{collect_conjuncts, Rel};
use super::QeResult;

/// Refuse conjunctions larger than this: the test set grows as `1 + 2n` and
/// each disjunct re-instantiates every literal, so this bounds output size.
const MAX_LITERALS: usize = 64;

/// Number of seeded pseudo-random ground assignments sampled by the
/// self-check, in addition to the deterministic batteries.
const RANDOM_SAMPLES: usize = 200;

/// Eliminate a single existential `∃x. φ` where `x` is Real-sorted and `φ` is
/// a conjunction of linear real literals (see the module docs). Bodies whose
/// literals bridge from Int through `(to_real t)` applications are handled by
/// purifying each bridge node into a fresh Real variable first (see
/// [`purify_to_real`] for the soundness argument), running the UNCHANGED
/// parse/LW/self-check pipeline on the purified body, and substituting the
/// bridge terms back into the verified output.
///
/// # Returns
/// * [`QeResult::Eliminated`] with the quantifier-free equivalent, **only**
///   after it has passed the interval-exact equivalence self-check.
/// * [`QeResult::NotSupported`] if the input is out of fragment or the
///   self-check fails (fail-closed).
pub fn eliminate_exists_real(terms: &mut TermStore, body: TermId, var: TermId) -> QeResult {
    if !matches!(terms.get(var), TermData::Var(_, _)) {
        return QeResult::NotSupported;
    }
    if !matches!(terms.sort(var), Sort::Real) {
        return QeResult::NotSupported;
    }

    match purify_to_real(terms, body, var) {
        ToRealPurify::Absent => eliminate_core(terms, body, var),
        ToRealPurify::Refused => QeResult::NotSupported,
        ToRealPurify::Purified {
            body: purified,
            freshes,
            origs,
        } => match eliminate_core(terms, purified, var) {
            QeResult::Eliminated(qf) => {
                // Instantiate the verified equivalence at `u := to_real(t)`.
                // The back-substitution rebuilds through the folding
                // constructors (`mk_le`/`mk_lt`/`mk_eq_coerce` via
                // `rebuild_app`), so `to_real(n) ⋈ c` atoms fold to pure Int
                // atoms where the audited to_real-integrality rewrites apply.
                let qf2 = terms.substitute(qf, &freshes, &origs);
                // Defence-in-depth: a fresh variable surviving into the
                // adopted assertion set would be a new-symbol regression.
                if freshes.iter().any(|&f| occurs(terms, qf2, f)) {
                    return QeResult::NotSupported;
                }
                QeResult::Eliminated(qf2)
            }
            QeResult::NotSupported => QeResult::NotSupported,
        },
    }
}

/// The unchanged parse → LW → self-check pipeline over a body free of
/// `to_real` applications (either originally, or after purification).
fn eliminate_core(terms: &mut TermStore, body: TermId, var: TermId) -> QeResult {
    let Some(literals) = collect_conjuncts(terms, body) else {
        return QeResult::NotSupported;
    };
    if literals.is_empty() || literals.len() > MAX_LITERALS {
        return QeResult::NotSupported;
    }

    let mut parsed: Vec<(Rel, LinRat)> = Vec::with_capacity(literals.len());
    for lit in &literals {
        match parse_literal(terms, *lit) {
            Some(p) => parsed.push(p),
            None => return QeResult::NotSupported,
        }
    }

    let result = lw(terms, &parsed, var);

    // HARD soundness gate: independently verify `result ≡ ∃x.φ` before use.
    if equivalence_self_check(terms, &parsed, var, result) {
        QeResult::Eliminated(result)
    } else {
        // Fail-closed: never ship an unverified elimination.
        QeResult::NotSupported
    }
}

// ===========================================================================
// to_real purification (mixed-sort quantifier blocks)
// ===========================================================================

/// Outcome of [`purify_to_real`].
enum ToRealPurify {
    /// No `to_real` application occurs in the body: run the pipeline as-is.
    Absent,
    /// Purification refused (shadowed builtin, malformed node, argument
    /// mentioning the eliminated variable, or an untraversable node kind).
    /// Fail-closed: the caller returns [`QeResult::NotSupported`].
    Refused,
    /// Purified body plus the parallel fresh-variable / original-node lists.
    Purified {
        body: TermId,
        freshes: Vec<TermId>,
        origs: Vec<TermId>,
    },
}

/// Replace every maximal `(to_real t)` application (Int-sorted `t`) in `body`
/// by a fresh Real variable, so the literal parser and the self-check operate
/// on genuine [`TermData::Var`] nodes.
///
/// # Soundness
///
/// `∃r.φ[to_real(t)] ≡ (∃r.φ[u])[u := to_real(t)]` — the instantiation is
/// valid because the eliminated variable `r` does not occur in any purified
/// argument `t` (checked explicitly below: `r` CAN reach an Int-sorted
/// argument through `to_int`, e.g. `to_real(to_int(r))`, so this must not be
/// assumed) and the LW equivalence `∃r.φ[u] ≡ ψ(u)` proved for the purified
/// body ranges over ALL real values of the free variable `u` — a superset of
/// the integral image of `to_real`. NOTE on the gate: the per-elimination
/// self-check samples a finite battery of ground assignments
/// ([`build_assignments`], ~285 points) — universality comes from the LW
/// algorithm itself; the check is a probabilistic fail-closed gate, not an
/// exhaustive proof.
///
/// A user-shadowed `to_real` (uninterpreted redeclaration) is refused: the
/// back-substitution rebuilds through the to_real-integrality constructor
/// folds (themselves gated on the same flag), and treating a free function as
/// the Int→Real embedding would fabricate semantics.
///
/// The fresh `TermId`s are held directly and never recovered by name, so the
/// "`mk_fresh_var` does not register names" hazard from `qe_light` does not
/// apply. [`TermStore::substitute`] performs `TermId`-identity simultaneous
/// replacement and `body` is a quantifier-free matrix, so there is no capture
/// concern.
fn purify_to_real(terms: &mut TermStore, body: TermId, var: TermId) -> ToRealPurify {
    let mut stack = vec![body];
    let mut seen: HashSet<TermId> = HashSet::new();
    let mut origs: Vec<TermId> = Vec::new();
    while let Some(t) = stack.pop() {
        if !seen.insert(t) {
            continue;
        }
        match terms.get(t) {
            TermData::App(sym, args) if sym.name() == "to_real" => {
                if terms.to_real_is_shadowed()
                    || args.len() != 1
                    || !matches!(terms.sort(args[0]), Sort::Int)
                    || !matches!(terms.sort(t), Sort::Real)
                {
                    return ToRealPurify::Refused;
                }
                // The eliminated variable must not occur in the Int argument
                // (see Soundness above). Today's only caller screens `to_int`
                // out beforehand, but `eliminate_exists_real` is `pub` and
                // its contract must not silently depend on caller screening.
                if occurs(terms, args[0], var) {
                    return ToRealPurify::Refused;
                }
                origs.push(t);
                // Do not descend: the node is replaced wholesale. A nested
                // `to_real` under a `to_int` inside `args[0]` goes with it;
                // if that nested node also occurs OUTSIDE this one, it is
                // reached and collected through its other parent.
            }
            TermData::Const(_) | TermData::Var(_, _) => {}
            TermData::Not(inner) => stack.push(*inner),
            TermData::App(_, args) => stack.extend(args.iter().copied()),
            TermData::Ite(c, a, b) => {
                stack.push(*c);
                stack.push(*a);
                stack.push(*b);
            }
            // `TermData` is `#[non_exhaustive]`: an untraversed node kind
            // could hide `to_real` occurrences the substitution would miss.
            // Refuse (fail-closed) — the literal parser refuses these bodies
            // anyway.
            _ => return ToRealPurify::Refused,
        }
    }
    if origs.is_empty() {
        return ToRealPurify::Absent;
    }
    let freshes: Vec<TermId> = origs
        .iter()
        .map(|_| terms.mk_fresh_var("__ay_qe_toreal", Sort::Real))
        .collect();
    let purified = terms.substitute(body, &origs, &freshes);
    ToRealPurify::Purified {
        body: purified,
        freshes,
        origs,
    }
}

/// Whether `var` occurs in `term`. Fail-closed: an untraversable
/// (`#[non_exhaustive]`) node kind cannot prove absence and counts as an
/// occurrence.
fn occurs(terms: &TermStore, term: TermId, var: TermId) -> bool {
    let mut stack = vec![term];
    let mut seen: HashSet<TermId> = HashSet::new();
    while let Some(t) = stack.pop() {
        if !seen.insert(t) {
            continue;
        }
        if t == var {
            return true;
        }
        match terms.get(t) {
            TermData::Const(_) | TermData::Var(_, _) => {}
            TermData::Not(inner) => stack.push(*inner),
            TermData::App(_, args) => stack.extend(args.iter().copied()),
            TermData::Ite(c, a, b) => {
                stack.push(*c);
                stack.push(*a);
                stack.push(*b);
            }
            _ => return true,
        }
    }
    false
}

// ===========================================================================
// Linear rational terms
// ===========================================================================

/// A linear real term: `Σ coeff·var + constant` with rational coefficients.
#[derive(Debug, Clone, PartialEq, Eq)]
struct LinRat {
    /// `var -> nonzero coefficient` (deterministic order).
    coeffs: BTreeMap<TermId, BigRational>,
    /// The additive constant.
    constant: BigRational,
}

impl LinRat {
    fn zero() -> Self {
        Self {
            coeffs: BTreeMap::new(),
            constant: BigRational::zero(),
        }
    }

    fn add_var(&mut self, var: TermId, c: BigRational) {
        if c.is_zero() {
            return;
        }
        let entry = self.coeffs.entry(var).or_insert_with(BigRational::zero);
        *entry += c;
        if entry.is_zero() {
            self.coeffs.remove(&var);
        }
    }

    fn add(&mut self, other: &Self) {
        for (v, c) in &other.coeffs {
            self.add_var(*v, c.clone());
        }
        self.constant += &other.constant;
    }

    fn sub(&mut self, other: &Self) {
        for (v, c) in &other.coeffs {
            self.add_var(*v, -c.clone());
        }
        self.constant -= &other.constant;
    }

    fn scale(&mut self, factor: &BigRational) {
        if factor.is_zero() {
            self.coeffs.clear();
            self.constant = BigRational::zero();
            return;
        }
        for c in self.coeffs.values_mut() {
            *c *= factor;
        }
        self.constant *= factor;
    }

    /// Coefficient of `var` (0 if absent).
    fn coeff_of(&self, var: TermId) -> BigRational {
        self.coeffs
            .get(&var)
            .cloned()
            .unwrap_or_else(BigRational::zero)
    }

    /// Return `self` with `var` removed (the "rest" of the term).
    fn without(&self, var: TermId) -> Self {
        let mut c = self.clone();
        c.coeffs.remove(&var);
        c
    }

    /// Substitute `x := value` (a linear term without `x`) into `self`.
    fn substitute(&self, var: TermId, value: &Self) -> Self {
        let c = self.coeff_of(var);
        let mut out = self.without(var);
        if !c.is_zero() {
            let mut scaled = value.clone();
            scaled.scale(&c);
            out.add(&scaled);
        }
        out
    }

    /// Evaluate under a ground rational assignment (all vars must be bound).
    fn eval(&self, assign: &HashMap<TermId, BigRational>) -> Option<BigRational> {
        let mut acc = self.constant.clone();
        for (v, c) in &self.coeffs {
            acc += c * assign.get(v)?;
        }
        Some(acc)
    }

    /// Build the corresponding hash-consed Real term.
    fn to_term(&self, terms: &mut TermStore) -> TermId {
        let mut summands: Vec<TermId> = Vec::new();
        for (var, coeff) in &self.coeffs {
            if coeff.is_one() {
                summands.push(*var);
            } else {
                let c = terms.mk_rational(coeff.clone());
                summands.push(terms.mk_mul(vec![c, *var]));
            }
        }
        if !self.constant.is_zero() || summands.is_empty() {
            summands.push(terms.mk_rational(self.constant.clone()));
        }
        if summands.len() == 1 {
            summands.pop().expect("nonempty")
        } else {
            terms.mk_add(summands)
        }
    }
}

// ===========================================================================
// Literal parsing & normalization
// ===========================================================================

/// Parse a single SMT literal into `(rel, t)` meaning `t ⋈ 0`. Returns `None`
/// outside the supported fragment.
fn parse_literal(terms: &TermStore, lit: TermId) -> Option<(Rel, LinRat)> {
    match terms.get(lit).clone() {
        TermData::App(Symbol::Named(name), args) if args.len() == 2 => {
            let (lhs, rhs) = (args[0], args[1]);
            match name.as_str() {
                "=" => parse_pair(terms, lhs, rhs, Rel::Eq),
                "<=" => parse_pair(terms, lhs, rhs, Rel::Le),
                "<" => parse_pair(terms, lhs, rhs, Rel::Lt),
                // `a >= b`  ≡  `b <= a` ; `a > b`  ≡  `b < a`
                ">=" => parse_pair(terms, rhs, lhs, Rel::Le),
                ">" => parse_pair(terms, rhs, lhs, Rel::Lt),
                _ => None,
            }
        }
        TermData::Not(inner) => match terms.get(inner).clone() {
            TermData::App(Symbol::Named(name), args) if args.len() == 2 => {
                let (lhs, rhs) = (args[0], args[1]);
                match name.as_str() {
                    "=" => parse_pair(terms, lhs, rhs, Rel::Ne),
                    // not(lhs ≤ rhs) ≡ rhs < lhs ; not(lhs < rhs) ≡ rhs ≤ lhs
                    "<=" => parse_pair(terms, rhs, lhs, Rel::Lt),
                    "<" => parse_pair(terms, rhs, lhs, Rel::Le),
                    // not(lhs ≥ rhs) ≡ lhs < rhs ; not(lhs > rhs) ≡ lhs ≤ rhs
                    ">=" => parse_pair(terms, lhs, rhs, Rel::Lt),
                    ">" => parse_pair(terms, lhs, rhs, Rel::Le),
                    _ => None,
                }
            }
            _ => None,
        },
        _ => None,
    }
}

/// Parse `lhs ⋈ rhs` into `(⋈, lhs - rhs)`.
fn parse_pair(terms: &TermStore, lhs: TermId, rhs: TermId, rel: Rel) -> Option<(Rel, LinRat)> {
    let l = parse_lin(terms, lhs)?;
    let r = parse_lin(terms, rhs)?;
    let mut t = l;
    t.sub(&r);
    Some((rel, t))
}

/// Rational value of a constant term (integer or rational literal, possibly
/// under a unary minus). `None` if not a constant.
fn rat_const(terms: &TermStore, t: TermId) -> Option<BigRational> {
    match terms.get(t) {
        TermData::Const(Constant::Int(n)) => Some(BigRational::from_integer(n.clone())),
        TermData::Const(Constant::Rational(r)) => Some(r.0.clone()),
        TermData::App(Symbol::Named(name), args) if name == "-" && args.len() == 1 => {
            Some(-rat_const(terms, args[0])?)
        }
        _ => None,
    }
}

/// Parse an arbitrary term into a [`LinRat`], failing (out of fragment) on
/// any non-linear-real structure: Int-sorted variables (a mixed-sort output
/// would not be well-sorted), products of two non-constants, division by a
/// non-constant or by zero, `ite`/quantifiers/UF, etc.
fn parse_lin(terms: &TermStore, t: TermId) -> Option<LinRat> {
    if let Some(c) = rat_const(terms, t) {
        return Some(LinRat {
            coeffs: BTreeMap::new(),
            constant: c,
        });
    }
    match terms.get(t).clone() {
        TermData::Var(_, _) => {
            if !matches!(terms.sort(t), Sort::Real) {
                return None;
            }
            let mut lt = LinRat::zero();
            lt.add_var(t, BigRational::one());
            Some(lt)
        }
        TermData::App(Symbol::Named(name), args) => match name.as_str() {
            "+" => {
                let mut acc = LinRat::zero();
                for a in &args {
                    let sub = parse_lin(terms, *a)?;
                    acc.add(&sub);
                }
                Some(acc)
            }
            "-" if args.len() == 1 => {
                let mut sub = parse_lin(terms, args[0])?;
                sub.scale(&-BigRational::one());
                Some(sub)
            }
            "-" if args.len() >= 2 => {
                let mut acc = parse_lin(terms, args[0])?;
                for a in &args[1..] {
                    let sub = parse_lin(terms, *a)?;
                    acc.sub(&sub);
                }
                Some(acc)
            }
            "*" => {
                // Linear multiplication: at most one non-constant factor.
                let mut const_product = BigRational::one();
                let mut nonconst: Option<LinRat> = None;
                for a in &args {
                    if let Some(c) = rat_const(terms, *a) {
                        const_product *= c;
                    } else {
                        if nonconst.is_some() {
                            return None; // Two non-constant factors ⇒ non-linear.
                        }
                        nonconst = Some(parse_lin(terms, *a)?);
                    }
                }
                match nonconst {
                    Some(mut lt) => {
                        lt.scale(&const_product);
                        Some(lt)
                    }
                    None => Some(LinRat {
                        coeffs: BTreeMap::new(),
                        constant: const_product,
                    }),
                }
            }
            "/" if args.len() == 2 => {
                let d = rat_const(terms, args[1])?;
                if d.is_zero() {
                    return None;
                }
                let mut num = parse_lin(terms, args[0])?;
                num.scale(&d.recip());
                Some(num)
            }
            _ => None,
        },
        _ => None,
    }
}

/// For the argument `t` of an `is_int(t)` atom, return the additive constant
/// `c` **iff** `t` linearly normalizes to exactly `1·var + c` where `c` is a
/// ground rational (coefficient of `var` is exactly one and no other variable
/// occurs). Fail-closed `None` on any other shape (coefficient ≠ 1, a
/// non-constant remainder, or an out-of-linear-fragment term). Reuses the
/// audited [`parse_lin`] normalizer so the dedicated `is_int` eliminator
/// ([`crate::qe::isint`]) never re-implements linear parsing.
pub(crate) fn isint_unit_offset(terms: &TermStore, t: TermId, var: TermId) -> Option<BigRational> {
    let lin = parse_lin(terms, t)?;
    if lin.coeff_of(var) != BigRational::one() {
        return None;
    }
    let rest = lin.without(var);
    if !rest.coeffs.is_empty() {
        return None;
    }
    Some(rest.constant)
}

// ===========================================================================
// Loos-Weispfenning virtual substitution
// ===========================================================================

/// Assemble the LW disjunction (see the module docs). Infallible within the
/// parsed fragment; equivalence is enforced by the caller's self-check.
fn lw(terms: &mut TermStore, literals: &[(Rel, LinRat)], var: TermId) -> TermId {
    let mut disjuncts: Vec<TermId> = Vec::new();

    // φ[x := −∞].
    disjuncts.push(subst_minus_inf(terms, literals, var));

    // Boundary points e = −rest/a of every literal with a ≠ 0: both the
    // exact point and the `+ε` neighborhood (superset test set; see docs).
    for (_, t) in literals {
        let a = t.coeff_of(var);
        if a.is_zero() {
            continue;
        }
        let mut e = t.without(var);
        e.scale(&(-a.recip()));
        disjuncts.push(subst_exact(terms, literals, var, &e));
        disjuncts.push(subst_plus_eps(terms, literals, var, &e));
    }

    terms.mk_or(disjuncts)
}

/// Build a relation term `t ⋈ 0` over Real.
fn rel_to_term(terms: &mut TermStore, rel: Rel, t: &LinRat) -> TermId {
    let lhs = t.to_term(terms);
    let zero = terms.mk_rational(BigRational::zero());
    match rel {
        Rel::Le => terms.mk_le(lhs, zero),
        Rel::Lt => terms.mk_lt(lhs, zero),
        Rel::Eq => terms.mk_eq(lhs, zero),
        Rel::Ne => {
            let eq = terms.mk_eq(lhs, zero);
            terms.mk_not(eq)
        }
    }
}

/// `φ[x := e]` — exact substitution of a linear point.
fn subst_exact(
    terms: &mut TermStore,
    literals: &[(Rel, LinRat)],
    var: TermId,
    e: &LinRat,
) -> TermId {
    let conj: Vec<TermId> = literals
        .iter()
        .map(|(rel, t)| {
            let inst = t.substitute(var, e);
            rel_to_term(terms, *rel, &inst)
        })
        .collect();
    terms.mk_and(conj)
}

/// `φ[x := e + ε]` — truth on a right-neighborhood of `e`, with the
/// coefficient-sign branch resolved statically (`a` is a rational constant).
fn subst_plus_eps(
    terms: &mut TermStore,
    literals: &[(Rel, LinRat)],
    var: TermId,
    e: &LinRat,
) -> TermId {
    let mut conj: Vec<TermId> = Vec::with_capacity(literals.len());
    for (rel, t) in literals {
        let a = t.coeff_of(var);
        if a.is_zero() {
            conj.push(rel_to_term(terms, *rel, t));
            continue;
        }
        let lit = match rel {
            // a·(e+ε) + r = 0 is false for all sufficiently small ε > 0
            // (a ≠ 0); its negation is correspondingly true.
            Rel::Eq => terms.mk_bool(false),
            Rel::Ne => terms.mk_bool(true),
            // v + a·ε ⋈ 0 for all sufficiently small ε > 0, where v = a·e + r:
            // a > 0 ⟹ v < 0 (both ≤ and <); a < 0 ⟹ v ≤ 0 (both).
            Rel::Le | Rel::Lt => {
                let v = t.substitute(var, e);
                if a.is_negative() {
                    rel_to_term(terms, Rel::Le, &v)
                } else {
                    rel_to_term(terms, Rel::Lt, &v)
                }
            }
        };
        conj.push(lit);
    }
    terms.mk_and(conj)
}

/// `φ[x := −∞]` — truth as `x → −∞`, resolved statically per literal.
fn subst_minus_inf(terms: &mut TermStore, literals: &[(Rel, LinRat)], var: TermId) -> TermId {
    let mut conj: Vec<TermId> = Vec::with_capacity(literals.len());
    for (rel, t) in literals {
        let a = t.coeff_of(var);
        if a.is_zero() {
            conj.push(rel_to_term(terms, *rel, t));
            continue;
        }
        let truth = match rel {
            Rel::Eq => false,
            Rel::Ne => true,
            // a > 0: a·x → −∞ ⟹ t < 0 eventually true; a < 0: t → +∞ ⟹ false.
            Rel::Le | Rel::Lt => a.is_positive(),
        };
        conj.push(terms.mk_bool(truth));
    }
    terms.mk_and(conj)
}

// ===========================================================================
// Equivalence self-check (independent oracle, fail-closed)
// ===========================================================================

/// Verify `result ≡ ∃x.φ` on a battery of ground rational assignments to the
/// free variables. `∃x.φ[σ]` is decided EXACTLY by interval intersection;
/// `result[σ]` is evaluated by an independent recursive evaluator. Returns
/// `true` only if every case agrees and every evaluation was definite.
fn equivalence_self_check(
    terms: &TermStore,
    literals: &[(Rel, LinRat)],
    var: TermId,
    result: TermId,
) -> bool {
    // Free variables of φ (all vars except x) plus every rational constant of
    // BOTH φ and the result (folding result constants into the battery, so
    // endpoint arithmetic introduced by LW is exercised at its own values).
    let mut free_vars: Vec<TermId> = Vec::new();
    let mut free_seen: HashSet<TermId> = HashSet::new();
    let mut consts: Vec<BigRational> = Vec::new();
    for (_, t) in literals {
        for &v in t.coeffs.keys() {
            if v != var && free_seen.insert(v) {
                free_vars.push(v);
            }
        }
        consts.push(t.constant.clone());
        for c in t.coeffs.values() {
            consts.push(c.clone());
        }
    }
    collect_result_vars_and_consts(
        terms,
        result,
        var,
        &mut free_vars,
        &mut free_seen,
        &mut consts,
    );

    let assignments = build_assignments(&free_vars, &consts);

    for assign in &assignments {
        // 1. Evaluate result[σ] — must be a definite boolean.
        let o_val = match eval_real(terms, result, assign) {
            Some(RealEval::Bool(b)) => b,
            _ => return false, // Unknown / non-boolean — fail closed.
        };
        // 2. Decide ∃x.φ[σ] exactly by interval intersection.
        let exists_val = match exists_x_holds(literals, var, assign) {
            Some(b) => b,
            None => return false,
        };
        // 3. They must agree.
        if o_val != exists_val {
            return false;
        }
    }
    true
}

/// One-variable bound state for the exact interval decision.
struct Interval {
    /// Lower bound: `(value, strict)`; `None` = unbounded below.
    lo: Option<(BigRational, bool)>,
    /// Upper bound: `(value, strict)`; `None` = unbounded above.
    hi: Option<(BigRational, bool)>,
    /// `≠` punctures.
    punctures: Vec<BigRational>,
}

impl Interval {
    fn new() -> Self {
        Self {
            lo: None,
            hi: None,
            punctures: Vec::new(),
        }
    }

    fn add_lower(&mut self, v: BigRational, strict: bool) {
        let replace = match &self.lo {
            None => true,
            Some((cur, cur_strict)) => v > *cur || (v == *cur && strict && !cur_strict),
        };
        if replace {
            self.lo = Some((v, strict));
        }
    }

    fn add_upper(&mut self, v: BigRational, strict: bool) {
        let replace = match &self.hi {
            None => true,
            Some((cur, cur_strict)) => v < *cur || (v == *cur && strict && !cur_strict),
        };
        if replace {
            self.hi = Some((v, strict));
        }
    }

    /// Whether the constrained set is nonempty over the (dense) reals.
    fn nonempty(&self) -> bool {
        match (&self.lo, &self.hi) {
            (Some((lo, lo_strict)), Some((hi, hi_strict))) => {
                if lo > hi {
                    return false;
                }
                if lo == hi {
                    // A single point: must be closed on both sides and not
                    // punctured.
                    return !lo_strict && !hi_strict && !self.punctures.contains(lo);
                }
                // Interior is a nonempty open interval of reals: finitely
                // many punctures cannot empty it (density).
                true
            }
            // Unbounded on at least one side: infinitely many reals remain.
            _ => true,
        }
    }
}

/// Decide `∃x. (⋀ literals)[σ]` exactly: each literal grounds to
/// `a·x + c ⋈ 0`, which is a bound/point/puncture on `x`; intersect and test
/// nonemptiness. `None` when a free variable is missing from `σ` (treated as
/// a check failure by the caller).
fn exists_x_holds(
    literals: &[(Rel, LinRat)],
    var: TermId,
    assign: &HashMap<TermId, BigRational>,
) -> Option<bool> {
    let mut iv = Interval::new();
    for (rel, t) in literals {
        let a = t.coeff_of(var);
        let c = t.without(var).eval(assign)?;
        if a.is_zero() {
            // Ground literal: constant truth.
            let ok = match rel {
                Rel::Le => c <= BigRational::zero(),
                Rel::Lt => c < BigRational::zero(),
                Rel::Eq => c.is_zero(),
                Rel::Ne => !c.is_zero(),
            };
            if !ok {
                return Some(false);
            }
            continue;
        }
        // a·x + c ⋈ 0 with boundary e = −c/a.
        let e = -&c / &a;
        match rel {
            Rel::Eq => {
                iv.add_lower(e.clone(), false);
                iv.add_upper(e, false);
            }
            Rel::Ne => iv.punctures.push(e),
            Rel::Le => {
                if a.is_positive() {
                    iv.add_upper(e, false);
                } else {
                    iv.add_lower(e, false);
                }
            }
            Rel::Lt => {
                if a.is_positive() {
                    iv.add_upper(e, true);
                } else {
                    iv.add_lower(e, true);
                }
            }
        }
    }
    Some(iv.nonempty())
}

/// Result of the independent ground evaluator.
enum RealEval {
    Rat(BigRational),
    Bool(bool),
}

/// Independent recursive evaluator for the LW output (and its literal
/// building blocks): rational/integer/boolean constants, Real variables,
/// `+ - * /`, the comparisons, and `and`/`or`/`not`. Anything else returns
/// `None` (fail-closed at the caller).
fn eval_real(
    terms: &TermStore,
    term: TermId,
    assign: &HashMap<TermId, BigRational>,
) -> Option<RealEval> {
    match terms.get(term) {
        TermData::Const(Constant::Int(n)) => {
            Some(RealEval::Rat(BigRational::from_integer(n.clone())))
        }
        TermData::Const(Constant::Rational(r)) => Some(RealEval::Rat(r.0.clone())),
        TermData::Const(Constant::Bool(b)) => Some(RealEval::Bool(*b)),
        TermData::Var(_, _) => assign.get(&term).cloned().map(RealEval::Rat),
        TermData::Not(inner) => match eval_real(terms, *inner, assign)? {
            RealEval::Bool(b) => Some(RealEval::Bool(!b)),
            RealEval::Rat(_) => None,
        },
        TermData::App(Symbol::Named(name), args) => {
            let rat_args = |args: &[TermId]| -> Option<Vec<BigRational>> {
                args.iter()
                    .map(|&a| match eval_real(terms, a, assign) {
                        Some(RealEval::Rat(r)) => Some(r),
                        _ => None,
                    })
                    .collect()
            };
            let bool_args = |args: &[TermId]| -> Option<Vec<bool>> {
                args.iter()
                    .map(|&a| match eval_real(terms, a, assign) {
                        Some(RealEval::Bool(b)) => Some(b),
                        _ => None,
                    })
                    .collect()
            };
            match name.as_str() {
                "+" => {
                    let vs = rat_args(args)?;
                    Some(RealEval::Rat(
                        vs.into_iter().fold(BigRational::zero(), |a, b| a + b),
                    ))
                }
                "*" => {
                    let vs = rat_args(args)?;
                    Some(RealEval::Rat(
                        vs.into_iter().fold(BigRational::one(), |a, b| a * b),
                    ))
                }
                "-" => {
                    let vs = rat_args(args)?;
                    match vs.len() {
                        1 => Some(RealEval::Rat(-vs[0].clone())),
                        n if n >= 2 => {
                            let mut acc = vs[0].clone();
                            for v in &vs[1..] {
                                acc -= v;
                            }
                            Some(RealEval::Rat(acc))
                        }
                        _ => None,
                    }
                }
                "/" => {
                    let vs = rat_args(args)?;
                    if vs.len() != 2 || vs[1].is_zero() {
                        return None;
                    }
                    Some(RealEval::Rat(&vs[0] / &vs[1]))
                }
                "=" => {
                    if let Some(vs) = rat_args(args) {
                        if vs.len() == 2 {
                            return Some(RealEval::Bool(vs[0] == vs[1]));
                        }
                        return None;
                    }
                    let vs = bool_args(args)?;
                    if vs.len() == 2 {
                        Some(RealEval::Bool(vs[0] == vs[1]))
                    } else {
                        None
                    }
                }
                "<" | "<=" | ">" | ">=" => {
                    let vs = rat_args(args)?;
                    if vs.len() != 2 {
                        return None;
                    }
                    let b = match name.as_str() {
                        "<" => vs[0] < vs[1],
                        "<=" => vs[0] <= vs[1],
                        ">" => vs[0] > vs[1],
                        _ => vs[0] >= vs[1],
                    };
                    Some(RealEval::Bool(b))
                }
                "and" => Some(RealEval::Bool(bool_args(args)?.into_iter().all(|b| b))),
                "or" => Some(RealEval::Bool(bool_args(args)?.into_iter().any(|b| b))),
                "not" if args.len() == 1 => match eval_real(terms, args[0], assign)? {
                    RealEval::Bool(b) => Some(RealEval::Bool(!b)),
                    RealEval::Rat(_) => None,
                },
                _ => None,
            }
        }
        _ => None,
    }
}

/// Collect free Real variables (≠ `var`) and rational constants from the LW
/// result term, folding them into the sample battery.
fn collect_result_vars_and_consts(
    terms: &TermStore,
    term: TermId,
    var: TermId,
    free_vars: &mut Vec<TermId>,
    free_seen: &mut HashSet<TermId>,
    consts: &mut Vec<BigRational>,
) {
    match terms.get(term) {
        TermData::Const(Constant::Int(n)) => consts.push(BigRational::from_integer(n.clone())),
        TermData::Const(Constant::Rational(r)) => consts.push(r.0.clone()),
        TermData::Const(_) => {}
        TermData::Var(_, _) => {
            if term != var && free_seen.insert(term) {
                free_vars.push(term);
            }
        }
        TermData::Not(inner) => {
            collect_result_vars_and_consts(terms, *inner, var, free_vars, free_seen, consts);
        }
        TermData::App(_, args) => {
            for &a in args {
                collect_result_vars_and_consts(terms, a, var, free_vars, free_seen, consts);
            }
        }
        _ => {}
    }
}

/// Build the assignment battery: boundary values (small integers, halves,
/// thirds, LARGE magnitudes), the collected constants ± offsets (including
/// fractional offsets — the ε/−∞ cases are exactly where integer-only
/// samples can miss a strictness bug), alternating-sign mixes, and seeded
/// pseudo-random rationals with varied denominators.
fn build_assignments(
    free_vars: &[TermId],
    consts: &[BigRational],
) -> Vec<HashMap<TermId, BigRational>> {
    let rat = |n: i64, d: i64| BigRational::new(BigInt::from(n), BigInt::from(d));
    let mut out: Vec<HashMap<TermId, BigRational>> = Vec::new();

    // Uniform boundary values.
    let boundary = [
        rat(0, 1),
        rat(1, 1),
        rat(-1, 1),
        rat(2, 1),
        rat(-2, 1),
        rat(3, 1),
        rat(-3, 1),
        rat(1, 2),
        rat(-1, 2),
        rat(3, 2),
        rat(-3, 2),
        rat(1, 3),
        rat(-1, 3),
        rat(1000, 1),
        rat(-1000, 1),
        rat(12345, 7),
        rat(-12345, 7),
    ];
    for v in &boundary {
        let mut m = HashMap::new();
        for &fv in free_vars {
            m.insert(fv, v.clone());
        }
        out.push(m);
    }

    // Constants of φ and the result, exercised at and around their values.
    let offsets = [rat(0, 1), rat(1, 1), rat(-1, 1), rat(1, 2), rat(-1, 2)];
    for c in consts.iter().take(16) {
        for off in &offsets {
            let mut m = HashMap::new();
            for &fv in free_vars {
                m.insert(fv, c + off);
            }
            out.push(m);
        }
    }

    // Alternating-sign mixed points.
    for base in &[1i64, 2, 5] {
        let mut m = HashMap::new();
        for (i, &fv) in free_vars.iter().enumerate() {
            let sign = if i % 2 == 0 { 1 } else { -1 };
            m.insert(fv, rat(sign * base * (i as i64 + 1), 1));
        }
        out.push(m);
    }

    // Seeded random rationals with varied denominators (reproducible).
    let mut rng = SplitMix64::new(0xACE1_F00D_5EED_CAFE);
    let denominators = [1i64, 2, 3, 4, 5, 7, 8];
    for _ in 0..RANDOM_SAMPLES {
        let mut m = HashMap::new();
        for &fv in free_vars {
            let n = (rng.next_u64() % 49) as i64 - 24;
            let d = denominators[(rng.next_u64() % denominators.len() as u64) as usize];
            m.insert(fv, rat(n, d));
        }
        out.push(m);
    }

    out
}

/// Deterministic SplitMix64 PRNG (reproducible battery, no external
/// randomness sources).
struct SplitMix64 {
    state: u64,
}

impl SplitMix64 {
    fn new(seed: u64) -> Self {
        Self { state: seed }
    }
    fn next_u64(&mut self) -> u64 {
        self.state = self.state.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.state;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }
}

#[cfg(test)]
#[path = "lw_tests.rs"]
mod tests;
