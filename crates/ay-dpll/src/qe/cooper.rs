// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Cooper's quantifier elimination for linear integer arithmetic (LIA).
//!
//! Eliminates a single existential quantifier from a conjunction of linear
//! integer literals:
//!
//! ```text
//! ∃x. φ      where φ = L₁ ∧ L₂ ∧ … ∧ Lₙ
//! ```
//!
//! and each `Lᵢ` is one of (with `t` a linear term `Σ aⱼ·yⱼ + c` over integer
//! variables and integer coefficients):
//!
//! ```text
//! t ≤ 0   t < 0   t = 0   t ≠ 0   d | t   ¬(d | t)
//!                                     (d a positive integer literal)
//! ```
//!
//! The output `O` is a quantifier-free LIA formula over the remaining free
//! variables that is logically equivalent to `∃x. φ`.
//!
//! # Fragment (hard boundary)
//!
//! Anything outside the fragment above is **refused**: the procedure returns
//! [`QeResult::NotSupported`] and the caller must keep the original formula.
//! Refused inputs include nested quantifiers, non-linear terms (`x*x`, `x*y`),
//! `div`/`mod` of the eliminated variable other than the explicit `d | t`
//! form, real-sorted terms, boolean/ite structure, disjunction, universals,
//! and any literal whose head is not one of the supported relations.
//!
//! # Internal literal normal form
//!
//! Every parsed literal is stored as `term ⋈ 0` or `divisor | term`, where the
//! eliminated variable `x` may appear with coefficient `c` of either sign. The
//! downstream Cooper logic always interprets a literal using **both** its
//! relation `⋈` and the **sign of `c`** together, so we never need a separate
//! `>`/`≥` relation token.
//!
//! # Algorithm (Cooper, −∞ / lower-bound form)
//!
//! Reference: D. C. Cooper, "Theorem Proving in Arithmetic without
//! Multiplication" (1972); Harrison, *Handbook of Practical Logic and
//! Automated Reasoning*, §5.7; Bradley & Manna, *The Calculus of
//! Computation*, §7.3.
//!
//! 1. **Unit-coefficient reduction.** Let `m = lcm` of all `|c|`. Multiply each
//!    literal so the coefficient of `x` becomes `±m`, then replace `m·x` by a
//!    fresh `x'` and add the divisibility literal `m | x'`. Now every literal
//!    mentions `x'` with coefficient `±1`. (We keep `x` as the variable symbol
//!    and just record `coeff(x) = ±1` after scaling.)
//! 2. **Period.** Let `δ = lcm` of every divisor appearing in a divisibility
//!    literal (including the new `m`).
//! 3. **−∞ form.** Build `φ₋∞` by replacing each inequality/equality literal by
//!    its truth value as `x → −∞`, keeping divisibility literals unchanged.
//! 4. **Result.**
//!    ```text
//!    ∃x.φ  ≡  (⋁_{j=1..δ} φ₋∞[x := j])
//!          ∨  (⋁_{b ∈ B} ⋁_{j=1..δ} φ[x := b + j])
//!    ```
//!    where `B` is the set of lower-bound witnesses `b` with the property that
//!    `x = b + 1` is the least value some literal could newly satisfy. A
//!    literal `c·x + a ⋈ 0` contributes to `B` when it is a *lower* bound on
//!    `x` (after accounting for the sign of `c`); equalities and disequalities
//!    contribute their boundary point.
//!
//! # Candidate regression gate
//!
//! See [`selfcheck::equivalence_self_check`]. The output is verified against the
//! input on a finite deterministic ground battery before being returned; on any
//! observed failure the result is discarded. This check is complete in the
//! eliminated variable after each sampled assignment, but it does not prove the
//! outer equivalence for all free-variable assignments and must not be used as
//! public verdict authority by itself.

use ay_core::term::{Constant, Symbol, TermData};
use ay_core::{Sort, TermId, TermStore};
use num_bigint::BigInt;
use num_integer::Integer;
use num_traits::{One, Signed, Zero};
use std::collections::BTreeMap;

mod eval;
mod selfcheck;

#[cfg(test)]
mod tests;

/// Outcome of a quantifier-elimination attempt.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum QeResult {
    /// Elimination succeeded and the result passed the bounded differential
    /// check.
    ///
    /// The contained term is a quantifier-free LIA formula over the free
    /// variables of the input (everything except the eliminated variable),
    /// intended to be logically equivalent to `∃x. φ`. Public decision
    /// paths require separate exact-source or equivalence authority.
    Eliminated(TermId),
    /// The input is outside the supported fragment, or the eliminated result
    /// failed the bounded differential check. Either way the caller must keep the
    /// original quantified formula. This is the fail-closed outcome.
    NotSupported,
}

/// Eliminate a single existential `∃x. φ` where `φ` is a conjunction of LIA
/// literals over the supported fragment (see the module docs).
///
/// # Arguments
/// * `terms` — the hash-consed term store; the result is interned into it.
/// * `body` — the matrix `φ` (a conjunction of literals, or a single literal).
/// * `var` — the integer-sorted variable `x` to eliminate. Must be a
///   [`TermData::Var`] of sort [`Sort::Int`].
///
/// # Returns
/// * [`QeResult::Eliminated`] with the quantifier-free candidate, **only**
///   after it has passed the bounded differential check.
/// * [`QeResult::NotSupported`] if the input is out of fragment or the
///   self-check fails (fail-closed).
pub fn eliminate_exists(terms: &mut TermStore, body: TermId, var: TermId) -> QeResult {
    // The eliminated variable must be an integer-sorted variable.
    if !matches!(terms.get(var), TermData::Var(_, _)) {
        return QeResult::NotSupported;
    }
    if !matches!(terms.sort(var), Sort::Int) {
        return QeResult::NotSupported;
    }

    let Some(literals) = collect_conjuncts(terms, body) else {
        return QeResult::NotSupported;
    };
    if literals.is_empty() {
        return QeResult::NotSupported;
    }

    // Parse each literal into the internal normalized form.
    let mut parsed: Vec<Literal> = Vec::with_capacity(literals.len());
    for lit in &literals {
        match parse_literal(terms, *lit) {
            Some(p) => parsed.push(p),
            None => return QeResult::NotSupported,
        }
    }

    // Run Cooper's algorithm.
    let Some(result) = cooper(terms, &parsed, var) else {
        return QeResult::NotSupported;
    };

    // Bounded differential gate: reject every observed mismatch. This does not
    // discharge the universal free-variable equivalence obligation; callers at
    // a public verdict boundary need separate symbolic authority.
    if selfcheck::equivalence_self_check(terms, &literals, var, result) {
        QeResult::Eliminated(result)
    } else {
        // Fail-closed: never ship an unverified elimination.
        QeResult::NotSupported
    }
}

// ===========================================================================
// Internal linear-term representation
// ===========================================================================

/// A linear integer term: `Σ coeff·var + constant`.
///
/// Variables are keyed by their hash-consed [`TermId`]. Only genuine
/// [`TermData::Var`] nodes are admitted as keys; anything else makes parsing
/// fail (out of fragment).
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct LinTerm {
    /// `var -> nonzero coefficient`. A `BTreeMap` keeps a deterministic order
    /// for term reconstruction and equality.
    pub coeffs: BTreeMap<TermId, BigInt>,
    /// The additive constant.
    pub constant: BigInt,
}

impl LinTerm {
    fn zero() -> Self {
        Self {
            coeffs: BTreeMap::new(),
            constant: BigInt::zero(),
        }
    }

    fn add_var(&mut self, var: TermId, c: BigInt) {
        if c.is_zero() {
            return;
        }
        let entry = self.coeffs.entry(var).or_insert_with(BigInt::zero);
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

    fn scale(&mut self, factor: &BigInt) {
        if factor.is_zero() {
            self.coeffs.clear();
            self.constant = BigInt::zero();
            return;
        }
        for c in self.coeffs.values_mut() {
            *c *= factor;
        }
        self.constant *= factor;
    }

    /// Coefficient of `var` (0 if absent).
    fn coeff_of(&self, var: TermId) -> BigInt {
        self.coeffs.get(&var).cloned().unwrap_or_else(BigInt::zero)
    }

    /// Return `self` with `var` removed (the "rest" of the term).
    fn without(&self, var: TermId) -> Self {
        let mut c = self.clone();
        c.coeffs.remove(&var);
        c
    }

    /// Build the corresponding hash-consed integer term.
    fn to_term(&self, terms: &mut TermStore) -> TermId {
        let mut summands: Vec<TermId> = Vec::new();
        for (var, coeff) in &self.coeffs {
            if coeff.is_one() {
                summands.push(*var);
            } else {
                let c = terms.mk_int(coeff.clone());
                summands.push(terms.mk_mul(vec![c, *var]));
            }
        }
        if !self.constant.is_zero() || summands.is_empty() {
            summands.push(terms.mk_int(self.constant.clone()));
        }
        if summands.len() == 1 {
            summands.pop().expect("nonempty")
        } else {
            terms.mk_add(summands)
        }
    }
}

// ===========================================================================
// Normalized literal representation
// ===========================================================================

/// The relational kind of an arithmetic literal, after normalization so the
/// term is compared against `0`. Direction is read together with the sign of
/// the eliminated variable's coefficient.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Rel {
    /// `t ≤ 0`
    Le,
    /// `t < 0`
    Lt,
    /// `t = 0`
    Eq,
    /// `t ≠ 0`
    Ne,
}

/// A normalized literal: a relation `term ⋈ 0`, a divisibility
/// `divisor | term`, or a negated divisibility `¬(divisor | term)`.
#[derive(Debug, Clone)]
pub(crate) enum Literal {
    /// `term ⋈ 0`.
    Rel(Rel, LinTerm),
    /// `divisor | term`, with `divisor > 0`.
    Div(BigInt, LinTerm),
    /// `¬(divisor | term)`, with `divisor > 0` (parsed from
    /// `(not (= (mod t d) 0))`). Periodic like [`Literal::Div`]: it
    /// contributes its divisor to the period δ and yields no B-point.
    NDiv(BigInt, LinTerm),
}

impl Literal {
    /// The linear term of the literal, whatever its kind. Every literal kind
    /// carries exactly one `LinTerm`; new variants must extend this accessor,
    /// which keeps the step-1 coefficient-lcm loop in [`cooper`] exhaustive
    /// by construction (a variant silently missing from an or-pattern there
    /// would skip unit-coefficient scaling — a soundness bug).
    fn lin(&self) -> &LinTerm {
        match self {
            Literal::Rel(_, t) | Literal::Div(_, t) | Literal::NDiv(_, t) => t,
        }
    }
}

// ===========================================================================
// Conjunct collection
// ===========================================================================

/// Flatten the body into a list of literals.
///
/// Accepts a single literal or a (possibly nested) `(and …)`. Disjunction,
/// quantifier, ite, or boolean variable nodes are simply returned as opaque
/// literals; `parse_literal` then rejects them, so the fragment boundary is
/// enforced there. (`pub(crate)`: shared with the Loos-Weispfenning Real
/// eliminator, whose literal parser enforces its own fragment boundary.)
pub(crate) fn collect_conjuncts(terms: &TermStore, body: TermId) -> Option<Vec<TermId>> {
    let mut out = Vec::new();
    let mut stack = vec![body];
    while let Some(t) = stack.pop() {
        match terms.get(t) {
            TermData::App(Symbol::Named(name), args) if name == "and" => {
                for &a in args {
                    stack.push(a);
                }
            }
            _ => out.push(t),
        }
    }
    out.reverse();
    Some(out)
}

// ===========================================================================
// Literal parsing & normalization
// ===========================================================================

/// Parse a single SMT literal into normalized internal form. Returns `None` if
/// the literal is outside the supported fragment.
///
/// Linear-term parsing does not depend on *which* variable is being eliminated;
/// the eliminated variable's coefficient is read out later via
/// [`LinTerm::coeff_of`].
fn parse_literal(terms: &TermStore, lit: TermId) -> Option<Literal> {
    match terms.get(lit).clone() {
        TermData::App(Symbol::Named(name), args) if args.len() == 2 => {
            let (lhs, rhs) = (args[0], args[1]);
            match name.as_str() {
                "=" => parse_eq_like(terms, lhs, rhs, false),
                "<=" => parse_cmp(terms, lhs, rhs, Rel::Le),
                "<" => parse_cmp(terms, lhs, rhs, Rel::Lt),
                // `a >= b`  ≡  `b <= a`
                ">=" => parse_cmp(terms, rhs, lhs, Rel::Le),
                // `a > b`   ≡  `b < a`
                ">" => parse_cmp(terms, rhs, lhs, Rel::Lt),
                _ => None,
            }
        }
        TermData::Not(inner) => parse_negated(terms, inner),
        _ => None,
    }
}

/// Parse `(not inner)`. The complement of each supported relation maps back into
/// the supported relation set:
/// * `not(a = b)`  → `a ≠ b`   (a negated divisibility `not (= (mod t d) 0)`
///   becomes the dedicated [`Literal::NDiv`]),
/// * `not(a ≤ b)`  → `a > b`   ≡ `b < a`,
/// * `not(a < b)`  → `a ≥ b`   ≡ `b ≤ a`,
/// * `not(a ≥ b)`  → `a < b`,
/// * `not(a > b)`  → `a ≤ b`.
fn parse_negated(terms: &TermStore, inner: TermId) -> Option<Literal> {
    match terms.get(inner).clone() {
        TermData::App(Symbol::Named(name), args) if args.len() == 2 => {
            let (lhs, rhs) = (args[0], args[1]);
            match name.as_str() {
                "=" => {
                    // Negated divisibility `not (= (mod t d) 0)` → ¬(d | t).
                    if let Some((d, t)) = extract_mod_div(terms, lhs, rhs) {
                        return Some(Literal::NDiv(d, t));
                    }
                    // Fall through: ordinary negated equality → `≠`.
                    parse_eq_like(terms, lhs, rhs, true)
                }
                // not(lhs ≤ rhs) ≡ rhs < lhs
                "<=" => parse_cmp(terms, rhs, lhs, Rel::Lt),
                // not(lhs < rhs) ≡ rhs ≤ lhs
                "<" => parse_cmp(terms, rhs, lhs, Rel::Le),
                // not(lhs ≥ rhs) ≡ lhs < rhs
                ">=" => parse_cmp(terms, lhs, rhs, Rel::Lt),
                // not(lhs > rhs) ≡ lhs ≤ rhs
                ">" => parse_cmp(terms, lhs, rhs, Rel::Le),
                _ => None,
            }
        }
        _ => None,
    }
}

/// Parse a comparison `lhs op rhs` (op ∈ {≤, <}) into `(lhs - rhs) ⋈ 0`.
fn parse_cmp(terms: &TermStore, lhs: TermId, rhs: TermId, rel: Rel) -> Option<Literal> {
    let l = parse_lin(terms, lhs)?;
    let r = parse_lin(terms, rhs)?;
    let mut t = l;
    t.sub(&r);
    Some(Literal::Rel(rel, t))
}

/// Parse `lhs = rhs`. When `negated`, produce `Ne` instead of `Eq`. Detects the
/// divisibility encoding `(= (mod t d) 0)` (only in the non-negated case).
fn parse_eq_like(terms: &TermStore, lhs: TermId, rhs: TermId, negated: bool) -> Option<Literal> {
    if !negated {
        if let Some((d, t)) = extract_mod_div(terms, lhs, rhs) {
            return Some(Literal::Div(d, t));
        }
    }
    // Reject (dis)equalities over non-integer sorts.
    if !matches!(terms.sort(lhs), Sort::Int) || !matches!(terms.sort(rhs), Sort::Int) {
        return None;
    }
    let l = parse_lin(terms, lhs)?;
    let r = parse_lin(terms, rhs)?;
    let mut t = l;
    t.sub(&r);
    Some(Literal::Rel(if negated { Rel::Ne } else { Rel::Eq }, t))
}

/// Recognize a divisibility encoding `(= (mod t d) 0)` / `(= 0 (mod t d))`.
/// Returns `(d, t_as_lin)` with `d` the positive divisor literal.
fn extract_mod_div(terms: &TermStore, lhs: TermId, rhs: TermId) -> Option<(BigInt, LinTerm)> {
    let mod_term = if is_zero_const(terms, rhs) {
        lhs
    } else if is_zero_const(terms, lhs) {
        rhs
    } else {
        return None;
    };
    if let TermData::App(Symbol::Named(name), args) = terms.get(mod_term) {
        if name == "mod" && args.len() == 2 {
            let inner = args[0];
            let divisor = args[1];
            let d = get_int_const(terms, divisor)?;
            if d <= BigInt::zero() {
                return None;
            }
            let t = parse_lin(terms, inner)?;
            return Some((d, t));
        }
    }
    None
}

fn is_zero_const(terms: &TermStore, t: TermId) -> bool {
    matches!(terms.get(t), TermData::Const(Constant::Int(n)) if n.is_zero())
}

fn get_int_const(terms: &TermStore, t: TermId) -> Option<BigInt> {
    match terms.get(t) {
        TermData::Const(Constant::Int(n)) => Some(n.clone()),
        _ => None,
    }
}

/// Parse an arbitrary term into a [`LinTerm`], failing (out of fragment) on any
/// non-linear-integer structure: real constants, `*` of two non-constants,
/// `div`/`mod`/`ite`/quantifiers, uninterpreted functions, etc.
fn parse_lin(terms: &TermStore, t: TermId) -> Option<LinTerm> {
    // All terms must be integer-sorted within the fragment.
    if !matches!(terms.sort(t), Sort::Int) {
        return None;
    }
    match terms.get(t).clone() {
        TermData::Const(Constant::Int(n)) => Some(LinTerm {
            coeffs: BTreeMap::new(),
            constant: n,
        }),
        TermData::Var(_, _) => {
            let mut lt = LinTerm::zero();
            lt.add_var(t, BigInt::one());
            Some(lt)
        }
        TermData::App(Symbol::Named(name), args) => match name.as_str() {
            "+" => {
                let mut acc = LinTerm::zero();
                for a in &args {
                    let sub = parse_lin(terms, *a)?;
                    acc.add(&sub);
                }
                Some(acc)
            }
            "-" if args.len() == 1 => {
                let mut sub = parse_lin(terms, args[0])?;
                sub.scale(&BigInt::from(-1));
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
                // Linear multiplication: at most one factor may be non-constant.
                let mut const_product = BigInt::one();
                let mut nonconst: Option<LinTerm> = None;
                for a in &args {
                    if let Some(c) = get_int_const(terms, *a) {
                        const_product *= c;
                    } else {
                        if nonconst.is_some() {
                            // Two non-constant factors ⇒ non-linear.
                            return None;
                        }
                        nonconst = Some(parse_lin(terms, *a)?);
                    }
                }
                match nonconst {
                    Some(mut lt) => {
                        lt.scale(&const_product);
                        Some(lt)
                    }
                    None => Some(LinTerm {
                        coeffs: BTreeMap::new(),
                        constant: const_product,
                    }),
                }
            }
            // div / mod / abs / anything else: out of fragment.
            _ => None,
        },
        _ => None,
    }
}

// ===========================================================================
// Cooper's algorithm (−∞ / lower-bound form)
// ===========================================================================

/// Run Cooper's −∞ elimination, returning the quantifier-free result term.
fn cooper(terms: &mut TermStore, literals: &[Literal], var: TermId) -> Option<TermId> {
    // --- Step 1: unit-coefficient reduction -------------------------------
    // m = lcm of |coefficient of x| across all literals (1 if x absent).
    // `Literal::lin` covers every literal kind by construction.
    let mut m = BigInt::one();
    for lit in literals {
        let c = lit.lin().coeff_of(var);
        if !c.is_zero() {
            m = m.lcm(&c.abs());
        }
    }

    // Normalize so coeff(x) ∈ {-1, 0, +1}: multiply each literal by m/|c|.
    let mut norm: Vec<Literal> = Vec::with_capacity(literals.len() + 1);
    for lit in literals {
        norm.push(normalize_unit(lit, var, &m));
    }
    // If we scaled (m > 1), add the divisibility literal `m | x`.
    if m > BigInt::one() {
        let mut t = LinTerm::zero();
        t.add_var(var, BigInt::one());
        norm.push(Literal::Div(m, t));
    }

    // --- Step 2: period δ = lcm of all divisors ---------------------------
    // CORRECTNESS-CRITICAL: classic Cooper takes δ over ALL divisibility
    // constraints, negated or not — a ¬(d | t) literal is d-periodic in x
    // exactly like d | t, so omitting NDiv divisors here would make the
    // −∞/full instance sweeps miss residues.
    let mut delta = BigInt::one();
    for lit in &norm {
        if let Literal::Div(d, _) | Literal::NDiv(d, _) = lit {
            delta = delta.lcm(d);
        }
    }

    // --- Steps 3+4: assemble the two big disjunctions ---------------------
    // B = lower-bound witnesses (`b` such that `x = b+1` is a candidate).
    let mut bset: Vec<LinTerm> = Vec::new();
    for lit in &norm {
        if let Some(b) = lower_bound_witness(lit, var) {
            bset.push(b);
        }
    }

    let mut disjuncts: Vec<TermId> = Vec::new();

    // Disjunct A: ⋁_{j=1..δ} φ₋∞[x := j]
    {
        let mut j = BigInt::one();
        while j <= delta {
            disjuncts.push(build_minus_inf_instance(terms, &norm, var, &j));
            j += 1;
        }
    }

    // Disjunct B: ⋁_{b ∈ B} ⋁_{j=1..δ} φ[x := b + j]
    for b in &bset {
        let mut j = BigInt::one();
        while j <= delta {
            let mut subst = b.clone();
            subst.constant += &j;
            disjuncts.push(build_full_instance(terms, &norm, var, &subst));
            j += 1;
        }
    }

    if disjuncts.is_empty() {
        return Some(terms.mk_bool(false));
    }
    Some(terms.mk_or(disjuncts))
}

/// Multiply a literal by `m/|c|` so the magnitude of `x`'s coefficient becomes
/// `m`, then perform the standard Cooper renaming `x' = m·x` by *resetting*
/// `x`'s coefficient to its sign (`±1`). The renaming is sound because the
/// global constraint `m | x'` (added by [`cooper`]) ties `x'` back to a genuine
/// multiple of `m`.
///
/// Multiplying through by the positive factor `m/|c|` preserves the relation
/// direction; the sign of `coeff(x)` is left intact and read downstream
/// together with the relation. After this, every literal mentions `x` with
/// coefficient `−1`, `0`, or `+1`.
fn normalize_unit(lit: &Literal, var: TermId, m: &BigInt) -> Literal {
    match lit {
        Literal::Rel(rel, t) => {
            let c = t.coeff_of(var);
            if c.is_zero() {
                return Literal::Rel(*rel, t.clone());
            }
            let factor = m / c.abs(); // positive
            let mut nt = t.clone();
            nt.scale(&factor);
            // Renaming x' = m·x: collapse coeff(x) (= ±m) to ±1.
            set_unit_coeff(&mut nt, var);
            Literal::Rel(*rel, nt)
        }
        Literal::Div(d, t) => {
            let c = t.coeff_of(var);
            if c.is_zero() {
                return Literal::Div(d.clone(), t.clone());
            }
            let factor = m / c.abs();
            let mut nt = t.clone();
            nt.scale(&factor);
            // `d | t` ⟺ `(d·factor) | (t·factor)`.
            let nd = d * &factor;
            // Renaming x' = m·x: collapse coeff(x) (= ±m) to ±1.
            set_unit_coeff(&mut nt, var);
            Literal::Div(nd, nt)
        }
        Literal::NDiv(d, t) => {
            // Scales identically to Div: for positive f,
            // `¬(d | t)` ⟺ `¬((d·f) | (t·f))` (both sides of the ⟺ under
            // the un-negated equivalence, negated).
            let c = t.coeff_of(var);
            if c.is_zero() {
                return Literal::NDiv(d.clone(), t.clone());
            }
            let factor = m / c.abs();
            let mut nt = t.clone();
            nt.scale(&factor);
            let nd = d * &factor;
            set_unit_coeff(&mut nt, var);
            Literal::NDiv(nd, nt)
        }
    }
}

/// Replace `var`'s coefficient in `t` by its sign (`±1`), absorbing the
/// magnitude into the `x' = m·x` renaming. `t` must currently have a nonzero
/// coefficient for `var`.
fn set_unit_coeff(t: &mut LinTerm, var: TermId) {
    let c = t.coeff_of(var);
    debug_assert!(!c.is_zero());
    let sign = if c.is_negative() {
        BigInt::from(-1)
    } else {
        BigInt::one()
    };
    t.coeffs.insert(var, sign);
}

/// The lower-bound witness `b` such that satisfying this literal newly at the
/// smallest value happens at `x = b + 1`, or `None` if the literal is not a
/// lower bound on `x`.
///
/// Literals are post-normalization (`coeff(x) ∈ {-1, 0, +1}`). Writing a
/// literal as `c·x + a ⋈ 0` with `a = rest` (the non-x part) and `c = ±1`:
///
/// * `Lt`/`Le` with `c > 0`: upper bound on x — not a lower bound.
/// * `Lt` with `c < 0` (`-x + a < 0` ⟺ `x > a`):              `b = a`.
/// * `Le` with `c < 0` (`-x + a ≤ 0` ⟺ `x ≥ a` ⟺ `x > a-1`):  `b = a - 1`.
/// * `Eq` (`c·x + a = 0` ⟺ `x = e`): the unique witness `e`,    `b = e - 1`.
/// * `Ne` (`c·x + a ≠ 0`, excluding `x = e`): test just above,   `b = e`.
fn lower_bound_witness(lit: &Literal, var: TermId) -> Option<LinTerm> {
    // Div AND NDiv intentionally yield no B-point: both are δ-periodic in x
    // and are covered by the period sweep (δ includes their divisors — the
    // correctness-critical site is the δ loop in `cooper`, which the
    // compiler does NOT force to consider new variants; this let-else is the
    // other such site and is deliberately kind-agnostic).
    let Literal::Rel(rel, t) = lit else {
        return None;
    };
    let c = t.coeff_of(var);
    if c.is_zero() {
        return None;
    }
    let pos = c.is_positive();
    let rest = t.without(var); // "a"
    match (rel, pos) {
        (Rel::Lt, true) | (Rel::Le, true) => None,
        // -x + a < 0 ⟺ x > a → b = a
        (Rel::Lt, false) => Some(rest),
        // -x + a ≤ 0 ⟺ x ≥ a → b = a - 1
        (Rel::Le, false) => {
            let mut b = rest;
            b.constant -= BigInt::one();
            Some(b)
        }
        // c·x + a = 0 ⟺ x = e where e = -a (c>0) or e = a (c<0) (|c| = 1).
        // The only satisfying value is x = e, reached as b + 1 ⟹ b = e - 1.
        (Rel::Eq, _) => {
            let mut e = rest; // a
            if pos {
                e.scale(&BigInt::from(-1)); // -a  (c = +1 ⟹ x = -a)
            }
            // for c<0, x = a, so e = rest already.
            e.constant -= BigInt::one(); // b = e - 1
            Some(e)
        }
        // c·x + a ≠ 0 excludes the single point x = e (e as above). To recover
        // any witness immediately above the hole we test b + 1 = e + 1, i.e.
        // b = e. (The point e - 1 / the −∞ side cover values below the hole.)
        (Rel::Ne, _) => {
            let mut e = rest; // a
            if pos {
                e.scale(&BigInt::from(-1)); // -a  (c = +1 ⟹ x = -a)
            }
            // b = e (NOT e - 1): test the value just above the excluded point.
            Some(e)
        }
    }
}

/// Build `φ₋∞[x := j]`: the −∞ form with `x` set to the integer `j`.
fn build_minus_inf_instance(
    terms: &mut TermStore,
    norm: &[Literal],
    var: TermId,
    j: &BigInt,
) -> TermId {
    let mut conj: Vec<TermId> = Vec::new();
    for lit in norm {
        match lit {
            Literal::Rel(rel, t) => {
                let c = t.coeff_of(var);
                if c.is_zero() {
                    conj.push(rel_to_term(terms, *rel, t));
                } else {
                    let truth = minus_inf_truth(*rel, c.is_positive());
                    conj.push(terms.mk_bool(truth));
                }
            }
            Literal::Div(d, t) => {
                let inst = substitute_const(t, var, j);
                conj.push(div_to_term(terms, d, &inst));
            }
            Literal::NDiv(d, t) => {
                let inst = substitute_const(t, var, j);
                conj.push(ndiv_to_term(terms, d, &inst));
            }
        }
    }
    conj_to_term(terms, conj)
}

/// Build `φ[x := value]` (the full matrix with x replaced by linear `value`).
fn build_full_instance(
    terms: &mut TermStore,
    norm: &[Literal],
    var: TermId,
    value: &LinTerm,
) -> TermId {
    let mut conj: Vec<TermId> = Vec::new();
    for lit in norm {
        match lit {
            Literal::Rel(rel, t) => {
                let inst = substitute_lin(t, var, value);
                conj.push(rel_to_term(terms, *rel, &inst));
            }
            Literal::Div(d, t) => {
                let inst = substitute_lin(t, var, value);
                conj.push(div_to_term(terms, d, &inst));
            }
            Literal::NDiv(d, t) => {
                let inst = substitute_lin(t, var, value);
                conj.push(ndiv_to_term(terms, d, &inst));
            }
        }
    }
    conj_to_term(terms, conj)
}

/// Truth value of `c·x + a ⋈ 0` as `x → −∞`, given the sign of `c`.
fn minus_inf_truth(rel: Rel, coeff_positive: bool) -> bool {
    match (rel, coeff_positive) {
        // c>0: c·x → −∞
        (Rel::Lt, true) => true,
        (Rel::Le, true) => true,
        (Rel::Eq, true) => false,
        (Rel::Ne, true) => true,
        // c<0: c·x → +∞
        (Rel::Lt, false) => false,
        (Rel::Le, false) => false,
        (Rel::Eq, false) => false,
        (Rel::Ne, false) => true,
    }
}

/// Substitute `x := constant` into a linear term (folds into the constant).
fn substitute_const(t: &LinTerm, var: TermId, value: &BigInt) -> LinTerm {
    let c = t.coeff_of(var);
    let mut out = t.without(var);
    out.constant += c * value;
    out
}

/// Substitute `x := value` (a linear term) into a linear term.
fn substitute_lin(t: &LinTerm, var: TermId, value: &LinTerm) -> LinTerm {
    let c = t.coeff_of(var);
    let mut out = t.without(var);
    if !c.is_zero() {
        let mut scaled = value.clone();
        scaled.scale(&c);
        out.add(&scaled);
    }
    out
}

// ===========================================================================
// Term construction from normalized literals
// ===========================================================================

/// Build a relation term `t ⋈ 0`.
fn rel_to_term(terms: &mut TermStore, rel: Rel, t: &LinTerm) -> TermId {
    let lhs = t.to_term(terms);
    let zero = terms.mk_int(BigInt::zero());
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

/// Build a divisibility term `d | t`, encoded as `(= (mod t d) 0)`.
fn div_to_term(terms: &mut TermStore, d: &BigInt, t: &LinTerm) -> TermId {
    let lhs = t.to_term(terms);
    let dterm = terms.mk_int(d.clone());
    let m = terms.mk_mod(lhs, dterm);
    let zero = terms.mk_int(BigInt::zero());
    terms.mk_eq(m, zero)
}

/// Build a negated divisibility term `¬(d | t)`, encoded as
/// `(not (= (mod t d) 0))`. `mk_not` keeps equality atoms as `Not(=…)`
/// (only and/or/constants/double-negation are rewritten), so the emitted
/// literal round-trips through [`parse_negated`] and the self-check
/// evaluator's `Not`/`=`/`mod` arms.
fn ndiv_to_term(terms: &mut TermStore, d: &BigInt, t: &LinTerm) -> TermId {
    let eq = div_to_term(terms, d, t);
    terms.mk_not(eq)
}

fn conj_to_term(terms: &mut TermStore, conj: Vec<TermId>) -> TermId {
    if conj.is_empty() {
        terms.mk_bool(true)
    } else if conj.len() == 1 {
        conj.into_iter().next().expect("nonempty")
    } else {
        terms.mk_and(conj)
    }
}
