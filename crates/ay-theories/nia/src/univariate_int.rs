// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Sound univariate *integer*-arithmetic decision procedure for QF_NIA.
//!
//! AY's default NIA engine linearizes nonlinear products with tangent-plane /
//! McCormick lemmas and decides bounded problems by exhaustive integer
//! enumeration (see `bounded_enum.rs`). Neither path fires on a genuinely
//! nonlinear *unbounded* univariate problem such as `x*x = 16` with no bound on
//! `x`: tangent planes stall and the enumeration box is unbounded, so the
//! solver returns `unknown`.
//!
//! This module adds an *exact*, *sound* decision procedure for the single-
//! integer-variable polynomial fragment. The integer-univariate fragment is
//! decidable, and integer root-finding is much simpler than the general real
//! case: we never need Sturm sequences or irrational isolating intervals.
//!
//! ## Fragment
//!
//! Fires only when EVERY asserted atom is a comparison (`= distinct < <= > >=`)
//! whose two sides are polynomials (built from `+ - *`, integer constants, and a
//! SINGLE shared integer variable `x`). Any cross-variable coupling (e.g.
//! `x*y`), any unsupported operator (`/ div mod abs`, ite, ...), or any atom
//! mentioning a second variable => out of fragment => the caller falls through
//! unchanged (returns `None`, i.e. Unknown).
//!
//! ## Method
//!
//! Each atom becomes `p_i(x) REL 0` with exact [`BigInt`] coefficients. The
//! decision then rests on a complete, finite candidate set of integers, every
//! one of which is tested by EXACT substitution into ALL atoms:
//!
//!   * **Equality roots.** For an equality `p_i(x) = 0`, every integer root `r`
//!     divides `p_i`'s lowest non-zero coefficient (rational root theorem,
//!     after factoring out the `x^k` that a zero constant term contributes).
//!     Enumerating the divisors of that coefficient yields the COMPLETE set of
//!     integer roots of `p_i`. If the problem contains any equality, every
//!     model is one of that equality's integer roots, so testing them all is a
//!     complete decision.
//!
//!   * **Bounded middle + unbounded tails (no equality).** All real roots of
//!     every `p_i` lie in `[-B, B]` for a Cauchy bound `B` computed exactly from
//!     the coefficients. Beyond `B` (and below `-B`) every `p_i` is sign-
//!     constant, so each unbounded tail's feasibility is decided by ONE
//!     representative integer just past the extreme (`B+1`, `-B-1`). Inside
//!     `[-B, B]` we enumerate the integers directly (bounded by a cap; over the
//!     cap we return Unknown). The union {tail reps} ∪ {integers in [-B,B]}
//!     therefore contains a satisfying integer iff one exists.
//!
//! ## Soundness (the whole point)
//!
//! Exact [`BigInt`]/[`BigRational`] arithmetic only — never `f64`. The verdict
//! is fail-closed:
//!
//!   * **SAT** only with a concrete integer witness re-verified by exact
//!     substitution into EVERY original asserted atom (`eval_constraint_exact`,
//!     reused from `bounded_enum.rs`).
//!   * **UNSAT** only when the candidate set is a COMPLETE cover of the integers
//!     that could satisfy and none does (equality present => its full integer
//!     root set; inequality-only => full `[-B,B]` plus both tail reps).
//!   * Anything uncertain (out of fragment, divisor enumeration too large,
//!     middle range over the cap, an atom we cannot evaluate exactly) => `None`
//!     => caller falls through unchanged. Never a wrong sat/unsat.

use num_bigint::BigInt;
use num_integer::Integer;
use num_rational::BigRational;
use num_traits::{One, Signed, ToPrimitive, Zero};

use ay_core::term::{Constant, Symbol, TermData, TermId};
use ay_core::{TheoryLit, TheoryResult};

use super::*;

/// Largest |coefficient constant| whose divisors we will enumerate for the
/// rational-root candidate set. Trial division costs ~sqrt(c0) iterations, so
/// 1e12 keeps the worst case at ~1e6 cheap steps. Above this we return Unknown
/// (sound — declining to enumerate is never a wrong verdict).
const MAX_DIVISOR_CONSTANT: u64 = 1_000_000_000_000;

/// Largest width of the bounded middle integer range `[-B, B]` we will
/// enumerate for an inequality-only system. Above this we return Unknown.
const MAX_MIDDLE_WIDTH: i128 = 2_000_000;

/// A dense univariate polynomial over the integers; `coeffs[i]` is the
/// coefficient of `x^i`. The leading coefficient is non-zero for a non-zero
/// polynomial (maintained by [`IntPoly::normalize`]). The zero polynomial is
/// the empty vector.
#[derive(Clone, Debug, PartialEq, Eq)]
struct IntPoly {
    coeffs: Vec<BigInt>,
}

impl IntPoly {
    fn zero() -> Self {
        Self { coeffs: Vec::new() }
    }

    fn constant(c: BigInt) -> Self {
        let mut p = Self { coeffs: vec![c] };
        p.normalize();
        p
    }

    /// The monomial `x`.
    fn x() -> Self {
        Self {
            coeffs: vec![BigInt::zero(), BigInt::one()],
        }
    }

    /// Drop trailing zero coefficients so the leading coefficient is non-zero.
    fn normalize(&mut self) {
        while let Some(last) = self.coeffs.last() {
            if last.is_zero() {
                self.coeffs.pop();
            } else {
                break;
            }
        }
    }

    fn is_zero(&self) -> bool {
        self.coeffs.is_empty()
    }

    /// Degree, or `None` for the zero polynomial.
    fn degree(&self) -> Option<usize> {
        if self.coeffs.is_empty() {
            None
        } else {
            Some(self.coeffs.len() - 1)
        }
    }

    fn neg(&self) -> Self {
        Self {
            coeffs: self.coeffs.iter().map(|c| -c).collect(),
        }
    }

    fn add(&self, other: &Self) -> Self {
        let n = self.coeffs.len().max(other.coeffs.len());
        let mut coeffs = Vec::with_capacity(n);
        for i in 0..n {
            let a = self.coeffs.get(i).cloned().unwrap_or_else(BigInt::zero);
            let b = other.coeffs.get(i).cloned().unwrap_or_else(BigInt::zero);
            coeffs.push(a + b);
        }
        let mut p = Self { coeffs };
        p.normalize();
        p
    }

    fn sub(&self, other: &Self) -> Self {
        self.add(&other.neg())
    }

    fn mul(&self, other: &Self) -> Self {
        if self.is_zero() || other.is_zero() {
            return Self::zero();
        }
        let mut coeffs = vec![BigInt::zero(); self.coeffs.len() + other.coeffs.len() - 1];
        for (i, a) in self.coeffs.iter().enumerate() {
            if a.is_zero() {
                continue;
            }
            for (j, b) in other.coeffs.iter().enumerate() {
                coeffs[i + j] += a * b;
            }
        }
        let mut p = Self { coeffs };
        p.normalize();
        p
    }

    /// Evaluate at an exact integer point (Horner).
    fn eval(&self, x: &BigInt) -> BigInt {
        let mut acc = BigInt::zero();
        for c in self.coeffs.iter().rev() {
            acc = acc * x + c;
        }
        acc
    }
}

/// A polynomial paired with the single variable it depends on (if any).
struct VarPoly {
    poly: IntPoly,
    var: Option<TermId>,
}

impl VarPoly {
    /// Combine two var-polynomials under addition, failing if they mention two
    /// distinct variables.
    fn combine_add(self, other: Self) -> Option<Self> {
        let var = merge_var(self.var, other.var).ok()?;
        Some(Self {
            poly: self.poly.add(&other.poly),
            var,
        })
    }

    /// Combine two var-polynomials under multiplication, failing if they mention
    /// two distinct variables.
    fn combine_mul(self, other: Self) -> Option<Self> {
        let var = merge_var(self.var, other.var).ok()?;
        Some(Self {
            poly: self.poly.mul(&other.poly),
            var,
        })
    }
}

/// The six comparison relations against zero.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Rel {
    Lt,
    Le,
    Eq,
    Ge,
    Gt,
    Ne,
}

impl Rel {
    /// Does `sign(p) {rel} 0` hold, where `sign` is -1, 0 or +1?
    fn holds_for_sign(self, sign: i32) -> bool {
        match self {
            Self::Lt => sign < 0,
            Self::Le => sign <= 0,
            Self::Eq => sign == 0,
            Self::Ge => sign >= 0,
            Self::Gt => sign > 0,
            Self::Ne => sign != 0,
        }
    }
}

/// A single constraint reduced to `poly REL 0` over the shared variable.
struct IntConstraint {
    poly: IntPoly,
    rel: Rel,
}

/// Classification of one asserted atom.
enum AtomClass {
    /// A pure-constant atom that is always true (contributes nothing).
    ConstTrue,
    /// A pure-constant atom that is always false (=> whole problem UNSAT).
    ConstFalse,
    /// A univariate constraint over `var`.
    Univariate(TermId, IntConstraint),
    /// Out of fragment — caller must fall through.
    OutOfScope,
}

impl NiaSolver<'_> {
    /// Attempt to decide the current assertion set with the exact univariate-
    /// integer procedure. Returns `None` whenever anything is outside the
    /// supported fragment or cannot be confirmed exactly (caller treats `None`
    /// as Unknown and falls through unchanged).
    ///
    /// SAT results carry an exact integer witness, recorded into
    /// `bounded_enum_model` so the executor can build a concrete model. UNSAT
    /// results carry the full asserted-literal conflict set.
    pub(crate) fn try_univariate_integer(&mut self) -> Option<TheoryResult> {
        // Collect constraints; all must share a single integer variable.
        let mut var: Option<TermId> = None;
        let mut constraints: Vec<IntConstraint> = Vec::new();

        for &(atom, value) in &self.asserted {
            match self.atom_to_int_univariate(atom, value) {
                AtomClass::ConstFalse => {
                    return Some(self.univariate_unsat());
                }
                AtomClass::ConstTrue => {}
                AtomClass::Univariate(v, c) => {
                    match var {
                        None => var = Some(v),
                        Some(existing) if existing == v => {}
                        // Two distinct constrained variables => out of fragment.
                        Some(_) => return None,
                    }
                    constraints.push(c);
                }
                AtomClass::OutOfScope => return None,
            }
        }

        // Need exactly one constrained variable for this decider.
        let var = var?;
        if constraints.is_empty() {
            return None;
        }

        // The variable must be integer-sorted (defensive; QF_NIA vars are Int).
        if !matches!(self.terms.sort(var), Sort::Int) {
            return None;
        }

        // Build the complete candidate integer set.
        let candidates = self.collect_int_candidates(&constraints)?;

        // SAT: test each candidate by exact substitution into ALL atoms. The
        // candidate set is a complete cover (see module docs), so the first
        // satisfying integer is a genuine witness and the absence of any
        // satisfying candidate is a genuine UNSAT.
        for cand in &candidates {
            if self.int_satisfies_all(var, cand) {
                self.record_univariate_model(var, cand);
                if self.debug {
                    safe_eprintln!("[NIA] univariate-int: SAT with {var:?}={cand}");
                }
                return Some(TheoryResult::Sat);
            }
        }

        if self.debug {
            safe_eprintln!(
                "[NIA] univariate-int: UNSAT (no integer among {} complete candidates)",
                candidates.len()
            );
        }
        Some(self.univariate_unsat())
    }

    /// Build the asserted-literal conflict for a univariate UNSAT verdict.
    fn univariate_unsat(&self) -> TheoryResult {
        let conflict: Vec<TheoryLit> = self
            .asserted
            .iter()
            .map(|&(term, value)| TheoryLit::new(term, value))
            .collect();
        TheoryResult::Unsat(conflict)
    }

    /// Test whether the integer assignment `var = value` satisfies EVERY
    /// asserted atom by exact substitution. Reuses `eval_constraint_exact`
    /// (the same evaluator bounded enumeration trusts). Any atom that cannot be
    /// evaluated exactly makes this return `false` (so we never claim SAT on an
    /// unverified witness).
    fn int_satisfies_all(&self, var: TermId, value: &BigInt) -> bool {
        let Some(v64) = value.to_i64() else {
            // `eval_constraint_exact` works over an i64 var map. Witnesses that
            // do not fit i64 cannot be verified by it; treat as unverified.
            // (Candidates are derived from divisors / a bounded range, so this
            // only rejects astronomically large tail reps, which is sound — we
            // just decline to claim SAT for them.)
            return false;
        };
        let mut var_map: HashMap<TermId, i64> = HashMap::default();
        var_map.insert(var, v64);
        for &(term, polarity) in &self.asserted {
            match self.eval_constraint_exact(term, polarity, &var_map) {
                Some(true) => {}
                Some(false) | None => return false,
            }
        }
        true
    }

    /// Record an exact integer witness so the executor can extract a model.
    fn record_univariate_model(&mut self, var: TermId, value: &BigInt) {
        let mut model: HashMap<TermId, BigInt> = HashMap::default();
        model.insert(var, value.clone());
        // Materialize any registered monomial aux vars under this assignment so
        // the model is consistent (e.g. the aux var for `x*x`).
        let Some(v64) = value.to_i64() else {
            self.bounded_enum_model = Some(model);
            return;
        };
        let mut var_map: HashMap<TermId, i64> = HashMap::default();
        var_map.insert(var, v64);
        for mon in self.monomials.values() {
            if let Some(value) = self.eval_term(mon.aux_var, &var_map) {
                model.insert(mon.aux_var, value);
            }
        }
        self.bounded_enum_model = Some(model);
    }

    /// Assemble the complete candidate integer set described in the module
    /// docs. Returns `None` if completeness cannot be guaranteed cheaply
    /// (divisor constant too large, or the bounded middle exceeds the cap).
    fn collect_int_candidates(&self, constraints: &[IntConstraint]) -> Option<Vec<BigInt>> {
        let mut candidates: Vec<BigInt> = Vec::new();

        // Path A: if any equality is present, its integer roots form a COMPLETE
        // cover of the satisfying integers (every model is a root of that
        // equality). Enumerate the integer roots of the *first* such equality;
        // testing them against all atoms decides the problem.
        for c in constraints {
            if c.rel == Rel::Eq {
                let roots = integer_roots(&c.poly)?;
                for r in roots {
                    if !candidates.contains(&r) {
                        candidates.push(r);
                    }
                }
                // One equality suffices for completeness.
                return Some(candidates);
            }
        }

        // Path B: inequality-only system. Cover all integers via a Cauchy bound
        // `B` (all real roots lie in [-B, B]) plus both unbounded tails.
        let b = cauchy_bound(constraints)?;
        // Tail representatives: just past the extreme roots. Each tail is
        // sign-constant for every constraint poly (no roots beyond [-B, B]), so
        // one representative integer decides the whole tail.
        push_unique(&mut candidates, &b + BigInt::one());
        push_unique(&mut candidates, -&b - BigInt::one());

        // Bounded middle: enumerate every integer in [-B, B]. Cap the width so
        // pathological bounds return Unknown rather than enumerating forever.
        let width: BigRational = BigRational::from_integer(&b + &b) + BigRational::one();
        let width_i128 = width.to_integer().to_i128()?;
        if width_i128 > MAX_MIDDLE_WIDTH {
            return None;
        }
        let mut k = -b.clone();
        while k <= b {
            push_unique(&mut candidates, k.clone());
            k += BigInt::one();
        }
        Some(candidates)
    }

    /// Classify an asserted atom into `poly REL 0` over at most one variable.
    fn atom_to_int_univariate(&self, atom: TermId, value: bool) -> AtomClass {
        let Some((rel0, lhs, rhs)) = self.int_comparison_parts(atom) else {
            return AtomClass::OutOfScope;
        };
        // Apply polarity: a false-asserted atom negates the relation.
        let rel = if value { rel0 } else { negate_rel(rel0) };

        let lhs_poly = match self.term_to_intpoly(lhs) {
            Some(p) => p,
            None => return AtomClass::OutOfScope,
        };
        let rhs_poly = match self.term_to_intpoly(rhs) {
            Some(p) => p,
            None => return AtomClass::OutOfScope,
        };

        let var = match merge_var(lhs_poly.var, rhs_poly.var) {
            Ok(v) => v,
            Err(()) => return AtomClass::OutOfScope, // two distinct variables
        };

        let poly = lhs_poly.poly.sub(&rhs_poly.poly);

        match var {
            None => {
                // Pure-constant constraint: evaluate the constant's sign.
                let sign = match poly.degree() {
                    None => 0,                               // zero polynomial
                    Some(0) => bigint_sign(&poly.coeffs[0]), // constant
                    Some(_) => return AtomClass::OutOfScope, // unreachable; be safe
                };
                if rel.holds_for_sign(sign) {
                    AtomClass::ConstTrue
                } else {
                    AtomClass::ConstFalse
                }
            }
            Some(v) => AtomClass::Univariate(v, IntConstraint { poly, rel }),
        }
    }

    /// Extract `(rel, lhs, rhs)` from a binary comparison atom.
    fn int_comparison_parts(&self, atom: TermId) -> Option<(Rel, TermId, TermId)> {
        match self.terms.get(atom) {
            TermData::App(Symbol::Named(name), args) if args.len() == 2 => {
                let rel = match name.as_str() {
                    "<" => Rel::Lt,
                    "<=" => Rel::Le,
                    "=" => Rel::Eq,
                    ">=" => Rel::Ge,
                    ">" => Rel::Gt,
                    "distinct" | "!=" => Rel::Ne,
                    _ => return None,
                };
                Some((rel, args[0], args[1]))
            }
            _ => None,
        }
    }

    /// Convert an arithmetic term to an integer polynomial plus its (≤1)
    /// variable. Returns `None` for unsupported operators, non-integer rational
    /// constants, or two distinct variables.
    fn term_to_intpoly(&self, term: TermId) -> Option<VarPoly> {
        match self.terms.get(term) {
            TermData::Const(Constant::Int(n)) => Some(VarPoly {
                poly: IntPoly::constant(n.clone()),
                var: None,
            }),
            TermData::Const(Constant::Rational(r)) => {
                // Only integer-valued rationals are in scope.
                if r.0.denom().is_one() {
                    Some(VarPoly {
                        poly: IntPoly::constant(r.0.numer().clone()),
                        var: None,
                    })
                } else {
                    None
                }
            }
            TermData::Var(_, _) => {
                // Only integer-sorted variables are in scope.
                if matches!(self.terms.sort(term), Sort::Int) {
                    Some(VarPoly {
                        poly: IntPoly::x(),
                        var: Some(term),
                    })
                } else {
                    None
                }
            }
            TermData::App(Symbol::Named(name), args) => match name.as_str() {
                "+" if !args.is_empty() => {
                    let mut acc = VarPoly {
                        poly: IntPoly::zero(),
                        var: None,
                    };
                    for &a in args {
                        let p = self.term_to_intpoly(a)?;
                        acc = acc.combine_add(p)?;
                    }
                    Some(acc)
                }
                "-" if args.len() == 1 => {
                    let p = self.term_to_intpoly(args[0])?;
                    Some(VarPoly {
                        poly: p.poly.neg(),
                        var: p.var,
                    })
                }
                "-" if args.len() >= 2 => {
                    let mut acc = self.term_to_intpoly(args[0])?;
                    for &a in &args[1..] {
                        let p = self.term_to_intpoly(a)?;
                        let negated = VarPoly {
                            poly: p.poly.neg(),
                            var: p.var,
                        };
                        acc = acc.combine_add(negated)?;
                    }
                    Some(acc)
                }
                "*" if !args.is_empty() => {
                    let mut acc = VarPoly {
                        poly: IntPoly::constant(BigInt::one()),
                        var: None,
                    };
                    for &a in args {
                        let p = self.term_to_intpoly(a)?;
                        acc = acc.combine_mul(p)?;
                    }
                    Some(acc)
                }
                // Unsupported: /, div, mod, abs, transcendental, etc.
                _ => None,
            },
            _ => None,
        }
    }
}

/// Push `c` into `out` only if not already present (small sets; linear scan).
fn push_unique(out: &mut Vec<BigInt>, c: BigInt) {
    if !out.contains(&c) {
        out.push(c);
    }
}

/// Merge two optional variable identities for a binary combination. A `None`
/// operand means "constant"; two equal variables collapse to that variable;
/// two distinct variables make the combination non-univariate (`Err`).
///
/// `Ok(Some(v))` => univariate in `v`; `Ok(None)` => constant; `Err(())` =>
/// out of fragment (two distinct variables).
fn merge_var(a: Option<TermId>, b: Option<TermId>) -> Result<Option<TermId>, ()> {
    match (a, b) {
        (None, None) => Ok(None),
        (Some(v), None) | (None, Some(v)) => Ok(Some(v)),
        (Some(x), Some(y)) if x == y => Ok(Some(x)),
        (Some(_), Some(_)) => Err(()),
    }
}

/// Sign of a `BigInt`: -1, 0, or +1.
fn bigint_sign(n: &BigInt) -> i32 {
    if n.is_zero() {
        0
    } else if n.is_positive() {
        1
    } else {
        -1
    }
}

/// Negate a comparison relation (used when an atom is asserted false).
fn negate_rel(rel: Rel) -> Rel {
    match rel {
        Rel::Lt => Rel::Ge,
        Rel::Le => Rel::Gt,
        Rel::Eq => Rel::Ne,
        Rel::Ge => Rel::Lt,
        Rel::Gt => Rel::Le,
        Rel::Ne => Rel::Eq,
    }
}

/// Enumerate the COMPLETE set of integer roots of integer polynomial `p`.
///
/// By the rational root theorem, every integer root `r` of `p` divides the
/// constant term — but after factoring out the largest `x^k` dividing `p`
/// (which contributes the root `0` when the literal constant term is zero), the
/// relevant divisor target is `p`'s lowest NON-ZERO coefficient `c0`. Every
/// non-zero integer root divides `c0`; together with the root `0` (present iff
/// `k > 0`) this is the full integer root set.
///
/// Returns `None` if `|c0|` is too large to enumerate divisors cheaply (caller
/// then returns Unknown — sound, never a wrong verdict).
fn integer_roots(p: &IntPoly) -> Option<Vec<BigInt>> {
    if p.is_zero() {
        // The zero polynomial is identically zero: every integer is a root.
        // That is not a finite candidate set; decline (caller -> Unknown).
        // (In practice `0 = 0` is classified ConstTrue, not as a constraint.)
        return None;
    }
    if p.degree() == Some(0) {
        // Non-zero constant: no roots at all.
        return Some(Vec::new());
    }

    let mut roots: Vec<BigInt> = Vec::new();

    // Lowest non-zero coefficient and whether x=0 is a root (constant term 0).
    let constant_is_zero = p.coeffs[0].is_zero();
    if constant_is_zero {
        roots.push(BigInt::zero());
    }
    let c0 = p
        .coeffs
        .iter()
        .find(|c| !c.is_zero())
        .expect("non-zero polynomial has a non-zero coefficient");

    // Enumerate divisors of |c0| (both signs); a divisor is a root iff p
    // evaluates to zero there (verified exactly). This is the complete set of
    // non-zero integer roots.
    let divisors = small_divisors_bigint(c0)?;
    for d in &divisors {
        for signed in [d.clone(), -d.clone()] {
            if signed.is_zero() {
                continue;
            }
            if p.eval(&signed).is_zero() && !roots.contains(&signed) {
                roots.push(signed);
            }
        }
    }
    Some(roots)
}

/// Positive divisors of `|n|` (n != 0), or `None` if `|n|` is too large to
/// enumerate cheaply.
fn small_divisors_bigint(n: &BigInt) -> Option<Vec<BigInt>> {
    let an = n.abs();
    if an.is_zero() {
        // |n| == 0 should not reach here (caller passes a non-zero c0).
        return Some(vec![BigInt::one()]);
    }
    if an > BigInt::from(MAX_DIVISOR_CONSTANT) {
        return None;
    }
    let small = an.to_u64()?;
    let mut divs = Vec::new();
    let mut d: u64 = 1;
    while d.checked_mul(d).map(|dd| dd <= small).unwrap_or(false) {
        if small % d == 0 {
            divs.push(BigInt::from(d));
            divs.push(BigInt::from(small / d));
        }
        d += 1;
    }
    Some(divs)
}

/// A Cauchy-style integer bound `B` such that EVERY real root of EVERY
/// constraint polynomial satisfies `|root| <= B`.
///
/// For `p(x) = a_n x^n + ... + a_0` with `a_n != 0`, every real (hence every
/// integer) root satisfies `|x| <= 1 + max_i |a_i| / |a_n|`. We compute that
/// bound exactly per polynomial, take the maximum across all constraints, and
/// round up to an integer.
///
/// Returns `None` if there is no non-constant polynomial (then the caller
/// should not be on this path) — defensive.
fn cauchy_bound(constraints: &[IntConstraint]) -> Option<BigInt> {
    let mut bound = BigRational::one();
    let mut saw_nonconstant = false;
    for c in constraints {
        let deg = c.poly.degree()?;
        if deg == 0 {
            continue; // constant atom contributes no roots
        }
        saw_nonconstant = true;
        let lead = c.poly.coeffs[deg].abs();
        let mut max_other = BigInt::zero();
        for coeff in &c.poly.coeffs[..deg] {
            let a = coeff.abs();
            if a > max_other {
                max_other = a;
            }
        }
        // 1 + max_other / lead
        let this = BigRational::one() + BigRational::new(max_other, lead);
        if this > bound {
            bound = this;
        }
    }
    if !saw_nonconstant {
        return None;
    }
    // Round up to an integer bound.
    Some(rational_ceil_int(&bound))
}

/// Ceiling of a non-negative rational as a `BigInt`.
fn rational_ceil_int(r: &BigRational) -> BigInt {
    let (quot, rem) = r.numer().div_rem(r.denom());
    if rem.is_zero() || r.numer() < &BigInt::zero() {
        quot
    } else {
        quot + BigInt::one()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn xpoly() -> IntPoly {
        IntPoly::x()
    }

    #[test]
    fn test_intpoly_eval() {
        // p = x^2 - 16
        let x2 = xpoly().mul(&xpoly());
        let p = x2.sub(&IntPoly::constant(BigInt::from(16)));
        assert_eq!(p.eval(&BigInt::from(4)), BigInt::zero());
        assert_eq!(p.eval(&BigInt::from(-4)), BigInt::zero());
        assert_eq!(p.eval(&BigInt::from(5)), BigInt::from(9));
    }

    #[test]
    fn test_integer_roots_x2_minus_16() {
        let x2 = xpoly().mul(&xpoly());
        let p = x2.sub(&IntPoly::constant(BigInt::from(16)));
        let mut roots = integer_roots(&p).expect("small enough");
        roots.sort();
        assert_eq!(roots, vec![BigInt::from(-4), BigInt::from(4)]);
    }

    #[test]
    fn test_integer_roots_x2_minus_15_none() {
        // x^2 - 15 has no integer roots.
        let x2 = xpoly().mul(&xpoly());
        let p = x2.sub(&IntPoly::constant(BigInt::from(15)));
        let roots = integer_roots(&p).expect("small enough");
        assert!(
            roots.is_empty(),
            "x^2=15 has no integer roots, got {roots:?}"
        );
    }

    #[test]
    fn test_integer_roots_x3_minus_27() {
        // x^3 - 27, root x=3 only.
        let x3 = xpoly().mul(&xpoly()).mul(&xpoly());
        let p = x3.sub(&IntPoly::constant(BigInt::from(27)));
        let roots = integer_roots(&p).expect("small enough");
        assert_eq!(roots, vec![BigInt::from(3)]);
    }

    #[test]
    fn test_integer_roots_x2_only_zero() {
        // x^2 = 0 -> only root 0 (constant term zero).
        let p = xpoly().mul(&xpoly());
        let roots = integer_roots(&p).expect("small enough");
        assert_eq!(roots, vec![BigInt::from(0)]);
    }

    #[test]
    fn test_integer_roots_x4_minus_16() {
        // x^4 - 16, integer roots +/-2.
        let x4 = xpoly().mul(&xpoly()).mul(&xpoly()).mul(&xpoly());
        let p = x4.sub(&IntPoly::constant(BigInt::from(16)));
        let mut roots = integer_roots(&p).expect("small enough");
        roots.sort();
        assert_eq!(roots, vec![BigInt::from(-2), BigInt::from(2)]);
    }

    #[test]
    fn test_integer_roots_2x2_minus_32() {
        // 2x^2 - 32, integer roots +/-4.
        let two_x2 = IntPoly::constant(BigInt::from(2))
            .mul(&xpoly())
            .mul(&xpoly());
        let p = two_x2.sub(&IntPoly::constant(BigInt::from(32)));
        let mut roots = integer_roots(&p).expect("small enough");
        roots.sort();
        assert_eq!(roots, vec![BigInt::from(-4), BigInt::from(4)]);
    }

    #[test]
    fn test_integer_roots_linear_leading_two() {
        // 2x - 6 = 0 -> x=3 (3 divides 6, the constant; leading coeff 2).
        let p = IntPoly::constant(BigInt::from(2))
            .mul(&xpoly())
            .sub(&IntPoly::constant(BigInt::from(6)));
        let roots = integer_roots(&p).expect("small enough");
        assert_eq!(roots, vec![BigInt::from(3)]);
    }

    #[test]
    fn test_cauchy_bound_x2_ge_16() {
        // x^2 - 16 >= 0; Cauchy bound 1 + 16/1 = 17.
        let x2 = xpoly().mul(&xpoly());
        let p = x2.sub(&IntPoly::constant(BigInt::from(16)));
        let c = IntConstraint {
            poly: p,
            rel: Rel::Ge,
        };
        let b = cauchy_bound(std::slice::from_ref(&c)).expect("nonconstant");
        assert_eq!(b, BigInt::from(17));
    }

    #[test]
    fn test_rational_ceil_int() {
        assert_eq!(
            rational_ceil_int(&BigRational::new(BigInt::from(17), BigInt::from(1))),
            BigInt::from(17)
        );
        assert_eq!(
            rational_ceil_int(&BigRational::new(BigInt::from(5), BigInt::from(2))),
            BigInt::from(3)
        );
        assert_eq!(
            rational_ceil_int(&BigRational::new(BigInt::from(3), BigInt::from(1))),
            BigInt::from(3)
        );
    }
}
