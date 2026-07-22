// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Sound interval contraction for bounded NIA enumeration (#nia-interval-contract).
//!
//! `try_bounded_enumeration` (bounded_enum.rs) is an exact finite-box decision
//! procedure, but it needs a COMPLETE finite box: every enumeration variable
//! must have both an integer lower and upper bound. Many bounded-domain
//! queries constrain some variables only *through* nonlinear atoms — e.g.
//!
//! ```text
//! x*x = 2*y*y + 1,  100 < x < 130
//! ```
//!
//! has no direct bound on `y`, yet `y` is finitely bounded semantically:
//! `y*y = (x*x - 1)/2 <= (129^2 - 1)/2 = 8320`, so `|y| <= 91`. Without that
//! inference the enumeration bails and the solver answers `unknown` where the
//! problem is decidable by exhaustive search.
//!
//! This module implements a small HC4-revise-style *contractor*: for each
//! asserted comparison atom it evaluates the two sides with exact integer
//! interval arithmetic (forward pass) and then propagates the implied
//! interval back down through `+`, `-` and `*` nodes to the variable leaves
//! (backward pass), iterating to a (budgeted) fixpoint.
//!
//! ## Soundness contract
//!
//! The ONLY consumer-visible effect is *tightening* the per-variable bounds
//! map fed to bounded enumeration. Every rule removes only values that cannot
//! participate in ANY solution of the asserted atoms:
//!
//! * Forward interval arithmetic over-approximates the range of each term
//!   (standard interval arithmetic, with `0 * inf = 0` endpoint convention,
//!   sound for non-empty intervals).
//! * Backward rules are the algebraic inversions (`a + b = n` implies
//!   `a = n - b`; `a * b = n` with `b` sign-definite implies `a ∈ n / b`;
//!   `s^m ∈ S` implies `|s| <= floor(max(S)^(1/m))` for even `m`, and
//!   `s ∈ [ceil(min(S)^(1/m)), floor(max(S)^(1/m))]` for odd `m`), each with
//!   OUTWARD-safe rounding for integer-valued terms (`ceil` on lower bounds,
//!   `floor` on upper bounds — the term's true value is an integer inside the
//!   real interval, so this rounding never excludes a feasible integer).
//! * Anything the contractor does not understand (opaque operators, non-Int
//!   sorts, divisor intervals containing 0, oversized numbers, empty
//!   intersections) makes it SKIP or STOP — never guess. On an empty
//!   intersection the contraction pass simply stops; verdicts are NEVER
//!   derived here. All SAT/UNSAT decisions remain with the exhaustive
//!   enumeration, which re-checks every atom at every point by exact
//!   substitution.
//!
//! ## Budgets
//!
//! * at most [`MAX_CONTRACT_ROUNDS`] fixpoint rounds;
//! * skipped entirely beyond [`MAX_CONTRACT_ATOMS`] asserted atoms;
//! * recursion depth capped at [`MAX_CONTRACT_DEPTH`];
//! * any endpoint wider than [`MAX_ENDPOINT_BITS`] bits is widened to
//!   infinity (sound: widening only loses precision, never solutions).

use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Signed, ToPrimitive, Zero};

use super::*;

/// Maximum number of full fixpoint rounds over the asserted atoms.
const MAX_CONTRACT_ROUNDS: usize = 8;

/// Skip contraction entirely when there are more asserted atoms than this
/// (keeps the pass trivially cheap on large industrial instances; bounded
/// enumeration itself scans all atoms per point, so this bound is generous).
const MAX_CONTRACT_ATOMS: usize = 64;

/// Recursion depth cap for the forward/backward passes.
const MAX_CONTRACT_DEPTH: usize = 64;

/// Endpoints wider than this many bits are widened to infinity. Keeps the
/// BigInt arithmetic bounded even on adversarial nesting.
const MAX_ENDPOINT_BITS: u64 = 256;

/// Extended integer endpoint: -inf, finite, or +inf.
#[derive(Clone, Debug, PartialEq, Eq)]
enum Ep {
    NegInf,
    Fin(BigInt),
    PosInf,
}

impl Ep {
    fn fin(n: i64) -> Ep {
        Ep::Fin(BigInt::from(n))
    }

    /// Total order: NegInf < Fin(a) < Fin(b) < PosInf (a < b).
    fn cmp_ep(&self, other: &Ep) -> std::cmp::Ordering {
        use std::cmp::Ordering::{Equal, Greater, Less};
        match (self, other) {
            (Ep::NegInf, Ep::NegInf) | (Ep::PosInf, Ep::PosInf) => Equal,
            (Ep::NegInf, _) | (_, Ep::PosInf) => Less,
            (_, Ep::NegInf) | (Ep::PosInf, _) => Greater,
            (Ep::Fin(a), Ep::Fin(b)) => a.cmp(b),
        }
    }

    /// Widen oversized finite endpoints to the given infinity (sound: the
    /// widened interval is a superset).
    fn widen(self, to_pos: bool) -> Ep {
        match &self {
            Ep::Fin(n) if n.bits() > MAX_ENDPOINT_BITS => {
                if to_pos {
                    Ep::PosInf
                } else {
                    Ep::NegInf
                }
            }
            _ => self,
        }
    }
}

/// Integer interval with extended endpoints. Invariant (enforced by all
/// constructors used below): `lo != PosInf`, `hi != NegInf`. May be EMPTY
/// (`lo > hi`); emptiness is checked explicitly via [`Iv::is_empty`].
#[derive(Clone, Debug, PartialEq, Eq)]
struct Iv {
    lo: Ep,
    hi: Ep,
}

impl Iv {
    fn top() -> Iv {
        Iv {
            lo: Ep::NegInf,
            hi: Ep::PosInf,
        }
    }

    fn point(n: BigInt) -> Iv {
        Iv {
            lo: Ep::Fin(n.clone()),
            hi: Ep::Fin(n),
        }
    }

    fn is_empty(&self) -> bool {
        self.lo.cmp_ep(&self.hi) == std::cmp::Ordering::Greater
    }

    fn intersect(&self, other: &Iv) -> Iv {
        let lo = if self.lo.cmp_ep(&other.lo) == std::cmp::Ordering::Greater {
            self.lo.clone()
        } else {
            other.lo.clone()
        };
        let hi = if self.hi.cmp_ep(&other.hi) == std::cmp::Ordering::Less {
            self.hi.clone()
        } else {
            other.hi.clone()
        };
        Iv { lo, hi }
    }

    /// Apply the oversized-endpoint widening to both endpoints.
    fn widened(self) -> Iv {
        Iv {
            lo: self.lo.widen(false),
            hi: self.hi.widen(true),
        }
    }

    /// `self + other` (exact interval addition; inf absorbs).
    fn add(&self, other: &Iv) -> Iv {
        let lo = match (&self.lo, &other.lo) {
            (Ep::Fin(a), Ep::Fin(b)) => Ep::Fin(a + b),
            _ => Ep::NegInf,
        };
        let hi = match (&self.hi, &other.hi) {
            (Ep::Fin(a), Ep::Fin(b)) => Ep::Fin(a + b),
            _ => Ep::PosInf,
        };
        Iv { lo, hi }.widened()
    }

    /// `-self`.
    fn neg(&self) -> Iv {
        let lo = match &self.hi {
            Ep::Fin(a) => Ep::Fin(-a),
            Ep::PosInf => Ep::NegInf,
            Ep::NegInf => Ep::PosInf, // unreachable under the invariant
        };
        let hi = match &self.lo {
            Ep::Fin(a) => Ep::Fin(-a),
            Ep::NegInf => Ep::PosInf,
            Ep::PosInf => Ep::NegInf, // unreachable under the invariant
        };
        Iv { lo, hi }
    }

    /// `self - other`.
    fn sub(&self, other: &Iv) -> Iv {
        self.add(&other.neg())
    }

    /// Endpoint product with the standard `0 * inf = 0` convention (sound
    /// for computing bounds of products of non-empty sets).
    fn mul_ep(a: &Ep, b: &Ep) -> Ep {
        match (a, b) {
            (Ep::Fin(x), Ep::Fin(y)) => Ep::Fin(x * y),
            (Ep::Fin(x), inf) | (inf, Ep::Fin(x)) => {
                if x.is_zero() {
                    Ep::Fin(BigInt::zero())
                } else if (x.is_positive()) == matches!(inf, Ep::PosInf) {
                    Ep::PosInf
                } else {
                    Ep::NegInf
                }
            }
            (Ep::PosInf, Ep::PosInf) | (Ep::NegInf, Ep::NegInf) => Ep::PosInf,
            _ => Ep::NegInf,
        }
    }

    /// `self * other` via endpoint candidates (valid for non-empty intervals).
    fn mul(&self, other: &Iv) -> Iv {
        let cands = [
            Self::mul_ep(&self.lo, &other.lo),
            Self::mul_ep(&self.lo, &other.hi),
            Self::mul_ep(&self.hi, &other.lo),
            Self::mul_ep(&self.hi, &other.hi),
        ];
        let mut lo = cands[0].clone();
        let mut hi = cands[0].clone();
        for c in &cands[1..] {
            if c.cmp_ep(&lo) == std::cmp::Ordering::Less {
                lo = c.clone();
            }
            if c.cmp_ep(&hi) == std::cmp::Ordering::Greater {
                hi = c.clone();
            }
        }
        Iv { lo, hi }.widened()
    }

    /// `self^m` for `m >= 1`, exploiting even-power non-negativity (this is
    /// TIGHTER than repeated `mul` on intervals straddling 0, and sound: the
    /// range of `s^m` for `s` in the interval is exactly what is computed,
    /// modulo endpoint widening).
    fn pow(&self, m: usize) -> Iv {
        fn pow_ep(e: &Ep, m: usize) -> Ep {
            match e {
                Ep::Fin(n) => Ep::Fin(n.pow(m as u32)),
                Ep::PosInf => Ep::PosInf,
                Ep::NegInf => {
                    if m.is_multiple_of(2) {
                        Ep::PosInf
                    } else {
                        Ep::NegInf
                    }
                }
            }
        }
        if m == 1 {
            return self.clone();
        }
        let zero = Ep::Fin(BigInt::zero());
        if m % 2 == 1 {
            // Odd power: monotone.
            return Iv {
                lo: pow_ep(&self.lo, m),
                hi: pow_ep(&self.hi, m),
            }
            .widened();
        }
        // Even power.
        if self.lo.cmp_ep(&zero) != std::cmp::Ordering::Less {
            // lo >= 0: monotone increasing.
            Iv {
                lo: pow_ep(&self.lo, m),
                hi: pow_ep(&self.hi, m),
            }
            .widened()
        } else if self.hi.cmp_ep(&zero) != std::cmp::Ordering::Greater {
            // hi <= 0: monotone decreasing.
            Iv {
                lo: pow_ep(&self.hi, m),
                hi: pow_ep(&self.lo, m),
            }
            .widened()
        } else {
            // Straddles 0: [0, max(|lo|, |hi|)^m].
            let abs_lo = match &self.lo {
                Ep::Fin(n) => Ep::Fin(n.abs()),
                _ => Ep::PosInf,
            };
            let abs_hi = match &self.hi {
                Ep::Fin(n) => Ep::Fin(n.abs()),
                _ => Ep::PosInf,
            };
            let biggest = if abs_lo.cmp_ep(&abs_hi) == std::cmp::Ordering::Greater {
                abs_lo
            } else {
                abs_hi
            };
            Iv {
                lo: zero,
                hi: pow_ep(&biggest, m),
            }
            .widened()
        }
    }

    /// True iff the interval excludes 0 with a definite sign (`lo > 0` or
    /// `hi < 0`). Required before dividing by it.
    fn sign_definite_nonzero(&self) -> bool {
        let zero = Ep::Fin(BigInt::zero());
        self.lo.cmp_ep(&zero) == std::cmp::Ordering::Greater
            || self.hi.cmp_ep(&zero) == std::cmp::Ordering::Less
    }

    /// Integer contraction of `self / other` where `self` is an interval of
    /// an INTEGER-valued quantity `q` known to satisfy `q * o = n` for some
    /// `n ∈ self`, `o ∈ other`, and `other` is sign-definite (no 0). Returns
    /// `None` when the division is not usable. The rational quotient interval
    /// is rounded INWARD (`ceil` lower / `floor` upper), sound because the
    /// true `q` is an integer inside the real quotient interval.
    fn div_int(&self, other: &Iv) -> Option<Iv> {
        if !other.sign_definite_nonzero() {
            return None;
        }
        // Extended-rational endpoint candidates.
        #[derive(Clone)]
        enum Rq {
            NegInf,
            Fin(BigRational),
            PosInf,
        }
        impl Rq {
            fn cmp_rq(&self, other: &Rq) -> std::cmp::Ordering {
                use std::cmp::Ordering::{Equal, Greater, Less};
                match (self, other) {
                    (Rq::NegInf, Rq::NegInf) | (Rq::PosInf, Rq::PosInf) => Equal,
                    (Rq::NegInf, _) | (_, Rq::PosInf) => Less,
                    (_, Rq::NegInf) | (Rq::PosInf, _) => Greater,
                    (Rq::Fin(a), Rq::Fin(b)) => a.cmp(b),
                }
            }
        }
        fn div_ep(n: &Ep, d: &Ep) -> Rq {
            match (n, d) {
                (Ep::Fin(a), Ep::Fin(b)) => {
                    // `b != 0` is guaranteed by sign_definite_nonzero.
                    Rq::Fin(BigRational::new(a.clone(), b.clone()))
                }
                // Finite numerator over an infinite divisor: the quotient
                // tends to 0; using 0 as the candidate is a sound
                // over-approximation of the endpoint.
                (Ep::Fin(_), _) => Rq::Fin(BigRational::zero()),
                // Infinite numerator: sign(n) * sign(d).
                (Ep::PosInf, d) => {
                    if matches!(d, Ep::NegInf) || matches!(d, Ep::Fin(x) if x.is_negative()) {
                        Rq::NegInf
                    } else {
                        Rq::PosInf
                    }
                }
                (Ep::NegInf, d) => {
                    if matches!(d, Ep::NegInf) || matches!(d, Ep::Fin(x) if x.is_negative()) {
                        Rq::PosInf
                    } else {
                        Rq::NegInf
                    }
                }
            }
        }
        let cands = [
            div_ep(&self.lo, &other.lo),
            div_ep(&self.lo, &other.hi),
            div_ep(&self.hi, &other.lo),
            div_ep(&self.hi, &other.hi),
        ];
        let mut qlo = cands[0].clone();
        let mut qhi = cands[0].clone();
        for c in &cands[1..] {
            if c.cmp_rq(&qlo) == std::cmp::Ordering::Less {
                qlo = c.clone();
            }
            if c.cmp_rq(&qhi) == std::cmp::Ordering::Greater {
                qhi = c.clone();
            }
        }
        let lo = match qlo {
            Rq::NegInf => Ep::NegInf,
            Rq::Fin(r) => Ep::Fin(rational_ceil_big(&r)),
            Rq::PosInf => return None, // degenerate; do not use
        };
        let hi = match qhi {
            Rq::PosInf => Ep::PosInf,
            Rq::Fin(r) => Ep::Fin(rational_floor_big(&r)),
            Rq::NegInf => return None, // degenerate; do not use
        };
        Some(Iv { lo, hi }.widened())
    }

    /// Contract `s` from `s^m ∈ self` (`m >= 1`). Returns the interval for
    /// `s`, or `None` when no (usable) contraction exists. Even powers use
    /// only the UPPER bound (`|s| <= floor(hi^(1/m))`); the lower bound of an
    /// even power describes a disjunction (`s <= -r or s >= r`) that a single
    /// interval cannot express, so it is (soundly) ignored.
    fn root_contract(&self, m: usize) -> Option<Iv> {
        if m == 1 {
            return Some(self.clone());
        }
        if m.is_multiple_of(2) {
            match &self.hi {
                Ep::Fin(h) => {
                    if h.is_negative() {
                        // s^m >= 0 always; an all-negative target is empty.
                        // Represent as an explicitly empty interval; the
                        // caller treats empties as "stop the pass".
                        return Some(Iv {
                            lo: Ep::Fin(BigInt::one()),
                            hi: Ep::Fin(BigInt::zero()),
                        });
                    }
                    let r = floor_nth_root(h, m);
                    Some(Iv {
                        lo: Ep::Fin(-r.clone()),
                        hi: Ep::Fin(r),
                    })
                }
                _ => None,
            }
        } else {
            let lo = match &self.lo {
                Ep::Fin(l) => Ep::Fin(ceil_nth_root(l, m)),
                _ => Ep::NegInf,
            };
            let hi = match &self.hi {
                Ep::Fin(h) => Ep::Fin(floor_nth_root(h, m)),
                _ => Ep::PosInf,
            };
            Some(Iv { lo, hi })
        }
    }
}

/// Largest integer `r` with `r^m <= n` (`m >= 1`; any sign of `n` for odd
/// `m`, `n >= 0` required for even `m` — callers guarantee this). Uses the
/// truncated `nth_root` as a seed and adjusts with exact comparisons.
fn floor_nth_root(n: &BigInt, m: usize) -> BigInt {
    let m32 = m as u32;
    let mut r = n.nth_root(m32);
    // nth_root truncates toward zero: exact floor for n >= 0, but for
    // negative n with odd m the truncated root can be one too HIGH.
    while r.pow(m32) > *n {
        r -= 1;
    }
    while (&r + BigInt::one()).pow(m32) <= *n {
        r += 1;
    }
    r
}

/// Smallest integer `r` with `r^m >= n` (same domain as [`floor_nth_root`]).
fn ceil_nth_root(n: &BigInt, m: usize) -> BigInt {
    let f = floor_nth_root(n, m);
    if f.pow(m as u32) == *n {
        f
    } else {
        f + 1
    }
}

/// `ceil` of a rational as a BigInt.
fn rational_ceil_big(r: &BigRational) -> BigInt {
    r.ceil().to_integer()
}

/// `floor` of a rational as a BigInt.
fn rational_floor_big(r: &BigRational) -> BigInt {
    r.floor().to_integer()
}

/// Signal that the contraction pass should stop (empty intersection seen or
/// an internal budget tripped). Contractions applied SO FAR remain valid —
/// each individual tightening is independently sound — so the caller keeps
/// them; it simply must not derive any verdict from the emptiness.
struct StopContraction;

struct Contractor<'a, 'b> {
    solver: &'b NiaSolver<'a>,
    /// Working bounds for the enumeration variables (BigInt endpoints).
    bounds: HashMap<TermId, Iv>,
    /// Whether any variable interval changed in the current round.
    changed: bool,
}

impl Contractor<'_, '_> {
    /// Forward pass: over-approximate the integer range of `term`.
    fn fwd(&self, term: TermId, depth: usize) -> Iv {
        if depth > MAX_CONTRACT_DEPTH {
            return Iv::top();
        }
        match self.solver.terms.get(term) {
            TermData::Var(_, _) => self.bounds.get(&term).cloned().unwrap_or_else(Iv::top),
            TermData::Const(Constant::Int(n)) => Iv::point(n.clone()),
            TermData::Const(Constant::Rational(r)) if r.0.denom().is_one() => {
                Iv::point(r.0.numer().clone())
            }
            TermData::App(Symbol::Named(name), args) => match name.as_str() {
                "+" => {
                    let mut acc = Iv::point(BigInt::zero());
                    for &arg in args {
                        acc = acc.add(&self.fwd(arg, depth + 1));
                    }
                    acc
                }
                "-" if args.len() == 1 => self.fwd(args[0], depth + 1).neg(),
                "-" if args.len() == 2 => self
                    .fwd(args[0], depth + 1)
                    .sub(&self.fwd(args[1], depth + 1)),
                "*" => {
                    // Group repeated factors so `x*x` evaluates via `pow`
                    // (square-aware: non-negative even when `x` straddles 0).
                    let (c, groups) = group_product_args(self.solver, args);
                    let mut acc = Iv::point(c);
                    for (child, mult) in groups {
                        acc = acc.mul(&self.fwd(child, depth + 1).pow(mult));
                    }
                    acc
                }
                _ => Iv::top(),
            },
            _ => Iv::top(),
        }
    }

    /// Backward pass: `term`'s value is known to lie in `target`; propagate
    /// down to variable leaves, tightening `self.bounds`.
    fn bwd(&mut self, term: TermId, target: &Iv, depth: usize) -> Result<(), StopContraction> {
        if depth > MAX_CONTRACT_DEPTH {
            return Ok(());
        }
        let refined = self.fwd(term, depth).intersect(target);
        if refined.is_empty() {
            return Err(StopContraction);
        }
        match self.solver.terms.get(term) {
            TermData::Var(_, _) => {
                // Only Int-sorted variables participate.
                if !matches!(self.solver.terms.sort(term), Sort::Int) {
                    return Ok(());
                }
                let cur = self.bounds.get(&term).cloned().unwrap_or_else(Iv::top);
                let tightened = cur.intersect(&refined);
                if tightened.is_empty() {
                    return Err(StopContraction);
                }
                if tightened != cur {
                    self.changed = true;
                    self.bounds.insert(term, tightened);
                }
                Ok(())
            }
            TermData::App(Symbol::Named(name), args) => match name.as_str() {
                "+" => {
                    for (i, &arg) in args.iter().enumerate() {
                        let mut others = Iv::point(BigInt::zero());
                        for (j, &other) in args.iter().enumerate() {
                            if j != i {
                                others = others.add(&self.fwd(other, depth + 1));
                            }
                        }
                        self.bwd(arg, &refined.sub(&others), depth + 1)?;
                    }
                    Ok(())
                }
                "-" if args.len() == 1 => self.bwd(args[0], &refined.neg(), depth + 1),
                "-" if args.len() == 2 => {
                    // a - b ∈ refined  =>  a ∈ refined + b,  b ∈ a - refined.
                    let b_ivl = self.fwd(args[1], depth + 1);
                    self.bwd(args[0], &refined.add(&b_ivl), depth + 1)?;
                    let a_ivl = self.fwd(args[0], depth + 1);
                    self.bwd(args[1], &a_ivl.sub(&refined), depth + 1)
                }
                "*" => {
                    let (c, groups) = group_product_args(self.solver, args);
                    if c.is_zero() {
                        // Product is identically 0; nothing to invert.
                        return Ok(());
                    }
                    for (i, (child, mult)) in groups.iter().enumerate() {
                        // other = c * prod_{j != i} fwd(child_j)^mult_j
                        let mut other = Iv::point(c.clone());
                        for (j, (oc, om)) in groups.iter().enumerate() {
                            if j != i {
                                other = other.mul(&self.fwd(*oc, depth + 1).pow(*om));
                            }
                        }
                        // child^mult ∈ refined / other (when invertible).
                        let Some(pow_target) = refined.div_int(&other) else {
                            continue;
                        };
                        let Some(child_target) = pow_target.root_contract(*mult) else {
                            continue;
                        };
                        if child_target.is_empty() {
                            return Err(StopContraction);
                        }
                        self.bwd(*child, &child_target, depth + 1)?;
                    }
                    Ok(())
                }
                _ => Ok(()),
            },
            _ => Ok(()),
        }
    }

    /// Contract from one asserted atom. Unsupported shapes are skipped.
    fn contract_atom(&mut self, term: TermId, positive: bool) -> Result<(), StopContraction> {
        match self.solver.terms.get(term) {
            TermData::Not(inner) => self.contract_atom(*inner, !positive),
            TermData::App(Symbol::Named(name), args) if args.len() == 2 => {
                let (a, b) = (args[0], args[1]);
                // Only Int-sorted comparisons (strict-inequality tightening
                // below assumes integer-valued sides).
                if !matches!(self.solver.terms.sort(a), Sort::Int)
                    || !matches!(self.solver.terms.sort(b), Sort::Int)
                {
                    return Ok(());
                }
                let op = match (name.as_str(), positive) {
                    ("=", true) | ("distinct", false) => "=",
                    ("<", true) | (">=", false) => "<",
                    ("<=", true) | (">", false) => "<=",
                    (">", true) | ("<=", false) => ">",
                    (">=", true) | ("<", false) => ">=",
                    _ => return Ok(()),
                };
                let ia = self.fwd(a, 0);
                let ib = self.fwd(b, 0);
                match op {
                    "=" => {
                        let both = ia.intersect(&ib);
                        if both.is_empty() {
                            return Err(StopContraction);
                        }
                        self.bwd(a, &both, 0)?;
                        self.bwd(b, &both, 0)?;
                    }
                    "<" | "<=" => {
                        // a <= b - d, b >= a + d  with d = 1 for "<", 0 for "<=".
                        let d = BigInt::from(if op == "<" { 1 } else { 0 });
                        let a_hi = match &ib.hi {
                            Ep::Fin(h) => Ep::Fin(h - &d),
                            other => other.clone(),
                        };
                        let b_lo = match &ia.lo {
                            Ep::Fin(l) => Ep::Fin(l + &d),
                            other => other.clone(),
                        };
                        self.bwd(
                            a,
                            &Iv {
                                lo: Ep::NegInf,
                                hi: a_hi,
                            },
                            0,
                        )?;
                        self.bwd(
                            b,
                            &Iv {
                                lo: b_lo,
                                hi: Ep::PosInf,
                            },
                            0,
                        )?;
                    }
                    ">" | ">=" => {
                        let d = BigInt::from(if op == ">" { 1 } else { 0 });
                        let a_lo = match &ib.lo {
                            Ep::Fin(l) => Ep::Fin(l + &d),
                            other => other.clone(),
                        };
                        let b_hi = match &ia.hi {
                            Ep::Fin(h) => Ep::Fin(h - &d),
                            other => other.clone(),
                        };
                        self.bwd(
                            a,
                            &Iv {
                                lo: a_lo,
                                hi: Ep::PosInf,
                            },
                            0,
                        )?;
                        self.bwd(
                            b,
                            &Iv {
                                lo: Ep::NegInf,
                                hi: b_hi,
                            },
                            0,
                        )?;
                    }
                    _ => unreachable!(),
                }
                Ok(())
            }
            _ => Ok(()),
        }
    }
}

/// Split a product's argument list into (constant factor, [(child, mult)])
/// with the children grouped by TermId (so `x*x` is recognized as a square).
/// Order is deterministic (first-occurrence order of the argument list).
fn group_product_args(solver: &NiaSolver<'_>, args: &[TermId]) -> (BigInt, Vec<(TermId, usize)>) {
    let mut c = BigInt::one();
    let mut groups: Vec<(TermId, usize)> = Vec::new();
    for &arg in args {
        if let Some(k) = solver.terms.extract_integer_constant(arg) {
            c *= k;
        } else if let Some(entry) = groups.iter_mut().find(|(t, _)| *t == arg) {
            entry.1 += 1;
        } else {
            groups.push((arg, 1));
        }
    }
    (c, groups)
}

impl NiaSolver<'_> {
    /// Tighten `var_bounds` for the enumeration variables `vars` using
    /// interval contraction over the asserted atoms (#nia-interval-contract).
    ///
    /// PURELY a bounds tightener: never returns a verdict, never asserts
    /// anything into LIA. Every removed value is provably excluded by the
    /// asserted atoms, so the tightened box still contains every model —
    /// bounded enumeration's exhaustive UNSAT over the tightened box remains
    /// sound, and any SAT witness it finds is independently re-verified by
    /// exact substitution anyway.
    pub(crate) fn contract_enum_bounds(
        &self,
        vars: &[TermId],
        var_bounds: &mut HashMap<TermId, (Option<i64>, Option<i64>)>,
    ) {
        if self.asserted.len() > MAX_CONTRACT_ATOMS {
            return;
        }
        // Seed the working map from the incoming i64 bounds.
        let mut bounds: HashMap<TermId, Iv> = HashMap::default();
        for &v in vars {
            let (lo, hi) = var_bounds.get(&v).copied().unwrap_or((None, None));
            bounds.insert(
                v,
                Iv {
                    lo: lo.map(Ep::fin).unwrap_or(Ep::NegInf),
                    hi: hi.map(Ep::fin).unwrap_or(Ep::PosInf),
                },
            );
        }
        let mut ctr = Contractor {
            solver: self,
            bounds,
            changed: true,
        };
        for _round in 0..MAX_CONTRACT_ROUNDS {
            if !ctr.changed {
                break;
            }
            ctr.changed = false;
            let mut stopped = false;
            for &(term, positive) in &self.asserted {
                if ctr.contract_atom(term, positive).is_err() {
                    // Empty intersection (or an equivalent stop signal):
                    // keep tightenings applied so far (each one is
                    // independently sound) but stop deriving more. No
                    // verdict is drawn from emptiness here.
                    stopped = true;
                    break;
                }
            }
            if stopped {
                break;
            }
        }
        // Export: only ACCEPT contracted endpoints that fit i64 (otherwise
        // keep the original bound — sound, merely looser). By construction
        // (pure intersections) the contracted interval is a subset of the
        // seed, so this only ever tightens.
        for &v in vars {
            let Some(iv) = ctr.bounds.get(&v) else {
                continue;
            };
            let (old_lo, old_hi) = var_bounds.get(&v).copied().unwrap_or((None, None));
            let new_lo = match &iv.lo {
                Ep::Fin(n) => n.to_i64().or(old_lo),
                _ => old_lo,
            };
            let new_hi = match &iv.hi {
                Ep::Fin(n) => n.to_i64().or(old_hi),
                _ => old_hi,
            };
            var_bounds.insert(v, (new_lo, new_hi));
        }
        if self.debug {
            for &v in vars {
                safe_eprintln!(
                    "[NIA] interval-contract: {:?} -> {:?}",
                    v,
                    var_bounds.get(&v)
                );
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn fin(n: i64) -> Ep {
        Ep::fin(n)
    }

    fn iv(lo: i64, hi: i64) -> Iv {
        Iv {
            lo: fin(lo),
            hi: fin(hi),
        }
    }

    fn iv_lo(lo: i64) -> Iv {
        Iv {
            lo: fin(lo),
            hi: Ep::PosInf,
        }
    }

    fn iv_hi(hi: i64) -> Iv {
        Iv {
            lo: Ep::NegInf,
            hi: fin(hi),
        }
    }

    fn contains(i: &Iv, v: i64) -> bool {
        let v = Ep::fin(v);
        i.lo.cmp_ep(&v) != std::cmp::Ordering::Greater
            && i.hi.cmp_ep(&v) != std::cmp::Ordering::Less
    }

    #[test]
    fn test_add_neg_sub() {
        assert_eq!(iv(1, 2).add(&iv(10, 20)), iv(11, 22));
        assert_eq!(iv(1, 2).neg(), iv(-2, -1));
        assert_eq!(iv(1, 2).sub(&iv(10, 20)), iv(-19, -8));
        assert_eq!(iv_lo(3).add(&iv(1, 1)), iv_lo(4));
        assert_eq!(iv_hi(3).neg(), iv_lo(-3));
    }

    #[test]
    fn test_mul_basic() {
        assert_eq!(iv(2, 3).mul(&iv(4, 5)), iv(8, 15));
        assert_eq!(iv(-2, 3).mul(&iv(4, 5)), iv(-10, 15));
        assert_eq!(iv(-2, -1).mul(&iv(-3, -2)), iv(2, 6));
        // 0-width times unbounded.
        assert_eq!(
            Iv::point(BigInt::zero()).mul(&Iv::top()),
            Iv::point(BigInt::zero())
        );
        // [0,1] * (-inf, inf) = (-inf, inf)
        assert_eq!(iv(0, 1).mul(&Iv::top()), Iv::top());
        // [-1, 0] * [5, inf) = (-inf, 0]
        assert_eq!(iv(-1, 0).mul(&iv_lo(5)), iv_hi(0));
    }

    #[test]
    fn test_mul_exhaustive_small() {
        // Property: for all small finite intervals, interval product bounds
        // every pointwise product.
        for alo in -3i64..=3 {
            for ahi in alo..=3 {
                for blo in -3i64..=3 {
                    for bhi in blo..=3 {
                        let p = iv(alo, ahi).mul(&iv(blo, bhi));
                        for a in alo..=ahi {
                            for b in blo..=bhi {
                                assert!(
                                    contains(&p, a * b),
                                    "{a}*{b} not in {:?} (A=[{alo},{ahi}] B=[{blo},{bhi}])",
                                    p
                                );
                            }
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn test_pow_soundness_small() {
        for lo in -4i64..=4 {
            for hi in lo..=4 {
                for m in 1usize..=4 {
                    let p = iv(lo, hi).pow(m);
                    for s in lo..=hi {
                        let v = BigInt::from(s).pow(m as u32);
                        let v64 = v.to_i64().unwrap();
                        assert!(
                            contains(&p, v64),
                            "{s}^{m}={v64} not in {:?} ([{lo},{hi}])",
                            p
                        );
                    }
                }
            }
        }
    }

    #[test]
    fn test_pow_square_awareness() {
        // Straddling zero: square is [0, max^2], not [-a*b, ...].
        assert_eq!(iv(-3, 2).pow(2), iv(0, 9));
        // Unbounded var squared: [0, inf).
        assert_eq!(Iv::top().pow(2), iv_lo(0));
        // Odd power of unbounded stays top.
        assert_eq!(Iv::top().pow(3), Iv::top());
    }

    #[test]
    fn test_div_int_soundness_small() {
        // Property: q integer with q*o = n, n in N, o in D (sign-definite D)
        // implies q in N.div_int(D).
        for nlo in -6i64..=6 {
            for nhi in nlo..=6 {
                for dlo in -3i64..=3 {
                    for dhi in dlo..=3 {
                        let d = iv(dlo, dhi);
                        if !d.sign_definite_nonzero() {
                            assert!(iv(nlo, nhi).div_int(&d).is_none());
                            continue;
                        }
                        let q = iv(nlo, nhi).div_int(&d).unwrap();
                        for o in dlo..=dhi {
                            if o == 0 {
                                continue;
                            }
                            for n in nlo..=nhi {
                                if n % o == 0 {
                                    assert!(
                                        contains(&q, n / o),
                                        "{n}/{o} not in {:?} (N=[{nlo},{nhi}] D=[{dlo},{dhi}])",
                                        q
                                    );
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn test_div_int_infinite() {
        // [10, 20] / [2, inf) ⊇ (0, 10] -> integer [0, 10].
        let q = iv(10, 20).div_int(&iv_lo(2)).unwrap();
        assert_eq!(q, iv(0, 10));
        // (-inf, -8] / [2, 4] = (-inf, -2].
        let q = iv_hi(-8).div_int(&iv(2, 4)).unwrap();
        assert_eq!(q, iv_hi(-2));
        // [4, 8] / [-2, -1] = [-8, -2].
        let q = iv(4, 8).div_int(&iv(-2, -1)).unwrap();
        assert_eq!(q, iv(-8, -2));
    }

    #[test]
    fn test_roots() {
        assert_eq!(floor_nth_root(&BigInt::from(8320), 2), BigInt::from(91));
        assert_eq!(floor_nth_root(&BigInt::from(8281), 2), BigInt::from(91));
        assert_eq!(floor_nth_root(&BigInt::from(8280), 2), BigInt::from(90));
        assert_eq!(floor_nth_root(&BigInt::from(27), 3), BigInt::from(3));
        assert_eq!(floor_nth_root(&BigInt::from(-27), 3), BigInt::from(-3));
        assert_eq!(floor_nth_root(&BigInt::from(-28), 3), BigInt::from(-4));
        assert_eq!(floor_nth_root(&BigInt::from(-26), 3), BigInt::from(-3));
        assert_eq!(ceil_nth_root(&BigInt::from(26), 3), BigInt::from(3));
        assert_eq!(ceil_nth_root(&BigInt::from(27), 3), BigInt::from(3));
        assert_eq!(ceil_nth_root(&BigInt::from(28), 3), BigInt::from(4));
        assert_eq!(ceil_nth_root(&BigInt::from(-26), 3), BigInt::from(-2));
    }

    #[test]
    fn test_roots_exhaustive_small() {
        // floor_nth_root/ceil_nth_root exact on a small grid.
        for n in -64i64..=64 {
            for m in 1usize..=5 {
                if m % 2 == 0 && n < 0 {
                    continue;
                }
                let f = floor_nth_root(&BigInt::from(n), m);
                assert!(f.pow(m as u32) <= BigInt::from(n));
                assert!((&f + BigInt::one()).pow(m as u32) > BigInt::from(n));
                let c = ceil_nth_root(&BigInt::from(n), m);
                assert!(c.pow(m as u32) >= BigInt::from(n));
                // Minimality of the ceil root: `(c-1)^m < n`. Only meaningful
                // where `r^m` is monotone at `c-1` (odd m always; even m for
                // `c-1 >= 0`) — production uses ceil_nth_root for odd m only.
                if m % 2 == 1 || c >= BigInt::one() {
                    assert!((&c - BigInt::one()).pow(m as u32) < BigInt::from(n));
                }
            }
        }
    }

    #[test]
    fn test_root_contract_even() {
        // s^2 in [5100, 8320] -> s in [-91, 91].
        let s = iv(5100, 8320).root_contract(2).unwrap();
        assert_eq!(s, iv(-91, 91));
        // s^2 in [-5, -1] -> empty.
        let s = iv(-5, -1).root_contract(2).unwrap();
        assert!(s.is_empty());
        // No upper bound -> no contraction.
        assert!(iv_lo(4).root_contract(2).is_none());
    }

    #[test]
    fn test_root_contract_odd() {
        // s^3 in [-30, 100] -> s in [-3, 4].
        let s = iv(-30, 100).root_contract(3).unwrap();
        assert_eq!(s, iv(-3, 4));
        // Half-open passes through.
        let s = iv_hi(26).root_contract(3).unwrap();
        assert_eq!(s, iv_hi(2));
    }

    #[test]
    fn test_root_contract_soundness_small() {
        // Property: s in [-8, 8], s^m in target => s in contract(target, m).
        for tlo in -70i64..=70 {
            for thi in tlo..=70 {
                for m in 2usize..=3 {
                    let Some(c) = iv(tlo, thi).root_contract(m) else {
                        continue;
                    };
                    for s in -8i64..=8 {
                        let p = BigInt::from(s).pow(m as u32).to_i64().unwrap();
                        if p >= tlo && p <= thi {
                            assert!(
                                contains(&c, s),
                                "s={s} (s^{m}={p} in [{tlo},{thi}]) excluded by {:?}",
                                c
                            );
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn test_widening() {
        let huge = BigInt::from(2).pow(300);
        let w = Iv {
            lo: Ep::Fin(-huge.clone()),
            hi: Ep::Fin(huge),
        }
        .widened();
        assert_eq!(w, Iv::top());
    }
}
