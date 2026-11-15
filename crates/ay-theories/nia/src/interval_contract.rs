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

/// Above this many asserted atoms, contraction is restricted to atoms
/// mentioning a monomial factor/aux variable (keeps the pass cheap on
/// large industrial instances without disabling it outright;
/// #nia-contract-relevant-atoms).
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
    /// Atom currently being contracted (premise for derived bounds).
    current_atom: Option<(TermId, bool)>,
    /// Product-sum-derived endpoints with narrow premise literals:
    /// `(var, is_lower, premises)`. Exported so factor split can cite
    /// them instead of every asserted literal.
    derived: Vec<(TermId, bool, Vec<(TermId, bool)>)>,
    /// Subset re-derivation filter (#nia-contract-subset-refutes): when
    /// set, alias/definition/sign lookups over `solver.asserted` see
    /// only these literals, so an emptiness result is justified by the
    /// subset alone and the subset is a sound conflict.
    lit_filter: Option<std::collections::BTreeSet<(TermId, bool)>>,
    /// Eqdv definition terms per variable (#nia-contract-definitions):
    /// `var -> X` where `var <= X` and `var >= X` are both asserted
    /// true (filter-respecting). Precomputed once per contraction —
    /// depends only on `solver.asserted` and `lit_filter`, both
    /// fixed for the Contractor's lifetime — replacing an
    /// O(|asserted|) rescan inside every `linear_form` variable
    /// expansion (top contractor leaf on VeryMax trails).
    var_definitions: HashMap<TermId, TermId>,
    /// Memoized `linear_form` results (#nia-contract-form-cache).
    /// A form depends on the term DAG, `var_definitions` (both fixed
    /// for the Contractor's lifetime), and the point shortcut over
    /// `bounds` — so the cache is cleared at the one bounds-tightening
    /// site in `bwd`. Entries are depth-independent: a `Some` form is
    /// exact at any depth, and a `None` is only stored from a depth-0
    /// computation (monotone: less depth budget cannot succeed where
    /// depth 0 failed). Without this, premise scans
    /// (`sign_premise`/`point_premise` via `single_var_atom_bound`)
    /// recompute the same forms for every product-sum contraction,
    /// multiplied by every subset-shrink re-derivation.
    form_cache: std::cell::RefCell<HashMap<TermId, Option<std::rc::Rc<LinearForm>>>>,
    /// Monotone counter bumped whenever a computation takes the
    /// point-bound shortcut or consumes an impure cached form; a
    /// computation is pure iff the counter did not move during it.
    form_taint: std::cell::Cell<usize>,
    /// Memoized normalized atom difference forms (`form(lhs) -
    /// form(rhs)`, zero coefficients retained out), keyed by atom
    /// term (polarity only selects the comparison operator at use
    /// sites). Premise scans (`sign_premise`/`point_premise`) walk
    /// every asserted literal per derivation; without this each
    /// scan rebuilt every atom's merged coefficient map. Same
    /// purity/retain discipline as `form_cache`. (#nia-form-retain)
    atom_form_cache: std::cell::RefCell<HashMap<TermId, Option<std::rc::Rc<LinearForm>>>>,
}

/// An exact integer linear form: `term == sum(coeffs * var) + constant`.
struct LinearForm {
    coeffs: HashMap<TermId, BigInt>,
    constant: BigInt,
    /// True when computing this form never read `bounds` through the
    /// point shortcut (transitively), so the form is a pure term
    /// identity given the Contractor's fixed `var_definitions`.
    pure: bool,
}

impl Contractor<'_, '_> {
    fn lit_allowed(&self, term: TermId, positive: bool) -> bool {
        self.lit_filter
            .as_ref()
            .is_none_or(|set| set.contains(&(term, positive)))
    }

    /// One-pass build of `var_definitions`, byte-identical to the
    /// per-variable scan it replaces: per variable, upper/lower
    /// candidate X terms in asserted order, keeping the first upper
    /// X that also appears as a lower X (the `a == b` self-atom
    /// contributes only from the args[0] perspective, matching the
    /// original match-arm priority).
    fn build_var_definitions(
        solver: &NiaSolver<'_>,
        lit_filter: &Option<std::collections::BTreeSet<(TermId, bool)>>,
    ) -> HashMap<TermId, TermId> {
        let allowed = |term: TermId, positive: bool| {
            lit_filter
                .as_ref()
                .is_none_or(|set| set.contains(&(term, positive)))
        };
        let mut upper: HashMap<TermId, Vec<TermId>> = HashMap::default();
        let mut lower: HashMap<TermId, Vec<TermId>> = HashMap::default();
        for &(term, positive) in &solver.asserted {
            if !positive || !allowed(term, positive) {
                continue;
            }
            let TermData::App(Symbol::Named(name), args) = solver.terms.get(term) else {
                continue;
            };
            if args.len() != 2 {
                continue;
            }
            let (a, b) = (args[0], args[1]);
            if a == b {
                // Self-atom: the original match tries the upper arm
                // group first for both ops, so only an upper entry.
                if matches!(name.as_str(), "<=" | ">=") {
                    upper.entry(a).or_default().push(b);
                }
                continue;
            }
            match name.as_str() {
                "<=" => {
                    upper.entry(a).or_default().push(b);
                    lower.entry(b).or_default().push(a);
                }
                ">=" => {
                    lower.entry(a).or_default().push(b);
                    upper.entry(b).or_default().push(a);
                }
                _ => {}
            }
        }
        let mut definitions = HashMap::default();
        for (var, uppers) in &upper {
            if let Some(lowers) = lower.get(var) {
                if let Some(def) = uppers.iter().find(|x| lowers.contains(x)) {
                    definitions.insert(*var, *def);
                }
            }
        }
        definitions
    }

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
                    // Forms read bounds through the point shortcut.
                    // Retain pure forms not mentioning `term`: their
                    // recomputation cannot take a new shortcut (every
                    // Var leaf was either pinned, tainting purity, or
                    // appears as a coefficient), so it is identical.
                    // `None` entries and entries mentioning `term`
                    // drop, preserving pin-makes-product-linear
                    // precision. (#nia-form-retain)
                    self.form_cache.borrow_mut().retain(|_, entry| {
                        matches!(entry, Some(form) if form.pure && !form.coeffs.contains_key(&term))
                    });
                    self.atom_form_cache.borrow_mut().retain(|_, entry| {
                        matches!(entry, Some(form) if form.pure && !form.coeffs.contains_key(&term))
                    });
                }
                Ok(())
            }
            TermData::App(Symbol::Named(name), args) => match name.as_str() {
                "+" => {
                    self.contract_product_sum(args, &refined, depth)?;
                    self.contract_product_sum_linear(args, &refined, depth)?;
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

    /// Exact integer linear form of `term`: `(coeffs, constant)` with
    /// `term == sum(coeff * var) + constant`, or `None` for shapes outside
    /// `+`/`-`/constant-scaled products.
    fn linear_form(&self, term: TermId, depth: usize) -> Option<std::rc::Rc<LinearForm>> {
        if depth > MAX_CONTRACT_DEPTH {
            return None;
        }
        if let Some(hit) = self.form_cache.borrow().get(&term).cloned() {
            if let Some(form) = &hit {
                if !form.pure {
                    self.form_taint.set(self.form_taint.get() + 1);
                }
            }
            return hit;
        }
        let taint0 = self.form_taint.get();
        let computed = self.linear_form_compute(term, depth);
        let result = computed.map(|(coeffs, constant)| {
            std::rc::Rc::new(LinearForm {
                coeffs,
                constant,
                pure: self.form_taint.get() == taint0,
            })
        });
        // `Some` is exact at any depth; `None` is only monotone-safe
        // to reuse when computed with the full depth budget.
        if result.is_some() || depth == 0 {
            self.form_cache.borrow_mut().insert(term, result.clone());
        }
        if let Some(form) = &result {
            if !form.pure {
                // Consuming an impure form taints any enclosing
                // computation (already counted via taint0 delta for
                // the direct caller, but a hit path needs the bump
                // above; keep symmetric for nested computes).
                self.form_taint.set(self.form_taint.get() + 1);
            }
        }
        result
    }

    fn linear_form_compute(
        &self,
        term: TermId,
        depth: usize,
    ) -> Option<(HashMap<TermId, BigInt>, BigInt)> {
        match self.solver.terms.get(term) {
            TermData::Var(_, _) => {
                // An eqdv-style difference variable (executor
                // preprocessing replaces a nested equality atom by
                // `d = rhs` with `d` a fresh var and the definition
                // asserted as a `<=`/`>=` pair): expand to its
                // definition so alias detection sees the real equality.
                // This must precede the point-bound shortcut below: an
                // asserted `(= 0 d)` also pins `d` to the point 0 in
                // LIA, and returning the constant would erase exactly
                // the equality being recovered.
                if let Some(form) = self.var_definition_form(term, depth) {
                    return Some((form.coeffs.clone(), form.constant.clone()));
                }
                // A variable the contractor has already pinned to a
                // point interval is a constant for form purposes: this
                // keeps `(* a v)` linear when an asserted `a = 1` was
                // not substituted into the term DAG (e.g. the fixing
                // assertion comes last in the file), so alias detection
                // still sees the equality as `u = v + d`.
                if let Some(iv) = self.bounds.get(&term) {
                    if let (Ep::Fin(lo), Ep::Fin(hi)) = (&iv.lo, &iv.hi) {
                        if lo == hi {
                            self.form_taint.set(self.form_taint.get() + 1);
                            return Some((HashMap::default(), lo.clone()));
                        }
                    }
                }
                let mut coeffs = HashMap::default();
                coeffs.insert(term, BigInt::one());
                Some((coeffs, BigInt::zero()))
            }
            TermData::Const(Constant::Int(n)) => Some((HashMap::default(), n.clone())),
            TermData::Const(Constant::Rational(r)) if r.0.denom().is_one() => {
                Some((HashMap::default(), r.0.numer().clone()))
            }
            TermData::App(Symbol::Named(name), args) => match name.as_str() {
                "+" => {
                    let mut coeffs: HashMap<TermId, BigInt> = HashMap::default();
                    let mut constant = BigInt::zero();
                    for &arg in args {
                        let f = self.linear_form(arg, depth + 1)?;
                        for (v, coeff) in &f.coeffs {
                            *coeffs.entry(*v).or_insert_with(BigInt::zero) += coeff;
                        }
                        constant += &f.constant;
                    }
                    Some((coeffs, constant))
                }
                "-" if args.len() == 1 => {
                    let f = self.linear_form(args[0], depth + 1)?;
                    Some((
                        f.coeffs
                            .iter()
                            .map(|(v, coeff)| (*v, -coeff.clone()))
                            .collect(),
                        -f.constant.clone(),
                    ))
                }
                "-" if args.len() == 2 => {
                    let f0 = self.linear_form(args[0], depth + 1)?;
                    let mut coeffs = f0.coeffs.clone();
                    let mut constant = f0.constant.clone();
                    let f1 = self.linear_form(args[1], depth + 1)?;
                    for (v, coeff) in &f1.coeffs {
                        *coeffs.entry(*v).or_insert_with(BigInt::zero) -= coeff;
                    }
                    constant -= &f1.constant;
                    Some((coeffs, constant))
                }
                "*" => self.linear_form_mul(args, depth),
                _ => None,
            },
            _ => None,
        }
    }

    /// Linear form of a product: only constant scaling stays linear.
    fn linear_form_mul(
        &self,
        args: &[TermId],
        depth: usize,
    ) -> Option<(HashMap<TermId, BigInt>, BigInt)> {
        let mut scale: Option<BigInt> = None;
        let mut form: Option<(HashMap<TermId, BigInt>, BigInt)> = None;
        for &arg in args {
            let f = self.linear_form(arg, depth + 1)?;
            if f.coeffs.is_empty() {
                scale = Some(match scale {
                    Some(s) => s * &f.constant,
                    None => f.constant.clone(),
                });
            } else if form.is_none() {
                form = Some((f.coeffs.clone(), f.constant.clone()));
            } else {
                return None;
            }
        }
        let s = scale.unwrap_or_else(BigInt::one);
        match form {
            Some((c, k)) => Some((
                c.into_iter().map(|(v, coeff)| (v, coeff * &s)).collect(),
                k * &s,
            )),
            None => Some((HashMap::default(), s)),
        }
    }

    /// Definition of an auxiliary difference variable: asserted atoms
    /// `var <= X` and `var >= X` (either argument order) with the same
    /// `X` term, both true, force `var = X`; returns `X`'s linear form.
    fn var_definition_form(&self, var: TermId, depth: usize) -> Option<std::rc::Rc<LinearForm>> {
        // #nia-contract-definitions: definition terms are
        // precomputed in `build_var_definitions` (identical
        // selection); only the expansion stays per call because it
        // reads the tightening bounds.
        let def = self.var_definitions.get(&var)?;
        self.linear_form(*def, depth + 1)
    }

    /// Whether an asserted equality atom forces `u == v`: its normalized
    /// linear form is `k*u - k*v = 0` for some nonzero integer `k`.
    fn vars_asserted_equal(&self, u: TermId, v: TermId) -> bool {
        self.vars_asserted_equal_premise(u, v).is_some()
    }

    /// As [`Self::vars_asserted_equal`], returning the justifying
    /// literal: `Some(None)` for the same variable, `Some(Some(lit))`
    /// via an asserted equality atom, `None` when not equal.
    fn vars_asserted_equal_premise(&self, u: TermId, v: TermId) -> Option<Option<(TermId, bool)>> {
        if u == v {
            return Some(None);
        }
        for &(term, positive) in &self.solver.asserted {
            if !self.lit_allowed(term, positive) {
                continue;
            }
            let TermData::App(Symbol::Named(name), args) = self.solver.terms.get(term) else {
                continue;
            };
            let is_equality =
                (name.as_str() == "=" && positive) || (name.as_str() == "distinct" && !positive);
            if !is_equality || args.len() != 2 {
                continue;
            }
            let _ = args;
            let Some(diff) = self.atom_diff_form(term) else {
                continue;
            };
            if !diff.constant.is_zero() {
                continue;
            }
            let coeffs = &diff.coeffs;
            if coeffs.len() == 2 {
                if let (Some(cu), Some(cv)) = (coeffs.get(&u), coeffs.get(&v)) {
                    if !cu.is_zero() && cu == &-cv.clone() {
                        return Some(Some((term, positive)));
                    }
                }
            }
        }
        None
    }

    /// Normalized comparison operator of an asserted atom, mirroring
    /// `contract_atom`'s polarity handling.
    fn comparison_op(name: &str, positive: bool) -> Option<&'static str> {
        match (name, positive) {
            ("=", true) | ("distinct", false) => Some("="),
            ("<", true) | (">=", false) => Some("<"),
            ("<=", true) | (">", false) => Some("<="),
            (">", true) | ("<=", false) => Some(">"),
            (">=", true) | ("<", false) => Some(">="),
            _ => None,
        }
    }

    /// Normalized difference form of a binary atom: `form(lhs) -
    /// form(rhs)` with zero coefficients removed, so the atom reads
    /// `sum(coeffs * var) + constant (op) 0` for its normalized
    /// comparison operator. Memoized in `atom_form_cache`.
    fn atom_diff_form(&self, term: TermId) -> Option<std::rc::Rc<LinearForm>> {
        if let Some(hit) = self.atom_form_cache.borrow().get(&term).cloned() {
            if let Some(form) = &hit {
                if !form.pure {
                    self.form_taint.set(self.form_taint.get() + 1);
                }
            }
            return hit;
        }
        let result = (|| {
            let TermData::App(Symbol::Named(_), args) = self.solver.terms.get(term) else {
                return None;
            };
            if args.len() != 2 {
                return None;
            }
            let lf = self.linear_form(args[0], 0)?;
            let rf = self.linear_form(args[1], 0)?;
            let mut coeffs = lf.coeffs.clone();
            for (v, coeff) in &rf.coeffs {
                *coeffs.entry(*v).or_insert_with(BigInt::zero) -= coeff;
            }
            coeffs.retain(|_, coeff| !coeff.is_zero());
            Some(std::rc::Rc::new(LinearForm {
                coeffs,
                constant: &lf.constant - &rf.constant,
                pure: lf.pure && rf.pure,
            }))
        })();
        self.atom_form_cache
            .borrow_mut()
            .insert(term, result.clone());
        if let Some(form) = &result {
            if !form.pure {
                self.form_taint.set(self.form_taint.get() + 1);
            }
        }
        result
    }

    /// Implied integer bound `(lo, hi)` on `var` from one asserted
    /// comparison atom whose normalized form is a single variable with
    /// coefficient `±1`; `None` outside that shape.
    fn single_var_atom_bound(
        &self,
        term: TermId,
        positive: bool,
        var: TermId,
    ) -> Option<(Option<BigInt>, Option<BigInt>)> {
        let TermData::App(Symbol::Named(name), args) = self.solver.terms.get(term) else {
            return None;
        };
        if args.len() != 2 {
            return None;
        }
        let op = Self::comparison_op(name.as_str(), positive)?;
        let _ = args;
        let diff = self.atom_diff_form(term)?;
        if diff.coeffs.len() != 1 {
            return None;
        }
        let k = diff.coeffs.get(&var)?.clone();
        if !k.is_one() && k != -BigInt::one() {
            return None;
        }
        // Form: k*var + c (op) 0; solve for var.
        let c = diff.constant.clone();
        let neg_c = -&c;
        // var bound when k == 1: var (op) -c; k == -1 flips the op.
        let eff = if k.is_one() {
            op
        } else {
            match op {
                "<" => ">",
                "<=" => ">=",
                ">" => "<",
                ">=" => "<=",
                other => other,
            }
        };
        let one = BigInt::one();
        Some(match eff {
            "=" => (Some(neg_c.clone()), Some(neg_c)),
            ">=" => (Some(neg_c), None),
            ">" => (Some(neg_c + &one), None),
            "<=" => (None, Some(neg_c)),
            "<" => (None, Some(neg_c - &one)),
            _ => return None,
        })
    }

    /// Asserted literal implying `var >= 0` (`want_nonneg`) or
    /// `var <= 0`, for product-sum provenance.
    fn sign_premise(&self, var: TermId, want_nonneg: bool) -> Option<(TermId, bool)> {
        for &(term, positive) in &self.solver.asserted {
            if !self.lit_allowed(term, positive) {
                continue;
            }
            let Some((lo, hi)) = self.single_var_atom_bound(term, positive, var) else {
                continue;
            };
            let ok = if want_nonneg {
                lo.is_some_and(|b| !b.is_negative())
            } else {
                hi.is_some_and(|b| !b.is_positive())
            };
            if ok {
                return Some((term, positive));
            }
        }
        None
    }

    /// Asserted literal implying `var == p`, for product-sum provenance.
    fn point_premise(&self, var: TermId, p: &BigInt) -> Option<(TermId, bool)> {
        for &(term, positive) in &self.solver.asserted {
            if !self.lit_allowed(term, positive) {
                continue;
            }
            let Some((lo, hi)) = self.single_var_atom_bound(term, positive, var) else {
                continue;
            };
            if lo.as_ref() == Some(p) && hi.as_ref() == Some(p) {
                return Some((term, positive));
            }
        }
        None
    }

    /// `term` as `k * var` (a lone variable counts as `k = 1`).
    fn scaled_var(&self, term: TermId) -> Option<(BigInt, TermId)> {
        match self.solver.terms.get(term) {
            TermData::Var(_, _) => Some((BigInt::one(), term)),
            TermData::App(Symbol::Named(name), args) if name.as_str() == "*" => {
                let (c, groups) = group_product_args(self.solver, args);
                match groups.as_slice() {
                    [(child, 1)]
                        if matches!(self.solver.terms.get(*child), TermData::Var(_, _)) =>
                    {
                        Some((c, *child))
                    }
                    _ => None,
                }
            }
            _ => None,
        }
    }

    /// `term` as an unscaled binary product of two variables.
    fn binary_var_product(&self, term: TermId) -> Option<(TermId, TermId)> {
        match self.solver.terms.get(term) {
            TermData::App(Symbol::Named(name), args) if name.as_str() == "*" => {
                let (c, groups) = group_product_args(self.solver, args);
                if !c.is_one() {
                    return None;
                }
                match groups.as_slice() {
                    [(a, 1), (b, 1)]
                        if matches!(self.solver.terms.get(*a), TermData::Var(_, _))
                            && matches!(self.solver.terms.get(*b), TermData::Var(_, _)) =>
                    {
                        Some((*a, *b))
                    }
                    _ => None,
                }
            }
            _ => None,
        }
    }

    /// Product-sum threshold rule (#nia-product-sum-bound): a sum child
    /// pair `k*u` and `c*v` with `u == v` asserted (or the same variable)
    /// is `(k + c) * v`. When the sum's remaining children leave
    /// `(k + c) * v ∈ t` with a finite endpoint past zero and `v` is
    /// sign-definite, `k + c` must share that sign strictly: e.g.
    /// `t.lo >= 1` and `v >= 0` force `c >= 1 - k` (otherwise
    /// `(k + c) * v <= 0`). This is the correlation plain HC4 loses
    /// (it treats `k*u` and `c*v` independently), and it is what bounds
    /// the shared Farkas factor below (`(6 + C) * v > 1` gives
    /// `C >= -5`) so bounded factor split can enumerate it.
    fn contract_product_sum(
        &mut self,
        args: &[TermId],
        refined: &Iv,
        depth: usize,
    ) -> Result<(), StopContraction> {
        for (i, &lin) in args.iter().enumerate() {
            let Some((k, u)) = self.scaled_var(lin) else {
                continue;
            };
            for (j, &prod) in args.iter().enumerate() {
                if i == j {
                    continue;
                }
                let Some((f1, f2)) = self.binary_var_product(prod) else {
                    continue;
                };
                for (v, c) in [(f1, f2), (f2, f1)] {
                    let Some(alias_lit) = self.vars_asserted_equal_premise(u, v) else {
                        continue;
                    };
                    let v_iv = self.bounds.get(&v).cloned().unwrap_or_else(Iv::top);
                    let v_nonneg = matches!(&v_iv.lo, Ep::Fin(n) if !n.is_negative());
                    let v_nonpos = matches!(&v_iv.hi, Ep::Fin(n) if !n.is_positive());
                    if !v_nonneg && !v_nonpos {
                        continue;
                    }
                    let mut rest = Iv::point(BigInt::zero());
                    let mut premises = self.base_premises(alias_lit, v, v_nonneg);
                    for (m, &other) in args.iter().enumerate() {
                        if m != i && m != j {
                            rest = rest.add(&self.fwd(other, depth + 1));
                            if let Some(p) = &mut premises {
                                match self.child_point_premise(other) {
                                    Some(lits) => p.extend(lits),
                                    None => premises = None,
                                }
                            }
                        }
                    }
                    let t = refined.sub(&rest);
                    self.apply_product_threshold(c, &k, &v_iv, &t, depth, premises)?;
                }
            }
        }
        Ok(())
    }

    /// Narrow premises shared by both product-sum rules: the atom
    /// being contracted, the alias equality (when via an atom), and a
    /// sign literal for `w`. `None` when any piece is unavailable
    /// (callers then record no derivation; factor split falls back to
    /// citing every asserted literal).
    fn base_premises(
        &self,
        alias_lit: Option<(TermId, bool)>,
        w: TermId,
        w_nonneg: bool,
    ) -> Option<Vec<(TermId, bool)>> {
        let mut premises = vec![self.current_atom?];
        if let Some(lit) = alias_lit {
            premises.push(lit);
        }
        premises.push(self.sign_premise(w, w_nonneg)?);
        Some(premises)
    }

    /// Premise literals for one rest child of a product-sum: constants
    /// need none; a point-bounded variable needs its fixing literal;
    /// anything else has no narrow provenance.
    fn child_point_premise(&self, other: TermId) -> Option<Vec<(TermId, bool)>> {
        if self.solver.terms.extract_integer_constant(other).is_some() {
            return Some(Vec::new());
        }
        if matches!(self.solver.terms.get(other), TermData::Var(_, _)) {
            if let Some(iv) = self.bounds.get(&other) {
                if let (Ep::Fin(lo), Ep::Fin(hi)) = (&iv.lo, &iv.hi) {
                    if lo == hi {
                        return self.point_premise(other, lo).map(|lit| vec![lit]);
                    }
                }
            }
        }
        None
    }

    /// Integer sign threshold for `(k + f) * w ∈ t` with `w`
    /// sign-definite: a finite endpoint of `t` past zero forces
    /// `k + f` to that side strictly (e.g. `t.lo >= 1` and `w >= 0`
    /// give `f >= 1 - k`, since `k + f <= 0` would make the product
    /// `<= 0`). Tightens `f` in place.
    fn apply_product_threshold(
        &mut self,
        f: TermId,
        k: &BigInt,
        w_iv: &Iv,
        t: &Iv,
        depth: usize,
        premises: Option<Vec<(TermId, bool)>>,
    ) -> Result<(), StopContraction> {
        let w_nonneg = matches!(&w_iv.lo, Ep::Fin(n) if !n.is_negative());
        let w_nonpos = matches!(&w_iv.hi, Ep::Fin(n) if !n.is_positive());
        if !w_nonneg && !w_nonpos {
            return Ok(());
        }
        let cur = self.bounds.get(&f).cloned().unwrap_or_else(Iv::top);
        let one = BigInt::one();
        if let Ep::Fin(tl) = &t.lo {
            if *tl >= one {
                let (bound, is_lower) = if w_nonneg {
                    (
                        Iv {
                            lo: Ep::Fin(&one - k),
                            hi: Ep::PosInf,
                        },
                        true,
                    )
                } else {
                    (
                        Iv {
                            lo: Ep::NegInf,
                            hi: Ep::Fin(-&one - k),
                        },
                        false,
                    )
                };
                self.record_derived(f, is_lower, &bound, &cur, &premises);
                self.bwd(f, &bound, depth + 1)?;
            }
        }
        if let Ep::Fin(th) = &t.hi {
            if *th <= -one.clone() {
                let (bound, is_lower) = if w_nonneg {
                    (
                        Iv {
                            lo: Ep::NegInf,
                            hi: Ep::Fin(-&one - k),
                        },
                        false,
                    )
                } else {
                    (
                        Iv {
                            lo: Ep::Fin(&one - k),
                            hi: Ep::PosInf,
                        },
                        true,
                    )
                };
                self.record_derived(f, is_lower, &bound, &cur, &premises);
                self.bwd(f, &bound, depth + 1)?;
            }
        }
        Ok(())
    }

    /// Record a product-sum derivation when `bound` actually tightens
    /// `f` past `cur` and narrow premises are available.
    fn record_derived(
        &mut self,
        f: TermId,
        is_lower: bool,
        bound: &Iv,
        cur: &Iv,
        premises: &Option<Vec<(TermId, bool)>>,
    ) {
        let Some(premises) = premises else {
            return;
        };
        let tightens = if is_lower {
            match (&bound.lo, &cur.lo) {
                (Ep::Fin(n), Ep::Fin(c)) => n > c,
                (Ep::Fin(_), Ep::NegInf) => true,
                _ => false,
            }
        } else {
            match (&bound.hi, &cur.hi) {
                (Ep::Fin(n), Ep::Fin(c)) => n < c,
                (Ep::Fin(_), Ep::PosInf) => true,
                _ => false,
            }
        };
        if tightens {
            self.derived.push((f, is_lower, premises.clone()));
        }
    }

    /// Asserted offset equality `u = v + d`: an asserted equality atom
    /// whose normalized linear form is `k0*u - k0*v + c0 = 0` with
    /// `k0 != 0` and `k0 | c0`, giving `d = -c0 / k0`.
    fn vars_asserted_offset(&self, u: TermId, v: TermId) -> Option<BigInt> {
        self.vars_asserted_offset_premise(u, v).map(|(d, _)| d)
    }

    /// As [`Self::vars_asserted_offset`], also returning the justifying
    /// literal (`None` for the same variable).
    fn vars_asserted_offset_premise(
        &self,
        u: TermId,
        v: TermId,
    ) -> Option<(BigInt, Option<(TermId, bool)>)> {
        if u == v {
            return Some((BigInt::zero(), None));
        }
        for &(term, positive) in &self.solver.asserted {
            if !self.lit_allowed(term, positive) {
                continue;
            }
            let TermData::App(Symbol::Named(name), args) = self.solver.terms.get(term) else {
                continue;
            };
            let is_equality =
                (name.as_str() == "=" && positive) || (name.as_str() == "distinct" && !positive);
            if !is_equality || args.len() != 2 {
                continue;
            }
            let _ = args;
            let Some(diff) = self.atom_diff_form(term) else {
                continue;
            };
            let coeffs = &diff.coeffs;
            if coeffs.len() != 2 {
                continue;
            }
            let (Some(cu), Some(cv)) = (coeffs.get(&u), coeffs.get(&v)) else {
                continue;
            };
            if cu.is_zero() || *cu != -cv.clone() {
                continue;
            }
            let c0 = diff.constant.clone();
            if (&c0 % cu).is_zero() {
                return Some((-(&c0 / cu), Some((term, positive))));
            }
        }
        None
    }

    /// Interval range of a linear form's remainder under current bounds.
    fn linear_form_interval(&self, coeffs: &HashMap<TermId, BigInt>, constant: &BigInt) -> Iv {
        let mut acc = Iv::point(constant.clone());
        for (var, coeff) in coeffs {
            let var_iv = self.bounds.get(var).cloned().unwrap_or_else(Iv::top);
            acc = acc.add(&Iv::point(coeff.clone()).mul(&var_iv));
        }
        acc
    }

    /// Linear-form product-sum rule (#nia-product-sum-bound, offset
    /// form): for a monomial child `f * v` whose sibling sum children
    /// are all linear with joint form `L`, substitute an asserted
    /// offset equality `u = v + d` for a variable `u` in `L`
    /// (coefficient `k`, with any `v` coefficient folded in). The sum
    /// is `(k + f) * u + (l - d) * f + R`, where `l` is `f`'s own
    /// linear coefficient in `L` and `R` the remaining linear part.
    /// When `l == d` the stray `f` term cancels — the A1 Farkas shape
    /// (`6u + Cv - 1 - (C + 3a)` with `u = v - 1` becomes
    /// `(6 + C) * u - 2` at `a = 1`) — and the sign threshold on
    /// `(k + f) * u ∈ refined - R` bounds `f`.
    fn contract_product_sum_linear(
        &mut self,
        args: &[TermId],
        refined: &Iv,
        depth: usize,
    ) -> Result<(), StopContraction> {
        for (j, &prod) in args.iter().enumerate() {
            let Some((f1, f2)) = self.binary_var_product(prod) else {
                continue;
            };
            // Joint linear form of every other child; bail on any
            // nonlinear sibling (the child-pair rule covers that case).
            let mut coeffs: HashMap<TermId, BigInt> = HashMap::default();
            let mut constant = BigInt::zero();
            let mut linear = true;
            for (i, &other) in args.iter().enumerate() {
                if i == j {
                    continue;
                }
                let Some(f) = self.linear_form(other, depth + 1) else {
                    linear = false;
                    break;
                };
                for (var, coeff) in &f.coeffs {
                    *coeffs.entry(*var).or_insert_with(BigInt::zero) += coeff;
                }
                constant += &f.constant;
            }
            if !linear {
                continue;
            }
            coeffs.retain(|_, coeff| !coeff.is_zero());
            for (v, f) in [(f1, f2), (f2, f1)] {
                let l = coeffs.get(&f).cloned().unwrap_or_else(BigInt::zero);
                let kv = coeffs.get(&v).cloned().unwrap_or_else(BigInt::zero);
                // Candidate alias targets: v itself (d = 0) and every
                // other variable in the linear form.
                let mut us: Vec<TermId> = coeffs.keys().copied().collect();
                if !us.contains(&v) {
                    us.push(v);
                }
                for u in us {
                    if u == f {
                        continue;
                    }
                    let Some((d, alias_lit)) = self.vars_asserted_offset_premise(u, v) else {
                        continue;
                    };
                    if l != d {
                        continue;
                    }
                    let ku = coeffs.get(&u).cloned().unwrap_or_else(BigInt::zero);
                    let k_total = if u == v { kv.clone() } else { &ku + &kv };
                    if k_total.is_zero() && u != v {
                        continue;
                    }
                    // R: L with u, v, f removed; substituting v = u - d
                    // in kv*v contributes the constant -kv*d.
                    let mut rest_coeffs = coeffs.clone();
                    rest_coeffs.remove(&u);
                    rest_coeffs.remove(&v);
                    rest_coeffs.remove(&f);
                    let rest_const = &constant - &(&kv * &d);
                    let rest_iv = self.linear_form_interval(&rest_coeffs, &rest_const);
                    let t = refined.sub(&rest_iv);
                    let u_iv = self.bounds.get(&u).cloned().unwrap_or_else(Iv::top);
                    let u_nonneg = matches!(&u_iv.lo, Ep::Fin(n) if !n.is_negative());
                    let mut premises = self.base_premises(alias_lit, u, u_nonneg);
                    if let Some(p) = &mut premises {
                        for var in rest_coeffs.keys() {
                            match self.child_point_premise(*var) {
                                Some(lits) => p.extend(lits),
                                None => {
                                    premises = None;
                                    break;
                                }
                            }
                        }
                    }
                    self.apply_product_threshold(f, &k_total, &u_iv, &t, depth, premises)?;
                }
            }
        }
        Ok(())
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
    /// Seed `bounds` with justified LIA bounds for every Int variable
    /// occurring in the asserted atoms (#nia-product-sum-bound):
    /// alias/definition reasoning inside the contractor needs
    /// point-bounded factors (e.g. an asserted `a = 1` whose effect
    /// reaches LIA as a direct bound) even when they are not
    /// enumeration variables. Extra seeds only ever tighten the
    /// contractor's internal map; exported bounds still cover exactly
    /// the requested `vars`.
    fn seed_extra_atom_vars(&self, bounds: &mut HashMap<TermId, Iv>) {
        let mut extra: Vec<TermId> = Vec::new();
        for &(term, _) in &self.asserted {
            self.collect_int_var_leaves(term, &mut extra);
            if extra.len() >= 256 {
                break;
            }
        }
        for v in extra {
            if bounds.contains_key(&v) {
                continue;
            }
            let (lo, hi) = match self.get_integer_bounds(v) {
                Some((lo, hi)) => (Some(lo), Some(hi)),
                None => self.get_partial_integer_bounds(v),
            };
            if lo.is_some() || hi.is_some() {
                bounds.insert(
                    v,
                    Iv {
                        lo: lo.map(Ep::fin).unwrap_or(Ep::NegInf),
                        hi: hi.map(Ep::fin).unwrap_or(Ep::PosInf),
                    },
                );
            }
        }
    }

    /// #nia-contract-relevant-atoms: above MAX_CONTRACT_ATOMS asserted
    /// atoms the contractor used to return empty, which on searched
    /// trails (VeryMax: 103 atoms asserted to the theory) left the
    /// shared monomial factor with no contracted bounds at all and
    /// factor split with no candidate — while the same components
    /// refute as ground files under the cap. Above the threshold,
    /// contract only atoms whose term mentions a monomial factor or
    /// aux variable: an atom touching none of them cannot tighten a
    /// tracked bound in one step (multi-step chains through such
    /// atoms are the only loss, and only where today there is no
    /// contraction at all). At or below the threshold behavior is
    /// unchanged (every atom contracted), signaled by `None`.
    fn contract_relevant_set(&self, vars: &[TermId]) -> Option<std::collections::BTreeSet<TermId>> {
        if self.asserted.len() <= MAX_CONTRACT_ATOMS {
            return None;
        }
        let mut set: std::collections::BTreeSet<TermId> = Default::default();
        set.extend(vars.iter().copied());
        set.extend(self.monomials.values().map(|m| m.aux_var));
        Some(set)
    }

    /// Returns `(derived endpoint premises, refuted)`. In the
    /// relevant-filtered mode only, `refuted` is set when some asserted
    /// atom's contraction produced an empty interval: every tightening
    /// is an interval consequence of asserted literals over
    /// verdict-grade seed bounds, so emptiness refutes the asserted
    /// set as a whole (#nia-contract-empty-refutes).
    pub(crate) fn contract_enum_bounds(
        &self,
        vars: &[TermId],
        var_bounds: &mut HashMap<TermId, (Option<i64>, Option<i64>)>,
    ) -> (HashMap<(TermId, bool), Vec<(TermId, bool)>>, bool) {
        let relevant = self.contract_relevant_set(vars);
        let atom_relevant = |solver: &Self, term: TermId| -> bool {
            let Some(set) = &relevant else { return true };
            solver.atom_mentions_any(term, set)
        };
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
        self.seed_extra_atom_vars(&mut bounds);
        let mut ctr = Contractor {
            solver: self,
            bounds,
            changed: true,
            current_atom: None,
            derived: Vec::new(),
            lit_filter: None,
            var_definitions: Contractor::build_var_definitions(self, &None),
            form_cache: std::cell::RefCell::new(HashMap::default()),
            form_taint: std::cell::Cell::new(0),
            atom_form_cache: std::cell::RefCell::new(HashMap::default()),
        };
        let mut refuted = false;
        for _round in 0..MAX_CONTRACT_ROUNDS {
            if !ctr.changed {
                break;
            }
            ctr.changed = false;
            let mut stopped = false;
            for &(term, positive) in &self.asserted {
                if !atom_relevant(self, term) {
                    continue;
                }
                ctr.current_atom = Some((term, positive));
                if ctr.contract_atom(term, positive).is_err() {
                    // Empty intersection: keep tightenings applied so far
                    // (each independently sound) but stop deriving more.
                    // In the relevant-filtered mode (> MAX_CONTRACT_ATOMS,
                    // where contraction was previously disabled outright)
                    // this also refutes the asserted set; below the
                    // threshold the historical contract stands — no
                    // verdict is drawn from emptiness and exhaustive
                    // enumeration remains the decider (pinned by the
                    // Phase-2 isolation tests in bounded_enum).
                    if relevant.is_some() {
                        refuted = true;
                    }
                    stopped = true;
                    break;
                }
            }
            if stopped {
                break;
            }
        }
        Self::export_contracted_bounds(&ctr, vars, var_bounds);
        if self.debug {
            for &v in vars {
                safe_eprintln!(
                    "[NIA] interval-contract: {:?} -> {:?}",
                    v,
                    var_bounds.get(&v)
                );
            }
        }
        let mut derived: HashMap<(TermId, bool), Vec<(TermId, bool)>> = HashMap::default();
        for (var, is_lower, premises) in ctr.derived {
            derived.entry((var, is_lower)).or_insert(premises);
        }
        (derived, refuted)
    }

    /// Export contracted endpoints back to i64 bounds: only ACCEPT
    /// endpoints that fit i64 (otherwise keep the original bound —
    /// sound, merely looser). By construction (pure intersections)
    /// the contracted interval is a subset of the seed, so this
    /// only ever tightens.
    fn export_contracted_bounds(
        ctr: &Contractor<'_, '_>,
        vars: &[TermId],
        var_bounds: &mut HashMap<TermId, (Option<i64>, Option<i64>)>,
    ) {
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
    }

    /// Whether `term`'s DAG contains any term from `set`.
    pub(crate) fn atom_mentions_any(
        &self,
        term: TermId,
        set: &std::collections::BTreeSet<TermId>,
    ) -> bool {
        let mut stack = vec![term];
        let mut seen: std::collections::BTreeSet<TermId> = Default::default();
        while let Some(t) = stack.pop() {
            if set.contains(&t) {
                return true;
            }
            if !seen.insert(t) {
                continue;
            }
            match self.terms.get(t) {
                TermData::App(_, args) => stack.extend(args.iter().copied()),
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(c, a, b) => {
                    stack.push(*c);
                    stack.push(*a);
                    stack.push(*b);
                }
                _ => {}
            }
        }
        false
    }

    /// Whether interval contraction over ONLY `lits` (subset seeds from
    /// var-vs-constant literals in `lits`, alias/definition lookups
    /// filtered to `lits`, no LIA bounds) empties some interval. When
    /// true, `lits` alone are unsatisfiable and form a sound conflict
    /// (#nia-contract-subset-refutes) — the shrinking oracle for the
    /// full-cover emptiness conflicts, whose ~100 literals block
    /// exactly one Boolean trail each in the CEGAR loop.
    pub(crate) fn contract_subset_refutes(&self, lits: &[(TermId, bool)]) -> bool {
        let mut bounds: HashMap<TermId, Iv> = HashMap::default();
        for &(term, positive) in lits {
            let Some((var, lo, hi)) = self.asserted_integer_bound(term, positive) else {
                continue;
            };
            let seed = Iv {
                lo: lo.map(Ep::fin).unwrap_or(Ep::NegInf),
                hi: hi.map(Ep::fin).unwrap_or(Ep::PosInf),
            };
            let entry = bounds.entry(var).or_insert_with(Iv::top);
            *entry = entry.intersect(&seed);
            if entry.is_empty() {
                return true;
            }
        }
        let lit_filter: Option<std::collections::BTreeSet<(TermId, bool)>> =
            Some(lits.iter().copied().collect());
        let var_definitions = Contractor::build_var_definitions(self, &lit_filter);
        let mut ctr = Contractor {
            solver: self,
            bounds,
            changed: true,
            current_atom: None,
            derived: Vec::new(),
            lit_filter,
            var_definitions,
            form_cache: std::cell::RefCell::new(HashMap::default()),
            form_taint: std::cell::Cell::new(0),
            atom_form_cache: std::cell::RefCell::new(HashMap::default()),
        };
        for _round in 0..MAX_CONTRACT_ROUNDS {
            if !ctr.changed {
                break;
            }
            ctr.changed = false;
            for &(term, positive) in lits {
                ctr.current_atom = Some((term, positive));
                if ctr.contract_atom(term, positive).is_err() {
                    return true;
                }
            }
        }
        false
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
                                    "{a}*{b} not in {p:?} (A=[{alo},{ahi}] B=[{blo},{bhi}])"
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
                            "{s}^{m}={v64} not in {p:?} ([{lo},{hi}])"
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
                                        "{n}/{o} not in {q:?} (N=[{nlo},{nhi}] D=[{dlo},{dhi}])"
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
                                "s={s} (s^{m}={p} in [{tlo},{thi}]) excluded by {c:?}"
                            );
                        }
                    }
                }
            }
        }
    }

    /// Form-cache invalidation (#nia-contract-form-cache): a form
    /// computed while `x` is free must not survive `x` being tightened
    /// to a point, because the point shortcut changes the form.
    #[test]
    fn linear_form_cache_invalidated_on_tighten() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Int);
        let v = terms.mk_var("v", Sort::Int);
        let prod = terms.mk_mul(vec![x, v]);
        let solver = NiaSolver::new(&terms);
        let mut ctr = Contractor {
            solver: &solver,
            bounds: HashMap::default(),
            changed: false,
            current_atom: None,
            derived: Vec::new(),
            lit_filter: None,
            var_definitions: HashMap::default(),
            form_cache: std::cell::RefCell::new(HashMap::default()),
            form_taint: std::cell::Cell::new(0),
            atom_form_cache: std::cell::RefCell::new(HashMap::default()),
        };
        // `x*v` is not linear while both factors are free.
        assert!(ctr.linear_form(prod, 0).is_none());
        assert!(
            ctr.form_cache.borrow().contains_key(&prod),
            "top-level form must be memoized"
        );
        // Tighten `x` to the point 1 through the normal backward pass.
        assert!(
            ctr.bwd(x, &Iv::point(BigInt::one()), 0).is_ok(),
            "tightening to a point cannot empty the interval"
        );
        let form = ctr
            .linear_form(prod, 0)
            .expect("with x pinned to 1 the product is linear in v");
        assert_eq!(form.coeffs.get(&v), Some(&BigInt::one()));
        assert!(form.constant.is_zero());
    }

    #[test]
    fn pure_form_survives_unrelated_tighten() {
        // #nia-form-retain: tightening a variable retains pure forms
        // that do not mention it (their recomputation is identical),
        // while forms mentioning it and `None` entries drop.
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Int);
        let v = terms.mk_var("v", Sort::Int);
        let w = terms.mk_var("w", Sort::Int);
        let sum = terms.mk_add(vec![v, w]);
        let solver = NiaSolver::new(&terms);
        let mut ctr = Contractor {
            solver: &solver,
            bounds: HashMap::default(),
            changed: false,
            current_atom: None,
            derived: Vec::new(),
            lit_filter: None,
            var_definitions: HashMap::default(),
            form_cache: std::cell::RefCell::new(HashMap::default()),
            form_taint: std::cell::Cell::new(0),
            atom_form_cache: std::cell::RefCell::new(HashMap::default()),
        };
        let before = ctr.linear_form(sum, 0).expect("v + w is linear");
        assert!(before.pure, "no bounds were read");
        // Tighten the unrelated variable x to a point.
        assert!(ctr.bwd(x, &Iv::point(BigInt::one()), 0).is_ok());
        let after = ctr.linear_form(sum, 0).expect("v + w is linear");
        assert!(
            std::rc::Rc::ptr_eq(&before, &after),
            "pure form not mentioning x must be retained, not recomputed"
        );
        // Tightening a mentioned variable drops the entry: the form
        // is recomputed (with the point shortcut available).
        assert!(ctr.bwd(v, &Iv::point(BigInt::from(3)), 0).is_ok());
        let pinned = ctr.linear_form(sum, 0).expect("v + w is linear");
        assert!(!std::rc::Rc::ptr_eq(&before, &pinned));
        assert_eq!(pinned.constant, BigInt::from(3));
        assert_eq!(pinned.coeffs.get(&w), Some(&BigInt::one()));
        assert!(!pinned.pure, "point shortcut was used");
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
