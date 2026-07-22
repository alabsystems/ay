// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! FP forward-error tactic: pre-solve refutation of rounding-error claims.
//!
//! Recognizes goals of the form
//!
//! ```smt
//! (assert (>= (- (fp.to_real DAG) MIRROR) c))   ; and <=, <, >, either order
//! ```
//!
//! where `DAG` is an `fp.add`/`fp.sub`/`fp.mul`/`fp.neg` dag (all rounded ops
//! RNE) over FP *variables* and `MIRROR` is the exact-real mirror of the dag
//! (the same polynomial over the `fp.to_real` of the leaves). Given asserted
//! input facts — `(fp.isNormal x)` plus magnitude bounds such as
//! `(<= (fp.to_real (fp.abs x)) B)` — it propagates a sound interval enclosure
//! of every intermediate together with an accumulated bound `E` on
//! `|fp.to_real(DAG) - MIRROR|`, all in exact `BigRational` arithmetic (no
//! outward rounding is ever needed: +, -, * on rationals are exact). If the
//! asserted claim contradicts `E`, the whole formula is UNSAT and the tactic
//! reports the refutation; otherwise it abstains and the ordinary (bit-precise
//! but incomplete) `fp.to_real` refinement path runs unchanged.
//!
//! # Rounding model (sound, standard, binade-aware)
//!
//! For a binary op `z = fp.op(RNE, a, b)` with exact operand values in the
//! interval `S = A ∘ B`, the exact result `v ∈ S` rounds to
//! `to_real(z) = fl(v)` with
//!
//! ```text
//! |fl(v) - v| <= r(M),   M = max(|S.lo|, |S.hi|)
//! r(M) = 2^(max(k-1, emin) - sb)   where 2^(k-1) < M <= 2^k
//! ```
//!
//! i.e. half the point spacing of the format in the highest binade reached by
//! `|v|`, floored at half the subnormal spacing (`emin = 1 - emax`,
//! `emax = 2^(eb-1) - 1`, `sb` = significand bits incl. the hidden bit). This
//! is the classical `|fl(v) - v| <= (1/2) ulp(v)` bound for round-to-nearest
//! and is at least as tight as the textbook gamma model `u·|v| + eta`
//! (`u = 2^-sb`): for `M` in `(2^(k-1), 2^k]`, `r(M) = 2^(k-1-sb) <= u·M`. It
//! is valid for **any** finite RNE result — normal, subnormal, or zero — so no
//! intermediate-normality side condition is required (requiring one would be
//! both unsound to assume and impossible to establish for cancelling sums).
//!
//! Value intervals additionally use monotonicity of RNE: if an interval
//! endpoint is itself exactly representable in the format, `fl` cannot cross
//! it, so the rounded interval is clamped at that endpoint instead of being
//! widened by `r(M)`.
//!
//! Error accumulation is the standard forward analysis:
//! `add/sub: e = e_a + e_b + r(M)`; `mul: e = mag(V_a)·e_b + mag(R_b)·e_a +
//! r(M)` (from `|v_a·v_b - r_a·r_b| <= |v_a|·|v_b - r_b| + |r_b|·|v_a - r_a|`,
//! where `R_b` is the mirror-value interval `V_b ± e_b`).
//!
//! # Side conditions — all checked, never assumed
//!
//! The tactic abstains (leaves the goal untouched, so the solver stays on its
//! honest `unknown` path) unless it establishes ALL of:
//!
//! - every dag leaf is an FP variable with `(fp.isNormal x)` asserted (leaves
//!   are therefore finite and non-NaN, so `fp.to_real` is IEEE-interpreted on
//!   them — SMT-LIB leaves `fp.to_real` unconstrained on NaN/±oo) **and** a
//!   finite magnitude enclosure derived from asserted `fp.to_real` bounds;
//! - every rounded op uses the RNE rounding mode (matched structurally; any
//!   other mode, or a non-constant mode, aborts);
//! - no overflow at every intermediate: the exact-result interval must satisfy
//!   `M <= 2^emax` (conservative; guarantees `fl(v)` is finite, hence — by
//!   induction over the dag — no NaN/oo ever arises and `fp.to_real` stays
//!   IEEE-interpreted). Underflow needs no side condition: `r(M)` already
//!   floors at half the subnormal spacing;
//! - the real-side expression is the *exact* mirror of the dag: both sides are
//!   normalized to polynomials over the leaf atoms `to_real(x_i)` with exact
//!   rational coefficients and compared for identity (sound for any valuation;
//!   handles associativity/commutativity/distribution differences);
//! - the claim constant strictly contradicts the certified bound, with the
//!   comparison direction handled exactly (see `is_refuted_by_bound`).
//!
//! The tactic only ever strengthens `unknown` to `unsat`; it never reports
//! `sat` (the bound `E` is an over-approximation, so failure to refute proves
//! nothing) and never weakens an existing verdict.
//!
//! # Proof story
//!
//! A refutation returned here surfaces as a direct UNSAT from the FP theory
//! path. The Alethe proof for it is closed by the executor's existing audited
//! fallback (`derive_empty_via_trust_lemma`), i.e. the gamma/half-ulp lemma is
//! recorded as a `:rule trust` hole and counted by `terminal_trust_report` —
//! exactly like other theory conflicts detected outside the SAT loop. A
//! kernel-checked gamma lemma (validating `r(M)` and the accumulation steps
//! from the input-bound assumptions) is the follow-up that would discharge
//! this hole; see the development design notes.

use std::collections::BTreeMap;

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::{Constant, TermData};
use ay_core::{Sort, TermId, TermStore};
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};

/// Cap on distinct dag nodes analyzed (guards against pathological inputs).
const MAX_DAG_NODES: usize = 1024;
/// Cap on monomials in any normalized polynomial.
const MAX_MONOMIALS: usize = 512;
/// Cap on the degree of any monomial.
const MAX_DEGREE: usize = 8;
/// Cap on exponent-field width: keeps `2^emax` shifts small (Float256 has
/// eb = 19; eb = 24 allows every realistic format while bounding BigInt
/// shifts to ~2^23 bits).
const MAX_EXPONENT_BITS: u32 = 24;
/// Cap on significand width (Float256 has sb = 237).
const MAX_SIGNIFICAND_BITS: u32 = 1024;

/// A successful forward-error refutation: `goal` is unsatisfiable in every
/// model of the mined input-bound assertions, because the asserted deviation
/// contradicts the certified bound `|fp.to_real(dag) - mirror| <= bound`.
pub(super) struct ForwardErrorRefutation {
    /// The refuted assertion (or conjunct of an assertion).
    pub(super) goal: TermId,
    /// The certified accumulated error bound `E` (scaled by the goal's
    /// coefficient on the computed atom).
    pub(super) bound: BigRational,
}

/// Try to refute one assertion (or conjunct) as an FP forward-error claim.
///
/// Returns `Some` iff some assertion is *provably false* in every model of
/// the remaining assertions — i.e. the whole assertion set is UNSAT. Returns
/// `None` in every other case, including any unestablished side condition.
pub(super) fn try_refute_forward_error_goal(
    terms: &TermStore,
    assertions: &[TermId],
) -> Option<ForwardErrorRefutation> {
    // 1. Flatten top-level conjunctions once: bound facts and candidate goals
    //    are both mined from the conjunct list. (Refuting a single conjunct
    //    refutes the whole formula.) `collect_conjuncts` caps its output, so
    //    a pathological hash-consed `and` DAG cannot blow up; hitting the cap
    //    aborts the tactic (abstention is always sound).
    let mut conjuncts: Vec<TermId> = Vec::new();
    for &a in assertions {
        collect_conjuncts(terms, a, &mut conjuncts);
        if conjuncts.len() >= 4 * MAX_DAG_NODES {
            return None;
        }
    }

    // 2. Mine input facts (normality + magnitude bounds on fp.to_real).
    let facts = mine_input_facts(terms, &conjuncts);
    tracing::debug!(
        conjuncts = conjuncts.len(),
        normal = facts.normal.len(),
        lo = facts.lo.len(),
        hi = facts.hi.len(),
        "fp-forward-error: mined input facts"
    );
    if facts.normal.is_empty() {
        return None;
    }

    // 3. Try each conjunct as a forward-error claim.
    let mut poly_memo: HashMap<TermId, Option<Poly>> = HashMap::default();
    let mut mirror_memo: HashMap<TermId, Option<Poly>> = HashMap::default();
    let mut enclosure_memo: HashMap<TermId, Option<Enclosure>> = HashMap::default();
    for &goal in &conjuncts {
        if let Some(refutation) = try_refute_conjunct(
            terms,
            goal,
            &facts,
            &mut poly_memo,
            &mut mirror_memo,
            &mut enclosure_memo,
        ) {
            return Some(refutation);
        }
    }
    None
}

// ---------------------------------------------------------------------------
// Input-fact mining
// ---------------------------------------------------------------------------

/// Facts about FP input variables established by the asserted formula.
struct InputFacts {
    /// Variables with `(fp.isNormal x)` asserted (⇒ finite, non-NaN, ≠ 0).
    normal: HashSet<TermId>,
    /// Lower bounds `lo <= fp.to_real(x)`.
    lo: HashMap<TermId, BigRational>,
    /// Upper bounds `fp.to_real(x) <= hi`.
    hi: HashMap<TermId, BigRational>,
}

/// Flatten nested `and` into individual conjuncts.
///
/// Output is capped at `4 * MAX_DAG_NODES` entries so a hash-consed `and`
/// DAG (shared subterms re-expanded down every path) cannot cause an
/// exponential blowup; the caller treats hitting the cap as abstention.
fn collect_conjuncts(terms: &TermStore, t: TermId, out: &mut Vec<TermId>) {
    if out.len() >= 4 * MAX_DAG_NODES {
        return;
    }
    match terms.get(t) {
        TermData::App(sym, args) if sym.name() == "and" => {
            for &a in args {
                collect_conjuncts(terms, a, out);
            }
        }
        _ => out.push(t),
    }
}

/// `t` is an FP-sorted variable.
fn as_fp_var(terms: &TermStore, t: TermId) -> Option<TermId> {
    match (terms.get(t), terms.sort(t)) {
        (TermData::Var(..), Sort::FloatingPoint(..)) => Some(t),
        _ => None,
    }
}

/// Evaluate a ground rational expression (`Const`, and `+ - * /` over them).
fn eval_ground_rational(terms: &TermStore, t: TermId) -> Option<BigRational> {
    match terms.get(t) {
        TermData::Const(Constant::Rational(r)) => Some(r.0.clone()),
        TermData::Const(Constant::Int(i)) => Some(BigRational::from_integer(i.clone())),
        TermData::App(sym, args) if !args.is_empty() => {
            let vals: Option<Vec<BigRational>> = args
                .iter()
                .map(|&a| eval_ground_rational(terms, a))
                .collect();
            let vals = vals?;
            match sym.name() {
                "+" => Some(vals.into_iter().sum()),
                "*" => Some(vals.into_iter().product()),
                "-" if vals.len() == 1 => Some(-vals[0].clone()),
                "-" => {
                    let mut acc = vals[0].clone();
                    for v in &vals[1..] {
                        acc -= v;
                    }
                    Some(acc)
                }
                "/" => {
                    let mut acc = vals[0].clone();
                    for v in &vals[1..] {
                        if v.is_zero() {
                            return None;
                        }
                        acc /= v;
                    }
                    Some(acc)
                }
                _ => None,
            }
        }
        _ => None,
    }
}

/// Mine normality facts and `fp.to_real` bounds from the conjunct list.
fn mine_input_facts(terms: &TermStore, conjuncts: &[TermId]) -> InputFacts {
    let mut facts = InputFacts {
        normal: HashSet::default(),
        lo: HashMap::default(),
        hi: HashMap::default(),
    };
    for &c in conjuncts {
        let TermData::App(sym, args) = terms.get(c) else {
            continue;
        };
        match (sym.name(), args.len()) {
            ("fp.isNormal", 1) => {
                if let Some(v) = as_fp_var(terms, args[0]) {
                    facts.normal.insert(v);
                }
            }
            ("<=" | "<" | ">=" | ">", 2) => {
                // Normalize to `small <= big` (using `<` as the weaker `<=`
                // is sound: the premise is only ever weakened).
                let (small, big) = match sym.name() {
                    "<=" | "<" => (args[0], args[1]),
                    _ => (args[1], args[0]),
                };
                mine_bound(terms, small, big, &mut facts);
            }
            _ => {}
        }
    }
    facts
}

/// Record a bound from a normalized comparison `small <= big`.
fn mine_bound(terms: &TermStore, small: TermId, big: TermId, facts: &mut InputFacts) {
    // Upper bounds: to_real(x) <= c   or   to_real(fp.abs(x)) <= c.
    if let Some(c) = eval_ground_rational(terms, big) {
        if let TermData::App(sym, args) = terms.get(small) {
            if sym.name() == "fp.to_real" && args.len() == 1 {
                match terms.get(args[0]) {
                    // |x| <= c: two-sided magnitude bound.
                    TermData::App(abs_sym, abs_args)
                        if abs_sym.name() == "fp.abs" && abs_args.len() == 1 =>
                    {
                        if let Some(v) = as_fp_var(terms, abs_args[0]) {
                            if !c.is_negative() {
                                tighten_hi(&mut facts.hi, v, c.clone());
                                tighten_lo(&mut facts.lo, v, -c);
                            }
                        }
                    }
                    _ => {
                        if let Some(v) = as_fp_var(terms, args[0]) {
                            tighten_hi(&mut facts.hi, v, c);
                        }
                    }
                }
            }
        }
        return;
    }
    // Lower bounds: c <= to_real(x). (Lower bounds on |x| carry no useful
    // enclosure information for this analysis and are ignored.)
    if let Some(c) = eval_ground_rational(terms, small) {
        if let TermData::App(sym, args) = terms.get(big) {
            if sym.name() == "fp.to_real" && args.len() == 1 {
                if let Some(v) = as_fp_var(terms, args[0]) {
                    tighten_lo(&mut facts.lo, v, c);
                }
            }
        }
    }
}

fn tighten_hi(map: &mut HashMap<TermId, BigRational>, key: TermId, val: BigRational) {
    match map.get(&key) {
        Some(old) if *old <= val => {}
        _ => {
            map.insert(key, val);
        }
    }
}

fn tighten_lo(map: &mut HashMap<TermId, BigRational>, key: TermId, val: BigRational) {
    match map.get(&key) {
        Some(old) if *old >= val => {}
        _ => {
            map.insert(key, val);
        }
    }
}

// ---------------------------------------------------------------------------
// Polynomial normalization (exact mirror check)
// ---------------------------------------------------------------------------

/// A polynomial atom: `fp.to_real` of a leaf FP variable, or of a computed
/// (rounded) FP dag. The mirror check requires the goal to contain exactly
/// one `Computed` atom, linearly.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Atom {
    /// `fp.to_real(x)` for an FP variable `x` (exact input value).
    Leaf(TermId),
    /// `fp.to_real(t)` for a compound FP term `t` (rounded dag value).
    Computed(TermId),
}

/// A monomial: sorted multiset of atoms (empty = the constant term).
type Monomial = Vec<Atom>;

/// A normalized polynomial with exact rational coefficients. Zero
/// coefficients are never stored.
#[derive(Clone, Debug, PartialEq, Eq, Default)]
struct Poly(BTreeMap<Monomial, BigRational>);

impl Poly {
    fn constant(c: BigRational) -> Self {
        let mut p = Self::default();
        p.accumulate(Vec::new(), c);
        p
    }

    fn atom(a: Atom) -> Self {
        let mut p = Self::default();
        p.accumulate(vec![a], BigRational::one());
        p
    }

    fn accumulate(&mut self, mono: Monomial, coeff: BigRational) {
        if coeff.is_zero() {
            return;
        }
        let entry = self.0.entry(mono);
        match entry {
            std::collections::btree_map::Entry::Vacant(v) => {
                v.insert(coeff);
            }
            std::collections::btree_map::Entry::Occupied(mut o) => {
                *o.get_mut() += coeff;
                if o.get().is_zero() {
                    o.remove();
                }
            }
        }
    }

    fn add_assign(&mut self, other: &Self) -> Option<()> {
        for (m, c) in &other.0 {
            self.accumulate(m.clone(), c.clone());
        }
        (self.0.len() <= MAX_MONOMIALS).then_some(())
    }

    fn neg(&self) -> Self {
        Self(
            self.0
                .iter()
                .map(|(m, c)| (m.clone(), -c.clone()))
                .collect(),
        )
    }

    fn scale(&self, k: &BigRational) -> Self {
        if k.is_zero() {
            return Self::default();
        }
        Self(
            self.0
                .iter()
                .map(|(m, c)| (m.clone(), c.clone() * k))
                .collect(),
        )
    }

    fn mul(&self, other: &Self) -> Option<Self> {
        let mut out = Self::default();
        for (ma, ca) in &self.0 {
            for (mb, cb) in &other.0 {
                if ma.len() + mb.len() > MAX_DEGREE {
                    return None;
                }
                let mut m = ma.clone();
                m.extend_from_slice(mb);
                m.sort_unstable();
                out.accumulate(m, ca.clone() * cb.clone());
                if out.0.len() > MAX_MONOMIALS {
                    return None;
                }
            }
        }
        Some(out)
    }
}

/// Normalize a Real-sorted expression into a `Poly` over `Atom`s.
///
/// Supported: rational/integer constants, `+ - *`, `/` by nonzero constants,
/// and `fp.to_real` of FP variables (Leaf) or compound FP terms (Computed).
/// Anything else (free Real variables, ite, ...) aborts with `None`.
fn poly_real(
    terms: &TermStore,
    t: TermId,
    memo: &mut HashMap<TermId, Option<Poly>>,
) -> Option<Poly> {
    if let Some(cached) = memo.get(&t) {
        return cached.clone();
    }
    let result = poly_real_uncached(terms, t, memo);
    memo.insert(t, result.clone());
    result
}

fn poly_real_uncached(
    terms: &TermStore,
    t: TermId,
    memo: &mut HashMap<TermId, Option<Poly>>,
) -> Option<Poly> {
    match terms.get(t) {
        TermData::Const(Constant::Rational(r)) => Some(Poly::constant(r.0.clone())),
        TermData::Const(Constant::Int(i)) => {
            Some(Poly::constant(BigRational::from_integer(i.clone())))
        }
        TermData::App(sym, args) => match (sym.name(), args.len()) {
            ("fp.to_real", 1) => match (terms.get(args[0]), terms.sort(args[0])) {
                (TermData::Var(..), Sort::FloatingPoint(..)) => {
                    Some(Poly::atom(Atom::Leaf(args[0])))
                }
                (TermData::App(..), Sort::FloatingPoint(..)) => {
                    Some(Poly::atom(Atom::Computed(args[0])))
                }
                _ => None,
            },
            ("+", n) if n >= 1 => {
                let mut acc = Poly::default();
                for &a in args {
                    acc.add_assign(&poly_real(terms, a, memo)?)?;
                }
                Some(acc)
            }
            ("-", 1) => Some(poly_real(terms, args[0], memo)?.neg()),
            ("-", n) if n >= 2 => {
                let mut acc = poly_real(terms, args[0], memo)?;
                for &a in &args[1..] {
                    acc.add_assign(&poly_real(terms, a, memo)?.neg())?;
                }
                Some(acc)
            }
            ("*", n) if n >= 1 => {
                let mut acc = Poly::constant(BigRational::one());
                for &a in args {
                    acc = acc.mul(&poly_real(terms, a, memo)?)?;
                }
                Some(acc)
            }
            ("/", n) if n >= 2 => {
                let mut acc = poly_real(terms, args[0], memo)?;
                for &a in &args[1..] {
                    let c = eval_ground_rational(terms, a)?;
                    if c.is_zero() {
                        return None;
                    }
                    acc = acc.scale(&c.recip());
                }
                Some(acc)
            }
            _ => None,
        },
        _ => None,
    }
}

/// The exact-real mirror of an FP dag as a `Poly` over `Leaf` atoms.
///
/// `fp.add/sub/mul` map to `+/-/*`; `fp.neg` to negation; leaves to their
/// `to_real` atoms. Rounding modes are NOT checked here — `analyze` does that
/// (the mirror is a purely syntactic object).
fn mirror_poly(
    terms: &TermStore,
    t: TermId,
    memo: &mut HashMap<TermId, Option<Poly>>,
) -> Option<Poly> {
    if let Some(cached) = memo.get(&t) {
        return cached.clone();
    }
    if memo.len() > MAX_DAG_NODES {
        return None;
    }
    let result = match terms.get(t) {
        TermData::Var(..) if matches!(terms.sort(t), Sort::FloatingPoint(..)) => {
            Some(Poly::atom(Atom::Leaf(t)))
        }
        TermData::App(sym, args) => match (sym.name(), args.len()) {
            ("fp.neg", 1) => mirror_poly(terms, args[0], memo).map(|p| p.neg()),
            ("fp.add", 3) => {
                let mut a = mirror_poly(terms, args[1], memo)?;
                a.add_assign(&mirror_poly(terms, args[2], memo)?)?;
                Some(a)
            }
            ("fp.sub", 3) => {
                let mut a = mirror_poly(terms, args[1], memo)?;
                a.add_assign(&mirror_poly(terms, args[2], memo)?.neg())?;
                Some(a)
            }
            ("fp.mul", 3) => {
                let a = mirror_poly(terms, args[1], memo)?;
                a.mul(&mirror_poly(terms, args[2], memo)?)
            }
            _ => None,
        },
        _ => None,
    };
    memo.insert(t, result.clone());
    result
}

// ---------------------------------------------------------------------------
// Interval / error propagation
// ---------------------------------------------------------------------------

/// Sound enclosure of one dag node: `to_real(node) ∈ [lo, hi]` and
/// `|to_real(node) - mirror(node)| <= err`, in every model of the mined
/// input facts.
#[derive(Clone, Debug)]
struct Enclosure {
    lo: BigRational,
    hi: BigRational,
    err: BigRational,
}

impl Enclosure {
    /// Largest magnitude in the value interval.
    fn mag(&self) -> BigRational {
        let al = self.lo.abs();
        let ah = self.hi.abs();
        if al >= ah {
            al
        } else {
            ah
        }
    }
}

/// `2^e` as an exact rational (`e` may be negative).
fn pow2(e: i64) -> BigRational {
    if e >= 0 {
        BigRational::from_integer(BigInt::one() << e as usize)
    } else {
        BigRational::new(BigInt::one(), BigInt::one() << (-e) as usize)
    }
}

/// `m <= 2^k` for `m > 0`.
fn le_pow2(m: &BigRational, k: i64) -> bool {
    if k >= 0 {
        *m.numer() <= (m.denom() << k as usize)
    } else {
        (m.numer() << (-k) as usize) <= *m.denom()
    }
}

/// Smallest `k` with `m <= 2^k`, for `m > 0`.
fn ceil_log2(m: &BigRational) -> i64 {
    let mut k = m.numer().bits() as i64 - m.denom().bits() as i64;
    while !le_pow2(m, k) {
        k += 1;
    }
    while le_pow2(m, k - 1) {
        k -= 1;
    }
    k
}

/// Per-format constants derived from `Sort::FloatingPoint(eb, sb)`.
struct FpFormat {
    /// Maximum exponent (= bias): binade `[2^emax, 2^(emax+1))` is the last.
    emax: i64,
    /// Minimum normal exponent, `1 - emax`.
    emin: i64,
    /// Significand bits including the hidden bit.
    sb: i64,
}

impl FpFormat {
    fn from_sort(sort: &Sort) -> Option<Self> {
        let &Sort::FloatingPoint(eb, sb) = sort else {
            return None;
        };
        if !(2..=MAX_EXPONENT_BITS).contains(&eb) || !(2..=MAX_SIGNIFICAND_BITS).contains(&sb) {
            return None;
        }
        let emax = (1i64 << (eb - 1)) - 1;
        Some(Self {
            emax,
            emin: 1 - emax,
            sb: i64::from(sb),
        })
    }

    /// Sound bound on `|fl(v) - v|` (RNE, no overflow) for all `|v| <= m`:
    /// half the point spacing in the highest binade reached, floored at half
    /// the subnormal spacing. Valid for normal, subnormal, and zero results.
    fn round_err_bound(&self, m: &BigRational) -> BigRational {
        if m.is_zero() {
            return BigRational::zero();
        }
        let k = ceil_log2(m);
        pow2((k - 1).max(self.emin) - self.sb)
    }

    /// `x` is exactly representable in this format (used for the monotone
    /// rounding clamp: `v <= x` and `x` representable imply `fl(v) <= x`).
    fn is_representable(&self, x: &BigRational) -> bool {
        if x.is_zero() {
            return true;
        }
        let a = x.abs();
        if !le_pow2(&a, self.emax) {
            return false;
        }
        let k = ceil_log2(&a);
        let spacing = pow2((k - 1).max(self.emin) + 1 - self.sb);
        (a / spacing).is_integer()
    }
}

/// Compute a sound enclosure for an FP dag node, or `None` if any side
/// condition cannot be established from the asserted facts.
fn analyze(
    terms: &TermStore,
    t: TermId,
    facts: &InputFacts,
    memo: &mut HashMap<TermId, Option<Enclosure>>,
) -> Option<Enclosure> {
    if let Some(cached) = memo.get(&t) {
        return cached.clone();
    }
    if memo.len() > MAX_DAG_NODES {
        return None;
    }
    let result = analyze_uncached(terms, t, facts, memo);
    memo.insert(t, result.clone());
    result
}

fn analyze_uncached(
    terms: &TermStore,
    t: TermId,
    facts: &InputFacts,
    memo: &mut HashMap<TermId, Option<Enclosure>>,
) -> Option<Enclosure> {
    match terms.get(t) {
        // Leaf: FP variable with asserted normality and a finite enclosure.
        // Normality ⇒ finite and non-NaN ⇒ `fp.to_real` is IEEE-interpreted
        // and the asserted bounds genuinely enclose the input value.
        TermData::Var(..) if matches!(terms.sort(t), Sort::FloatingPoint(..)) => {
            if !facts.normal.contains(&t) {
                return None;
            }
            let lo = facts.lo.get(&t)?.clone();
            let hi = facts.hi.get(&t)?.clone();
            if lo > hi {
                // Contradictory input bounds: abstain rather than exploit.
                return None;
            }
            Some(Enclosure {
                lo,
                hi,
                err: BigRational::zero(),
            })
        }
        TermData::App(sym, args) => match (sym.name(), args.len()) {
            // fp.neg is exact: negate the interval, keep the error.
            ("fp.neg", 1) => {
                let a = analyze(terms, args[0], facts, memo)?;
                Some(Enclosure {
                    lo: -a.hi,
                    hi: -a.lo,
                    err: a.err,
                })
            }
            (op @ ("fp.add" | "fp.sub" | "fp.mul"), 3) => {
                // Side condition: rounding mode must be RNE (the half-ulp
                // model below is specific to round-to-nearest).
                if !is_rne(terms, args[0]) {
                    return None;
                }
                let format = FpFormat::from_sort(terms.sort(t))?;
                let a = analyze(terms, args[1], facts, memo)?;
                let b = analyze(terms, args[2], facts, memo)?;

                // Exact-result interval S = A ∘ B and propagated error
                // (rationals: exact, no outward rounding required).
                let (s_lo, s_hi, e_prop) = match op {
                    "fp.add" => (
                        a.lo.clone() + &b.lo,
                        a.hi.clone() + &b.hi,
                        a.err.clone() + &b.err,
                    ),
                    "fp.sub" => (
                        a.lo.clone() - &b.hi,
                        a.hi.clone() - &b.lo,
                        a.err.clone() + &b.err,
                    ),
                    _ => {
                        let products = [
                            a.lo.clone() * &b.lo,
                            a.lo.clone() * &b.hi,
                            a.hi.clone() * &b.lo,
                            a.hi.clone() * &b.hi,
                        ];
                        let s_lo = products.iter().min()?.clone();
                        let s_hi = products.iter().max()?.clone();
                        // |va·vb - ra·rb| <= |va|·err_b + |rb|·err_a with
                        // |rb| <= mag(V_b) + err_b (mirror interval).
                        let e = a.mag() * &b.err + (b.mag() + &b.err) * &a.err;
                        (s_lo, s_hi, e)
                    }
                };

                // Side condition: no overflow. `M <= 2^emax` keeps the exact
                // result strictly below the RNE overflow threshold, so fl(v)
                // is finite (conservative but ample in practice).
                let m = {
                    let al = s_lo.abs();
                    let ah = s_hi.abs();
                    if al >= ah {
                        al
                    } else {
                        ah
                    }
                };
                if !m.is_zero() && !le_pow2(&m, format.emax) {
                    return None;
                }

                let r = format.round_err_bound(&m);

                // Rounded-value interval with monotone clamping: RNE is
                // monotone, so an exactly-representable endpoint bounds the
                // rounded result without widening.
                let lo = if format.is_representable(&s_lo) {
                    s_lo
                } else {
                    s_lo - &r
                };
                let hi = if format.is_representable(&s_hi) {
                    s_hi
                } else {
                    s_hi + &r
                };

                Some(Enclosure {
                    lo,
                    hi,
                    err: e_prop + r,
                })
            }
            _ => None,
        },
        _ => None,
    }
}

/// `t` is the RNE rounding-mode constant. Matched structurally against the
/// canonical short name the frontend produces (nullary app) plus the `Var`
/// spelling some frontends use. Anything else — including other modes and
/// non-constant modes — is NOT RNE.
fn is_rne(terms: &TermStore, t: TermId) -> bool {
    match terms.get(t) {
        TermData::App(sym, args) => args.is_empty() && sym.name() == "RNE",
        TermData::Var(name, _) => name == "RNE",
        _ => false,
    }
}

// ---------------------------------------------------------------------------
// Goal recognition and refutation
// ---------------------------------------------------------------------------

/// Comparison operator of a candidate goal, normalized as `q OP 0`.
#[derive(Clone, Copy, Debug)]
enum CmpOp {
    Ge,
    Gt,
    Le,
    Lt,
}

impl CmpOp {
    fn negate(self) -> Self {
        match self {
            Self::Ge => Self::Lt,
            Self::Gt => Self::Le,
            Self::Le => Self::Gt,
            Self::Lt => Self::Ge,
        }
    }
}

/// Decompose `t` (possibly under `not`) into `lhs OP rhs`.
fn decompose_cmp(terms: &TermStore, t: TermId) -> Option<(CmpOp, TermId, TermId)> {
    match terms.get(t) {
        TermData::Not(inner) => {
            let (op, l, r) = decompose_cmp(terms, *inner)?;
            Some((op.negate(), l, r))
        }
        TermData::App(sym, args) if args.len() == 2 => {
            let op = match sym.name() {
                ">=" => CmpOp::Ge,
                ">" => CmpOp::Gt,
                "<=" => CmpOp::Le,
                "<" => CmpOp::Lt,
                _ => return None,
            };
            Some((op, args[0], args[1]))
        }
        _ => None,
    }
}

/// `q = a·D + c0` with `|a·D| <= bound` in every model: is `q OP 0`
/// unsatisfiable?
fn is_refuted_by_bound(op: CmpOp, c0: &BigRational, bound: &BigRational) -> bool {
    match op {
        // a·D >= -c0 requires bound >= -c0.
        CmpOp::Ge => *c0 < -bound.clone(),
        // a·D > -c0 requires bound > -c0.
        CmpOp::Gt => *c0 <= -bound.clone(),
        // a·D <= -c0 requires -bound <= -c0.
        CmpOp::Le => c0 > bound,
        // a·D < -c0 requires -bound < -c0.
        CmpOp::Lt => c0 >= bound,
    }
}

fn try_refute_conjunct(
    terms: &TermStore,
    goal: TermId,
    facts: &InputFacts,
    poly_memo: &mut HashMap<TermId, Option<Poly>>,
    mirror_memo: &mut HashMap<TermId, Option<Poly>>,
    enclosure_memo: &mut HashMap<TermId, Option<Enclosure>>,
) -> Option<ForwardErrorRefutation> {
    let (op, lhs, rhs) = decompose_cmp(terms, goal)?;
    // Only Real comparisons can be forward-error claims.
    if !matches!(terms.sort(lhs), Sort::Real) && !matches!(terms.sort(rhs), Sort::Real) {
        return None;
    }
    let mut q = poly_real(terms, lhs, poly_memo)?;
    q.add_assign(&poly_real(terms, rhs, poly_memo)?.neg())?;

    // Decompose q = a·Computed(dag) + P(leaves) + c0. Exactly one computed
    // atom, degree 1, is required.
    let mut computed: Option<(TermId, BigRational)> = None;
    let mut mirror_part = Poly::default();
    let mut c0 = BigRational::zero();
    for (mono, coeff) in &q.0 {
        if mono.is_empty() {
            c0 = coeff.clone();
        } else if mono.iter().any(|a| matches!(a, Atom::Computed(_))) {
            if computed.is_some() || mono.len() != 1 {
                return None;
            }
            let Atom::Computed(dag) = mono[0] else {
                return None;
            };
            computed = Some((dag, coeff.clone()));
        } else {
            mirror_part.accumulate(mono.clone(), coeff.clone());
        }
    }
    let (dag, a) = computed?;

    // Mirror check: the leaf-polynomial part must be exactly -a times the
    // dag's exact-real mirror, so q = a·(to_real(dag) - mirror) + c0.
    let mirror = mirror_poly(terms, dag, mirror_memo)?;
    if mirror_part != mirror.scale(&-a.clone()) {
        tracing::debug!("fp-forward-error: mirror mismatch");
        return None;
    }

    // Certified bound on |a·(to_real(dag) - mirror)|.
    let enclosure = analyze(terms, dag, facts, enclosure_memo)?;
    let bound = a.abs() * &enclosure.err;
    tracing::debug!(%bound, "fp-forward-error: certified bound");

    is_refuted_by_bound(op, &c0, &bound).then_some(ForwardErrorRefutation { goal, bound })
}

#[cfg(test)]
mod tests;
