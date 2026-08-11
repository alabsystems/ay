// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Strict-mode semantic validation for `TheoryLemmaKind::FpForwardError` proof
//! steps (#trust-count→0).
//!
//! An FP forward-error lemma clause is the disjunction of the NEGATED premises
//! of a forward-error refutation:
//!
//! ```text
//! (cl (not F_1) ... (not F_n) (not G))
//! ```
//!
//! where the `F_i` are input facts — `(fp.isNormal x)` conjuncts and
//! `fp.to_real` magnitude bounds such as `(<= (fp.to_real (fp.abs x)) B)` —
//! and `G` is a rounding-error goal comparison
//! `(>= (- (fp.to_real DAG) MIRROR) c)` (any of `>= > <= <`, either operand
//! order, possibly under `not`) over an `fp.add`/`fp.sub`/`fp.mul`/`fp.neg`
//! dag whose every rounded op uses RNE. The clause is a theory tautology iff
//! the conjunction of the premises is unsatisfiable, i.e. iff the certified
//! forward-error bound derived from the facts strictly contradicts the goal.
//!
//! This checker re-derives that refutation INDEPENDENTLY and fail-closed from
//! nothing but the clause, in exact `BigRational` arithmetic:
//!
//! 1. un-negate the literals to recover the premises (any literal that is not
//!    a Bool-sorted formula rejects the clause);
//! 2. re-mine `fp.isNormal` facts and two-sided magnitude enclosures per FP
//!    leaf variable (a leaf without both is rejected during analysis);
//! 3. re-check the RNE-only rounding-mode side condition structurally and the
//!    no-overflow side condition (`M <= 2^emax`) at every dag node;
//! 4. re-run the enclosure/error propagation with the binade-aware half-ulp
//!    bound `r(M) = 2^(max(k-1, emin) - sb)` for `2^(k-1) < M <= 2^k`, RNE
//!    monotonicity clamping at exactly-representable endpoints, and the
//!    standard accumulation (`add/sub: e_a + e_b + r(M)`;
//!    `mul: mag(V_a)·e_b + (mag(V_b) + e_b)·e_a + r(M)`);
//! 5. re-normalize the goal polynomial over the atoms `to_real(x_i)` /
//!    `to_real(DAG)` and verify the leaf part is EXACTLY `-a·mirror(DAG)`
//!    (identity of polynomials with exact rational coefficients);
//! 6. accept ONLY if `|a|·E` strictly contradicts the claim constant with the
//!    comparison direction handled exactly.
//!
//! Anything unrecognized — an unsupported FP op in the dag, a non-RNE or
//! non-constant rounding mode, a missing normality/bound fact, a mirror
//! mismatch, a bound that does not contradict the claim — rejects the lemma
//! (fail closed), so a forged clause can never be accepted (no false-UNSAT).
//! Extra premise literals beyond the needed refutation subset are tolerated
//! (they only strengthen the refuted conjunction) provided each is a
//! well-formed Bool-sorted literal.
//!
//! ## Why a standalone implementation
//!
//! The solver-side tactic lives in `ay-dpll` (`theories/fp/forward_error.rs`),
//! downstream of this crate — and the entire point of the lemma kind is an
//! INDEPENDENT re-derivation: the proof classifier promotes a `Generic`/trust
//! lemma to `FpForwardError` only when [`recognize_fp_forward_error`] (which
//! IS this validator) accepts it, so classifier and checker cannot drift.
//! Like [`super::fp_bounded`], the module depends only on `ay-core` term
//! utilities plus `num-bigint`/`num-rational` (no native floats, no solver
//! stack), so it stays amenable to independent (e.g. Lean) re-verification.

use std::collections::BTreeMap;

use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};

use ay_core::{Constant, ProofId, Sort, TermData, TermId, TermStore};

use super::ProofCheckError;

/// Cap on distinct dag nodes analyzed (guards against pathological inputs).
const MAX_DAG_NODES: usize = 1024;
/// Cap on flattened premise conjuncts (a hash-consed `and` DAG re-expanded
/// down every path must not blow up; hitting the cap rejects — fail closed).
const MAX_CONJUNCTS: usize = 4 * MAX_DAG_NODES;
/// Cap on monomials in any normalized polynomial.
const MAX_MONOMIALS: usize = 512;
/// Cap on the degree of any monomial.
const MAX_DEGREE: usize = 8;
/// Cap on exponent-field width (bounds `2^emax` BigInt shifts).
const MAX_EXPONENT_BITS: u32 = 24;
/// Cap on significand width (Float256 has sb = 237).
const MAX_SIGNIFICAND_BITS: u32 = 1024;

/// Recognize whether `clause` is a strict-checkable FP forward-error lemma —
/// i.e. whether [`validate_fp_forward_error`] would accept it. By construction
/// the exact inverse of the validator (it calls the validator), so the proof
/// classifier (`ay-dpll`) and the strict checker cannot drift: a `Generic`
/// trust lemma is upgraded to `FpForwardError` ONLY when strict mode will
/// independently re-validate it by the full analytic re-derivation.
#[must_use]
pub fn recognize_fp_forward_error(terms: &TermStore, clause: &[TermId]) -> bool {
    validate_fp_forward_error(terms, ProofId(0), clause).is_ok()
}

/// Validate an `FpForwardError` lemma in strict mode by re-deriving the
/// forward-error refutation from the clause (see module docs).
pub(crate) fn validate_fp_forward_error(
    terms: &TermStore,
    step_id: ProofId,
    clause: &[TermId],
) -> Result<(), ProofCheckError> {
    let reject = |reason: &str| ProofCheckError::InvalidTheoryLemma {
        step: step_id,
        reason: format!("fp_forward_error: {reason}"),
    };

    if clause.is_empty() {
        return Err(reject("clause must be non-empty"));
    }

    // 1. Un-negate literals into premises. Every literal must be a
    //    well-formed Bool-sorted formula; a `(not P)` literal contributes the
    //    positive premise `P`, and a positive literal `L` contributes the
    //    negative premise `¬L` (the assumption it negates was itself a
    //    negation). Anything else rejects.
    let mut positive: Vec<TermId> = Vec::new();
    let mut negative: Vec<TermId> = Vec::new();
    for &lit in clause {
        if !matches!(terms.sort(lit), Sort::Bool) {
            return Err(reject("literal is not Bool-sorted"));
        }
        match terms.get(lit) {
            TermData::Not(inner) => positive.push(*inner),
            _ => negative.push(lit),
        }
    }

    // 2. Flatten positive premises into conjuncts (facts + goal candidates).
    let mut conjuncts: Vec<TermId> = Vec::new();
    for &p in &positive {
        collect_conjuncts(terms, p, &mut conjuncts);
        if conjuncts.len() >= MAX_CONJUNCTS {
            return Err(reject("premise conjunct cap exceeded"));
        }
    }

    // 3. Re-mine input facts from the positive conjuncts.
    let facts = mine_input_facts(terms, &conjuncts);
    if facts.normal.is_empty() {
        return Err(reject("no fp.isNormal premise found"));
    }

    // 4. Try every conjunct as the refuted goal comparison; negative premises
    //    `¬L` are candidate goals under an outer negation.
    let mut poly_memo: Memo<Option<Poly>> = Memo::default();
    let mut mirror_memo: Memo<Option<Poly>> = Memo::default();
    let mut enclosure_memo: Memo<Option<Enclosure>> = Memo::default();
    let refuted = conjuncts
        .iter()
        .map(|&g| (g, false))
        .chain(negative.iter().map(|&g| (g, true)))
        .any(|(goal, negated)| {
            try_refute_conjunct(
                terms,
                goal,
                negated,
                &facts,
                &mut poly_memo,
                &mut mirror_memo,
                &mut enclosure_memo,
            )
        });
    if refuted {
        Ok(())
    } else {
        Err(reject(
            "no premise conjunct is a rounding-error claim strictly \
             contradicted by the certified forward-error bound",
        ))
    }
}

/// Deterministic memo table keyed by `TermId`.
type Memo<T> = BTreeMap<TermId, T>;

// ===========================================================================
// Premise flattening + input-fact mining.
// ===========================================================================

/// Facts about FP input variables established by the premises.
struct InputFacts {
    /// Variables with `(fp.isNormal x)` asserted (⇒ finite, non-NaN).
    normal: Vec<TermId>,
    /// Lower bounds `lo <= fp.to_real(x)`.
    lo: BTreeMap<TermId, BigRational>,
    /// Upper bounds `fp.to_real(x) <= hi`.
    hi: BTreeMap<TermId, BigRational>,
}

/// Flatten nested `and` into individual conjuncts (output capped by caller).
fn collect_conjuncts(terms: &TermStore, t: TermId, out: &mut Vec<TermId>) {
    if out.len() >= MAX_CONJUNCTS {
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
        normal: Vec::new(),
        lo: BTreeMap::new(),
        hi: BTreeMap::new(),
    };
    for &c in conjuncts {
        let TermData::App(sym, args) = terms.get(c) else {
            continue;
        };
        match (sym.name(), args.len()) {
            ("fp.isNormal", 1) => {
                if let Some(v) = as_fp_var(terms, args[0]) {
                    if !facts.normal.contains(&v) {
                        facts.normal.push(v);
                    }
                }
            }
            ("<=" | "<" | ">=" | ">", 2) => {
                // Normalize to `small <= big` (reading `<` as the weaker `<=`
                // only weakens the premise — sound).
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
    // Lower bounds: c <= to_real(x).
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

fn tighten_hi(map: &mut BTreeMap<TermId, BigRational>, key: TermId, val: BigRational) {
    match map.get(&key) {
        Some(old) if *old <= val => {}
        _ => {
            map.insert(key, val);
        }
    }
}

fn tighten_lo(map: &mut BTreeMap<TermId, BigRational>, key: TermId, val: BigRational) {
    match map.get(&key) {
        Some(old) if *old >= val => {}
        _ => {
            map.insert(key, val);
        }
    }
}

// ===========================================================================
// Polynomial normalization (exact mirror identity check).
// ===========================================================================

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
        match self.0.entry(mono) {
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
fn poly_real(terms: &TermStore, t: TermId, memo: &mut Memo<Option<Poly>>) -> Option<Poly> {
    if let Some(cached) = memo.get(&t) {
        return cached.clone();
    }
    if memo.len() > MAX_DAG_NODES {
        return None;
    }
    let result = poly_real_uncached(terms, t, memo);
    memo.insert(t, result.clone());
    result
}

fn poly_real_uncached(terms: &TermStore, t: TermId, memo: &mut Memo<Option<Poly>>) -> Option<Poly> {
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
fn mirror_poly(terms: &TermStore, t: TermId, memo: &mut Memo<Option<Poly>>) -> Option<Poly> {
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

// ===========================================================================
// Interval / error propagation.
// ===========================================================================

/// Sound enclosure of one dag node: `to_real(node) ∈ [lo, hi]` and
/// `|to_real(node) - mirror(node)| <= err`, in every model of the premises.
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
/// condition cannot be established from the mined facts.
fn analyze(
    terms: &TermStore,
    t: TermId,
    facts: &InputFacts,
    memo: &mut Memo<Option<Enclosure>>,
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
    memo: &mut Memo<Option<Enclosure>>,
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
                // Contradictory input bounds: reject rather than exploit.
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
                // model is specific to round-to-nearest).
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
            // Any other op — fp.div, fp.fma, conversions, ... — fails closed.
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

// ===========================================================================
// Goal recognition and refutation.
// ===========================================================================

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

/// Try `goal` (under an outer negation when `negated`) as the refuted
/// forward-error comparison. `true` iff the certified bound strictly
/// contradicts it.
fn try_refute_conjunct(
    terms: &TermStore,
    goal: TermId,
    negated: bool,
    facts: &InputFacts,
    poly_memo: &mut Memo<Option<Poly>>,
    mirror_memo: &mut Memo<Option<Poly>>,
    enclosure_memo: &mut Memo<Option<Enclosure>>,
) -> bool {
    let Some((op, lhs, rhs)) = decompose_cmp(terms, goal) else {
        return false;
    };
    let op = if negated { op.negate() } else { op };
    // Only Real comparisons can be forward-error claims.
    if !matches!(terms.sort(lhs), Sort::Real) && !matches!(terms.sort(rhs), Sort::Real) {
        return false;
    }
    let Some(lhs_poly) = poly_real(terms, lhs, poly_memo) else {
        return false;
    };
    let Some(rhs_poly) = poly_real(terms, rhs, poly_memo) else {
        return false;
    };
    let mut q = lhs_poly;
    if q.add_assign(&rhs_poly.neg()).is_none() {
        return false;
    }

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
                return false;
            }
            let Atom::Computed(dag) = mono[0] else {
                return false;
            };
            computed = Some((dag, coeff.clone()));
        } else {
            mirror_part.accumulate(mono.clone(), coeff.clone());
        }
    }
    let Some((dag, a)) = computed else {
        return false;
    };

    // Mirror check: the leaf-polynomial part must be exactly -a times the
    // dag's exact-real mirror, so q = a·(to_real(dag) - mirror) + c0.
    let Some(mirror) = mirror_poly(terms, dag, mirror_memo) else {
        return false;
    };
    if mirror_part != mirror.scale(&-a.clone()) {
        return false;
    }

    // Certified bound on |a·(to_real(dag) - mirror)|.
    let Some(enclosure) = analyze(terms, dag, facts, enclosure_memo) else {
        return false;
    };
    let bound = a.abs() * &enclosure.err;

    is_refuted_by_bound(op, &c0, &bound)
}

#[cfg(test)]
mod tests {
    use super::*;
    use ay_core::Symbol;

    const F64: Sort = Sort::FloatingPoint(11, 53);

    /// Build the pieces shared by the tests: two Float64 leaves `x`, `y`
    /// with normality + `|·| <= 1` facts, the dag `z = fp.add RNE x y`, and
    /// the exact mirror `to_real(x) + to_real(y)`.
    struct Fixture {
        t: TermStore,
        rne: TermId,
        x: TermId,
        y: TermId,
        fact_x: TermId,
        fact_y: TermId,
        dag: TermId,
        mirror: TermId,
    }

    fn app(t: &mut TermStore, op: &str, args: Vec<TermId>, sort: Sort) -> TermId {
        t.mk_app(Symbol::named(op), args, sort)
    }

    fn rat(t: &mut TermStore, num: i64, den: i64) -> TermId {
        t.mk_rational(BigRational::new(BigInt::from(num), BigInt::from(den)))
    }

    /// `(and (fp.isNormal v) (<= (fp.to_real (fp.abs v)) bound))`.
    fn input_fact(t: &mut TermStore, v: TermId, bound: TermId) -> TermId {
        let is_normal = app(t, "fp.isNormal", vec![v], Sort::Bool);
        let abs_v = app(t, "fp.abs", vec![v], F64);
        let tr = app(t, "fp.to_real", vec![abs_v], Sort::Real);
        let le = app(t, "<=", vec![tr, bound], Sort::Bool);
        app(t, "and", vec![is_normal, le], Sort::Bool)
    }

    fn fixture() -> Fixture {
        let mut t = TermStore::new();
        let rne = t.mk_var("RNE", Sort::Uninterpreted("RoundingMode".to_string()));
        let x = t.mk_var("x", F64);
        let y = t.mk_var("y", F64);
        let one = rat(&mut t, 1, 1);
        let fact_x = input_fact(&mut t, x, one);
        let fact_y = input_fact(&mut t, y, one);
        let dag = app(&mut t, "fp.add", vec![rne, x, y], F64);
        let trx = app(&mut t, "fp.to_real", vec![x], Sort::Real);
        let tr_y = app(&mut t, "fp.to_real", vec![y], Sort::Real);
        let mirror = app(&mut t, "+", vec![trx, tr_y], Sort::Real);
        Fixture {
            t,
            rne,
            x,
            y,
            fact_x,
            fact_y,
            dag,
            mirror,
        }
    }

    /// `(>= (- (fp.to_real dag) mirror) claim)`.
    fn goal_ge(t: &mut TermStore, dag: TermId, mirror: TermId, claim: TermId) -> TermId {
        let tr_dag = app(t, "fp.to_real", vec![dag], Sort::Real);
        let diff = app(t, "-", vec![tr_dag, mirror], Sort::Real);
        app(t, ">=", vec![diff, claim], Sort::Bool)
    }

    /// The lemma clause: negation of every premise.
    fn lemma_clause(t: &mut TermStore, premises: &[TermId]) -> Vec<TermId> {
        premises.iter().map(|&p| t.mk_not_raw(p)).collect()
    }

    #[test]
    fn accepts_guard_claim_shape() {
        // z = fp.add RNE x y, |x|,|y| <= 1 ⇒ |to_real(z) - (x+y)| <= 2^-53;
        // the claim `>= 3/10` is strictly contradicted → valid lemma.
        let mut fx = fixture();
        let claim = rat(&mut fx.t, 3, 10);
        let goal = goal_ge(&mut fx.t, fx.dag, fx.mirror, claim);
        let clause = lemma_clause(&mut fx.t, &[fx.fact_x, fx.fact_y, goal]);
        validate_fp_forward_error(&fx.t, ProofId(0), &clause)
            .expect("guard-claim-shaped lemma must validate");
        assert!(recognize_fp_forward_error(&fx.t, &clause));
    }

    #[test]
    fn accepts_with_extra_premise_literals() {
        // The Generic lemma negates ALL resolvable assumptions; extra negated
        // premises beyond the needed refutation subset must be tolerated.
        let mut fx = fixture();
        let claim = rat(&mut fx.t, 3, 10);
        let goal = goal_ge(&mut fx.t, fx.dag, fx.mirror, claim);
        let w = fx.t.mk_var("w", F64);
        let extra = app(&mut fx.t, "fp.isNormal", vec![w], Sort::Bool);
        let clause = lemma_clause(&mut fx.t, &[fx.fact_x, extra, fx.fact_y, goal]);
        validate_fp_forward_error(&fx.t, ProofId(0), &clause)
            .expect("extra premise literals must not defeat validation");
    }

    #[test]
    fn rejects_missing_normality() {
        // Drop `fp.isNormal x`: to_real is unconstrained on NaN/±oo, so the
        // enclosure is unestablished — must fail closed.
        let mut fx = fixture();
        let one = rat(&mut fx.t, 1, 1);
        let abs_x = app(&mut fx.t, "fp.abs", vec![fx.x], F64);
        let tr = app(&mut fx.t, "fp.to_real", vec![abs_x], Sort::Real);
        let bound_only = app(&mut fx.t, "<=", vec![tr, one], Sort::Bool);
        let claim = rat(&mut fx.t, 3, 10);
        let goal = goal_ge(&mut fx.t, fx.dag, fx.mirror, claim);
        let clause = lemma_clause(&mut fx.t, &[bound_only, fx.fact_y, goal]);
        assert!(
            validate_fp_forward_error(&fx.t, ProofId(0), &clause).is_err(),
            "missing normality premise must reject"
        );
    }

    #[test]
    fn rejects_non_rne_op() {
        // The dag rounds with RTZ: the half-ulp model does not apply.
        let mut fx = fixture();
        let rtz =
            fx.t.mk_var("RTZ", Sort::Uninterpreted("RoundingMode".to_string()));
        let dag = app(&mut fx.t, "fp.add", vec![rtz, fx.x, fx.y], F64);
        let claim = rat(&mut fx.t, 3, 10);
        let goal = goal_ge(&mut fx.t, dag, fx.mirror, claim);
        let clause = lemma_clause(&mut fx.t, &[fx.fact_x, fx.fact_y, goal]);
        assert!(
            validate_fp_forward_error(&fx.t, ProofId(0), &clause).is_err(),
            "non-RNE rounded op must reject"
        );
    }

    #[test]
    fn rejects_claim_not_contradicted() {
        // TAMPERED CLAIM CONSTANT: `>= 2^-60` is below the certified bound
        // 2^-53 — the deviation is genuinely reachable, accepting would be a
        // false-UNSAT.
        let mut fx = fixture();
        let claim = rat(&mut fx.t, 1, 1i64 << 60);
        let goal = goal_ge(&mut fx.t, fx.dag, fx.mirror, claim);
        let clause = lemma_clause(&mut fx.t, &[fx.fact_x, fx.fact_y, goal]);
        assert!(
            validate_fp_forward_error(&fx.t, ProofId(0), &clause).is_err(),
            "a claim the bound does not contradict must reject"
        );
    }

    #[test]
    fn rejects_tampered_mirror() {
        // TAMPERED MIRROR: `to_real(x) + to_real(x)` is not the exact mirror
        // of `fp.add RNE x y` — the polynomial identity must fail.
        let mut fx = fixture();
        let trx = app(&mut fx.t, "fp.to_real", vec![fx.x], Sort::Real);
        let bad_mirror = app(&mut fx.t, "+", vec![trx, trx], Sort::Real);
        let claim = rat(&mut fx.t, 3, 10);
        let goal = goal_ge(&mut fx.t, fx.dag, bad_mirror, claim);
        let clause = lemma_clause(&mut fx.t, &[fx.fact_x, fx.fact_y, goal]);
        assert!(
            validate_fp_forward_error(&fx.t, ProofId(0), &clause).is_err(),
            "a tampered mirror polynomial must reject"
        );
    }

    #[test]
    fn rejects_overflow_range() {
        // Magnitude bounds of 2^1023 make the exact sum reach 2^1024 > 2^emax:
        // the no-overflow side condition fails and the lemma must reject.
        let mut fx = fixture();
        let huge =
            fx.t.mk_rational(BigRational::from_integer(BigInt::one() << 1023usize));
        let fact_x = input_fact(&mut fx.t, fx.x, huge);
        let fact_y = input_fact(&mut fx.t, fx.y, huge);
        let claim = rat(&mut fx.t, 3, 10);
        let goal = goal_ge(&mut fx.t, fx.dag, fx.mirror, claim);
        let clause = lemma_clause(&mut fx.t, &[fact_x, fact_y, goal]);
        assert!(
            validate_fp_forward_error(&fx.t, ProofId(0), &clause).is_err(),
            "an overflow-capable intermediate must reject"
        );
    }

    #[test]
    fn rejects_unknown_dag_op() {
        // fp.div is outside the supported dag ops — fail closed.
        let mut fx = fixture();
        let dag = app(&mut fx.t, "fp.div", vec![fx.rne, fx.x, fx.y], F64);
        let trx = app(&mut fx.t, "fp.to_real", vec![fx.x], Sort::Real);
        let tr_y = app(&mut fx.t, "fp.to_real", vec![fx.y], Sort::Real);
        let mirror = app(&mut fx.t, "/", vec![trx, tr_y], Sort::Real);
        let claim = rat(&mut fx.t, 3, 10);
        let goal = goal_ge(&mut fx.t, dag, mirror, claim);
        let clause = lemma_clause(&mut fx.t, &[fx.fact_x, fx.fact_y, goal]);
        assert!(
            validate_fp_forward_error(&fx.t, ProofId(0), &clause).is_err(),
            "an unknown dag op (fp.div) must fail closed"
        );
    }

    #[test]
    fn rejects_non_bool_literal() {
        // A malformed clause with a non-Bool literal is not un-negatable.
        let mut fx = fixture();
        let claim = rat(&mut fx.t, 3, 10);
        let goal = goal_ge(&mut fx.t, fx.dag, fx.mirror, claim);
        let mut clause = lemma_clause(&mut fx.t, &[fx.fact_x, fx.fact_y, goal]);
        clause.push(claim); // Real-sorted junk literal.
        assert!(
            validate_fp_forward_error(&fx.t, ProofId(0), &clause).is_err(),
            "a non-Bool literal must reject"
        );
    }

    #[test]
    fn rejects_facts_only_clause() {
        // No refutable goal comparison at all.
        let mut fx = fixture();
        let clause = lemma_clause(&mut fx.t, &[fx.fact_x, fx.fact_y]);
        assert!(
            validate_fp_forward_error(&fx.t, ProofId(0), &clause).is_err(),
            "a clause without a refuted goal must reject"
        );
        assert!(!recognize_fp_forward_error(&fx.t, &clause));
    }
}
