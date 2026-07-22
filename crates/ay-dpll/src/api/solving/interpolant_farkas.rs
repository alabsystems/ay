// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Certificate-based theory-lemma leaf interpolation (rank-4 increment 4).
//!
//! When a `TheoryLemma` proof leaf carries a Farkas certificate (rank-4
//! increment 2), its partial interpolant is derived from the certificate per
//! the labeled interpolation system for linear arithmetic (McMillan CAV'03,
//! D'Silva et al. VMCAI'10; OpenSMT LRA interpolation):
//!
//! - **Equality-implication conflicts** (the increment-2 affine shape:
//!   weighted equality rows plus at most one disequality refuted by a
//!   both-branch case split): the partial interpolant is the A-side equality
//!   system projected onto the shared variables by Gaussian elimination when
//!   the disequality is B-labeled or absent, and the negated B-side projection
//!   when the disequality is A-labeled. For linear equality systems the
//!   eliminated system generates ALL implied shared-only equalities
//!   (elimination ideal), so the certificate's A-part combination is entailed
//!   by the projection — the node contract holds structurally:
//!   1. `A /\ not(C|A) |= I` — the projection is a linear consequence of
//!      the A-side rows;
//!   2. `B /\ not(C|B) /\ I |= false` — the certificate's weighted sum
//!      factors through the shared projection (both case-split branches).
//! - **Pure inequality conflicts**: the A-part weighted sum (each A-labeled
//!   conflict inequality scaled by its Farkas coefficient), the standard
//!   Farkas-based partial interpolant.
//!
//! Shared (AB-labeled) atoms follow the labeling system in use: McMillan
//! (`Strongest`) labels them `b`, McMillan' (`Weakest`) labels them `a`, and
//! Pudlak (`Default`) labels them `ab` — an `ab` literal participates in BOTH
//! side restrictions of the node contract, so assigning its row to the B side
//! keeps both contract obligations intact.
//!
//! SOUNDNESS: every certificate is semantically re-verified
//! (`verify_farkas_conflict_lits_full`) BEFORE use; any off-shape leaf
//! (uncertified, non-affine, unlabeled atoms, multiple disequalities, mixed
//! equality/inequality support) returns `None`, keeping the previous
//! behavior. The final interpolant is additionally validated by the
//! consumer's Craig checks (ay-chc `is_valid_interpolant_until`) before use.

use std::cell::Cell;
use std::collections::BTreeMap;

use ay_core::kani_compat::DetHashSet as HashSet;
use ay_core::proof_validation::verify_farkas_conflict_lits_full;
use ay_core::term::{Constant, TermData};
use ay_core::{FarkasAnnotation, Sort, Symbol, TermId, TermStore, TheoryLit};
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};

use crate::api::types::InterpolantStrength;

// ---------------------------------------------------------------------------
// Per-traversal stats (thread-local: a traversal runs on one thread)
// ---------------------------------------------------------------------------

/// Counters for certificate-leaf interpolation within one proof traversal.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub(crate) struct CertLeafStats {
    /// `TheoryLemma` leaves carrying a Farkas annotation.
    pub attempted: usize,
    /// Certificates that passed semantic re-verification.
    pub verified: usize,
    /// Leaves whose partial interpolant was derived from the certificate.
    pub served: usize,
}

thread_local! {
    static CERT_LEAF_STATS: Cell<CertLeafStats> = const { Cell::new(CertLeafStats {
        attempted: 0,
        verified: 0,
        served: 0,
    }) };
}

/// Reset the per-traversal certificate-leaf counters.
pub(crate) fn reset_cert_leaf_stats() {
    CERT_LEAF_STATS.with(|c| c.set(CertLeafStats::default()));
}

/// Counters from the most recent traversal on this thread (test/diagnostic
/// observability; the spike test asserts the production cert-leaf counts).
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) fn last_cert_leaf_stats() -> CertLeafStats {
    CERT_LEAF_STATS.with(Cell::get)
}

fn bump(f: impl Fn(&mut CertLeafStats)) {
    CERT_LEAF_STATS.with(|c| {
        let mut s = c.get();
        f(&mut s);
        c.set(s);
    });
}

// ---------------------------------------------------------------------------
// Partition view (atom/variable coloring context from the traversal)
// ---------------------------------------------------------------------------

/// Coloring context for certificate leaves, borrowed from the traversal.
pub(crate) struct CertPartition<'a> {
    /// Atomic predicates occurring in the A partition.
    pub a_atoms: &'a HashSet<TermId>,
    /// Atomic predicates occurring in the B partition.
    pub b_atoms: &'a HashSet<TermId>,
    /// Variables occurring in the A partition.
    pub a_vars: &'a HashSet<TermId>,
    /// Variables occurring in the B partition.
    pub b_vars: &'a HashSet<TermId>,
    /// Variables shared between A and B.
    pub shared_vars: &'a HashSet<TermId>,
}

/// Occurrence class of an atom relative to the (A, B) partition.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum AtomClass {
    /// Occurs only in A.
    A,
    /// Occurs only in B.
    B,
    /// Occurs in both (shared).
    Ab,
}

impl CertPartition<'_> {
    /// Occurrence-based atom class with a variable-occurrence fallback for
    /// synthetic atoms (same scheme the interpolation spike validated).
    /// Returns `None` for unclassifiable atoms (certificate path bails).
    pub(crate) fn class_of_atom(&self, terms: &TermStore, atom: TermId) -> Option<AtomClass> {
        match (self.a_atoms.contains(&atom), self.b_atoms.contains(&atom)) {
            (true, true) => Some(AtomClass::Ab),
            (true, false) => Some(AtomClass::A),
            (false, true) => Some(AtomClass::B),
            (false, false) => {
                let mut vars = HashSet::default();
                collect_var_ids(terms, atom, &mut vars);
                if vars.is_empty() {
                    return Some(AtomClass::Ab);
                }
                if vars.iter().all(|v| self.shared_vars.contains(v)) {
                    Some(AtomClass::Ab)
                } else if vars.iter().all(|v| self.a_vars.contains(v)) {
                    Some(AtomClass::A)
                } else if vars.iter().all(|v| self.b_vars.contains(v)) {
                    Some(AtomClass::B)
                } else {
                    None
                }
            }
        }
    }
}

/// Side assignment of an atom class under the labeling system in use:
/// shared atoms are labeled `b` by McMillan (`Strongest`), `a` by McMillan'
/// (`Weakest`), and `ab` by Pudlak (`Default`). An `ab` literal belongs to
/// both side restrictions of the node contract, so assigning its (shared-only)
/// row to the B side preserves both contract obligations.
fn side_is_a(class: AtomClass, strength: InterpolantStrength) -> bool {
    match class {
        AtomClass::A => true,
        AtomClass::B => false,
        AtomClass::Ab => matches!(strength, InterpolantStrength::Weakest),
    }
}

fn collect_var_ids(terms: &TermStore, tid: TermId, out: &mut HashSet<TermId>) {
    let mut stack = vec![tid];
    let mut seen: HashSet<TermId> = HashSet::default();
    while let Some(t) = stack.pop() {
        if !seen.insert(t) {
            continue;
        }
        match terms.get(t) {
            TermData::Var(_, _) => {
                out.insert(t);
            }
            TermData::Const(_) => {}
            _ => {
                for child in terms.children(t) {
                    stack.push(child);
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Linear parsing
// ---------------------------------------------------------------------------

/// A linear combination `sum coeffs[v]*v + constant` over arithmetic
/// variables. Only genuine `Var` terms may carry coefficients; any opaque
/// subterm fails the parse (certificate path bails).
#[derive(Debug, Clone, Default)]
struct LinComb {
    coeffs: BTreeMap<TermId, BigRational>,
    constant: BigRational,
}

impl LinComb {
    fn add_scaled(&mut self, other: &Self, scale: &BigRational) {
        if scale.is_zero() {
            return;
        }
        self.constant += scale * &other.constant;
        for (v, c) in &other.coeffs {
            let should_remove = {
                let entry = self.coeffs.entry(*v).or_insert_with(BigRational::zero);
                *entry += scale * c;
                entry.is_zero()
            };
            if should_remove {
                self.coeffs.remove(v);
            }
        }
    }
}

/// Parse an arithmetic term as a linear combination. Supports `Var`,
/// integer/rational constants, `+`, unary/n-ary `-`, and products with at
/// most one non-constant factor. Returns `false` on anything else.
fn linear_of(terms: &TermStore, tid: TermId, mult: &BigRational, out: &mut LinComb) -> bool {
    match terms.get(tid) {
        TermData::Var(_, _) if matches!(terms.sort(tid), Sort::Int | Sort::Real) => {
            let should_remove = {
                let entry = out.coeffs.entry(tid).or_insert_with(BigRational::zero);
                *entry += mult;
                entry.is_zero()
            };
            if should_remove {
                out.coeffs.remove(&tid);
            }
            true
        }
        TermData::Const(Constant::Int(c)) => {
            out.constant += mult * BigRational::from(c.clone());
            true
        }
        TermData::Const(Constant::Rational(r)) => {
            out.constant += mult * &r.0;
            true
        }
        TermData::App(Symbol::Named(name), args) => match name.as_str() {
            "+" => args.iter().all(|&a| linear_of(terms, a, mult, out)),
            "-" if args.len() == 1 => {
                let neg = -mult.clone();
                linear_of(terms, args[0], &neg, out)
            }
            "-" if args.len() >= 2 => {
                if !linear_of(terms, args[0], mult, out) {
                    return false;
                }
                let neg = -mult.clone();
                args[1..].iter().all(|&a| linear_of(terms, a, &neg, out))
            }
            "*" => {
                // Product of constants with at most one non-constant factor.
                let mut const_part = BigRational::one();
                let mut non_const: Option<TermId> = None;
                for &a in args {
                    match terms.get(a) {
                        TermData::Const(Constant::Int(c)) => {
                            const_part *= BigRational::from(c.clone());
                        }
                        TermData::Const(Constant::Rational(r)) => const_part *= &r.0,
                        _ if non_const.is_none() => non_const = Some(a),
                        _ => return false,
                    }
                }
                match non_const {
                    Some(sub) => {
                        let m = mult * const_part;
                        linear_of(terms, sub, &m, out)
                    }
                    None => {
                        out.constant += mult * const_part;
                        true
                    }
                }
            }
            _ => false,
        },
        _ => false,
    }
}

/// `lhs - rhs` of a binary arithmetic application as a linear combination.
fn linear_difference(terms: &TermStore, lhs: TermId, rhs: TermId) -> Option<LinComb> {
    let mut out = LinComb::default();
    if !linear_of(terms, lhs, &BigRational::one(), &mut out) {
        return None;
    }
    let neg_one = -BigRational::one();
    if !linear_of(terms, rhs, &neg_one, &mut out) {
        return None;
    }
    Some(out)
}

// ---------------------------------------------------------------------------
// Conflict-literal decoding
// ---------------------------------------------------------------------------

/// What a nonzero-weight clause literal asserts inside the theory conflict
/// (the conflict asserts the NEGATION of every clause literal).
enum ConflictAtom {
    /// An asserted linear equality `lin = 0` (from a negated `=` literal).
    EqualityRow(LinComb),
    /// The asserted disequality `lin != 0` (from a positive `=` literal).
    Disequality(LinComb),
    /// An asserted inequality `lin <= 0` (`strict`: `< 0`).
    Inequality { lin: LinComb, strict: bool },
}

/// Decode a clause literal into the constraint its negation asserts.
fn decode_conflict_literal(terms: &TermStore, lit: TermId) -> Option<ConflictAtom> {
    // The conflict asserts NOT(lit): strip negations, tracking the asserted
    // truth value of the underlying atom.
    let mut atom = lit;
    let mut value = false;
    while let TermData::Not(inner) = terms.get(atom) {
        atom = *inner;
        value = !value;
    }
    let TermData::App(Symbol::Named(name), args) = terms.get(atom) else {
        return None;
    };
    if args.len() != 2 {
        return None;
    }
    let (lhs, rhs) = (args[0], args[1]);
    match (name.as_str(), value) {
        ("=", v) => {
            // Arithmetic equalities only (Bool `=` is not a linear row).
            if !matches!(terms.sort(lhs), Sort::Int | Sort::Real) {
                return None;
            }
            if v {
                Some(ConflictAtom::EqualityRow(linear_difference(
                    terms, lhs, rhs,
                )?))
            } else {
                Some(ConflictAtom::Disequality(linear_difference(
                    terms, lhs, rhs,
                )?))
            }
        }
        ("<", true) | (">=", false) => Some(ConflictAtom::Inequality {
            lin: linear_difference(terms, lhs, rhs)?,
            strict: true,
        }),
        ("<=", true) | (">", false) => Some(ConflictAtom::Inequality {
            lin: linear_difference(terms, lhs, rhs)?,
            strict: false,
        }),
        (">", true) | ("<=", false) => Some(ConflictAtom::Inequality {
            lin: linear_difference(terms, rhs, lhs)?,
            strict: true,
        }),
        (">=", true) | ("<", false) => Some(ConflictAtom::Inequality {
            lin: linear_difference(terms, rhs, lhs)?,
            strict: false,
        }),
        _ => None,
    }
}

/// Strip negation, returning the underlying atom.
fn atom_of_literal(terms: &TermStore, lit: TermId) -> TermId {
    let mut atom = lit;
    while let TermData::Not(inner) = terms.get(atom) {
        atom = *inner;
    }
    atom
}

// ---------------------------------------------------------------------------
// Direct semantic verification of equality-implication conflicts
// ---------------------------------------------------------------------------

/// Echelon basis of a linear equality row space (each row asserts `lin = 0`).
struct EchelonBasis {
    /// Rows normalized to lead coefficient 1, in elimination order.
    rows: Vec<(TermId, LinComb)>,
    /// The row space contains `0 = c` with `c != 0` (inconsistent system).
    inconsistent: bool,
}

impl EchelonBasis {
    fn build(rows: &[LinComb]) -> Self {
        let mut basis: Vec<(TermId, LinComb)> = Vec::new();
        let mut inconsistent = false;
        for row in rows {
            let mut r = row.clone();
            Self::reduce_in_place(&basis, &mut r);
            if let Some((&lead, _)) = r.coeffs.iter().next() {
                let inv = BigRational::one() / r.coeffs[&lead].clone();
                let mut normalized = LinComb::default();
                normalized.add_scaled(&r, &inv);
                basis.push((lead, normalized));
            } else if !r.constant.is_zero() {
                inconsistent = true;
            }
        }
        Self {
            rows: basis,
            inconsistent,
        }
    }

    fn reduce_in_place(basis: &[(TermId, LinComb)], target: &mut LinComb) {
        for (lead, row) in basis {
            if let Some(c) = target.coeffs.get(lead).cloned() {
                let scale = -c;
                target.add_scaled(row, &scale);
            }
        }
    }

    /// Whether `lin = 0` is implied by the row space (span membership; for a
    /// consistent linear equality system this is COMPLETE: implied equalities
    /// are exactly the span).
    fn implies(&self, lin: &LinComb) -> bool {
        if self.inconsistent {
            return true;
        }
        let mut residual = lin.clone();
        Self::reduce_in_place(&self.rows, &mut residual);
        residual.coeffs.is_empty() && residual.constant.is_zero()
    }
}

/// Complete semantic check for the equality-implication conflict shape:
/// the asserted rows must imply the disequality's equality (or be outright
/// inconsistent when no disequality participates).
///
/// This replaces the generic Farkas orientation search for this shape: that
/// search is capped (#W16-5) and incomplete beyond ~10 weighted equalities,
/// while span membership decides the affine-equality fragment exactly.
fn verify_equality_conflict(rows: &[LinComb], diseq: Option<&LinComb>) -> bool {
    let basis = EchelonBasis::build(rows);
    match diseq {
        Some(lin) => basis.implies(lin),
        None => basis.inconsistent,
    }
}

// ---------------------------------------------------------------------------
// Equality-system projection (Gaussian elimination of non-shared variables)
// ---------------------------------------------------------------------------

/// Result of projecting an equality system onto the shared variables.
enum Projection {
    /// The system itself is inconsistent (`0 = c`, `c != 0`).
    Inconsistent,
    /// Surviving shared-only equality rows (possibly empty).
    Rows(Vec<LinComb>),
}

/// Eliminate every non-shared variable from `rows` (each row asserts
/// `lin = 0`). The surviving rows generate ALL implied equalities over the
/// shared variables (the elimination ideal of a linear system).
fn project_onto_shared(mut rows: Vec<LinComb>, shared: &HashSet<TermId>) -> Projection {
    let local_vars: Vec<TermId> = {
        let mut vs: Vec<TermId> = rows
            .iter()
            .flat_map(|r| r.coeffs.keys().copied())
            .filter(|v| !shared.contains(v))
            .collect();
        vs.sort_unstable();
        vs.dedup();
        vs
    };
    for v in local_vars {
        let Some(pivot_idx) = rows.iter().position(|r| r.coeffs.contains_key(&v)) else {
            continue;
        };
        let pivot = rows.remove(pivot_idx);
        let pc = pivot.coeffs[&v].clone();
        for row in &mut rows {
            let Some(rc) = row.coeffs.get(&v).cloned() else {
                continue;
            };
            // row := row - pivot * (rc / pc)
            let scale = -(rc / &pc);
            row.add_scaled(&pivot, &scale);
        }
    }
    let mut surviving = Vec::new();
    for row in rows {
        if row.coeffs.is_empty() {
            if !row.constant.is_zero() {
                return Projection::Inconsistent;
            }
            continue; // trivial 0 = 0
        }
        surviving.push(row);
    }
    Projection::Rows(surviving)
}

// ---------------------------------------------------------------------------
// Term rendering
// ---------------------------------------------------------------------------

/// Integerize a linear combination: scale by the LCM of denominators, divide
/// by the GCD, and orient so the lead coefficient is positive. Returns the
/// integer (coeff, var) pairs and the integer constant (same scaling).
fn integerize(lin: &LinComb) -> (Vec<(BigInt, TermId)>, BigInt) {
    let mut denom_lcm = BigInt::one();
    for c in lin.coeffs.values().chain(std::iter::once(&lin.constant)) {
        denom_lcm = num_integer::lcm(denom_lcm, c.denom().clone());
    }
    let scaled: Vec<(BigInt, TermId)> = lin
        .coeffs
        .iter()
        .map(|(&v, c)| ((c * BigRational::from(denom_lcm.clone())).to_integer(), v))
        .collect();
    let mut constant = (&lin.constant * BigRational::from(denom_lcm)).to_integer();
    let mut gcd = constant.magnitude().clone();
    for (c, _) in &scaled {
        gcd = num_integer::gcd(gcd, c.magnitude().clone());
    }
    let gcd = BigInt::from(gcd);
    let mut scaled = scaled;
    if gcd > BigInt::one() {
        for (c, _) in &mut scaled {
            *c /= &gcd;
        }
        constant /= &gcd;
    }
    // Orient: lead (lowest-TermId) coefficient positive.
    if scaled.first().is_some_and(|(c, _)| c.is_negative()) {
        for (c, _) in &mut scaled {
            *c = -c.clone();
        }
        constant = -constant;
    }
    (scaled, constant)
}

/// Render `lin = 0` as an equality term `sum = -constant`.
fn row_to_eq_term(terms: &mut TermStore, lin: &LinComb) -> TermId {
    let (scaled, constant) = integerize(lin);
    let sum = render_sum(terms, &scaled);
    let rhs = terms.mk_int(-constant);
    terms.mk_eq(sum, rhs)
}

/// Render `lin <= 0` / `lin < 0` as an inequality term `sum <= -constant`.
fn comb_to_ineq_term(terms: &mut TermStore, lin: &LinComb, strict: bool) -> TermId {
    let mut denom_lcm = BigInt::one();
    for c in lin.coeffs.values().chain(std::iter::once(&lin.constant)) {
        denom_lcm = num_integer::lcm(denom_lcm, c.denom().clone());
    }
    let scaled: Vec<(BigInt, TermId)> = lin
        .coeffs
        .iter()
        .map(|(&v, c)| ((c * BigRational::from(denom_lcm.clone())).to_integer(), v))
        .collect();
    let constant = (&lin.constant * BigRational::from(denom_lcm)).to_integer();
    let sum = render_sum(terms, &scaled);
    let rhs = terms.mk_int(-constant);
    if strict {
        terms.mk_lt(sum, rhs)
    } else {
        terms.mk_le(sum, rhs)
    }
}

fn render_sum(terms: &mut TermStore, scaled: &[(BigInt, TermId)]) -> TermId {
    let mut parts = Vec::with_capacity(scaled.len());
    for (c, v) in scaled {
        if c == &BigInt::one() {
            parts.push(*v);
        } else {
            let coef = terms.mk_int(c.clone());
            parts.push(terms.mk_mul(vec![coef, *v]));
        }
    }
    if parts.len() == 1 {
        parts[0]
    } else {
        terms.mk_add(parts)
    }
}

// ---------------------------------------------------------------------------
// The certificate-leaf rule
// ---------------------------------------------------------------------------

/// Derive the partial interpolant of a Farkas-certified theory lemma.
///
/// Returns `None` whenever the certificate fails re-verification or the
/// conflict is outside the supported affine shapes; the caller keeps the
/// previous (occurrence-projection) behavior for those leaves.
#[allow(clippy::too_many_arguments)]
pub(crate) fn certificate_lemma_interpolant(
    terms: &mut TermStore,
    clause: &[TermId],
    farkas: &FarkasAnnotation,
    part: &CertPartition<'_>,
    strength: InterpolantStrength,
    true_tid: TermId,
    false_tid: TermId,
) -> Option<TermId> {
    bump(|s| s.attempted += 1);
    if farkas.coefficients.len() != clause.len() {
        return None;
    }

    // Decode + label the support (nonzero-weight literals).
    let zero = num_rational::Rational64::from(0);
    let mut a_rows: Vec<LinComb> = Vec::new();
    let mut b_rows: Vec<LinComb> = Vec::new();
    let mut a_ineqs: Vec<(LinComb, bool, BigRational)> = Vec::new();
    // Unified weighted support for the mixed equality/inequality rule
    // (rank-4 inc-6): every nonzero-weight row with its certificate weight,
    // side label, and shape (the disequality stays tracked separately).
    let mut support_rows: Vec<SupportRow> = Vec::new();
    let mut support_a = 0usize;
    let mut support_b = 0usize;
    let mut eq_rows = 0usize;
    let mut ineqs = 0usize;
    let mut diseq: Option<(LinComb, bool)> = None;
    for (&lit, coef) in clause.iter().zip(farkas.coefficients.iter()) {
        if *coef == zero {
            continue;
        }
        let atom = atom_of_literal(terms, lit);
        let class = part.class_of_atom(terms, atom)?;
        let side_a = side_is_a(class, strength);
        if side_a {
            support_a += 1;
        } else {
            support_b += 1;
        }
        let lambda = BigRational::new(BigInt::from(*coef.numer()), BigInt::from(*coef.denom()));
        match decode_conflict_literal(terms, lit) {
            Some(ConflictAtom::EqualityRow(row)) => {
                eq_rows += 1;
                support_rows.push(SupportRow {
                    lin: row.clone(),
                    strict: false,
                    is_eq: true,
                    lambda,
                    side_a,
                });
                if side_a {
                    a_rows.push(row);
                } else {
                    b_rows.push(row);
                }
            }
            Some(ConflictAtom::Disequality(lin)) => {
                if diseq.is_some() {
                    return None;
                }
                diseq = Some((lin, side_a));
            }
            Some(ConflictAtom::Inequality { lin, strict }) => {
                ineqs += 1;
                support_rows.push(SupportRow {
                    lin: lin.clone(),
                    strict,
                    is_eq: false,
                    lambda: lambda.clone(),
                    side_a,
                });
                if side_a {
                    a_ineqs.push((lin, strict, lambda));
                }
            }
            None => {
                return None;
            }
        }
    }
    if support_a == 0 && support_b == 0 {
        return None;
    }

    // VERIFY the conflict before trusting it (rank-4 covenant).
    //
    // - Equality-implication shape: span membership decides the affine
    //   fragment COMPLETELY (`verify_equality_conflict`); the generic Farkas
    //   orientation search (`verify_farkas_conflict_lits_full`) is capped at
    //   ~10 weighted equalities (#W16-5) and rejects the larger lustre-class
    //   equality networks, so it is tried first and the span check decides
    //   what its cap leaves behind.
    // - Mixed shape (inc-17): the exact affine solve
    //   (`solve_affine_refutation`) decides what the capped orientation
    //   search leaves behind — EqDiffVar-reduced guarded-eq networks carry
    //   dozens of weighted equalities per conflict.
    // - Inequality shape: the weighted-sum verifier is exact (one orientation
    //   per literal).
    let is_eq_shape = ineqs == 0;
    let verified = {
        let conflict: Vec<TheoryLit> = clause.iter().map(|&l| TheoryLit::new(l, false)).collect();
        match verify_farkas_conflict_lits_full(terms, &conflict, farkas) {
            Ok(()) => true,
            Err(_) if is_eq_shape => {
                let all_rows: Vec<LinComb> = a_rows.iter().chain(b_rows.iter()).cloned().collect();
                verify_equality_conflict(&all_rows, diseq.as_ref().map(|(l, _)| l))
            }
            // Mixed equality/inequality conflict: the exact affine solve
            // is a complete decision procedure for this shape, so a
            // refutation found here is no less verified than the
            // orientation search's.
            Err(_) if diseq.is_none() => solve_affine_refutation(&support_rows).is_some(),
            Err(_) => false,
        }
    };
    if !verified {
        return None;
    }
    bump(|s| s.verified += 1);

    // One-sided supports: the refutation lives entirely in one side
    // restriction, so the partial interpolant is a constant.
    if support_b == 0 {
        bump(|s| s.served += 1);
        return Some(false_tid);
    }
    if support_a == 0 {
        bump(|s| s.served += 1);
        return Some(true_tid);
    }

    let result = if is_eq_shape {
        // Equality-implication shape (weighted rows + optional disequality).
        equality_partial_interpolant(
            terms,
            a_rows,
            b_rows,
            diseq.map(|(_, side_a)| side_a),
            part.shared_vars,
            true_tid,
            false_tid,
        )
    } else if eq_rows == 0 && diseq.is_none() {
        // Pure inequality conflict: the A-part weighted sum.
        inequality_partial_interpolant(terms, &a_ineqs, part.shared_vars, true_tid, false_tid)
    } else if diseq.is_none() {
        // Mixed equality+inequality conflict (rank-4 inc-6): the executor's
        // lia_generic conflicts mix equality rows with bound inequalities.
        // The general Farkas-sum rule applies once each equality row is
        // ORIENTED the way the certificate's contradiction uses it (the
        // verifier searches orientations; re-derive one here), then the
        // partial interpolant is the A-part weighted sum, exactly like the
        // pure-inequality rule.
        mixed_partial_interpolant(terms, &support_rows, part.shared_vars, true_tid, false_tid)
    } else {
        None
    };
    if result.is_some() {
        bump(|s| s.served += 1);
    }
    result
}

/// Partial interpolant for an equality-implication conflict.
fn equality_partial_interpolant(
    terms: &mut TermStore,
    a_rows: Vec<LinComb>,
    b_rows: Vec<LinComb>,
    diseq_on_a: Option<bool>,
    shared_vars: &HashSet<TermId>,
    true_tid: TermId,
    false_tid: TermId,
) -> Option<TermId> {
    if diseq_on_a == Some(true) {
        // Disequality is A-labeled: the interpolant is the NEGATED B-side
        // shared projection. Contract (1) holds because for either case-split
        // branch the certificate's B-part combination is entailed by the
        // projection and contradicts `A /\ not(C|A)`; contract (2) holds
        // because the projection is a consequence of the B-side rows.
        match project_onto_shared(b_rows, shared_vars) {
            Projection::Inconsistent => {
                // B-side rows alone are contradictory: `true` suffices.
                Some(true_tid)
            }
            Projection::Rows(rows) if rows.is_empty() => {
                // No shared consequences: the refutation lives in the A side.
                Some(false_tid)
            }
            Projection::Rows(rows) => {
                let row_terms: Vec<TermId> =
                    rows.iter().map(|r| row_to_eq_term(terms, r)).collect();
                let conj = if row_terms.len() == 1 {
                    row_terms[0]
                } else {
                    terms.mk_and(row_terms)
                };
                Some(terms.mk_not(conj))
            }
        }
    } else {
        // Disequality B-labeled or absent: the interpolant is the A-side
        // shared projection (every certificate A-part combination over shared
        // variables is in its span).
        match project_onto_shared(a_rows, shared_vars) {
            Projection::Inconsistent => {
                // A-side rows alone are contradictory: `false` is exact.
                Some(false_tid)
            }
            Projection::Rows(rows) if rows.is_empty() => {
                // No shared consequences: the refutation lives in the B side.
                Some(true_tid)
            }
            Projection::Rows(rows) => {
                let row_terms: Vec<TermId> =
                    rows.iter().map(|r| row_to_eq_term(terms, r)).collect();
                Some(if row_terms.len() == 1 {
                    row_terms[0]
                } else {
                    terms.mk_and(row_terms)
                })
            }
        }
    }
}

/// One nonzero-weight affine constraint of a certified conflict, with its
/// certificate weight and side label (rank-4 inc-6, mixed-shape rule).
struct SupportRow {
    /// The asserted row: `lin = 0` for equalities, `lin <= 0` (`< 0` when
    /// `strict`) for inequalities, as decoded by `decode_conflict_literal`.
    lin: LinComb,
    strict: bool,
    is_eq: bool,
    lambda: BigRational,
    side_a: bool,
}

/// Exact affine refutation for a mixed equality/inequality support
/// (rank-4 inc-17, replacing the capped ±λ orientation search).
///
/// Inequality rows keep their certificate weights `λ >= 0` and fixed
/// orientation; an EQUALITY row entails every real multiple of itself, so
/// its multiplier is FREE. Instead of searching orientations (exponential in
/// the equality count — the EqDiffVar-reduced guarded-eq networks carry far
/// more than the old 10-equality cap), solve
///
///   Σ μ_i E_i  =  -(Σ λ_j I_j)   on the variable parts
///
/// exactly by Gaussian elimination with multiplier tracking. The refutation
/// is valid iff the variable parts cancel and the resulting constant `c`
/// contradicts (`c > 0`, or `c >= 0` when a strict inequality contributed) —
/// the same threshold as the semantic verifier's `is_contradiction`. When
/// the equality rows are inconsistent ON THEIR OWN (elimination yields
/// `0 = c`, `c != 0`), the tracked kernel combination is itself the
/// refutation (inequality multipliers zero).
///
/// Returns per-support-row multipliers: the certificate λ for inequalities,
/// the solved μ (possibly zero) for equalities. Completeness relative to
/// the old search: any contradicting ±λ orientation IS a solution of the
/// linear system, and the achievable constant is unique modulo the kernel
/// (a kernel row with nonzero constant is the inconsistent case above), so
/// every previously-found refutation is still found.
fn solve_affine_refutation(support: &[SupportRow]) -> Option<Vec<BigRational>> {
    // R = weighted inequality sum; strict iff any strict inequality.
    // The Farkas precondition λ >= 0 applies to INEQUALITY rows only (an
    // equality entails any real multiple); the strict verifier enforces it
    // via the annotation-shape check, which this exact fallback bypasses,
    // so re-check it here.
    let mut r = LinComb::default();
    let mut strict = false;
    for row in support.iter().filter(|row| !row.is_eq) {
        if row.lambda < BigRational::zero() {
            return None;
        }
        r.add_scaled(&row.lin, &row.lambda);
        strict = strict || row.strict;
    }

    // Tracked echelon basis over the equality rows: each basis row carries
    // its combination over original support indices.
    struct TrackedRow {
        lead: TermId,
        lin: LinComb,
        comb: BTreeMap<usize, BigRational>,
    }
    fn comb_add_scaled(
        target: &mut BTreeMap<usize, BigRational>,
        other: &BTreeMap<usize, BigRational>,
        scale: &BigRational,
    ) {
        for (i, c) in other {
            let entry = target.entry(*i).or_insert_with(BigRational::zero);
            *entry += scale * c;
            if entry.is_zero() {
                target.remove(i);
            }
        }
    }
    let mut basis: Vec<TrackedRow> = Vec::new();
    let mut kernel_inconsistent: Option<(BTreeMap<usize, BigRational>, BigRational)> = None;
    for (idx, row) in support.iter().enumerate().filter(|(_, row)| row.is_eq) {
        let mut lin = row.lin.clone();
        let mut comb: BTreeMap<usize, BigRational> = BTreeMap::new();
        comb.insert(idx, BigRational::one());
        for b in &basis {
            if let Some(c) = lin.coeffs.get(&b.lead).cloned() {
                let scale = -c;
                lin.add_scaled(&b.lin, &scale);
                comb_add_scaled(&mut comb, &b.comb, &scale);
            }
        }
        if let Some((&lead, _)) = lin.coeffs.iter().next() {
            let inv = BigRational::one() / lin.coeffs[&lead].clone();
            let mut nlin = LinComb::default();
            nlin.add_scaled(&lin, &inv);
            let mut ncomb = BTreeMap::new();
            comb_add_scaled(&mut ncomb, &comb, &inv);
            basis.push(TrackedRow {
                lead,
                lin: nlin,
                comb: ncomb,
            });
        } else if !lin.constant.is_zero() && kernel_inconsistent.is_none() {
            kernel_inconsistent = Some((comb, lin.constant.clone()));
        }
    }

    let mut multipliers = vec![BigRational::zero(); support.len()];
    if let Some((comb, constant)) = kernel_inconsistent {
        // The equalities alone are inconsistent: scale the kernel row so the
        // combined constant is positive (`0 = c` asserted with `c > 0`).
        let scale = if constant > BigRational::zero() {
            BigRational::one()
        } else {
            -BigRational::one()
        };
        for (i, c) in comb {
            multipliers[i] = c * &scale;
        }
        return Some(multipliers);
    }

    // resid = R + Σ μ_i E_i with μ chosen to eliminate R's variables.
    let mut resid = r;
    let mut used: BTreeMap<usize, BigRational> = BTreeMap::new();
    for b in &basis {
        if let Some(c) = resid.coeffs.get(&b.lead).cloned() {
            let scale = -c;
            resid.add_scaled(&b.lin, &scale);
            comb_add_scaled(&mut used, &b.comb, &scale);
        }
    }
    if !resid.coeffs.is_empty() {
        return None; // variable parts cannot cancel: no affine refutation
    }
    let contradicts = if strict {
        resid.constant >= BigRational::zero()
    } else {
        resid.constant > BigRational::zero()
    };
    if !contradicts {
        return None;
    }
    for (idx, row) in support.iter().enumerate() {
        if !row.is_eq {
            multipliers[idx] = row.lambda.clone();
        }
    }
    for (i, m) in used {
        multipliers[i] = m;
    }
    Some(multipliers)
}

/// Partial interpolant for a mixed equality/inequality conflict with no
/// disequality (rank-4 inc-6; exact multipliers since inc-17): solve the
/// affine refutation (equality multipliers free, inequality weights from
/// the certificate), then emit the A-part of that very combination — the
/// standard Farkas partial interpolant, with equality rows contributing
/// their (signed) multiple.
///
/// Node contract: (1) `A /\ not(C|A)` asserts every A-labeled row, and a
/// nonnegative combination of its inequalities plus signed multiples of its
/// equalities entails the A-part sum. (2) the B-part sum is entailed by
/// `B /\ not(C|B)` the same way, and A-part + B-part is the refutation's
/// contradiction, so the conjunction with the A-part interpolant is UNSAT.
fn mixed_partial_interpolant(
    terms: &mut TermStore,
    support: &[SupportRow],
    shared_vars: &HashSet<TermId>,
    true_tid: TermId,
    false_tid: TermId,
) -> Option<TermId> {
    let multipliers = solve_affine_refutation(support)?;
    let mut sum = LinComb::default();
    let mut strict = false;
    for (row, m) in support.iter().zip(multipliers.iter()) {
        if !row.side_a {
            continue;
        }
        sum.add_scaled(&row.lin, m);
        strict = strict || (row.strict && !row.is_eq && !m.is_zero());
    }
    if sum.coeffs.is_empty() {
        // Ground A-part: evaluate `constant (<|<=) 0` directly.
        let holds = if strict {
            sum.constant < BigRational::zero()
        } else {
            sum.constant <= BigRational::zero()
        };
        return Some(if holds { true_tid } else { false_tid });
    }
    // Defensive locality check, same as the pure-inequality rule: any
    // non-shared variable surviving the A-part sum means the labeling
    // drifted; bail instead of emitting a non-local interpolant.
    if !sum.coeffs.keys().all(|v| shared_vars.contains(v)) {
        return None;
    }
    Some(comb_to_ineq_term(terms, &sum, strict))
}

/// Partial interpolant for a pure inequality conflict: the A-part weighted
/// sum `sum lambda_i * (lin_i <= 0)` (strict when any strict contributor).
fn inequality_partial_interpolant(
    terms: &mut TermStore,
    a_ineqs: &[(LinComb, bool, BigRational)],
    shared_vars: &HashSet<TermId>,
    true_tid: TermId,
    false_tid: TermId,
) -> Option<TermId> {
    let mut sum = LinComb::default();
    let mut strict = false;
    for (lin, s, lambda) in a_ineqs {
        sum.add_scaled(lin, lambda);
        strict = strict || *s;
    }
    if sum.coeffs.is_empty() {
        // Ground A-part: evaluate `constant (<|<=) 0` directly.
        let holds = if strict {
            sum.constant < BigRational::zero()
        } else {
            sum.constant <= BigRational::zero()
        };
        return Some(if holds { true_tid } else { false_tid });
    }
    // The Farkas cancellation forces every surviving variable to appear on
    // both sides; defensive check (unlabeled-coloring drift bails instead of
    // emitting a non-local interpolant).
    if !sum.coeffs.keys().all(|v| shared_vars.contains(v)) {
        return None;
    }
    Some(comb_to_ineq_term(terms, &sum, strict))
}

#[cfg(test)]
#[path = "interpolant_farkas_tests.rs"]
mod tests;
