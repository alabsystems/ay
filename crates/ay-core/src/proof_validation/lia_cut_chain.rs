// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Chvátal–Gomory cut-chain certificates for WIDE integer clauses.
//!
//! A clause `C = (cl L_1 … L_n)` is valid iff its negation `¬L_1 ∧ … ∧ ¬L_n`
//! has no integer model. Read every `¬L_i` as a row over `Int` atoms — an
//! equality `F_i = b_i` or an inequality `F_i ≥ b_i` (a strict comparison
//! over integers is the non-strict one moved by one). The clauses this rule
//! exists for are the ones whose negation is rationally SATISFIABLE and
//! integrally infeasible, refuted only after integer rounding. A rationally
//! infeasible clause is refuted too — its Farkas certificate is a chain with
//! no cut — and `TheoryLemmaKind::LraFarkas` owns it whenever a Farkas
//! certificate is at hand: the producer's own, or the unit multipliers the
//! payload-free funnel tries. One whose multipliers are not all one
//! (`x + 2y ≥ 4, x ≤ 1, y ≤ 1`) reaches this rule, and the executor's Farkas
//! reconstruction relabels it `LraFarkas` afterwards.
//!
//! # The certificate
//!
//! A chain of cuts `G_1 ≥ c_1, …, G_K ≥ c_K` and one final combination:
//!
//! * cut `k` is `Σ_i r_i·(row i) + Σ_{j<k} s_j·(cut j)` with `r_i ≥ 0` for
//!   every inequality row (any sign for an equality row) and `s_j ≥ 0`. That
//!   combination reads `G_k ≥ β_k` with `G_k` an INTEGER-coefficient form, and
//!   the cut is `G_k ≥ c_k` for `c_k ≤ ⌈β_k⌉`;
//! * the final combination, over the rows and all `K` cuts with the same sign
//!   rules, cancels every atom and reads `0 ≥ β` with `β > 0`.
//!
//! Soundness, by induction over the chain: in every integer model of the
//! rows, cuts `1..k-1` hold, so the non-negative combination gives
//! `G_k ≥ β_k`; `G_k` has integer coefficients over `Int`-sorted atoms, so it
//! takes only integer values, and `G_k ≥ ⌈β_k⌉` holds too — the Chvátal–Gomory
//! rounding rule (Chvátal 1973; Schrijver, *Theory of Linear and Integer
//! Programming*, §23). The final combination then yields `0 ≥ β > 0` in that
//! model, so there is none, and `C` is valid. `validate_cut_chain` checks
//! exactly this, with exact rational arithmetic, against rows it reads from
//! the clause itself; the search that proposes the chain
//! (`search::find_chain`) is not trusted — a wrong proposal can only be
//! declined here.
//!
//! Every atom of every row comes through `int_linear_diff`, which declines a
//! non-`Int` atom, and every cut form is a combination of those rows, so no
//! `Real` atom can reach the rounding step.
//!
//! # Why there is no payload
//!
//! Like the lattice rules this generalizes, the certificate is re-derived from
//! the clause: the producer-side classifier and the strict checker call the
//! same [`recognize_int_cg_cut_chain`], so there is nothing to forge and no
//! classifier/validator drift. The Alethe printer renders the same witness
//! ([`lia_cut_chain_witness`]) as one `la_generic` step per cut — the pinned
//! checker's integer strengthening of the negated cut literal is the rounding
//! step — plus a final `la_generic` and a resolution chain.
//!
//! # Bounds
//!
//! At most [`MAX_CHAIN_LITERALS`] literals, [`MAX_CHAIN_CUTS`] cuts and
//! multipliers of at most [`MAX_MULTIPLIER_BITS`] bits; the search has its own
//! round and fact caps. Anything outside declines, fail-closed: a decline is
//! never evidence that a clause is false.

use std::collections::BTreeMap;

use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};

use crate::term::{Symbol, TermData};
use crate::{TermId, TermStore};

mod search;

/// Canonical integer linear form: variable/opaque-atom term → coefficient.
type Coeffs = BTreeMap<TermId, BigInt>;

/// The widest clause this rule reads. A wider clause is declined outright,
/// never truncated, so the answer cannot depend on literal order.
const MAX_CHAIN_LITERALS: usize = 96;

/// The longest cut chain a certificate may carry.
const MAX_CHAIN_CUTS: usize = 48;

/// The widest numerator or denominator a certificate multiplier may have.
const MAX_MULTIPLIER_BITS: u64 = 512;

/// One clause literal read as the constraint its FALSITY asserts, in the
/// orientation the pinned `la_generic` reads the literal: `form = bound` or
/// `form ≥ bound`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ChainRow {
    /// `true` for `form = bound`, `false` for `form ≥ bound`.
    pub equality: bool,
    /// All-`Int` atoms and their integer coefficients.
    pub form: BTreeMap<TermId, BigInt>,
    /// The integer right-hand side. A strict comparison is read moved by
    /// one (`form ≥ bound` for the checker's `form > bound − 1`), exact over
    /// `Int` atoms.
    pub bound: BigInt,
}

/// One Chvátal–Gomory cut `form ≥ bound`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ChainCut {
    /// The cut form: nonzero integer coefficients.
    pub form: BTreeMap<TermId, BigInt>,
    /// The rounded right-hand side.
    pub bound: BigInt,
    /// Multiplier of each clause row, in clause order.
    pub row_multipliers: Vec<BigRational>,
    /// Multiplier of each EARLIER cut, in chain order.
    pub cut_multipliers: Vec<BigRational>,
}

/// A validated cut chain behind one clause. See the module docs.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LiaCutChainWitness {
    /// Each literal's row, in clause order.
    pub rows: Vec<ChainRow>,
    /// The cuts, each derived from the rows and the cuts before it.
    pub cuts: Vec<ChainCut>,
    /// Final multiplier of each clause row.
    pub final_row_multipliers: Vec<BigRational>,
    /// Final multiplier of each cut.
    pub final_cut_multipliers: Vec<BigRational>,
}

/// Recognize a WIDE integer clause refuted by a Chvátal–Gomory cut chain.
///
/// The recognizer IS the validator: `TheoryLemmaKind::IntCgCutChain` is
/// accepted by the strict checker exactly when this returns `true`.
#[must_use]
pub fn recognize_int_cg_cut_chain(terms: &TermStore, clause: &[TermId]) -> bool {
    lia_cut_chain_witness(terms, clause).is_some()
}

/// The validated cut chain behind `clause`, or `None`.
///
/// Every literal must read as an all-`Int` linear row; a clause wider than the
/// literal cap, a literal that does not read, and a clause the search cannot
/// refute all return `None`. A returned witness has passed the exact
/// validator (`validate_cut_chain`) against the rows read here.
#[must_use]
pub fn lia_cut_chain_witness(terms: &TermStore, clause: &[TermId]) -> Option<LiaCutChainWitness> {
    if clause.is_empty() || clause.len() > MAX_CHAIN_LITERALS {
        return None;
    }
    let rows = clause
        .iter()
        .map(|&literal| chain_row(terms, literal))
        .collect::<Option<Vec<_>>>()?;
    let chain = search::find_chain(&rows)?;
    let witness = LiaCutChainWitness {
        rows,
        cuts: chain.cuts,
        final_row_multipliers: chain.final_rows,
        final_cut_multipliers: chain.final_cuts,
    };
    validate_cut_chain(&witness).then_some(witness)
}

/// Read one literal as the row its falsity asserts, in the pinned checker's
/// orientation. `None` for anything but a binary `=`/`<=`/`<`/`>=`/`>` over
/// all-`Int` linear operands, and for a positive `=` (whose falsity is a
/// disequality, not a row).
pub(super) fn chain_row(terms: &TermStore, literal: TermId) -> Option<ChainRow> {
    let (atom, negated) = match terms.get(literal) {
        TermData::Not(inner) => (*inner, true),
        _ => (literal, false),
    };
    let TermData::App(Symbol::Named(op), args) = terms.get(atom) else {
        return None;
    };
    let mut operands = args.iter();
    let (Some(&lhs), Some(&rhs), None) = (operands.next(), operands.next(), operands.next()) else {
        return None;
    };
    // `lhs − rhs = form + constant`.
    let (form, constant) = super::lia::int_linear_diff(terms, lhs, rhs)?;
    let negated_form = || form.iter().map(|(atom, coeff)| (*atom, -coeff)).collect();
    let (equality, form, bound) = match (op.as_str(), negated) {
        // `lhs = rhs`.
        ("=", true) => (true, form.clone(), -&constant),
        // `lhs ≤ rhs`: `rhs − lhs ≥ 0`.
        ("<=", true) | (">", false) => (false, negated_form(), constant.clone()),
        // `lhs < rhs`: `rhs − lhs ≥ 1`.
        ("<", true) | (">=", false) => (false, negated_form(), &constant + 1),
        // `lhs ≥ rhs`.
        (">=", true) | ("<", false) => (false, form.clone(), -&constant),
        // `lhs > rhs`: `lhs − rhs ≥ 1`.
        (">", true) | ("<=", false) => (false, form.clone(), BigInt::one() - &constant),
        _ => return None,
    };
    Some(ChainRow {
        equality,
        form,
        bound,
    })
}

/// Whether `witness` is a Chvátal–Gomory refutation of its rows: every cut's
/// combination has admissible multipliers, equals the cut form exactly and
/// rounds to at least the cut bound, and the final combination cancels every
/// atom with a positive constant. See the module docs.
#[must_use]
pub(super) fn validate_cut_chain(witness: &LiaCutChainWitness) -> bool {
    if witness.cuts.len() > MAX_CHAIN_CUTS {
        return false;
    }
    for (index, cut) in witness.cuts.iter().enumerate() {
        if cut.form.is_empty() || cut.form.values().any(Zero::is_zero) {
            return false;
        }
        let Some((form, bound)) = combine(
            &witness.rows,
            &witness.cuts[..index],
            &cut.row_multipliers,
            &cut.cut_multipliers,
        ) else {
            return false;
        };
        let expected: BTreeMap<TermId, BigRational> = cut
            .form
            .iter()
            .map(|(atom, coeff)| (*atom, BigRational::from_integer(coeff.clone())))
            .collect();
        if form != expected || BigRational::from_integer(cut.bound.clone()) > bound.ceil() {
            return false;
        }
    }
    combine(
        &witness.rows,
        &witness.cuts,
        &witness.final_row_multipliers,
        &witness.final_cut_multipliers,
    )
    .is_some_and(|(form, bound)| form.is_empty() && bound.is_positive())
}

/// `Σ r_i·row_i + Σ s_j·cut_j` as `(form, bound)` meaning `form ≥ bound`, or
/// `None` when a multiplier vector has the wrong length, an inequality row or
/// a cut has a negative multiplier, or a multiplier is too wide.
fn combine(
    rows: &[ChainRow],
    cuts: &[ChainCut],
    row_multipliers: &[BigRational],
    cut_multipliers: &[BigRational],
) -> Option<(BTreeMap<TermId, BigRational>, BigRational)> {
    if row_multipliers.len() != rows.len() || cut_multipliers.len() != cuts.len() {
        return None;
    }
    let mut form = BTreeMap::new();
    let mut bound = BigRational::zero();
    let terms = rows
        .iter()
        .map(|row| (&row.form, &row.bound, row.equality))
        .zip(row_multipliers)
        .chain(
            cuts.iter()
                .map(|cut| (&cut.form, &cut.bound, false))
                .zip(cut_multipliers),
        );
    for ((row_form, row_bound, equality), multiplier) in terms {
        if multiplier_too_wide(multiplier) || (!equality && multiplier.is_negative()) {
            return None;
        }
        if multiplier.is_zero() {
            continue;
        }
        for (atom, coeff) in row_form {
            let entry = form.entry(*atom).or_insert_with(BigRational::zero);
            *entry += BigRational::from_integer(coeff.clone()) * multiplier;
            if entry.is_zero() {
                let _ = form.remove(atom);
            }
        }
        bound += BigRational::from_integer(row_bound.clone()) * multiplier;
    }
    Some((form, bound))
}

fn multiplier_too_wide(multiplier: &BigRational) -> bool {
    multiplier.numer().bits() > MAX_MULTIPLIER_BITS
        || multiplier.denom().bits() > MAX_MULTIPLIER_BITS
}
