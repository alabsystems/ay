// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Width-independent structural refutation for the source Bool/Int/BV fragment.
//!
//! # Why this lane exists
//!
//! [`super::authenticate_bv_lia_unsat_query`] decides its fragment by
//! ENUMERATING a finite source-derived domain. That is exact, but its cost is
//! the size of the domain, so `build_dimensions` declines outright the moment a
//! free 64-bit bit-vector variable survives propagation:
//!
//! ```text
//! a free 64-bit BV variable exceeds finite enumeration
//! ```
//!
//! Every `usize` in real Rust is a 64-bit carrier, so the whole class of
//! length/index obligations `deductive-checks` emits is STRUCTURALLY out of reach of
//! the enumerator — not "expensive", unreachable. The measured shape is a
//! length-companion bound: an Int-side range on a value bridged to a 64-bit BV
//! carrier,
//!
//! ```text
//! (and (<= 0 (+ len 1)) (<= (+ len 1) 18446744073709551615))
//! ```
//!
//! whose refutation needs no case split at all — only that `bv2nat` of a
//! width-`w` term lies in `[0, 2^w - 1]`, plus linear bound arithmetic.
//!
//! This module supplies that derivation. It is the same move as
//! `ay-dpll`'s `api/proofs/bv_int_bridge_schema.rs`: CHECK the fact
//! structurally instead of SEARCHING for it, so the cost is the size of the
//! FORMULA rather than the size of the domain.
//!
//! # What it proves
//!
//! Interval (bound) propagation over the exact source roots:
//!
//! * every Int-sorted term is normalised into a linear form
//!   `constant + sum(coefficient * atom)` over opaque Int atoms and unsigned
//!   views of BV terms — always a faithful rewriting, never an approximation,
//!   because any node the normaliser does not interpret becomes an atom;
//! * an atom starts with the bounds its SHAPE entails and nothing else:
//!   `bv2nat(t)` with `t : BitVec(w)` gives `[0, 2^w - 1]` (the SMT-LIB
//!   definition of the unsigned conversion), `(mod _ d)` with a positive
//!   integer literal `d` gives `[0, d - 1]`, `(abs _)` gives `[0, ...)`.
//!   Everything else starts unbounded;
//! * `bvult` and `bvule` literals are read as exact order relations between
//!   unsigned BV views. For each relevant `int2bv_w(e)` view the lane adds the
//!   universally valid clause
//!   `e < 0 OR e >= 2^w OR bv2nat(int2bv_w(e)) = e`; no unguarded round-trip is
//!   ever assumed;
//! * each source root is split into clauses (disjunctions of literals) by the
//!   standard polarity rewriting, and the clauses are unit-propagated: when
//!   every literal of a clause but one is REFUTED by the current bounds, the
//!   survivor is entailed, so its bounds may be assumed.
//!
//! UNSAT is reported only when a clause has all literals refuted, or an atom's
//! interval becomes empty. Both are entailments of the authored conjunction.
//!
//! # Soundness
//!
//! This is an ADDITIONAL accepting lane inside
//! [`super::QueryChecker::has_structural_contradiction`], not a relaxation of
//! any existing one. Every bound it records is entailed by the source roots:
//!
//! * shape bounds and the guarded `int2bv` clauses are theorems of the SMT-LIB
//!   semantics of the operators, derived here from the source term and its
//!   checked width rather than imported from a production solver;
//! * a literal is assumed only after every sibling disjunct has been shown
//!   FALSE under already-entailed bounds, which makes the survivor entailed;
//! * bound tightening is the textbook interval-consistency step over integers,
//!   using floor/ceil division so no non-integer bound is ever claimed;
//! * bounds are only ever narrowed, and narrowing uses a SNAPSHOT of the
//!   sibling bounds taken before the literal is processed, so no derivation
//!   depends on a bound established later in the same step.
//!
//! It performs no solving, consults no solver verdict and no production theory
//! lemma, and every shape it does not recognise contributes nothing. Running
//! out of any budget returns `false` (this lane cannot answer), never `true`.
//!
//! That last sentence is the one that is easy to break, because a budget can
//! fire in the READER as well as in the reasoning, and the reader's budgets
//! are not symmetric. Every budget in the normaliser degrades a term to an
//! opaque atom, which only ever WIDENS an interval and is therefore safe to
//! ignore. The budgets in the clause harvest do not degrade, they DROP — and a
//! dropped disjunct strengthens the clause it was dropped from, which is
//! exactly the direction that manufactures a refutation. [`Harvest`] carries
//! that distinction, and the harvest reports it instead of returning a clause
//! that says less than the source. Enlarging a harvest budget is never a fix
//! for one of these; it only moves the size at which the lane starts lying.

use std::collections::{BTreeMap, BTreeSet, HashMap};

use ay_core::{Constant, Sort, Symbol, TermData, TermId};
use num_bigint::BigInt;
use num_traits::{One, Signed, Zero};

use super::integer_evaluation::integer_limb_units;
use super::{
    BvLiaUnsatAuthenticationError, QueryChecker, MAX_BV_LIA_TAUTOLOGY_WORK_PER_LEMMA,
    MAX_INTEGER_BITS, MAX_TERM_DEPTH,
};

/// Fixpoint rounds over the clause set. Every additional round can only narrow
/// bounds further; the target shapes close in three.
const MAX_INTERVAL_ROUNDS: usize = 64;
/// Maximum clauses admitted after polarity splitting.
const MAX_CLAUSES: usize = 100_000;
/// Maximum literals harvested from one source root.
const MAX_CLAUSE_LITERALS: usize = 4_096;
/// Maximum distinct source `int2bv` terms for which this lane derives the
/// guarded no-wrap theorem. Crossing the cap declines the complete lane.
const MAX_RESIDUE_SCHEMAS: usize = 4_096;
/// Maximum distinct atoms in one linear form. A wider form is kept as a single
/// opaque atom rather than normalised.
const MAX_FORM_ATOMS: usize = 256;
/// Shared normalisation budget for the whole lane. Exhausting it makes the
/// remaining nodes opaque atoms, which is sound and simply weaker.
const MAX_FORM_NODES: u64 = 1_000_000;
/// Owned-`BigInt` envelope for the retained interval table, in 64-bit limbs.
const MAX_BOUND_LIMBS: u64 = 1 << 20;
/// Aggregate atom entries retained by generated residue clauses. This bounds
/// map/node overhead independently of logical work.
const MAX_RESIDUE_ATOM_COPIES: usize = 1 << 16;
/// Aggregate `BigInt` payload retained by generated residue clauses, in 64-bit
/// limbs. The interval state has a separate envelope above.
const MAX_RESIDUE_LIMBS: u64 = 1 << 20;
/// This lane's share of the query's deterministic work budget. It runs before
/// the finite enumerator, so it must be unable to starve it.
const MAX_INTERVAL_WORK: u64 = MAX_BV_LIA_TAUTOLOGY_WORK_PER_LEMMA / 8;

/// The integer denotation carried by one linear-form atom.
///
/// Keeping the unsigned BV view typed is load-bearing: the same BV term may
/// eventually acquire a signed view, which must never alias this value.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum LinearAtom {
    /// The exact value of an Int-sorted source term.
    Int(TermId),
    /// The exact unsigned integer value of a BV-sorted source term.
    UnsignedBv(TermId),
}

/// `constant + sum(coefficient * atom)` over exact integer denotations.
/// Coefficients are never zero.
#[derive(Clone, Debug, Default)]
struct LinearForm {
    constant: BigInt,
    atoms: BTreeMap<LinearAtom, BigInt>,
}

impl LinearForm {
    fn constant(value: BigInt) -> Self {
        Self {
            constant: value,
            atoms: BTreeMap::new(),
        }
    }

    fn atom(term: TermId) -> Self {
        let mut atoms = BTreeMap::new();
        atoms.insert(LinearAtom::Int(term), BigInt::one());
        Self {
            constant: BigInt::zero(),
            atoms,
        }
    }

    fn unsigned_bv_atom(term: TermId) -> Self {
        let mut atoms = BTreeMap::new();
        atoms.insert(LinearAtom::UnsignedBv(term), BigInt::one());
        Self {
            constant: BigInt::zero(),
            atoms,
        }
    }
}

/// A closed integer interval, open on either end when the bound is unknown.
#[derive(Clone, Debug, Default)]
struct Interval {
    lower: Option<BigInt>,
    upper: Option<BigInt>,
}

impl Interval {
    fn limbs(&self) -> u64 {
        let lower = self.lower.as_ref().map_or(0, integer_limb_units);
        let upper = self.upper.as_ref().map_or(0, integer_limb_units);
        lower.saturating_add(upper)
    }
}

/// A literal in the source-derived clause, meaning `form REL 0`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Relation {
    /// `form <= 0`. Strict `<` is normalised into this by the integrality of
    /// the fragment (`form < 0` iff `form + 1 <= 0`).
    LessOrEqual,
    /// `form = 0`.
    Equal,
    /// `form != 0`.
    Distinct,
}

#[derive(Clone, Debug)]
enum ClauseLiteral {
    /// An interpreted arithmetic literal.
    Arithmetic {
        form: LinearForm,
        relation: Relation,
    },
    /// Any other Boolean literal, carried by identity and polarity only. It is
    /// never interpreted; it participates solely so a clause can be recognised
    /// as unit once its siblings are refuted.
    Opaque { term: TermId, polarity: bool },
}

/// Whether the clause/literal harvest saw the whole authored formula.
///
/// # Why this exists — dropping a DISJUNCT is not a weakening
///
/// The harvest walks the asserted formula under budgets. What a budget does
/// when it fires is a SOUNDNESS question, and the answer differs by polarity:
///
/// * [`Self::collect_clauses`] splits a CONJUNCTION. Abandoning part of that
///   walk drops conjuncts, which yields a WEAKER formula: any refutation of
///   the retained conjuncts still refutes the authored conjunction. Sound.
/// * [`Self::collect_literals`] flattens a DISJUNCTION into one clause.
///   Abandoning part of THAT walk drops disjuncts, which yields a STRONGER
///   clause. The dropped disjuncts are exactly the ones that could have made
///   the clause TRUE, so a truncated clause can be "all literals refuted"
///   while the authored clause is satisfied — a FORGED refutation of a
///   satisfiable query, and the truncated clause equally poisons unit
///   propagation, whose survivor is only entailed when every sibling disjunct
///   really was refuted.
///
/// So a truncated harvest can never be propagated. It is reported upward and
/// the whole query declines: this is an additional accepting lane, and "I
/// cannot authenticate this" costs only coverage while the caller's other
/// lanes run exactly as before.
///
/// Both kinds of drop report `Truncated` here. Only the disjunctive one is
/// unsound, but the conjunctive walk is the one that CALLS the disjunctive
/// one, and a future rewriting added to it need not keep the polarity
/// argument above true. Declining on either is free — neither budget is
/// reachable by the shapes this lane exists to authenticate.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[must_use = "a truncated harvest must decline, never be propagated"]
enum Harvest {
    /// Every conjunct and every disjunct of the authored formula was visited.
    Complete,
    /// A budget stopped the walk with source structure still unvisited.
    Truncated,
}

impl Harvest {
    /// `Truncated` is absorbing: a walk is complete only if every part was.
    fn and(self, other: Self) -> Self {
        match (self, other) {
            (Self::Complete, Self::Complete) => Self::Complete,
            _ => Self::Truncated,
        }
    }

    fn is_truncated(self) -> bool {
        matches!(self, Self::Truncated)
    }
}

/// Outcome of assuming one entailed literal.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum AssumeOutcome {
    /// Nothing was learned.
    Stable,
    /// A bound or Boolean value was narrowed.
    Changed,
    /// The assumption is inconsistent with what is already entailed.
    Conflict,
    /// A budget was exhausted; this lane can no longer answer.
    Decline,
}

#[derive(Default)]
struct IntervalState {
    bounds: HashMap<LinearAtom, Interval>,
    booleans: HashMap<TermId, bool>,
    bound_limbs: u64,
}

impl IntervalState {
    fn interval(&self, atom: LinearAtom) -> Interval {
        self.bounds.get(&atom).cloned().unwrap_or_default()
    }
}

include!("bv_lia_query_interval/harvest.rs");

include!("bv_lia_query_interval/propagation.rs");

impl QueryChecker<'_> {
    // -----------------------------------------------------------------------
    // Bounded integer helpers
    // -----------------------------------------------------------------------

    /// `left + right`, or `None` when the magnitude envelope would be exceeded.
    ///
    /// This lane must never turn a magnitude refusal into a hard error: it is
    /// an additional accepting lane, so an unrepresentable intermediate simply
    /// means it cannot answer for that term.
    fn bounded_add(
        &mut self,
        left: &BigInt,
        right: &BigInt,
    ) -> Result<Option<BigInt>, BvLiaUnsatAuthenticationError> {
        if left.bits().max(right.bits()).saturating_add(1) > MAX_INTEGER_BITS {
            self.meter.charge(1)?;
            return Ok(None);
        }
        Ok(Some(self.add_bounded_ints(left, right)?))
    }

    /// `left - right`, or `None` when the magnitude envelope would be exceeded.
    fn bounded_subtract(
        &mut self,
        left: &BigInt,
        right: &BigInt,
    ) -> Result<Option<BigInt>, BvLiaUnsatAuthenticationError> {
        if left.bits().max(right.bits()).saturating_add(1) > MAX_INTEGER_BITS {
            self.meter.charge(1)?;
            return Ok(None);
        }
        Ok(Some(self.subtract_bounded_ints(left, right)?))
    }

    /// `left * right`, or `None` when the magnitude envelope would be exceeded.
    fn bounded_multiply(
        &mut self,
        left: &BigInt,
        right: &BigInt,
    ) -> Result<Option<BigInt>, BvLiaUnsatAuthenticationError> {
        if left.bits().saturating_add(right.bits()) > MAX_INTEGER_BITS {
            self.meter.charge(1)?;
            return Ok(None);
        }
        Ok(Some(
            self.multiply_bounded_ints(left.clone(), right.clone())?,
        ))
    }

    /// The greatest integer `q` with `q * divisor <= dividend`, for a positive
    /// divisor.
    fn floor_divide(
        &mut self,
        dividend: &BigInt,
        divisor: &BigInt,
    ) -> Result<BigInt, BvLiaUnsatAuthenticationError> {
        let (quotient, remainder) = self.divide_with_remainder(dividend, divisor)?;
        if remainder.is_zero() {
            return Ok(quotient);
        }
        // Rust truncates toward zero; adjust when the exact quotient is
        // negative so the result is the floor.
        if remainder.is_negative() != divisor.is_negative() {
            return self.subtract_bounded_ints(&quotient, &BigInt::one());
        }
        Ok(quotient)
    }

    /// The least integer `q` with `q * divisor >= dividend`, for a negative
    /// divisor.
    fn ceiling_divide(
        &mut self,
        dividend: &BigInt,
        divisor: &BigInt,
    ) -> Result<BigInt, BvLiaUnsatAuthenticationError> {
        let (quotient, remainder) = self.divide_with_remainder(dividend, divisor)?;
        if remainder.is_zero() {
            return Ok(quotient);
        }
        if remainder.is_negative() == divisor.is_negative() {
            return self.add_bounded_ints(&quotient, &BigInt::one());
        }
        Ok(quotient)
    }

    fn divide_with_remainder(
        &mut self,
        dividend: &BigInt,
        divisor: &BigInt,
    ) -> Result<(BigInt, BigInt), BvLiaUnsatAuthenticationError> {
        self.ensure_integer_magnitude(dividend)?;
        self.ensure_integer_magnitude(divisor)?;
        let work = integer_limb_units(dividend)
            .checked_mul(integer_limb_units(divisor))
            .ok_or(BvLiaUnsatAuthenticationError::ResourceLimit {
                resource: "interval division accounting",
            })?;
        self.meter.charge(work.max(1))?;
        Ok((dividend / divisor, dividend % divisor))
    }
}

/// The interval of a linear form plus the per-atom minimum contributions the
/// tightening step consumes.
struct FormInterval {
    minimum: Option<BigInt>,
    maximum: Option<BigInt>,
    /// `(atom, coefficient, minimum contribution)`, in form order.
    contributions: Vec<(LinearAtom, BigInt, Option<BigInt>)>,
}

/// The body of a Boolean negation, written either as the native `Not` node or
/// as a `not` application.
fn negation_body(checker: &QueryChecker<'_>, term: TermId) -> Option<TermId> {
    match checker.terms.get(term) {
        TermData::Not(inner) => Some(*inner),
        TermData::App(Symbol::Named(name), args) if name == "not" && args.len() == 1 => {
            Some(args[0])
        }
        _ => None,
    }
}

#[cfg(test)]
#[path = "bv_lia_query_interval_tests.rs"]
mod tests;
