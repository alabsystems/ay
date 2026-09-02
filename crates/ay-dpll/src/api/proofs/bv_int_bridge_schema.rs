// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Closed-form schema authentication for BV<->Int bridge lemmas.
//!
//! # Why this lane exists
//!
//! The BV/LIA bridge (`push_bv2nat_range`,
//! `collect_bv2nat_add_sub_modular_assertions`) feeds the arithmetic solver a
//! handful of `bv2nat` linkage facts. When a refutation leans on one of them
//! the Alethe presentation renders it `:rule trust`, so strict certification
//! defers it to `discharge_trust_clause`.
//!
//! The existing lanes are all *search*: `check_bv_clause`, `check_array_clause`,
//! the bounded source interpreter `authenticate_bv_lia_unsat_query`, and two
//! nested re-solves. Measured at this commit, the interpreter can only
//! authenticate these schemas by ENUMERATING the finite assignment space, so it
//! declines every width above 8:
//!
//! ```text
//! width=8  modular add/sub residue -> OK
//! width=16 modular add/sub residue -> outside the checked fragment:
//!                                     finite assignment space exceeds 65536
//! width=64 modular add/sub residue -> outside the checked fragment:
//!                                     a free 64-bit BV variable exceeds finite enumeration
//! ```
//!
//! Every remaining lane is a nested solve, and a nested solve cannot discharge
//! its own trust steps (the depth-0 re-entrancy guard in
//! `discharge_trust_steps_for_certification`). What was left was the
//! whole-problem re-solve, whose acceptance is wall-clock budgeted — so a
//! correct UNSAT published as `unsat` or as `unknown` depending on machine load.
//!
//! This module closes that by CHECKING the schemas instead of searching them.
//! All are exact theorems of the SMT-LIB `bv2nat` semantics with a two-line
//! derivation, and every quantity the derivation needs (the operand widths and
//! the modulus) is READ FROM THE TERM STORE AND VERIFIED — nothing is assumed
//! and no coefficient is hardcoded.
//!
//! # Soundness
//!
//! This is an ADDITIONAL accepting lane, not a relaxation of any existing one.
//! It accepts only when it has structurally re-derived the clause; every shape
//! it does not recognise returns `false` and the caller's remaining lanes run
//! unchanged. It performs no solving and consults no solver verdict, so it
//! cannot inherit a wrong UNSAT.
//!
//! ## Schema A — unsigned range
//!
//! For a width-`w` bit-vector `A`, `bv2nat(A)` is by definition an unsigned
//! integer in `[0, 2^w - 1]`. The bridge emits both endpoints as unit clauses;
//! checking the width and exact endpoint constants authenticates them without
//! enumerating the carrier.
//!
//! ## Schema B — modular add/sub residue
//!
//! For `T = (bvadd A B)` of width `w`, writing `a = bv2nat(A)`, `b = bv2nat(B)`:
//! `bv2nat(T) = (a + b) mod 2^w` by definition of `bvadd`. Since
//! `0 <= a, b <= 2^w - 1`, the sum lies in `[0, 2^(w+1) - 2]`, i.e. strictly
//! below `2 * 2^w`, so the residue is either `a + b` (no wrap) or
//! `a + b - 2^w` (one wrap). Hence
//! `bv2nat(T) = a + b  \/  bv2nat(T) = a + b - 2^w`. QED
//!
//! For `T = (bvsub A B)`: `bv2nat(T) = (a - b) mod 2^w` with
//! `a - b` in `(-2^w, 2^w)`, so the residue is `a - b` when non-negative and
//! `a - b + 2^w` otherwise. QED
//!
//! Both derivations need `width(A) = width(B) = width(T) = w` and the literal
//! modulus to be exactly `2^w`; both are checked here.
//!
//! ## Schema C — unsigned order bridge
//!
//! `bvult(A, B)` holds iff `bv2nat(A) < bv2nat(B)`, and `bvule(A, B)` iff
//! `bv2nat(A) <= bv2nat(B)` — this IS the SMT-LIB definition of the unsigned
//! comparison predicates. So whenever the AUTHORED assertions contain such a
//! literal as a positively-asserted conjunct, the corresponding `bv2nat` order
//! fact is entailed. Only `and` is traversed (each conjunct of an asserted
//! conjunction is itself asserted); `or`, `ite`, quantifiers and `not` of a
//! non-literal are never descended into, so no clause is ever discharged from a
//! premise that was not actually asserted.
//!
//! The signed predicates (`bvslt`/`bvsle`/...) are deliberately NOT handled:
//! they range over the two's-complement value, which is `bv2int`, not
//! `bv2nat`.

use std::collections::BTreeMap;

use ay_core::{Sort, Symbol, TermData, TermId, TermStore};
use num_bigint::BigInt;
use num_traits::{One, Zero};

/// Traversal budget for one clause. Every schema this lane recognises is a
/// handful of nodes; a larger term is not one of them, so exceeding the budget
/// declines rather than costing time.
const MAX_NODES: usize = 4_096;
/// Largest modular-residue word discharged by this closed-form lane. MODEL_CHECKER_CONSUMER
/// obligations are machine-word sized; wider words fall back to checked solver
/// lanes instead of allocating a width-sized `BigInt` here.
const MAX_MODULAR_RESIDUE_WIDTH: u32 = 128;
/// Maximum recursive Int-expression depth accepted by the linear normalizer.
const MAX_LINEAR_DEPTH: usize = 64;
/// Maximum distinct opaque atoms retained in one normalized linear form.
const MAX_LINEAR_ATOMS: usize = 64;
/// Maximum magnitude of any normalized constant or coefficient.
const MAX_LINEAR_INTEGER_BITS: u64 = 256;
/// Maximum authored assertions scanned for Schema B premises.
const MAX_PREMISE_ROOTS: usize = 4_096;
/// Maximum `and`-conjunct nesting descended when harvesting Schema B premises.
const MAX_CONJUNCT_DEPTH: usize = 64;

/// Independently discharge a deferred trust clause that is an instance of a
/// closed-form BV<->Int bridge schema.
///
/// Returns `true` only when the clause has been re-derived structurally from
/// the SMT-LIB semantics (Schema A) or from a positively-asserted authored
/// premise (Schema B). Every unrecognised shape returns `false`.
pub(super) fn discharge_bv_int_bridge_schema(
    terms: &TermStore,
    clause: &[TermId],
    assertions: &[TermId],
) -> bool {
    // Only unit clauses. A multi-literal clause is a disjunction of the
    // literals; recognising one of them proves nothing about the clause unless
    // that literal alone is valid, and this lane does not attempt that.
    let [literal] = clause else {
        return false;
    };
    let literal = *literal;
    if literal.index() >= terms.len() {
        return false;
    }
    if discharges_bv2nat_range(terms, literal) || discharges_modular_residue(terms, literal) {
        return true;
    }
    discharges_unsigned_order(terms, literal, assertions)
}

// ---------------------------------------------------------------------------
// Schema A: unsigned range
// ---------------------------------------------------------------------------

/// `0 <= bv2nat(A)` or `bv2nat(A) <= 2^w - 1`, with the endpoint and the
/// operand width read from the term store. These are the two exact unit clauses
/// emitted by `push_bv2nat_width_bounds`.
fn discharges_bv2nat_range(terms: &TermStore, literal: TermId) -> bool {
    let Some(args) = named_app(terms, literal, "<=") else {
        return false;
    };
    let [lhs, rhs] = args.as_slice() else {
        return false;
    };
    if let Some(bv) = bv2nat_argument(terms, *rhs) {
        return int_constant(terms, *lhs).is_some_and(BigInt::is_zero)
            && bounded_bv_width(terms, bv).is_some();
    }
    let Some(bv) = bv2nat_argument(terms, *lhs) else {
        return false;
    };
    let (Some(width), Some(endpoint)) = (bounded_bv_width(terms, bv), int_constant(terms, *rhs))
    else {
        return false;
    };
    endpoint == &((BigInt::one() << width as usize) - BigInt::one())
}

fn bounded_bv_width(terms: &TermStore, term: TermId) -> Option<u32> {
    let Sort::BitVec(width) = terms.sort(term) else {
        return None;
    };
    (width.width > 0 && width.width <= MAX_MODULAR_RESIDUE_WIDTH).then_some(width.width)
}

fn int_constant(terms: &TermStore, term: TermId) -> Option<&BigInt> {
    match terms.get(term) {
        TermData::Const(ay_core::Constant::Int(value)) => Some(value),
        _ => None,
    }
}

// ---------------------------------------------------------------------------
// Schema B: modular add/sub residue
// ---------------------------------------------------------------------------

/// `(or (= (bv2nat T) BASE) (= (bv2nat T) WRAPPED))` for `T = (bvadd A B)` or
/// `(bvsub A B)`, where `BASE`/`WRAPPED` are the no-wrap and wrapped residues.
fn discharges_modular_residue(terms: &TermStore, literal: TermId) -> bool {
    let Some(args) = named_app(terms, literal, "or") else {
        return false;
    };
    let [left, right] = args.as_slice() else {
        return false;
    };
    let (Some((nat_t_l, value_l)), Some((nat_t_r, value_r))) =
        (split_equation(terms, *left), split_equation(terms, *right))
    else {
        return false;
    };
    // Both disjuncts must constrain the SAME `bv2nat` term.
    if nat_t_l != nat_t_r {
        return false;
    }
    let Some(op_term) = bv2nat_argument(terms, nat_t_l) else {
        return false;
    };
    let Some((is_sub, a, b, width)) = bv_add_sub_operands(terms, op_term) else {
        return false;
    };

    // `bv2nat(A)` / `bv2nat(B)` as linear forms. A BitVec CONSTANT has a known
    // unsigned value and the producer's `mk_bv2nat` folds it to that integer,
    // so mirror that here; anything else contributes the opaque `bv2nat` atom,
    // which must then literally occur in the disjunct.
    let (Some(a_form), Some(b_form)) = (bv2nat_linear_form(terms, a), bv2nat_linear_form(terms, b))
    else {
        return false;
    };

    let Some(base) = (if is_sub {
        a_form.sub(&b_form)
    } else {
        a_form.add(&b_form)
    }) else {
        return false;
    };
    let Some(modulus) = LinearForm::constant(BigInt::one() << width as usize) else {
        return false;
    };
    // bvadd wraps DOWN by one modulus, bvsub wraps UP by one modulus.
    let Some(wrapped) = (if is_sub {
        base.add(&modulus)
    } else {
        base.sub(&modulus)
    }) else {
        return false;
    };

    let (Some(form_l), Some(form_r)) = (linear_form(terms, value_l), linear_form(terms, value_r))
    else {
        return false;
    };
    // The `or` arguments may appear in either order.
    (form_l == base && form_r == wrapped) || (form_l == wrapped && form_r == base)
}

/// Split `(= x y)` into `(bv2nat-term, other-side)` when exactly one side is a
/// `bv2nat` application. Returns `None` for any other equation shape.
fn split_equation(terms: &TermStore, term: TermId) -> Option<(TermId, TermId)> {
    let args = named_app(terms, term, "=")?;
    let [lhs, rhs] = args.as_slice() else {
        return None;
    };
    let lhs_is_nat = bv2nat_argument(terms, *lhs).is_some();
    let rhs_is_nat = bv2nat_argument(terms, *rhs).is_some();
    match (lhs_is_nat, rhs_is_nat) {
        (true, false) => Some((*lhs, *rhs)),
        (false, true) => Some((*rhs, *lhs)),
        // Both or neither: the schema does not apply.
        _ => None,
    }
}

/// The BitVec argument of a `bv2nat` application.
fn bv2nat_argument(terms: &TermStore, term: TermId) -> Option<TermId> {
    let args = named_app(terms, term, "bv2nat")?;
    let [arg] = args.as_slice() else {
        return None;
    };
    matches!(terms.sort(*arg), Sort::BitVec(_)).then_some(*arg)
}

/// `(bvadd A B)` / `(bvsub A B)` with all three sorts `BitVec(w)`, `w >= 1`.
/// Returns `(is_sub, A, B, w)`.
fn bv_add_sub_operands(terms: &TermStore, term: TermId) -> Option<(bool, TermId, TermId, u32)> {
    let TermData::App(Symbol::Named(name), args) = terms.get(term) else {
        return None;
    };
    let is_sub = match name.as_str() {
        "bvadd" => false,
        "bvsub" => true,
        _ => return None,
    };
    let [a, b] = args.as_slice() else {
        return None;
    };
    let Sort::BitVec(result_sort) = terms.sort(term).clone() else {
        return None;
    };
    let width = result_sort.width;
    if width == 0 || width > MAX_MODULAR_RESIDUE_WIDTH {
        return None;
    }
    // The residue derivation needs both operands at the RESULT width; a
    // mismatch is not this schema.
    let result = Sort::BitVec(result_sort);
    if *terms.sort(*a) != result || *terms.sort(*b) != result {
        return None;
    }
    Some((is_sub, *a, *b, width))
}

/// The linear form of `bv2nat(bv)`: the folded integer for a BitVec constant,
/// otherwise the opaque `bv2nat(bv)` atom — which must already exist in the
/// store, since the clause under test is required to mention it.
fn bv2nat_linear_form(terms: &TermStore, bv: TermId) -> Option<LinearForm> {
    if let TermData::Const(ay_core::Constant::BitVec { value, width }) = terms.get(bv) {
        // Do not TRUST the stored payload: `bv2nat` denotes the unsigned value,
        // so the literal is usable as an integer only when it is already the
        // canonical residue. A payload outside `[0, 2^width)` declines the lane
        // rather than silently importing a wrong constant.
        if *width == 0
            || *width > MAX_MODULAR_RESIDUE_WIDTH
            || value.sign() == num_bigint::Sign::Minus
            || value.bits() > u64::from(*width)
        {
            return None;
        }
        return LinearForm::constant(value.clone());
    }
    let nat = find_bv2nat(terms, bv)?;
    Some(LinearForm::atom(nat))
}

/// Locate an existing `bv2nat(bv)` term. Fail-closed: when the store holds no
/// such term the clause cannot be an instance of this schema.
fn find_bv2nat(terms: &TermStore, bv: TermId) -> Option<TermId> {
    terms.find_app(&Symbol::named("bv2nat"), &[bv])
}

// ---------------------------------------------------------------------------
// Schema C: unsigned order bridge
// ---------------------------------------------------------------------------

/// A `bv2nat` order fact entailed by a positively-asserted unsigned BV
/// comparison in the authored premises.
#[derive(Clone, Copy, PartialEq, Eq)]
struct OrderFact {
    /// `true` for `lhs < rhs`, `false` for `lhs <= rhs`.
    strict: bool,
    lhs: TermId,
    rhs: TermId,
}

fn discharges_unsigned_order(terms: &TermStore, literal: TermId, assertions: &[TermId]) -> bool {
    let Some(goal) = order_goal(terms, literal) else {
        return false;
    };
    if assertions.len() > MAX_PREMISE_ROOTS {
        return false;
    }
    let mut budget = MAX_NODES;
    let mut premises = Vec::new();
    for &assertion in assertions {
        if assertion.index() >= terms.len() {
            continue;
        }
        harvest_premises(terms, assertion, 0, &mut budget, &mut premises);
        if budget == 0 {
            return false;
        }
    }
    premises.iter().any(|premise| entails(*premise, goal))
}

/// Read the clause literal as a `bv2nat` order goal: `(< (bv2nat A) (bv2nat B))`
/// or `(<= (bv2nat A) (bv2nat B))`. The operands are kept as the underlying
/// BitVec terms so the premise match is on BitVec identity.
fn order_goal(terms: &TermStore, literal: TermId) -> Option<OrderFact> {
    let TermData::App(Symbol::Named(name), args) = terms.get(literal) else {
        return None;
    };
    let strict = match name.as_str() {
        "<" => true,
        "<=" => false,
        _ => return None,
    };
    let [lhs, rhs] = args.as_slice() else {
        return None;
    };
    let lhs = bv2nat_argument(terms, *lhs)?;
    let rhs = bv2nat_argument(terms, *rhs)?;
    Some(OrderFact { strict, lhs, rhs })
}

/// Collect the unsigned-order facts entailed by an ASSERTED formula.
///
/// Only `and` is descended: every conjunct of an asserted conjunction is itself
/// asserted. A `not` is read only when its body is a comparison LITERAL —
/// `not (and ...)`, `not (or ...)` and friends are left alone, so nothing is
/// ever harvested from a premise that was not actually asserted.
fn harvest_premises(
    terms: &TermStore,
    term: TermId,
    depth: usize,
    budget: &mut usize,
    out: &mut Vec<OrderFact>,
) {
    if *budget == 0 || depth > MAX_CONJUNCT_DEPTH {
        return;
    }
    *budget -= 1;
    if let Some(args) = named_app(terms, term, "and") {
        if args.len() > *budget {
            *budget = 0;
            return;
        }
        for &arg in args {
            harvest_premises(terms, arg, depth + 1, budget, out);
            if *budget == 0 {
                break;
            }
        }
        return;
    }
    let (body, negated) = match terms.get(term) {
        TermData::Not(inner) => (*inner, true),
        _ => (term, false),
    };
    let TermData::App(Symbol::Named(name), args) = terms.get(body) else {
        return;
    };
    // Unsigned comparisons ONLY. The signed predicates range over the
    // two's-complement value (`bv2int`), not `bv2nat`.
    let strict_when_positive = match name.as_str() {
        "bvult" => true,
        "bvule" => false,
        _ => return,
    };
    let [a, b] = args.as_slice() else {
        return;
    };
    let (Sort::BitVec(width_a), Sort::BitVec(width_b)) =
        (terms.sort(*a).clone(), terms.sort(*b).clone())
    else {
        return;
    };
    if width_a != width_b || width_a.width == 0 {
        return;
    }
    // Positive: `bvult(a,b) => a <u b`; `bvule(a,b) => a <=u b`.
    // Negative: `!bvult(a,b) => b <=u a`; `!bvule(a,b) => b <u a`.
    let fact = if negated {
        OrderFact {
            strict: !strict_when_positive,
            lhs: *b,
            rhs: *a,
        }
    } else {
        OrderFact {
            strict: strict_when_positive,
            lhs: *a,
            rhs: *b,
        }
    };
    out.push(fact);
}

/// A premise entails the goal when it relates the same ordered pair and is at
/// least as strong (`<` entails `<=`, never the converse).
fn entails(premise: OrderFact, goal: OrderFact) -> bool {
    premise.lhs == goal.lhs && premise.rhs == goal.rhs && (premise.strict || !goal.strict)
}

// ---------------------------------------------------------------------------
// Linear forms over Int terms
// ---------------------------------------------------------------------------

/// `constant + sum(coefficient * atom)` over opaque Int atoms.
#[derive(Clone, Debug, PartialEq, Eq)]
struct LinearForm {
    constant: BigInt,
    terms: BTreeMap<TermId, BigInt>,
}

impl LinearForm {
    fn constant(value: BigInt) -> Option<Self> {
        let form = Self {
            constant: value,
            terms: BTreeMap::new(),
        };
        form.is_bounded().then_some(form)
    }

    fn zero() -> Self {
        Self {
            constant: BigInt::zero(),
            terms: BTreeMap::new(),
        }
    }

    fn atom(term: TermId) -> Self {
        let mut terms = BTreeMap::new();
        terms.insert(term, BigInt::one());
        Self {
            constant: BigInt::zero(),
            terms,
        }
    }

    fn add(&self, other: &Self) -> Option<Self> {
        self.combine(other, false)
    }

    fn sub(&self, other: &Self) -> Option<Self> {
        self.combine(other, true)
    }

    fn combine(&self, other: &Self, negate_other: bool) -> Option<Self> {
        if !self.is_bounded() || !other.is_bounded() {
            return None;
        }
        let mut result = self.clone();
        if negate_other {
            result.constant -= &other.constant;
        } else {
            result.constant += &other.constant;
        }
        for (term, coefficient) in &other.terms {
            let entry = result.terms.entry(*term).or_insert_with(BigInt::zero);
            if negate_other {
                *entry -= coefficient;
            } else {
                *entry += coefficient;
            }
        }
        result.terms.retain(|_, coefficient| !coefficient.is_zero());
        result.is_bounded().then_some(result)
    }

    fn scale(&self, factor: &BigInt) -> Option<Self> {
        if !self.is_bounded() || !bounded_integer(factor) {
            return None;
        }
        if factor.is_zero() {
            return Some(Self::zero());
        }
        let constant = bounded_product(&self.constant, factor)?;
        let mut terms = BTreeMap::new();
        for (term, coefficient) in &self.terms {
            terms.insert(*term, bounded_product(coefficient, factor)?);
        }
        let result = Self { constant, terms };
        result.is_bounded().then_some(result)
    }

    fn negate(&self) -> Option<Self> {
        self.scale(&(-BigInt::one()))
    }

    fn is_bounded(&self) -> bool {
        self.terms.len() <= MAX_LINEAR_ATOMS
            && bounded_integer(&self.constant)
            && self.terms.values().all(bounded_integer)
    }
}

fn bounded_integer(value: &BigInt) -> bool {
    value.bits() <= MAX_LINEAR_INTEGER_BITS
}

fn bounded_product(lhs: &BigInt, rhs: &BigInt) -> Option<BigInt> {
    if !bounded_integer(lhs) || !bounded_integer(rhs) {
        return None;
    }
    if lhs.is_zero() || rhs.is_zero() {
        return Some(BigInt::zero());
    }
    let maximum_bits = lhs.bits().checked_add(rhs.bits())?.saturating_sub(1);
    if maximum_bits > MAX_LINEAR_INTEGER_BITS {
        return None;
    }
    let product = lhs * rhs;
    bounded_integer(&product).then_some(product)
}

/// Normalise an Int-sorted term into a linear form. `+`, `-` and
/// constant-scaled `*` are interpreted; every other node is an opaque atom, so
/// the normalisation is always a faithful rewriting (never an approximation).
fn linear_form(terms: &TermStore, term: TermId) -> Option<LinearForm> {
    let mut budget = MAX_NODES;
    linear_form_inner(terms, term, 0, &mut budget)
}

fn linear_form_inner(
    terms: &TermStore,
    term: TermId,
    depth: usize,
    budget: &mut usize,
) -> Option<LinearForm> {
    if *budget == 0 || depth > MAX_LINEAR_DEPTH {
        return None;
    }
    *budget -= 1;
    if *terms.sort(term) != Sort::Int {
        return None;
    }
    if let TermData::Const(ay_core::Constant::Int(value)) = terms.get(term) {
        if !bounded_integer(value) {
            return None;
        }
        return LinearForm::constant(value.clone());
    }
    let TermData::App(Symbol::Named(name), args) = terms.get(term) else {
        return Some(LinearForm::atom(term));
    };
    match name.as_str() {
        "+" => {
            if args.len() > *budget {
                return None;
            }
            let mut acc = LinearForm::zero();
            for &arg in args {
                acc = acc.add(&linear_form_inner(terms, arg, depth + 1, budget)?)?;
            }
            Some(acc)
        }
        "-" => match args.as_slice() {
            // SMT-LIB unary minus.
            [only] => linear_form_inner(terms, *only, depth + 1, budget)?.negate(),
            [first, rest @ ..] => {
                if args.len() > *budget {
                    return None;
                }
                let mut acc = linear_form_inner(terms, *first, depth + 1, budget)?;
                for &arg in rest {
                    acc = acc.sub(&linear_form_inner(terms, arg, depth + 1, budget)?)?;
                }
                Some(acc)
            }
            [] => None,
        },
        "*" => {
            if args.len() > *budget {
                return None;
            }
            // Linear only: at most one non-constant factor.
            let mut coefficient = BigInt::one();
            let mut symbolic: Option<LinearForm> = None;
            for &arg in args {
                let form = linear_form_inner(terms, arg, depth + 1, budget)?;
                if form.terms.is_empty() {
                    coefficient = bounded_product(&coefficient, &form.constant)?;
                } else if symbolic.is_none() {
                    symbolic = Some(form);
                } else {
                    // Two symbolic factors: not linear. Treat the whole product
                    // as an opaque atom rather than mis-normalising it.
                    return Some(LinearForm::atom(term));
                }
            }
            match symbolic {
                Some(form) => form.scale(&coefficient),
                None => LinearForm::constant(coefficient),
            }
        }
        _ => Some(LinearForm::atom(term)),
    }
}

// ---------------------------------------------------------------------------
// Shared helpers
// ---------------------------------------------------------------------------

fn named_app<'a>(terms: &'a TermStore, term: TermId, name: &str) -> Option<&'a Vec<TermId>> {
    match terms.get(term) {
        TermData::App(Symbol::Named(actual), args) if actual == name => Some(args),
        _ => None,
    }
}

#[cfg(test)]
#[path = "bv_int_bridge_schema_tests.rs"]
mod tests;
