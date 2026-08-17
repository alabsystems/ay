// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Sealed exact decision certificate for one narrow integer-existential shape.
//!
//! This is deliberately not a general quantifier-elimination checker. It
//! recognizes exactly one assumption-free hard root of the form
//!
//! ```text
//! (exists ((x Int)) (and (x > L) (x < U)))
//! ```
//!
//! (with either spelling/order of the two strict comparisons), where `L` and
//! `U` are integer affine expressions built only from variables, integer
//! constants, binary `+`, and unary/binary `-`. The bound variable must occur
//! as a bare comparison operand and nowhere in either affine endpoint. If the
//! free-variable coefficient maps of `L` and `U` are identical, `U - L` is a
//! constant `d`, and integer discreteness gives the complete theorem
//!
//! ```text
//! exists x. L < x < U    iff    d >= 2.
//! ```
//!
//! Every other shape declines. In particular, this module does not trust the
//! Cooper/QE-light candidate or its sampled self-check. It reparses the exact
//! authored root independently and binds a successful result to the public
//! query identity, source/scope stamp, ordered root vector, and immutable
//! structural term-store snapshot.

use std::collections::{BTreeMap, HashSet};

use ay_core::term::{Constant, Symbol, TermData, TermStoreSnapshotStamp};
use ay_core::{Sort, TermId, TermStore};
use ay_frontend::Context;
use num_bigint::BigInt;
use num_traits::Zero;

use super::{AuthoredPlainHardQueryPermit, Executor};

/// Canonical core identities to which this checker assigns theory semantics.
///
/// Legal source declarations using these surface spellings receive private
/// core identities. [`core_operators_are_unshadowed`] positively checks that
/// invariant at the authority boundary; every other application head is
/// rejected by the grammar below.
const CHECKED_CORE_OPERATORS: [&str; 5] = ["and", "+", "-", "<", ">"];

/// The accepted grammar is tiny, but keep malformed DAGs deterministically
/// bounded even when a caller constructs terms through the low-level Context
/// escape hatch.
const MAX_REACHABLE_NODES: usize = 64;
const MAX_INTEGER_BITS: u64 = 4096;

/// Successful exact theorem, before its truth polarity is sealed in a typed
/// SAT/UNSAT wrapper.
#[derive(Debug)]
struct CheckedExactExistsCommon {
    /// Linear authored-query capability. Owning rather than copying its fields
    /// prevents one permit from minting two independent decision tokens.
    permit: AuthoredPlainHardQueryPermit,
    term_snapshot: TermStoreSnapshotStamp,
}

/// Exact proof that the one authored root is true for every valuation of its
/// free integer constants.
#[derive(Debug)]
pub(in crate::executor) struct CheckedExactExistsSat(CheckedExactExistsCommon);

/// Exact proof that the one authored root is false for every valuation of its
/// free integer constants.
#[derive(Debug)]
pub(in crate::executor) struct CheckedExactExistsUnsat(CheckedExactExistsCommon);

/// Fail-closed outcome of the exact checker.
pub(in crate::executor) enum ExactExistsDecision {
    Sat(CheckedExactExistsSat),
    Unsat(CheckedExactExistsUnsat),
    /// Return the untouched linear permit so the existing projection checker
    /// can consume it when this much narrower theorem declines.
    Declined(AuthoredPlainHardQueryPermit),
}

impl CheckedExactExistsCommon {
    fn is_current_for(&self, executor: &Executor, expected: bool) -> bool {
        self.permit.is_current(executor)
            && self.term_snapshot == executor.ctx.terms.snapshot_stamp()
            && self.permit.roots() == executor.ctx.assertions
            // Re-run the small theorem checker immediately before minting. The
            // opaque snapshot already freezes the result; this redundant check
            // keeps a future evidence-field edit fail closed as well.
            && check_constant_truth(&executor.ctx, &executor.ctx.assertions) == Some(expected)
    }
}

impl CheckedExactExistsSat {
    pub(in crate::executor) fn is_current(&self, executor: &Executor) -> bool {
        self.0.is_current_for(executor, true)
    }
}

impl CheckedExactExistsUnsat {
    pub(in crate::executor) fn is_current(&self, executor: &Executor) -> bool {
        self.0.is_current_for(executor, false)
    }
}

impl Executor {
    /// Check the exact authored unit-difference theorem inside the final
    /// borrow-bound public transaction.
    pub(in crate::executor) fn try_authorize_exact_exists_decision(
        &self,
        permit: AuthoredPlainHardQueryPermit,
    ) -> ExactExistsDecision {
        if !permit.is_current(self) || permit.roots() != self.ctx.assertions {
            return ExactExistsDecision::Declined(permit);
        }

        let term_snapshot = self.ctx.terms.snapshot_stamp();
        let Some(truth) = check_constant_truth(&self.ctx, permit.roots()) else {
            return ExactExistsDecision::Declined(permit);
        };
        if term_snapshot != self.ctx.terms.snapshot_stamp() {
            return ExactExistsDecision::Declined(permit);
        }

        let common = CheckedExactExistsCommon {
            permit,
            term_snapshot,
        };
        if truth {
            ExactExistsDecision::Sat(CheckedExactExistsSat(common))
        } else {
            ExactExistsDecision::Unsat(CheckedExactExistsUnsat(common))
        }
    }
}

/// Prove the sole authored root constant true/false, or decline.
fn check_constant_truth(ctx: &Context, roots: &[TermId]) -> Option<bool> {
    let [root] = roots else {
        return None;
    };
    if !core_operators_are_unshadowed(ctx) {
        return None;
    }

    let terms = &ctx.terms;
    require_sort(terms, *root, &Sort::Bool)?;
    let TermData::Exists(vars, body, triggers) = live_term(terms, *root)? else {
        return None;
    };
    let [(binder_name, Sort::Int)] = vars.as_slice() else {
        return None;
    };
    if !triggers.is_empty() {
        return None;
    }
    require_sort(terms, *body, &Sort::Bool)?;

    let bound = unique_named_var(terms, *body, binder_name)?;
    require_sort(terms, bound, &Sort::Int)?;

    let TermData::App(Symbol::Named(and_name), conjuncts) = live_term(terms, *body)? else {
        return None;
    };
    if and_name != "and" || conjuncts.len() != 2 {
        return None;
    }

    let mut work = WorkBudget::new();
    let first = parse_strict_bound(terms, conjuncts[0], bound, &mut work)?;
    let second = parse_strict_bound(terms, conjuncts[1], bound, &mut work)?;
    let (lower, upper) = match (first, second) {
        (StrictBound::Lower(lower), StrictBound::Upper(upper))
        | (StrictBound::Upper(upper), StrictBound::Lower(lower)) => (lower, upper),
        _ => return None,
    };

    if lower.coeffs != upper.coeffs {
        return None;
    }
    let gap = checked_bigint(upper.constant - lower.constant)?;
    Some(gap >= BigInt::from(2u8))
}

/// No live declaration may own a canonical identity interpreted by this
/// checker. The frontend gives legal colliding surface declarations a private
/// identity; observing a canonical collision therefore means the source-kind
/// invariant was violated or bypassed, and authority must be refused.
fn core_operators_are_unshadowed(ctx: &Context) -> bool {
    ctx.symbol_iter().all(|(surface, info)| {
        !CHECKED_CORE_OPERATORS.contains(&ctx.symbol_identity_name(surface, info))
    })
}

fn live_term(terms: &TermStore, term: TermId) -> Option<&TermData> {
    terms.entry_stamp(term)?;
    Some(terms.get(term))
}

fn require_sort(terms: &TermStore, term: TermId, expected: &Sort) -> Option<()> {
    terms.entry_stamp(term)?;
    (terms.sort(term) == expected).then_some(())
}

/// Recover the exact binder identity and reject same-name ambiguity.
fn unique_named_var(terms: &TermStore, root: TermId, name: &str) -> Option<TermId> {
    let mut stack = vec![root];
    let mut seen = HashSet::new();
    let mut found = None;
    let mut remaining = MAX_REACHABLE_NODES;
    while let Some(term) = stack.pop() {
        if remaining == 0 {
            return None;
        }
        remaining -= 1;
        if !seen.insert(term) {
            continue;
        }
        match live_term(terms, term)? {
            TermData::Var(candidate, _) if candidate == name => match found {
                Some(previous) if previous != term => return None,
                _ => found = Some(term),
            },
            TermData::Var(_, _) | TermData::Const(_) => {}
            TermData::App(_, args) => stack.extend(args.iter().copied()),
            TermData::Not(inner) => stack.push(*inner),
            TermData::Ite(condition, then_term, else_term) => {
                stack.push(*condition);
                stack.push(*then_term);
                stack.push(*else_term);
            }
            TermData::Let(bindings, body) => {
                stack.extend(bindings.iter().map(|(_, value)| *value));
                stack.push(*body);
            }
            TermData::Forall(_, body, patterns) | TermData::Exists(_, body, patterns) => {
                stack.push(*body);
                stack.extend(patterns.iter().flatten().copied());
            }
            _ => return None,
        }
    }
    found
}

enum StrictBound {
    Lower(Affine),
    Upper(Affine),
}

fn parse_strict_bound(
    terms: &TermStore,
    atom: TermId,
    bound: TermId,
    work: &mut WorkBudget,
) -> Option<StrictBound> {
    work.spend()?;
    require_sort(terms, atom, &Sort::Bool)?;
    let TermData::App(Symbol::Named(operator), args) = live_term(terms, atom)? else {
        return None;
    };
    let [left, right] = args.as_slice() else {
        return None;
    };
    require_sort(terms, *left, &Sort::Int)?;
    require_sort(terms, *right, &Sort::Int)?;

    // Exactly one comparison operand must be the bare bound variable.
    if (*left == bound) == (*right == bound) {
        return None;
    }
    let endpoint = if *left == bound { *right } else { *left };
    match (operator.as_str(), *left == bound) {
        ("<", true) | (">", false) => Some(StrictBound::Upper(parse_affine(
            terms, endpoint, bound, work,
        )?)),
        ("<", false) | (">", true) => Some(StrictBound::Lower(parse_affine(
            terms, endpoint, bound, work,
        )?)),
        _ => None,
    }
}

#[derive(Default, PartialEq, Eq)]
struct Affine {
    coeffs: BTreeMap<TermId, BigInt>,
    constant: BigInt,
}

impl Affine {
    fn add_scaled(&mut self, other: Affine, sign: i8) -> Option<()> {
        let sign = BigInt::from(sign);
        for (var, coefficient) in other.coeffs {
            let entry = self.coeffs.entry(var).or_insert_with(BigInt::zero);
            *entry = checked_bigint(entry.clone() + coefficient * &sign)?;
            if entry.is_zero() {
                self.coeffs.remove(&var);
            }
        }
        self.constant = checked_bigint(self.constant.clone() + other.constant * sign)?;
        Some(())
    }
}

fn parse_affine(
    terms: &TermStore,
    term: TermId,
    bound: TermId,
    work: &mut WorkBudget,
) -> Option<Affine> {
    work.spend()?;
    require_sort(terms, term, &Sort::Int)?;
    match live_term(terms, term)? {
        TermData::Const(Constant::Int(value)) => Some(Affine {
            coeffs: BTreeMap::new(),
            constant: checked_bigint(value.clone())?,
        }),
        TermData::Var(_, _) if term != bound => {
            let mut coeffs = BTreeMap::new();
            coeffs.insert(term, BigInt::from(1u8));
            Some(Affine {
                coeffs,
                constant: BigInt::zero(),
            })
        }
        TermData::App(Symbol::Named(operator), args) if operator == "+" => {
            let [left, right] = args.as_slice() else {
                return None;
            };
            let mut result = parse_affine(terms, *left, bound, work)?;
            result.add_scaled(parse_affine(terms, *right, bound, work)?, 1)?;
            Some(result)
        }
        TermData::App(Symbol::Named(operator), args) if operator == "-" => match args.as_slice() {
            [inner] => {
                let mut result = Affine::default();
                result.add_scaled(parse_affine(terms, *inner, bound, work)?, -1)?;
                Some(result)
            }
            [left, right] => {
                let mut result = parse_affine(terms, *left, bound, work)?;
                result.add_scaled(parse_affine(terms, *right, bound, work)?, -1)?;
                Some(result)
            }
            _ => None,
        },
        _ => None,
    }
}

fn checked_bigint(value: BigInt) -> Option<BigInt> {
    (value.bits() <= MAX_INTEGER_BITS).then_some(value)
}

struct WorkBudget {
    remaining: usize,
}

impl WorkBudget {
    fn new() -> Self {
        Self {
            remaining: MAX_REACHABLE_NODES,
        }
    }

    fn spend(&mut self) -> Option<()> {
        if self.remaining == 0 {
            return None;
        }
        self.remaining -= 1;
        Some(())
    }
}

#[cfg(test)]
mod tests;
