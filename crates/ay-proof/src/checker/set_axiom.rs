// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Strict-mode schema validation for the set `TheoryLemmaKind`s.
//!
//! Currently one kind: `SetCardNonNegative`, the bridge axiom AY injects for
//! every `set.card` term it encounters.
//!
//! The axiom is `(<= 0 (set.card s))` for an arbitrary set term `s`. It holds
//! unconditionally -- a set has a non-negative number of elements whatever it
//! contains -- so the schema alone licenses it and no side condition on `s` is
//! needed. That is what makes it checkable at all: unlike
//! `ArrayExtensionality`, nothing here depends on the surrounding problem.
//!
//! The check is deliberately exact rather than "contains a cardinality term".
//! A lemma kind is a licence to believe a clause without a derivation, so a
//! loose schema here is a forging surface: accepting, say, any clause
//! MENTIONING `set.card` would licence `(<= 5 (set.card s))`, which is false
//! for the empty set and would let a refutation be built out of nothing.

use std::collections::VecDeque;
use std::mem::size_of;

use ay_core::{Constant, ProofId, Sort, TermData, TermId, TermStore};
use num_traits::Zero;

use ay_core::kani_compat::{DetHashMap, DetHashSet};

use crate::ProofCheckError;

/// Set terms the PROBLEM unconditionally asserts to be empty.
///
/// Built once per proof from the problem's TOP-LEVEL assertions, because only
/// those hold in every model. An equality nested under a negation or a
/// disjunction is NOT unconditional -- harvesting one would licence
/// `|s| = 0` for a set the problem never claims is empty.
#[derive(Debug, Default)]
pub(crate) struct EmptySetRegistry {
    known_empty: DetHashSet<TermId>,
}

impl EmptySetRegistry {
    /// Close the syntactically-empty sets under the problem's asserted
    /// equalities. `(assert (= s empty))` makes `s` empty; `(assert (= t s))`
    /// then makes `t` empty too, closing the whole equality component.
    pub(crate) fn collect(terms: &TermStore, problem_assertions: &[TermId]) -> Self {
        let mut unbounded = |_: usize, _: usize| true;
        // The unbounded callback cannot reject. A checked-size overflow is
        // therefore the only possible error, and an empty registry is the
        // fail-closed result: it may reject a valid lemma but cannot admit an
        // unsupported one.
        Self::collect_with_progress(terms, problem_assertions, &mut unbounded).unwrap_or_default()
    }

    /// Metered, linear-time construction for strict authentication.
    ///
    /// The old repeated equality scan was quadratic on a reverse-ordered
    /// chain. This builds an undirected equality graph once and propagates
    /// emptiness with one breadth-first traversal. `progress` is called before
    /// each allocation/work block, including every equality edge.
    pub(crate) fn collect_with_progress(
        terms: &TermStore,
        problem_assertions: &[TermId],
        progress: &mut dyn FnMut(usize, usize) -> bool,
    ) -> Result<Self, ProofCheckError> {
        let mut adjacency: DetHashMap<TermId, Vec<TermId>> = DetHashMap::default();
        let mut known_empty = DetHashSet::default();
        let mut queue = VecDeque::new();

        for &assertion in problem_assertions {
            registry_charge(progress, 1, 0)?;
            let TermData::App(operator, args) = terms.get(assertion) else {
                continue;
            };
            let [lhs, rhs] = args.as_slice() else {
                continue;
            };
            if operator.name() != "=" {
                continue;
            }

            // Conservatively charge a map entry and vector allocation in both
            // directions even when an endpoint already has an adjacency list.
            // Overcharging is safe and avoids allocator-specific accounting.
            let directed_edge_bytes = checked_registry_add(
                size_of::<TermId>(),
                checked_registry_add(size_of::<Vec<TermId>>(), size_of::<TermId>())?,
            )?;
            registry_charge(progress, 2, checked_registry_mul(directed_edge_bytes, 2)?)?;
            adjacency.entry(*lhs).or_default().push(*rhs);
            adjacency.entry(*rhs).or_default().push(*lhs);

            for side in [*lhs, *rhs] {
                let seed_bytes = checked_registry_add(size_of::<TermId>() * 2, 32)?;
                registry_charge(progress, 1, seed_bytes)?;
                if is_syntactically_empty_set(terms, side) && known_empty.insert(side) {
                    queue.push_back(side);
                }
            }
        }

        while let Some(empty) = queue.pop_front() {
            registry_charge(progress, 1, 0)?;
            let Some(neighbors) = adjacency.get(&empty) else {
                continue;
            };
            for &neighbor in neighbors {
                // Hash-set entry plus the possible queue element. Charging it
                // for duplicates too is conservative while work remains one
                // callback/predicate/insert attempt per directed edge.
                let discovered_bytes = checked_registry_add(size_of::<TermId>() * 2, 32)?;
                registry_charge(progress, 1, discovered_bytes)?;
                if known_empty.insert(neighbor) {
                    queue.push_back(neighbor);
                }
            }
        }

        Ok(Self { known_empty })
    }

    /// Whether the problem forces `term` to be the empty set.
    pub(crate) fn is_known_empty(&self, terms: &TermStore, term: TermId) -> bool {
        is_syntactically_empty_set(terms, term) || self.known_empty.contains(&term)
    }
}

fn registry_charge(
    progress: &mut dyn FnMut(usize, usize) -> bool,
    work: usize,
    bytes: usize,
) -> Result<(), ProofCheckError> {
    if progress(work, bytes) {
        Ok(())
    } else {
        Err(ProofCheckError::ResourceLimit)
    }
}

fn checked_registry_add(left: usize, right: usize) -> Result<usize, ProofCheckError> {
    left.checked_add(right)
        .ok_or(ProofCheckError::ResourceLimit)
}

fn checked_registry_mul(left: usize, right: usize) -> Result<usize, ProofCheckError> {
    left.checked_mul(right)
        .ok_or(ProofCheckError::ResourceLimit)
}

/// Validate a `SetCardEmptyByAssertion` lemma: `(= (set.card s) 0)` where the
/// PROBLEM asserts `s` empty.
///
/// Fails closed without a registry: no problem assertions means no evidence,
/// and this kind is not a tautology.
pub(crate) fn validate_set_card_empty_by_assertion(
    terms: &TermStore,
    step_id: ProofId,
    clause: &[TermId],
    empty_sets: Option<&EmptySetRegistry>,
) -> Result<(), ProofCheckError> {
    let reject = |reason: String| {
        Err(ProofCheckError::InvalidTheoryLemma {
            step: step_id,
            reason,
        })
    };

    let Some(empty_sets) = empty_sets else {
        return reject(
            "set-card-empty-by-assertion needs the problem assertions to know the \
             set is empty, and none were supplied"
                .to_string(),
        );
    };
    let [literal] = clause else {
        return reject("set-card-empty-by-assertion clause must be a single literal".to_string());
    };
    let TermData::App(equality, equality_args) = terms.get(*literal) else {
        return reject("set-card-empty-by-assertion literal must be an equality".to_string());
    };
    if equality.name() != "=" || equality_args.len() != 2 {
        return reject("set-card-empty-by-assertion literal must be a binary `=`".to_string());
    }
    match terms.get(equality_args[1]) {
        TermData::Const(Constant::Int(value)) if value.is_zero() => {}
        _ => return reject("set-card-empty-by-assertion must equate to 0".to_string()),
    }
    let TermData::App(operator, operator_args) = terms.get(equality_args[0]) else {
        return reject(format!(
            "set-card-empty-by-assertion must equate a `{OP_CARD}`"
        ));
    };
    if operator.name() != OP_CARD || operator_args.len() != 1 {
        return reject(format!(
            "set-card-empty-by-assertion must equate a unary `{OP_CARD}`"
        ));
    }
    if !empty_sets.is_known_empty(terms, operator_args[0]) {
        return reject(
            "set-card-empty-by-assertion applies only to a set the PROBLEM asserts \
             empty (directly, or through a chain of asserted equalities)"
                .to_string(),
        );
    }
    Ok(())
}

/// The SMT-LIB set cardinality operator, as AY spells it.
const OP_CARD: &str = "set.card";

/// Validate a `SetCardNonNegative` lemma: exactly `(<= 0 (set.card s))`.
pub(crate) fn validate_set_card_non_negative(
    terms: &TermStore,
    step_id: ProofId,
    clause: &[TermId],
) -> Result<(), ProofCheckError> {
    let reject = |reason: String| {
        Err(ProofCheckError::InvalidTheoryLemma {
            step: step_id,
            reason,
        })
    };

    // A unit clause. The axiom is a single positive literal, so anything else
    // -- extra literals, an empty clause -- is outside the schema.
    let [literal] = clause else {
        return reject(format!(
            "set-card-non-negative clause must be the single literal \
             `(<= 0 ({OP_CARD} s))`, got {} literals",
            clause.len()
        ));
    };
    if !matches!(terms.sort(*literal), Sort::Bool) {
        return reject("set-card-non-negative literal must be Boolean".to_string());
    }

    let TermData::App(comparison, comparison_args) = terms.get(*literal) else {
        return reject(format!(
            "set-card-non-negative literal must be an application of `<=`, \
             not {:?}",
            terms.get(*literal)
        ));
    };
    // `mk_ge(card, 0)` canonicalizes to `(<= 0 card)`, so `<=` with the bound
    // on the LEFT is the only shape AY produces and the only one accepted.
    if comparison.name() != "<=" || comparison_args.len() != 2 {
        return reject(format!(
            "set-card-non-negative literal must be `(<= 0 ({OP_CARD} s))`, \
             got a {}-ary `{}`",
            comparison_args.len(),
            comparison.name()
        ));
    }

    let (bound, cardinality) = (comparison_args[0], comparison_args[1]);
    match terms.get(bound) {
        TermData::Const(Constant::Int(value)) if value.is_zero() => {}
        TermData::Const(Constant::Int(value)) => {
            return reject(format!(
                "set-card-non-negative bound must be exactly 0, got {value} -- \
                 a positive lower bound is FALSE for the empty set"
            ));
        }
        other => {
            return reject(format!(
                "set-card-non-negative bound must be the integer literal 0, \
                 not {other:?}"
            ));
        }
    }

    let TermData::App(operator, operator_args) = terms.get(cardinality) else {
        return reject(format!(
            "set-card-non-negative must bound a `{OP_CARD}` application, not \
             {:?}",
            terms.get(cardinality)
        ));
    };
    if operator.name() != OP_CARD || operator_args.len() != 1 {
        return reject(format!(
            "set-card-non-negative must bound a unary `{OP_CARD}`, got a \
             {}-ary `{}`",
            operator_args.len(),
            operator.name()
        ));
    }

    // The cardinality itself must be an integer. The argument sort is
    // deliberately NOT constrained: the axiom holds for every set term,
    // including ones the checker has no sort information for.
    if !matches!(terms.sort(cardinality), Sort::Int) {
        return reject(format!(
            "`{OP_CARD}` must have sort Int, got {:?}",
            terms.sort(cardinality)
        ));
    }

    Ok(())
}

#[cfg(test)]
#[path = "set_axiom_tests.rs"]
mod tests;

/// The set a membership test is about, for either spelling.
///
/// Elaboration lowers `(set.member x s)` to `(select s x)`, so both reach the
/// checker; the set is arg0 of `select` and arg1 of `set.member`.
fn membership_set(terms: &TermStore, term: TermId) -> Option<TermId> {
    let TermData::App(operator, args) = terms.get(term) else {
        return None;
    };
    match (operator.name(), args.len()) {
        ("select", 2) => Some(args[0]),
        ("set.member", 2) => Some(args[1]),
        _ => None,
    }
}

/// `(<= <bound> (set.card s))` -- returns the set whose cardinality is bounded.
fn card_lower_bounded_by(terms: &TermStore, term: TermId, bound: i64) -> Option<TermId> {
    let TermData::App(comparison, comparison_args) = terms.get(term) else {
        return None;
    };
    if comparison.name() != "<=" || comparison_args.len() != 2 {
        return None;
    }
    match terms.get(comparison_args[0]) {
        TermData::Const(Constant::Int(value)) if *value == bound.into() => {}
        _ => return None,
    }
    let TermData::App(operator, operator_args) = terms.get(comparison_args[1]) else {
        return None;
    };
    (operator.name() == OP_CARD && operator_args.len() == 1).then(|| operator_args[0])
}

/// Validate a `SetCardMemberLowerBound` lemma:
/// `(ite (member x s) (<= 1 (set.card s)) (<= 0 (set.card s)))`.
pub(crate) fn validate_set_card_member_lower_bound(
    terms: &TermStore,
    step_id: ProofId,
    clause: &[TermId],
) -> Result<(), ProofCheckError> {
    let reject = |reason: String| {
        Err(ProofCheckError::InvalidTheoryLemma {
            step: step_id,
            reason,
        })
    };

    let [literal] = clause else {
        return reject(format!(
            "set-card-member-lower-bound clause must be a single ite literal, \
             got {} literals",
            clause.len()
        ));
    };
    let TermData::Ite(condition, then_branch, else_branch) = terms.get(*literal) else {
        return reject("set-card-member-lower-bound literal must be an `ite`".to_string());
    };

    let Some(tested) = membership_set(terms, *condition) else {
        return reject(
            "set-card-member-lower-bound condition must be a membership test \
             (`select` or `set.member`)"
                .to_string(),
        );
    };
    let Some(bounded_when_member) = card_lower_bounded_by(terms, *then_branch, 1) else {
        return reject(format!(
            "set-card-member-lower-bound `then` branch must be \
             `(<= 1 ({OP_CARD} s))`"
        ));
    };
    let Some(bounded_otherwise) = card_lower_bounded_by(terms, *else_branch, 0) else {
        return reject(format!(
            "set-card-member-lower-bound `else` branch must be \
             `(<= 0 ({OP_CARD} s))`"
        ));
    };

    // The identity IS the axiom. Without it this would licence
    // `x in s => |t| >= 1` for an unrelated `t`, which is plainly false.
    if tested != bounded_when_member || tested != bounded_otherwise {
        return reject(
            "set-card-member-lower-bound must bound the cardinality of the \
             SAME set the membership test is about"
                .to_string(),
        );
    }
    Ok(())
}

/// Whether `term` is SYNTACTICALLY the empty set.
///
/// The constant array with fill `false` (no member), or a nullary `set.empty`.
/// A `true` fill is the UNIVERSAL set and must never match here.
fn is_syntactically_empty_set(terms: &TermStore, term: TermId) -> bool {
    let TermData::App(operator, args) = terms.get(term) else {
        return false;
    };
    match operator.name() {
        "set.empty" => args.is_empty(),
        "const-array" => matches!(
            args.as_slice(),
            [fill] if matches!(terms.get(*fill), TermData::Const(Constant::Bool(false)))
        ),
        _ => false,
    }
}

/// Validate a `SetCardEmpty` lemma: exactly `(= (set.card e) 0)` for a
/// syntactically empty `e`.
pub(crate) fn validate_set_card_empty(
    terms: &TermStore,
    step_id: ProofId,
    clause: &[TermId],
) -> Result<(), ProofCheckError> {
    let reject = |reason: String| {
        Err(ProofCheckError::InvalidTheoryLemma {
            step: step_id,
            reason,
        })
    };

    let [literal] = clause else {
        return reject(format!(
            "set-card-empty clause must be the single literal \
             `(= ({OP_CARD} e) 0)`, got {} literals",
            clause.len()
        ));
    };
    let TermData::App(equality, equality_args) = terms.get(*literal) else {
        return reject("set-card-empty literal must be an equality".to_string());
    };
    if equality.name() != "=" || equality_args.len() != 2 {
        return reject("set-card-empty literal must be a binary `=`".to_string());
    }

    let (cardinality, zero) = (equality_args[0], equality_args[1]);
    match terms.get(zero) {
        TermData::Const(Constant::Int(value)) if value.is_zero() => {}
        _ => {
            return reject(
                "set-card-empty must equate the cardinality to the integer literal 0".to_string(),
            );
        }
    }

    let TermData::App(operator, operator_args) = terms.get(cardinality) else {
        return reject(format!(
            "set-card-empty must equate a `{OP_CARD}` application"
        ));
    };
    if operator.name() != OP_CARD || operator_args.len() != 1 {
        return reject(format!("set-card-empty must equate a unary `{OP_CARD}`"));
    }
    if !is_syntactically_empty_set(terms, operator_args[0]) {
        return reject(
            "set-card-empty applies only to a SYNTACTICALLY empty set (`set.empty`, \
             or a constant array with fill `false`); a `true` fill is the universal set"
                .to_string(),
        );
    }
    Ok(())
}

/// The integer literal an index term denotes, if it is one.
///
/// Only literals are accepted. Two VARIABLE indices could denote the same
/// element, so counting them as two members would licence `|{x}| >= 2`.
fn integer_index(terms: &TermStore, term: TermId) -> Option<&num_bigint::BigInt> {
    match terms.get(term) {
        TermData::Const(Constant::Int(value)) => Some(value),
        _ => None,
    }
}

const SET_MEMBER_COUNT_WORK_LIMIT: usize = 100_000_000;
const SET_MEMBER_COUNT_DEPTH_LIMIT: usize = 512;

fn charge_member_count(work: &mut usize, amount: usize) -> Result<(), String> {
    let Some(next) = work.checked_add(amount) else {
        return Err("set-card-member-count work accounting overflow".to_string());
    };
    if next > SET_MEMBER_COUNT_WORK_LIMIT {
        return Err(format!(
            "set-card-member-count exceeds {SET_MEMBER_COUNT_WORK_LIMIT} checked operations"
        ));
    }
    *work = next;
    Ok(())
}

/// Walk the membership tree, checking every leaf bounds `card` below by the
/// number of memberships holding on the path to it.
fn walk_member_count(
    terms: &TermStore,
    node: TermId,
    set: TermId,
    card: TermId,
    path: &mut Vec<num_bigint::BigInt>,
    work: &mut usize,
    depth: usize,
) -> Result<(), String> {
    if depth > SET_MEMBER_COUNT_DEPTH_LIMIT {
        return Err(format!(
            "set-card-member-count exceeds depth {SET_MEMBER_COUNT_DEPTH_LIMIT}"
        ));
    }
    charge_member_count(
        work,
        path.len()
            .checked_add(1)
            .ok_or_else(|| "set-card-member-count path-length accounting overflow".to_string())?,
    )?;
    let TermData::Ite(condition, then_branch, else_branch) = terms.get(node) else {
        // Leaf: `(<= |path| (set.card s))` over the SAME set.
        let Some(bounded) = card_lower_bounded_by_term(terms, node, path.len()) else {
            return Err(format!(
                "leaf must be `(<= {} ({OP_CARD} s))` for the {} membership(s) \
                 holding on its path",
                path.len(),
                path.len()
            ));
        };
        if bounded != card {
            return Err("every leaf must bound the SAME cardinality term".to_string());
        }
        return Ok(());
    };

    let Some(tested) = membership_set(terms, *condition) else {
        return Err("each interior condition must be a membership test".to_string());
    };
    if tested != set {
        return Err("every membership test must be about the SAME set".to_string());
    }
    let index = match terms.get(*condition) {
        TermData::App(operator, args) if operator.name() == "select" => args[1],
        TermData::App(_, args) => args[0],
        _ => return Err("malformed membership test".to_string()),
    };
    let Some(value) = integer_index(terms, index) else {
        return Err(
            "membership indices must be integer LITERALS: two variable indices \
             could denote the same element, so counting them separately would \
             licence a cardinality bound the set does not have"
                .to_string(),
        );
    };
    if path.contains(value) {
        return Err(
            "membership indices must be pairwise DISTINCT; counting one element \
             twice inflates the cardinality bound"
                .to_string(),
        );
    }

    path.push(value.clone());
    let child_depth = depth
        .checked_add(1)
        .ok_or_else(|| "set-card-member-count depth overflow".to_string())?;
    let then_ok = walk_member_count(terms, *then_branch, set, card, path, work, child_depth);
    path.pop();
    then_ok?;
    walk_member_count(terms, *else_branch, set, card, path, work, child_depth)
}

/// `(<= <count> (set.card s))` -- returns the bounded set, for a usize count.
fn card_lower_bounded_by_term(terms: &TermStore, term: TermId, count: usize) -> Option<TermId> {
    let TermData::App(comparison, comparison_args) = terms.get(term) else {
        return None;
    };
    if comparison.name() != "<=" || comparison_args.len() != 2 {
        return None;
    }
    match terms.get(comparison_args[0]) {
        TermData::Const(Constant::Int(value)) if *value == count.into() => {}
        _ => return None,
    }
    let TermData::App(operator, operator_args) = terms.get(comparison_args[1]) else {
        return None;
    };
    (operator.name() == OP_CARD && operator_args.len() == 1).then_some(comparison_args[1])
}

/// Validate a `SetCardMemberCount` lemma.
pub(crate) fn validate_set_card_member_count(
    terms: &TermStore,
    step_id: ProofId,
    clause: &[TermId],
) -> Result<(), ProofCheckError> {
    let reject = |reason: String| {
        Err(ProofCheckError::InvalidTheoryLemma {
            step: step_id,
            reason,
        })
    };

    let [literal] = clause else {
        return reject("set-card-member-count clause must be a single literal".to_string());
    };
    let TermData::Ite(condition, ..) = terms.get(*literal) else {
        return reject("set-card-member-count literal must be an `ite` tree".to_string());
    };
    let Some(set) = membership_set(terms, *condition) else {
        return reject("the root condition must be a membership test".to_string());
    };
    // Anchor the cardinality term from the set itself, so a leaf bounding some
    // OTHER set's cardinality cannot define the anchor and then match itself.
    let mut work = 0_usize;
    let Some(card) = find_card_of(terms, *literal, set, &mut work, 0).map_err(|reason| {
        ProofCheckError::InvalidTheoryLemma {
            step: step_id,
            reason: format!("set-card-member-count: {reason}"),
        }
    })?
    else {
        return reject(format!("no `({OP_CARD} s)` over the tested set was found"));
    };

    let mut path = Vec::new();
    match walk_member_count(terms, *literal, set, card, &mut path, &mut work, 0) {
        Ok(()) => Ok(()),
        Err(reason) => reject(format!("set-card-member-count: {reason}")),
    }
}

/// Find `(set.card set)` anywhere in `node` (the tree's leaves all use it).
fn find_card_of(
    terms: &TermStore,
    node: TermId,
    set: TermId,
    work: &mut usize,
    depth: usize,
) -> Result<Option<TermId>, String> {
    if depth > SET_MEMBER_COUNT_DEPTH_LIMIT {
        return Err(format!(
            "set-card-member-count search exceeds depth {SET_MEMBER_COUNT_DEPTH_LIMIT}"
        ));
    }
    charge_member_count(work, 1)?;
    let child_depth = depth
        .checked_add(1)
        .ok_or_else(|| "set-card-member-count search depth overflow".to_string())?;
    match terms.get(node) {
        TermData::Ite(_, then_branch, else_branch) => {
            if let Some(card) = find_card_of(terms, *then_branch, set, work, child_depth)? {
                Ok(Some(card))
            } else {
                find_card_of(terms, *else_branch, set, work, child_depth)
            }
        }
        TermData::App(operator, args) => {
            if operator.name() == OP_CARD && args.len() == 1 && args[0] == set {
                return Ok(Some(node));
            }
            for &arg in args {
                if let Some(card) = find_card_of(terms, arg, set, work, child_depth)? {
                    return Ok(Some(card));
                }
            }
            Ok(None)
        }
        _ => Ok(None),
    }
}
