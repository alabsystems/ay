// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Strict-mode schema validation for the set-cardinality STORE-CHAIN
//! recurrence — the definitional axiom AY injects for a `set.card` applied to
//! the elaborated form of `set.singleton` / `set.insert` / `set.remove`.
//!
//! # The schema
//!
//! Sets are carried as `Array(I → Bool)`; `set.insert` and `set.remove`
//! elaborate to `store(_, e, true)` / `store(_, e, false)`, and the empty set
//! to the constant-`false` array. The cardinality of such a chain is fixed by
//! the recurrence
//!
//! ```text
//! |B ∪ {e}| = |B| + 1   if e ∉ B        |B ∪ {e}| = |B|   if e ∈ B
//! |B \ {e}| = |B| − 1   if e ∈ B        |B \ {e}| = |B|   if e ∉ B
//! ```
//!
//! together with the base case `|∅| = 0`.
//!
//! # Why this is valid with no problem context
//!
//! EVERY sub-schema here requires the written-over base to be a store chain
//! ROOTED AT THE SYNTACTIC EMPTY SET. That single requirement is what makes the
//! axiom a theorem rather than an assumption: a finite chain of writes over the
//! empty carrier denotes a FINITE set, and the recurrence above is a theorem of
//! finite set theory. Over an unrestricted base it is NOT safe to hand out.
//! Take the interpretation
//!
//! ```text
//! card(X) = |X|   for finite X          card(X) = N   for infinite X
//! ```
//!
//! with `N` a fixed integer above every literal-membership count in the
//! problem. That interpretation satisfies every set-cardinality axiom AY
//! injects — `card ≥ 0`, the membership lower bound, `card(∅) = 0`, and the
//! recurrence over finite chains — and it falsifies
//! `|U| = |U \ {5}| + 1` (it reads `N = N + 1`) for the universal set `U`.
//! Requiring the empty root keeps every accepted instance inside the fragment
//! where the equations are simply true. AY's own producer imposes exactly the
//! same restriction and documents the same hazard: see
//! `Executor::is_covered_store_chain`, "admits a wrong model".
//!
//! # The two side conditions are established SEPARATELY
//!
//! There are two independent obligations on the written-over base `B`:
//!
//! 1. FINITENESS — `B` is a store chain rooted at the syntactic empty set.
//!    Decided by [`is_empty_rooted_chain`], which walks `B` all the way down.
//! 2. MEMBERSHIP — whether the written index is already in `B`. Decided by
//!    [`decide_membership`], which walks `B` only until the question is
//!    answered.
//!
//! These MUST NOT share a walk. [`decide_membership`] returns as soon as it
//! meets a write at the probed index, which on a chain like
//! `(store U 5 false)` happens at the OUTERMOST write — it never reaches, and
//! therefore never inspects, the root. A single walk answering both questions
//! accepts chains rooted at the universal set `((as const (Set Int)) true)` and
//! at a bare set VARIABLE, and the clause it then licenses is not a theorem.
//! [`matches_oriented`] therefore requires (1) on its own before consulting
//! (2), and `chain_root_is_not_reached_by_the_membership_walk` &c. in the test
//! module pin exactly that early-return path.
//!
//! The membership walk is likewise not taken on the producer's word: it steps
//! past a write ONLY when the write's index is syntactically identical to the
//! probe (a hit) or a DISTINCT LITERAL constant (a miss). Two symbolic indices
//! could denote the same element, so a chain that cannot be decided that way is
//! rejected fail-closed rather than guessed — the difference between
//! `|{x, y}| = 2` (false when `x = y`) and this module refusing to certify it.

use ay_core::{Constant, ProofId, Sort, Symbol, TermData, TermId, TermStore};

use crate::ProofCheckError;

#[cfg(test)]
#[path = "set_card_chain_tests.rs"]
mod tests;

/// The SMT-LIB set cardinality operator, as AY spells it.
///
/// A reserved operator name in `ay-frontend` (`RESERVED_OP_NAMES`), so a
/// surviving `set.card` application always denotes the native cardinality.
const OP_CARD: &str = "set.card";

/// Bound on the store chain this module will walk.
///
/// The walk is linear and every step is a constant-time syntactic test, so
/// this is a resource guard rather than a semantic one. Declining an oversized
/// chain leaves the verdict exactly as it is today (`unknown`), so the bound
/// can only ever cost completeness.
const MAX_CHAIN_DEPTH: usize = 4096;

/// Whether `term` is the SYNTACTIC empty set: a `set.empty` application, or
/// the constant array whose fill is exactly `false`.
///
/// The fill must be `false`. A `true` fill is the UNIVERSAL set, whose
/// cardinality is the index sort's size (unbounded over `Int`), so treating it
/// as a chain root would licence `|universe| = 0` and let a refutation be built
/// out of nothing.
fn is_syntactic_empty_set(terms: &TermStore, term: TermId) -> bool {
    if let Some(fill) = terms.get_const_array(term) {
        return matches!(terms.get(fill), TermData::Const(Constant::Bool(false)));
    }
    matches!(
        terms.get(term),
        TermData::App(Symbol::Named(name), args) if name == "set.empty" && args.is_empty()
    )
}

/// Decode a well-sorted `(store array index value)` over a `Bool`-valued
/// array — the elaborated form of a set insert/remove.
fn decode_set_store(terms: &TermStore, term: TermId) -> Option<(TermId, TermId, TermId)> {
    let TermData::App(Symbol::Named(name), args) = terms.get(term) else {
        return None;
    };
    if name != "store" {
        return None;
    }
    let [array, index, value] = args.as_slice() else {
        return None;
    };
    let Sort::Array(array_sort) = terms.sort(*array) else {
        return None;
    };
    // Well-sortedness at every position, and the membership carrier's `Bool`
    // element sort. A non-Bool carrier is a different theory's array and none
    // of the cardinality reasoning below applies to it.
    if array_sort.element_sort != Sort::Bool
        || terms.sort(*index) != &array_sort.index_sort
        || terms.sort(*value) != &Sort::Bool
        || terms.sort(term) != terms.sort(*array)
    {
        return None;
    }
    Some((*array, *index, *value))
}

/// FINITENESS. Whether `term` is a store chain bottoming out at the SYNTACTIC
/// empty set.
///
/// This is the whole justification for the recurrence being a theorem, so it is
/// decided on its own, by a walk that reaches the root or fails. It deliberately
/// asks NOTHING about membership: [`decide_membership`] short-circuits at the
/// first write on the probed index and can return an answer having seen only the
/// outermost link, so it can never be the thing that establishes this.
///
/// A chain rooted at a set VARIABLE, at the UNIVERSAL set (`const-array true`),
/// at a `select`/`ite`/uninterpreted array term, or at any non-`Bool` carrier is
/// rejected. So is a chain longer than [`MAX_CHAIN_DEPTH`] (fail-closed; the
/// verdict simply stays `unknown`).
///
/// Each link's stored VALUE may be symbolic: a `Bool`-valued write adds at most
/// one element whatever it evaluates to, so finiteness is preserved either way.
fn is_empty_rooted_chain(terms: &TermStore, term: TermId) -> bool {
    let mut current = term;
    for _ in 0..MAX_CHAIN_DEPTH {
        if is_syntactic_empty_set(terms, current) {
            return true;
        }
        let Some((inner, _, _)) = decode_set_store(terms, current) else {
            return false;
        };
        current = inner;
    }
    false
}

/// A term that is a literal CONSTANT, and therefore comparable for
/// distinctness by value.
///
/// Only constants qualify. Two distinct symbolic index terms may denote the
/// same element, so treating them as distinct is exactly the unsound step this
/// guards against.
fn literal_constant(terms: &TermStore, term: TermId) -> Option<&Constant> {
    match terms.get(term) {
        TermData::Const(constant) => Some(constant),
        _ => None,
    }
}

/// MEMBERSHIP. Statically decide `select(chain, probe)` by walking a store
/// chain outermost-first.
///
/// Returns `Some(true)` / `Some(false)` when the membership is decided by
/// syntax alone, and `None` when it is not — a symbolic index that is neither
/// syntactically the probe nor a distinct literal makes the chain
/// undecidable, and every caller then rejects.
///
/// THIS FUNCTION DOES NOT ESTABLISH THE EMPTY ROOT. It returns as soon as the
/// question is settled, which for a probe that the outermost write touches is
/// before a single deeper link has been looked at; on `(store U 5 false)` with
/// probe `5` it answers `Some(false)` while the universal set `U` sits
/// unexamined underneath. Callers must call [`is_empty_rooted_chain`]
/// separately. The `Some(false)` returned at a reached empty root is only ONE
/// of the ways this can answer, never a guarantee about the root.
fn decide_membership(terms: &TermStore, chain: TermId, probe: TermId) -> Option<bool> {
    let mut current = chain;
    for _ in 0..MAX_CHAIN_DEPTH {
        if is_syntactic_empty_set(terms, current) {
            return Some(false);
        }
        let (inner, index, value) = decode_set_store(terms, current)?;
        if index == probe {
            // A write AT the probe decides membership outright.
            return match terms.get(value) {
                TermData::Const(Constant::Bool(known)) => Some(*known),
                _ => None,
            };
        }
        // Skipping this write is sound only when the two indices are
        // provably different. Distinct literal constants are; anything else
        // is not, and the chain is undecidable.
        let (Some(written), Some(sought)) = (
            literal_constant(terms, index),
            literal_constant(terms, probe),
        ) else {
            return None;
        };
        if written == sought {
            // Equal by value but not syntactically identical (interning makes
            // this unreachable today). Treat it as a hit rather than skipping.
            return match terms.get(value) {
                TermData::Const(Constant::Bool(known)) => Some(*known),
                _ => None,
            };
        }
        current = inner;
    }
    None
}

/// Decode `(set.card s)`.
fn decode_card(terms: &TermStore, term: TermId) -> Option<TermId> {
    let TermData::App(Symbol::Named(name), args) = terms.get(term) else {
        return None;
    };
    if name != OP_CARD {
        return None;
    }
    let [set] = args.as_slice() else {
        return None;
    };
    (terms.sort(term) == &Sort::Int).then_some(*set)
}

/// Decode a binary `=`.
fn decode_equality(terms: &TermStore, term: TermId) -> Option<(TermId, TermId)> {
    let TermData::App(Symbol::Named(name), args) = terms.get(term) else {
        return None;
    };
    if name != "=" {
        return None;
    }
    let [left, right] = args.as_slice() else {
        return None;
    };
    Some((*left, *right))
}

/// Whether `term` is the integer constant `value`.
fn is_int_literal(terms: &TermStore, term: TermId, value: i64) -> bool {
    matches!(
        terms.get(term),
        TermData::Const(Constant::Int(actual)) if *actual == value.into()
    )
}

/// Decode `(<op> a b)` for `op` one of `+` / `-`.
fn decode_binary_arith(terms: &TermStore, term: TermId, op: &str) -> Option<(TermId, TermId)> {
    let TermData::App(Symbol::Named(name), args) = terms.get(term) else {
        return None;
    };
    if name != op {
        return None;
    }
    let [left, right] = args.as_slice() else {
        return None;
    };
    Some((*left, *right))
}

fn reject(step_id: ProofId, reason: String) -> Result<(), ProofCheckError> {
    Err(ProofCheckError::InvalidTheoryLemma {
        step: step_id,
        reason,
    })
}

/// Validate a [`TheoryLemmaKind::SetCardChainRecurrence`] lemma.
///
/// The clause is a single positive equality matching ONE of:
///
/// ```text
/// (= (set.card R) 0)                                   R syntactically empty
/// (= (set.card (store B e true))  (+ (set.card B) 1))   e ∉ B
/// (= (set.card (store B e true))  (set.card B))         e ∈ B
/// (= (set.card (store B e false)) (set.card B))         e ∉ B
/// (= (set.card (store B e false)) (- (set.card B) 1))   e ∈ B
/// ```
///
/// with `B` an EMPTY-ROOTED chain in every recurrence case, established by
/// [`is_empty_rooted_chain`] independently of the membership decision. Either
/// orientation of the `=` is accepted (equality is symmetric, so the two
/// spellings are the same claim); nothing else about the shape is searched.
///
/// The base case overlaps [`TheoryLemmaKind::SetCardEmpty`], whose validator
/// demands the identical syntactic-emptiness side condition and differs only in
/// fixing the equality's orientation. Nothing new is licensed by restating it.
///
/// A chain rooted at a set variable or at the universal set, and one whose
/// decisive index comparison is between symbolic terms, is rejected
/// fail-closed.
///
/// [`TheoryLemmaKind::SetCardChainRecurrence`]: ay_core::TheoryLemmaKind::SetCardChainRecurrence
/// [`TheoryLemmaKind::SetCardEmpty`]: ay_core::TheoryLemmaKind::SetCardEmpty
pub(crate) fn validate_set_card_chain_recurrence(
    terms: &TermStore,
    step_id: ProofId,
    clause: &[TermId],
) -> Result<(), ProofCheckError> {
    let [literal] = clause else {
        return reject(
            step_id,
            format!(
                "set-card-chain-recurrence clause must be a single equality literal, \
                 got {} literals",
                clause.len()
            ),
        );
    };
    if matches_chain_recurrence(terms, *literal) {
        return Ok(());
    }
    reject(
        step_id,
        "set-card-chain-recurrence literal does not match the exact schema: a positive \
         equality between `(set.card C)` for an EMPTY-ROOTED store chain `C` and the \
         value the definitional recurrence forces (`0` for the empty root; \
         `(+ (set.card B) 1)` / `(set.card B)` / `(- (set.card B) 1)` for a write over \
         an EMPTY-ROOTED `B`), with the write's membership side condition decided \
         syntactically by identical or distinct-literal indices"
            .to_string(),
    )
}

/// The whole schema, over both orientations of the equality.
fn matches_chain_recurrence(terms: &TermStore, literal: TermId) -> bool {
    if !matches!(terms.sort(literal), Sort::Bool) {
        return false;
    }
    let Some((left, right)) = decode_equality(terms, literal) else {
        return false;
    };
    matches_oriented(terms, left, right) || matches_oriented(terms, right, left)
}

/// One orientation: `(= (set.card OUTER) rhs)`.
fn matches_oriented(terms: &TermStore, card_side: TermId, rhs: TermId) -> bool {
    let Some(outer_set) = decode_card(terms, card_side) else {
        return false;
    };

    // Base case: the empty set has cardinality zero.
    if is_syntactic_empty_set(terms, outer_set) {
        return is_int_literal(terms, rhs, 0);
    }

    // Recurrence case: the outer set is one write over an empty-rooted chain.
    let Some((base, index, value)) = decode_set_store(terms, outer_set) else {
        return false;
    };
    // FINITENESS FIRST, and on its own walk. `decide_membership` below can
    // answer from the outermost write alone, so it must not be what confines
    // the schema to the finite fragment; without this line a chain rooted at
    // the universal set or at a set variable would be accepted and the clause
    // would not be a theorem.
    if !is_empty_rooted_chain(terms, base) {
        return false;
    }
    let TermData::Const(Constant::Bool(inserting)) = terms.get(value) else {
        return false;
    };
    // The membership side condition, re-derived rather than taken on trust.
    let Some(present) = decide_membership(terms, base, index) else {
        return false;
    };

    match (*inserting, present) {
        // Insert of an absent element: the count goes up by exactly one.
        (true, false) => matches_card_offset(terms, rhs, base, 1),
        // Insert of a present element, or removal of an absent one: no change.
        // The emitter folds the `+ 0` / `- 0` away, so the right-hand side is
        // the bare inner cardinality.
        (true, true) | (false, false) => matches_card_offset(terms, rhs, base, 0),
        // Removal of a present element: the count goes down by exactly one.
        (false, true) => matches_card_offset(terms, rhs, base, -1),
    }
}

/// Whether `rhs` is exactly `(set.card base) + offset`.
///
/// `TermStore` normalizes `a - b` into `(+ a (- b))` and folds a literal
/// negation, so the emitted spelling of a decrement is `(+ card -1)`. Both
/// that form and the literal `(- card 1)` are accepted, as is either operand
/// order of the commutative `+`. Every accepted spelling denotes the SAME
/// arithmetic term; nothing about the magnitude is searched.
fn matches_card_offset(terms: &TermStore, rhs: TermId, base: TermId, offset: i64) -> bool {
    let is_base_card = |term: TermId| decode_card(terms, term) == Some(base);

    if offset == 0 {
        return is_base_card(rhs);
    }
    if let Some((left, right)) = decode_binary_arith(terms, rhs, "+") {
        if (is_base_card(left) && is_int_literal(terms, right, offset))
            || (is_base_card(right) && is_int_literal(terms, left, offset))
        {
            return true;
        }
    }
    // The un-normalized `(- card k)` spelling, for a decrement only.
    if offset < 0 {
        if let Some((left, right)) = decode_binary_arith(terms, rhs, "-") {
            return is_base_card(left) && is_int_literal(terms, right, -offset);
        }
    }
    false
}

/// The CHECKER'S OWN matcher for the chain recurrence.
///
/// Producers call this rather than re-implementing the schema. The answer is a
/// hint only: [`validate_set_card_chain_recurrence`] re-runs the identical test
/// when the proof is checked, so a matcher bug can cost completeness but can
/// never admit an unchecked clause.
#[must_use]
pub fn recognize_set_card_chain_recurrence(
    terms: &TermStore,
    clause: &[TermId],
) -> Option<ay_core::TheoryLemmaKind> {
    validate_set_card_chain_recurrence(terms, ProofId(0), clause)
        .is_ok()
        .then_some(ay_core::TheoryLemmaKind::SetCardChainRecurrence)
}
