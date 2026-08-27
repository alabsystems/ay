// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Strict semantic validation for the two SYMBOLIC word-identity lemma kinds:
//!
//! - [`TheoryLemmaKind::StringContainmentIdentity`] — the reflexive and
//!   empty-string containment/order theorems of the SMT-LIB 2.6 string theory.
//! - [`TheoryLemmaKind::StringConcatCancellation`] — free-monoid cancellation,
//!   `u·w = v·w → u = v` and `w·u = w·v → u = v`.
//! - [`TheoryLemmaKind::StringGroundFactorConflict`] — a containment made
//!   impossible by the ground blocks it names.
//!
//! Both are counterparts of [`super::string_ground`]'s `StringGroundEval`,
//! which only decides facts whose subject is a CONSTANT. These two decide facts
//! whose subject is symbolic, and they do it the only way a checker honestly
//! can: by re-deriving the exact closed-form theorem from the clause itself.
//!
//! # Soundness
//!
//! Every accepted shape is a theorem of the SMT-LIB 2.6 Unicode-strings theory,
//! so a clause carrying it is true under every interpretation and the unit
//! lemma introducing it is valid.
//!
//! * A string contains, is a prefix of, is a suffix of, and is `str.<=` itself;
//!   it is never `str.<` itself. Those five are pure reflexivity/irreflexivity
//!   of relations SMT-LIB defines on the same word, so the ONLY thing this
//!   module checks is that the two argument positions hold the SAME `TermId` —
//!   the whole content of the theorem. Two syntactically different terms could
//!   denote different words, so nothing weaker is accepted.
//! * The empty word is a substring, a prefix and a suffix of every word.
//!   `str.contains` takes the container FIRST and the contained word second,
//!   `str.prefixof`/`str.suffixof` take the contained word first, so the
//!   empty-string position differs between them and is checked per operator.
//! * `str.++` denotes concatenation in the FREE monoid over the SMT-LIB
//!   alphabet, in which every element is cancellative on both sides:
//!   `u·w = v·w` forces `u = v`, and `w·u = w·v` forces `u = v`. The cancelled
//!   block must be a syntactically identical operand list, position by
//!   position, because two different terms may denote different words.
//! * `str.contains C T` says T's value is a CONTIGUOUS factor of C's, and a
//!   factor of a factor is a factor — so every concat block of T is a factor of
//!   C. A ground block absent from a ground container therefore refutes the
//!   containment for EVERY value of the symbolic blocks. `str.prefixof K T` and
//!   `str.suffixof K T` pin K against T's leading/trailing block: when K is no
//!   longer than that ground block, K must be its prefix/suffix, so a
//!   disagreement refutes the predicate outright. Both arguments are about the
//!   ground data the clause itself carries, never about the symbolic parts.
//!
//! # Fail-closed
//!
//! Anything not matching one of the exact shapes is REJECTED. There is no
//! "assume valid" arm, no label matching, and no call into the solver's string
//! theory — a producer's `kind` annotation carries no authority here.
//!
//! [`TheoryLemmaKind::StringContainmentIdentity`]: ay_core::TheoryLemmaKind::StringContainmentIdentity
//! [`TheoryLemmaKind::StringConcatCancellation`]: ay_core::TheoryLemmaKind::StringConcatCancellation

use ay_core::{Constant, ProofId, Sort, Symbol, TermData, TermId, TermStore};

use super::ProofCheckError;

/// Most `str.++` operands either side of a cancellation may carry. Exhaustion
/// REJECTS, so this is a bound on work, never on soundness.
const MAX_CONCAT_OPERANDS: usize = 1024;

// ---------------------------------------------------------------------------
// Shared helpers
// ---------------------------------------------------------------------------

/// Decompose `t` into `(name, args)` when it is a NAMED application. Indexed
/// applications (`(_ re.loop 3 5)`) are deliberately not accepted: none of the
/// theorems below is stated over one.
fn as_named_app(terms: &TermStore, t: TermId) -> Option<(&str, &[TermId])> {
    match terms.get(t) {
        TermData::App(Symbol::Named(name), args) => Some((name.as_str(), args.as_slice())),
        _ => None,
    }
}

/// Strip `Not` wrappers, returning `(atom, is_positive)`.
fn strip_negations(terms: &TermStore, mut t: TermId) -> (TermId, bool) {
    let mut positive = true;
    while let TermData::Not(inner) = terms.get(t) {
        t = *inner;
        positive = !positive;
    }
    (t, positive)
}

/// Whether `t` is the empty string constant `""`.
fn is_empty_string(terms: &TermStore, t: TermId) -> bool {
    matches!(
        (terms.get(t), terms.sort(t)),
        (TermData::Const(Constant::String(s)), Sort::String) if s.is_empty()
    )
}

fn is_string_sorted(terms: &TermStore, t: TermId) -> bool {
    matches!(terms.sort(t), Sort::String)
}

/// Reject a clause that is empty or carries a non-Boolean literal — the shared
/// hygiene every theory-lemma clause must satisfy.
fn check_propositional_clause(
    terms: &TermStore,
    step_id: ProofId,
    clause: &[TermId],
    context: &str,
) -> Result<(), ProofCheckError> {
    if clause.is_empty() {
        return Err(ProofCheckError::InvalidTheoryLemma {
            step: step_id,
            reason: format!("{context} clause must be non-empty"),
        });
    }
    for &lit in clause {
        if !matches!(terms.sort(lit), Sort::Bool) {
            return Err(ProofCheckError::InvalidTheoryLemma {
                step: step_id,
                reason: format!(
                    "{context} literal has non-Bool sort {:?}; lemma clauses must be \
                     propositional",
                    terms.sort(lit)
                ),
            });
        }
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// 1. Containment / order identities
// ---------------------------------------------------------------------------

/// Validate a `TheoryLemmaKind::StringContainmentIdentity` in strict mode.
pub(crate) fn validate_string_containment_identity(
    terms: &TermStore,
    step_id: ProofId,
    clause: &[TermId],
) -> Result<(), ProofCheckError> {
    check_propositional_clause(terms, step_id, clause, "string_containment_identity")?;
    if clause
        .iter()
        .any(|&lit| is_valid_containment_identity(terms, lit))
    {
        return Ok(());
    }
    Err(ProofCheckError::InvalidTheoryLemma {
        step: step_id,
        reason: "string_containment_identity clause has no literal the independent \
                 checker proves to be a universally-valid containment/order identity \
                 (self-containment, self-prefix, self-suffix, str.<= reflexivity, \
                 str.< irreflexivity, or an empty-string containment); rejecting in \
                 fail-closed mode"
            .to_string(),
    })
}

/// Recognize a clause the strict `StringContainmentIdentity` validator will
/// accept.
///
/// This is the EXACT precondition of `validate_string_containment_identity`,
/// so a proof producer can only tag clauses strict mode will then accept — no
/// producer/checker drift. Decision logic lives ONLY in this module.
#[must_use]
pub fn recognize_string_containment_identity(terms: &TermStore, clause: &[TermId]) -> bool {
    if clause.is_empty() {
        return false;
    }
    if clause
        .iter()
        .any(|&lit| !matches!(terms.sort(lit), Sort::Bool))
    {
        return false;
    }
    clause
        .iter()
        .any(|&lit| is_valid_containment_identity(terms, lit))
}

/// Whether `lit` is one of the recognized universally-valid identities.
fn is_valid_containment_identity(terms: &TermStore, lit: TermId) -> bool {
    let (atom, positive) = strip_negations(terms, lit);
    let Some((name, args)) = as_named_app(terms, atom) else {
        return false;
    };
    if args.len() != 2
        || !matches!(terms.sort(atom), Sort::Bool)
        || !is_string_sorted(terms, args[0])
        || !is_string_sorted(terms, args[1])
    {
        return false;
    }
    let same_word = args[0] == args[1];
    match (name, positive) {
        // A word contains itself, and it contains the empty word. SMT-LIB's
        // `str.contains` takes the CONTAINER first, so the empty-word position
        // is argument 1.
        ("str.contains", true) => same_word || is_empty_string(terms, args[1]),
        // A word is its own prefix/suffix, and the empty word is a prefix and a
        // suffix of every word. These take the CONTAINED word first, so the
        // empty-word position is argument 0.
        ("str.prefixof" | "str.suffixof", true) => same_word || is_empty_string(terms, args[0]),
        // `str.<=` is reflexive; the two positions must hold the SAME term,
        // which is the entire content of the theorem.
        ("str.<=", true) => same_word,
        // `str.<` is a STRICT order, so it is irreflexive: `(not (str.< t t))`.
        ("str.<", false) => same_word,
        _ => false,
    }
}

// ---------------------------------------------------------------------------
// 2. Free-monoid concatenation cancellation
// ---------------------------------------------------------------------------

/// Validate a `TheoryLemmaKind::StringConcatCancellation` in strict mode.
pub(crate) fn validate_string_concat_cancellation(
    terms: &TermStore,
    step_id: ProofId,
    clause: &[TermId],
) -> Result<(), ProofCheckError> {
    check_propositional_clause(terms, step_id, clause, "string_concat_cancellation")?;
    if clause_is_concat_cancellation(terms, clause) {
        return Ok(());
    }
    Err(ProofCheckError::InvalidTheoryLemma {
        step: step_id,
        reason: "string_concat_cancellation clause is not the two-literal \
                 free-monoid cancellation theorem \
                 `(cl (not (= (str.++ .. W) (str.++ .. W))) (= .. ..))` (or its \
                 left-cancellation mirror) with a syntactically identical \
                 cancelled block; rejecting in fail-closed mode"
            .to_string(),
    })
}

/// Recognize a clause the strict `StringConcatCancellation` validator will
/// accept.
///
/// This is the EXACT precondition of `validate_string_concat_cancellation`.
#[must_use]
pub fn recognize_string_concat_cancellation(terms: &TermStore, clause: &[TermId]) -> bool {
    if clause.is_empty() {
        return false;
    }
    if clause
        .iter()
        .any(|&lit| !matches!(terms.sort(lit), Sort::Bool))
    {
        return false;
    }
    clause_is_concat_cancellation(terms, clause)
}

fn clause_is_concat_cancellation(terms: &TermStore, clause: &[TermId]) -> bool {
    if clause.len() != 2 {
        return false;
    }
    // Exactly one negated premise equality and one positive conclusion
    // equality, in either clause order.
    let orientations = [(clause[0], clause[1]), (clause[1], clause[0])];
    orientations
        .into_iter()
        .any(|(premise_lit, conclusion_lit)| {
            let TermData::Not(premise) = terms.get(premise_lit) else {
                return false;
            };
            let premise = *premise;
            if matches!(terms.get(conclusion_lit), TermData::Not(_)) {
                return false;
            }
            let (Some((left, right)), Some((goal_left, goal_right))) = (
                decode_string_equality(terms, premise),
                decode_string_equality(terms, conclusion_lit),
            ) else {
                return false;
            };
            cancellation_holds(terms, left, right, goal_left, goal_right)
        })
}

/// Decode `(= a b)` over two String-sorted sides.
fn decode_string_equality(terms: &TermStore, t: TermId) -> Option<(TermId, TermId)> {
    let (name, args) = as_named_app(terms, t)?;
    if name != "="
        || args.len() != 2
        || !matches!(terms.sort(t), Sort::Bool)
        || !is_string_sorted(terms, args[0])
        || !is_string_sorted(terms, args[1])
    {
        return None;
    }
    Some((args[0], args[1]))
}

/// The top-level `str.++` operand list of `t`, or `[t]` when `t` is not a
/// concatenation (a single word is a one-operand product).
///
/// Returns `None` when an operand is not String-sorted or the list is over
/// budget. Nested concatenations are NOT flattened: a shared block is matched
/// operand-for-operand, and a nested `str.++` operand is simply one operand
/// that must match its counterpart exactly.
fn concat_operands(terms: &TermStore, t: TermId) -> Option<Vec<TermId>> {
    if !is_string_sorted(terms, t) {
        return None;
    }
    match as_named_app(terms, t) {
        Some(("str.++", args)) => {
            if args.is_empty() || args.len() > MAX_CONCAT_OPERANDS {
                return None;
            }
            if args.iter().any(|&arg| !is_string_sorted(terms, arg)) {
                return None;
            }
            Some(args.to_vec())
        }
        _ => Some(vec![t]),
    }
}

/// Whether `(= left right)` cancels to `(= goal_left goal_right)`.
///
/// Both cancellation directions are tried. The cancelled block must be a
/// non-empty, syntactically identical operand run at the same end of both
/// sides, and what remains on each side must denote exactly the corresponding
/// goal term.
fn cancellation_holds(
    terms: &TermStore,
    left: TermId,
    right: TermId,
    goal_left: TermId,
    goal_right: TermId,
) -> bool {
    let (Some(left_operands), Some(right_operands)) =
        (concat_operands(terms, left), concat_operands(terms, right))
    else {
        return false;
    };

    // Longest shared suffix / prefix run, operand for operand.
    let shared_suffix = left_operands
        .iter()
        .rev()
        .zip(right_operands.iter().rev())
        .take_while(|(l, r)| l == r)
        .count();
    let shared_prefix = left_operands
        .iter()
        .zip(right_operands.iter())
        .take_while(|(l, r)| l == r)
        .count();

    // RIGHT cancellation: drop a shared suffix of length `k >= 1`.
    for k in 1..=shared_suffix {
        let left_rest = &left_operands[..left_operands.len() - k];
        let right_rest = &right_operands[..right_operands.len() - k];
        if rest_matches_goal(terms, left_rest, right_rest, goal_left, goal_right) {
            return true;
        }
    }
    // LEFT cancellation: drop a shared prefix of length `k >= 1`.
    for k in 1..=shared_prefix {
        let left_rest = &left_operands[k..];
        let right_rest = &right_operands[k..];
        if rest_matches_goal(terms, left_rest, right_rest, goal_left, goal_right) {
            return true;
        }
    }
    false
}

/// Whether the two residual operand runs denote the goal equality's two sides,
/// in either orientation (`=` is symmetric).
fn rest_matches_goal(
    terms: &TermStore,
    left_rest: &[TermId],
    right_rest: &[TermId],
    goal_left: TermId,
    goal_right: TermId,
) -> bool {
    (rest_denotes(terms, left_rest, goal_left) && rest_denotes(terms, right_rest, goal_right))
        || (rest_denotes(terms, left_rest, goal_right)
            && rest_denotes(terms, right_rest, goal_left))
}

/// Whether the residual operand run denotes exactly `goal`.
///
/// An empty run is the empty word, so `goal` must be the `""` constant. A
/// single operand must BE `goal`. A longer run must be a `str.++` whose
/// operand list is exactly that run — the residual is not re-associated, so a
/// producer that rebuilds the term differently is rejected rather than guessed
/// at.
fn rest_denotes(terms: &TermStore, rest: &[TermId], goal: TermId) -> bool {
    match rest.len() {
        0 => is_empty_string(terms, goal),
        1 => rest[0] == goal,
        _ => match as_named_app(terms, goal) {
            Some(("str.++", args)) => args == rest && is_string_sorted(terms, goal),
            _ => false,
        },
    }
}

// ---------------------------------------------------------------------------
// 3. Ground-factor conflicts inside a symbolic containment
// ---------------------------------------------------------------------------

/// Validate a `TheoryLemmaKind::StringGroundFactorConflict` in strict mode.
pub(crate) fn validate_string_ground_factor_conflict(
    terms: &TermStore,
    step_id: ProofId,
    clause: &[TermId],
) -> Result<(), ProofCheckError> {
    check_propositional_clause(terms, step_id, clause, "string_ground_factor_conflict")?;
    if clause
        .iter()
        .any(|&lit| is_refuted_ground_factor_containment(terms, lit))
    {
        return Ok(());
    }
    Err(ProofCheckError::InvalidTheoryLemma {
        step: step_id,
        reason: "string_ground_factor_conflict clause has no literal the independent \
                 checker proves impossible (a str.contains whose container is a ground \
                 constant missing one of the contained word's ground concat blocks, or a \
                 str.prefixof/str.suffixof whose ground pattern is no longer than, and \
                 disagrees with, the container's ground boundary block); rejecting in \
                 fail-closed mode"
            .to_string(),
    })
}

/// Recognize a clause the strict `StringGroundFactorConflict` validator will
/// accept.
///
/// This is the EXACT precondition of
/// `validate_string_ground_factor_conflict`.
#[must_use]
pub fn recognize_string_ground_factor_conflict(terms: &TermStore, clause: &[TermId]) -> bool {
    if clause.is_empty() {
        return false;
    }
    if clause
        .iter()
        .any(|&lit| !matches!(terms.sort(lit), Sort::Bool))
    {
        return false;
    }
    clause
        .iter()
        .any(|&lit| is_refuted_ground_factor_containment(terms, lit))
}

/// Whether `lit` is a NEGATED containment predicate the checker refutes
/// outright from the ground blocks the clause itself carries.
fn is_refuted_ground_factor_containment(terms: &TermStore, lit: TermId) -> bool {
    let (atom, positive) = strip_negations(terms, lit);
    if positive {
        return false;
    }
    let Some((name, args)) = as_named_app(terms, atom) else {
        return false;
    };
    if args.len() != 2
        || !matches!(terms.sort(atom), Sort::Bool)
        || !is_string_sorted(terms, args[0])
        || !is_string_sorted(terms, args[1])
    {
        return false;
    }
    match name {
        // `(str.contains C T)`: T's value is a contiguous factor of C's, so
        // EVERY concat block of T is a factor of C too. A ground block that
        // does not occur in the ground container makes the containment
        // impossible for any value of the symbolic blocks.
        "str.contains" => {
            let Some(container) = string_constant(terms, args[0]) else {
                return false;
            };
            let Some(blocks) = concat_operands(terms, args[1]) else {
                return false;
            };
            blocks.iter().any(|&block| {
                string_constant(terms, block).is_some_and(|factor| {
                    !factor.is_empty() && !contains_factor(&container, &factor)
                })
            })
        }
        // `(str.prefixof K T)`: K is a prefix of T = m·rest. When K is no
        // longer than the ground FIRST block `m`, K must be a prefix of `m`.
        "str.prefixof" => {
            let Some(pattern) = string_constant(terms, args[0]) else {
                return false;
            };
            let Some(blocks) = concat_operands(terms, args[1]) else {
                return false;
            };
            let Some(boundary) = blocks.first().and_then(|&b| string_constant(terms, b)) else {
                return false;
            };
            pattern.len() <= boundary.len() && !boundary.starts_with(pattern.as_slice())
        }
        // `(str.suffixof K T)`: the mirror, against the ground LAST block.
        "str.suffixof" => {
            let Some(pattern) = string_constant(terms, args[0]) else {
                return false;
            };
            let Some(blocks) = concat_operands(terms, args[1]) else {
                return false;
            };
            let Some(boundary) = blocks.last().and_then(|&b| string_constant(terms, b)) else {
                return false;
            };
            pattern.len() <= boundary.len() && !boundary.ends_with(pattern.as_slice())
        }
        _ => false,
    }
}

/// The code points of a string-constant term, or `None`.
///
/// Oversized constants are rejected rather than searched: the factor scan below
/// is `O(|haystack| · |needle|)`, and exhaustion must never be able to turn a
/// rejection into an acceptance.
fn string_constant(terms: &TermStore, t: TermId) -> Option<Vec<char>> {
    match (terms.get(t), terms.sort(t)) {
        (TermData::Const(Constant::String(s)), Sort::String) => {
            if s.len() > MAX_GROUND_CONSTANT_BYTES {
                return None;
            }
            Some(s.chars().collect())
        }
        _ => None,
    }
}

/// Whether `needle` occurs as a CONTIGUOUS block of `haystack`.
fn contains_factor(haystack: &[char], needle: &[char]) -> bool {
    if needle.is_empty() {
        return true;
    }
    if needle.len() > haystack.len() {
        return false;
    }
    (0..=haystack.len() - needle.len())
        .any(|start| &haystack[start..start + needle.len()] == needle)
}

/// Largest string constant the factor scan will look at, in UTF-8 bytes.
const MAX_GROUND_CONSTANT_BYTES: usize = 1 << 16;

#[cfg(test)]
#[path = "string_word_identity_tests.rs"]
mod string_word_identity_tests;
