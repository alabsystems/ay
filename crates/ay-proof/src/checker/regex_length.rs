// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Strict semantic validation for `TheoryLemmaKind::RegexLengthLowerBound`.
//!
//! The lemma claims: "every word in the language of this GROUND regex has
//! length at least `k`, so a membership in it bounds `str.len` below by `k`".
//! The clause is
//!
//! ```text
//! (cl (not (str.in_re x R)) (<= k (str.len x)))
//! ```
//!
//! which is a tautology whenever `k` is a valid lower bound for `L(R)`: either
//! `x` is not in the language and the first literal holds, or it is and the
//! second does.
//!
//! # Soundness
//!
//! [`regex_min_length`] returns a LOWER bound on `|w|` over every `w ∈ L(R)`,
//! computed compositionally:
//!
//! | node | bound | why |
//! |---|---|---|
//! | `re.none` | `0` | `L = ∅`; every bound is vacuously valid |
//! | `re.all` | `0` | `""` is in the language |
//! | `re.allchar` | `1` | every word is exactly one code point |
//! | `(str.to_re c)` | `|c|` | the language is the single word `c` |
//! | `(re.range a b)` | `1` | non-empty only for single code points; empty otherwise, where any bound is valid |
//! | `(re.++ R…)` | `Σ bound(Rᵢ)` | a word is a concatenation of one word per factor |
//! | `(re.union R…)` | `min bound(Rᵢ)` | a word lies in SOME branch |
//! | `(re.inter R…)` | `max bound(Rᵢ)` | a word lies in EVERY branch |
//! | `(re.* R)`, `(re.opt R)` | `0` | `""` is in the language |
//! | `(re.+ R)` | `bound(R)` | at least one repetition |
//! | `(re.diff R S…)` | `bound(R)` | `L ⊆ L(R)` |
//! | `((_ re.loop lo hi) R)` | `lo · bound(R)` | at least `lo` repetitions; empty when `lo > hi`, where any bound is valid |
//! | `((_ re.^ n) R)` | `n · bound(R)` | exactly `n` repetitions |
//!
//! `re.comp` and every unrecognized node REJECT: a complement's language can
//! contain `""`, and guessing a bound for an operator this module does not
//! model would be exactly the kind of unchecked claim the strict gate exists to
//! stop. `0` is always a valid bound, so returning it for an EMPTY language is
//! sound and needs no emptiness analysis.
//!
//! # Fail-closed
//!
//! A non-ground regex leaf, an unmodelled operator, a mismatched membership
//! subject, a wrong clause shape, a negative or over-strong bound, and budget
//! exhaustion all REJECT. There is no "assume valid" arm.

use ay_core::{Constant, ProofId, Sort, Symbol, TermData, TermId, TermStore};
use num_bigint::BigInt;
use num_traits::Signed;

use super::ProofCheckError;

/// Regex nodes one bound computation may visit. Exhaustion REJECTS.
const MAX_REGEX_NODES: usize = 100_000;

/// Validate a `TheoryLemmaKind::RegexLengthLowerBound` in strict mode.
pub(crate) fn validate_regex_length_lower_bound(
    terms: &TermStore,
    step_id: ProofId,
    clause: &[TermId],
) -> Result<(), ProofCheckError> {
    if clause.is_empty() {
        return Err(ProofCheckError::InvalidTheoryLemma {
            step: step_id,
            reason: "regex_length_lower_bound clause must be non-empty".to_string(),
        });
    }
    for &lit in clause {
        if !matches!(terms.sort(lit), Sort::Bool) {
            return Err(ProofCheckError::InvalidTheoryLemma {
                step: step_id,
                reason: format!(
                    "regex_length_lower_bound literal has non-Bool sort {:?}; lemma \
                     clauses must be propositional",
                    terms.sort(lit)
                ),
            });
        }
    }
    if clause_is_regex_length_lower_bound(terms, clause) {
        return Ok(());
    }
    Err(ProofCheckError::InvalidTheoryLemma {
        step: step_id,
        reason: "regex_length_lower_bound clause is not \
                 `(cl (not (str.in_re x R)) (<= k (str.len x)))` over one common \
                 subject with a GROUND regex whose independently computed minimum \
                 word length is at least k; rejecting in fail-closed mode"
            .to_string(),
    })
}

/// Recognize a clause the strict `RegexLengthLowerBound` validator will accept.
///
/// This is the EXACT precondition of `validate_regex_length_lower_bound`, so
/// a producer can only tag clauses strict mode will then accept.
#[must_use]
pub fn recognize_regex_length_lower_bound(terms: &TermStore, clause: &[TermId]) -> bool {
    if clause.is_empty() {
        return false;
    }
    if clause
        .iter()
        .any(|&lit| !matches!(terms.sort(lit), Sort::Bool))
    {
        return false;
    }
    clause_is_regex_length_lower_bound(terms, clause)
}

fn clause_is_regex_length_lower_bound(terms: &TermStore, clause: &[TermId]) -> bool {
    if clause.len() != 2 {
        return false;
    }
    let orientations = [(clause[0], clause[1]), (clause[1], clause[0])];
    orientations.into_iter().any(|(membership_lit, bound_lit)| {
        let TermData::Not(membership) = terms.get(membership_lit) else {
            return false;
        };
        let Some((subject, regex)) = decode_membership(terms, *membership) else {
            return false;
        };
        let Some((bound, bounded)) = decode_lower_bound(terms, bound_lit) else {
            return false;
        };
        if bounded != subject || bound.is_negative() {
            return false;
        }
        let mut budget = MAX_REGEX_NODES;
        regex_min_length_inner(terms, regex, &mut budget).is_some_and(|minimum| bound <= minimum)
    })
}

/// Decode `(str.in_re x R)` into `(x, R)`.
fn decode_membership(terms: &TermStore, t: TermId) -> Option<(TermId, TermId)> {
    let TermData::App(Symbol::Named(name), args) = terms.get(t) else {
        return None;
    };
    if (name != "str.in_re" && name != "str.in.re")
        || args.len() != 2
        || !matches!(terms.sort(t), Sort::Bool)
        || !matches!(terms.sort(args[0]), Sort::String)
        || !matches!(terms.sort(args[1]), Sort::RegLan)
    {
        return None;
    }
    Some((args[0], args[1]))
}

/// Decode `(<= k (str.len x))` into `(k, x)`.
fn decode_lower_bound(terms: &TermStore, t: TermId) -> Option<(BigInt, TermId)> {
    let TermData::App(Symbol::Named(name), args) = terms.get(t) else {
        return None;
    };
    if name != "<=" || args.len() != 2 || !matches!(terms.sort(t), Sort::Bool) {
        return None;
    }
    let (TermData::Const(Constant::Int(bound)), Sort::Int) =
        (terms.get(args[0]), terms.sort(args[0]))
    else {
        return None;
    };
    let TermData::App(Symbol::Named(len_name), len_args) = terms.get(args[1]) else {
        return None;
    };
    if len_name != "str.len"
        || len_args.len() != 1
        || !matches!(terms.sort(args[1]), Sort::Int)
        || !matches!(terms.sort(len_args[0]), Sort::String)
    {
        return None;
    }
    Some((bound.clone(), len_args[0]))
}

/// A LOWER bound on the length of every word in `L(regex)`, or `None` when the
/// regex is not ground or uses an operator this module does not model.
///
/// Exposed so a proof producer can ask the CHECKER for the bound it will then
/// re-derive, rather than computing one of its own.
#[must_use]
pub fn regex_min_length(terms: &TermStore, regex: TermId) -> Option<BigInt> {
    let mut budget = MAX_REGEX_NODES;
    regex_min_length_inner(terms, regex, &mut budget)
}

fn regex_min_length_inner(terms: &TermStore, regex: TermId, budget: &mut usize) -> Option<BigInt> {
    if *budget == 0 || !matches!(terms.sort(regex), Sort::RegLan) {
        return None;
    }
    *budget -= 1;
    match terms.get(regex) {
        TermData::App(Symbol::Named(name), args) => {
            named_regex_min_length(terms, name.as_str(), args, budget)
        }
        TermData::App(Symbol::Indexed(name, indices), args) => {
            indexed_regex_min_length(terms, name.as_str(), indices, args, budget)
        }
        _ => None,
    }
}

fn named_regex_min_length(
    terms: &TermStore,
    name: &str,
    args: &[TermId],
    budget: &mut usize,
) -> Option<BigInt> {
    match (name, args.len()) {
        // `L = ∅`: every bound is vacuously valid, and `0` is always valid.
        ("re.none", 0) => Some(BigInt::from(0)),
        // `""` is in the language.
        ("re.all", 0) => Some(BigInt::from(0)),
        // Every word is exactly one code point.
        ("re.allchar", 0) => Some(BigInt::from(1)),
        // The language is the single word `c`.
        ("str.to_re" | "str.to.re", 1) => match terms.get(args[0]) {
            TermData::Const(Constant::String(literal))
                if matches!(terms.sort(args[0]), Sort::String) =>
            {
                Some(BigInt::from(literal.chars().count()))
            }
            _ => None,
        },
        // Non-empty only for single code points; when either endpoint is not a
        // one-character constant SMT-LIB makes the language empty, where any
        // bound holds. Both cases admit `1`.
        ("re.range", 2) => {
            let ok = [args[0], args[1]].into_iter().all(|arg| {
                matches!(
                    (terms.get(arg), terms.sort(arg)),
                    (TermData::Const(Constant::String(_)), Sort::String)
                )
            });
            ok.then(|| BigInt::from(1))
        }
        // A word is a concatenation of one word per factor.
        ("re.++", n) if n >= 1 => {
            let mut total = BigInt::from(0);
            for &arg in args {
                total += regex_min_length_inner(terms, arg, budget)?;
            }
            Some(total)
        }
        // A word lies in SOME branch, so the smallest branch bound applies.
        ("re.union", n) if n >= 1 => {
            let mut smallest: Option<BigInt> = None;
            for &arg in args {
                let bound = regex_min_length_inner(terms, arg, budget)?;
                smallest = Some(match smallest {
                    Some(current) if current <= bound => current,
                    _ => bound,
                });
            }
            smallest
        }
        // A word lies in EVERY branch, so the largest branch bound applies.
        ("re.inter", n) if n >= 1 => {
            let mut largest: Option<BigInt> = None;
            for &arg in args {
                let bound = regex_min_length_inner(terms, arg, budget)?;
                largest = Some(match largest {
                    Some(current) if current >= bound => current,
                    _ => bound,
                });
            }
            largest
        }
        // `""` is in both languages.
        ("re.*" | "re.opt", 1) => {
            let _ = regex_min_length_inner(terms, args[0], budget)?;
            Some(BigInt::from(0))
        }
        // At least one repetition.
        ("re.+", 1) => regex_min_length_inner(terms, args[0], budget),
        // `L ⊆ L(args[0])`.
        ("re.diff", n) if n >= 2 => {
            for &arg in &args[1..] {
                let _ = regex_min_length_inner(terms, arg, budget)?;
            }
            regex_min_length_inner(terms, args[0], budget)
        }
        // `re.comp` REJECTS: a complement's language routinely contains `""`,
        // and no bound better than the trivial one is derivable here without
        // modelling the complemented language.
        _ => None,
    }
}

fn indexed_regex_min_length(
    terms: &TermStore,
    name: &str,
    indices: &[u32],
    args: &[TermId],
    budget: &mut usize,
) -> Option<BigInt> {
    match (name, indices.len(), args.len()) {
        // At least `lo` repetitions. When `lo > hi` the language is empty and
        // any bound holds, so no ordering check is needed.
        ("re.loop", 2, 1) => {
            let inner = regex_min_length_inner(terms, args[0], budget)?;
            Some(inner * BigInt::from(indices[0]))
        }
        // Exactly `n` repetitions.
        ("re.^", 1, 1) => {
            let inner = regex_min_length_inner(terms, args[0], budget)?;
            Some(inner * BigInt::from(indices[0]))
        }
        _ => None,
    }
}

#[cfg(test)]
#[path = "regex_length_tests.rs"]
mod regex_length_tests;
