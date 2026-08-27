// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Strict semantic validation for `TheoryLemmaKind::StringLengthLemma`.
//!
//! A `StringLengthLemma` claims: "this clause carries a literal that is a
//! UNIVERSALLY VALID `str.len` theorem — true under every interpretation of the
//! SMT-LIB string theory." A clause with such a literal is a tautology, hence a
//! valid theory lemma.
//!
//! The solver injects a family of `str.len` facts during QF_SLIA/QF_S
//! preprocessing (`collect_str_len_axioms_from_roots`), none of which is an
//! authored problem premise, so they surface as foreign `assume` leaves that the
//! #8821 provenance gate rejects. Rather than weaken that gate, the emitter
//! RE-TAGS each such leaf as this certified kind, and this checker
//! INDEPENDENTLY re-derives the exact theorem. The recognized shapes are:
//!
//! 1. CONCAT-LENGTH: `(= (str.len (str.++ a₁ … aₙ)) (+ (str.len a₁) … (str.len aₙ)))`
//!    — the length of a concatenation is the sum of the operand lengths. The
//!    summands are matched against the concat operands as a MULTISET (so any
//!    permutation is accepted; `+` is commutative), a folded string-constant
//!    operand being allowed to appear as its literal length.
//! 2. EMPTY↔ZERO: `x = "" ↔ (str.len x) = 0`, in either implication direction —
//!    stored (after `=>` lowering) as `(or ±(= x "") ∓(= (str.len x) 0))` with
//!    OPPOSITE polarities. The two same-polarity `or`s are NOT tautologies and
//!    are rejected.
//! 3. NON-NEGATIVITY: `(<= 0 (str.len x))` — `str.len` is never negative.
//! 4. CONSTANT-LENGTH: `(= k (str.len c))` where `c` is a string constant and
//!    `k` is exactly its code-point length.
//! 5. EQUAL-LENGTH: `s = t → (str.len s) = (str.len t)` — stored as
//!    `(or (not (= s t)) LENEQ)`. `LENEQ` is `(= (str.len s) (str.len t))`, or,
//!    when one side is a string constant of length `k`, `(= (str.len other) k)`.
//! 6. CONTAINMENT-BOUND: `str.contains(x, s) → (str.len s) <= (str.len x)`, and
//!    the `str.prefixof` / `str.suffixof` analogues — a contained/prefix/suffix
//!    string is no longer than its container. Stored as
//!    `(or (not PRED) (<= (str.len contained) (str.len container)))`.
//!
//! # Soundness
//!
//! Every accepted shape is a theorem of the SMT-LIB 2.6 string theory, so the
//! unit clause introducing it is valid under every model. The checker performs
//! ONLY structural pattern matching plus the trivial "length of a string
//! constant is its code-point count" computation — it never calls the solver's
//! string theory, so it cannot launder a solver mistake into an accepted lemma.
//! Every recognized built-in must also carry its exact named-operator signature;
//! raw ill-sorted or indexed applications are rejected at this boundary.
//! The multiset / opposite-polarity / exact-bound / exact-operand conditions
//! reject any near-miss (a `+1`, a wrong operand, a `>= 1` bound, a same-polarity
//! `or`, a wrong constant length).
//!
//! # Fail-closed
//!
//! Anything not matching one of the exact shapes is REJECTED. There is no
//! "assume valid" arm.

use ay_core::{Constant, ProofId, Sort, Symbol, TermData, TermId, TermStore};
use num_bigint::BigInt;
use num_traits::{Signed, Zero};

use super::ProofCheckError;

#[path = "string_length_identity_containment.rs"]
mod containment;

/// Validate a `TheoryLemmaKind::StringLengthLemma` in strict mode.
pub(crate) fn validate_string_length_lemma(
    terms: &TermStore,
    step_id: ProofId,
    clause: &[TermId],
) -> Result<(), ProofCheckError> {
    if clause.is_empty() {
        return Err(ProofCheckError::InvalidTheoryLemma {
            step: step_id,
            reason: "string_length_lemma clause must be non-empty".to_string(),
        });
    }
    for &lit in clause {
        if !matches!(terms.sort(lit), Sort::Bool) {
            return Err(ProofCheckError::InvalidTheoryLemma {
                step: step_id,
                reason: format!(
                    "string_length_lemma literal has non-Bool sort {:?}; lemma \
                     clauses must be propositional",
                    terms.sort(lit)
                ),
            });
        }
    }
    if clause
        .iter()
        .any(|&lit| is_valid_str_len_theorem(terms, lit))
    {
        return Ok(());
    }
    Err(ProofCheckError::InvalidTheoryLemma {
        step: step_id,
        reason: "string_length_lemma clause has no literal the independent \
                 checker proves to be a universally-valid str.len theorem \
                 (concat-length sum, empty↔zero-length, non-negativity, \
                 constant-length, equal-length, or containment bound); \
                 rejecting in fail-closed mode"
            .to_string(),
    })
}

/// Recognize a clause the strict `StringLengthLemma` validator will accept:
/// non-empty, propositional, carrying at least one literal that is a
/// universally-valid `str.len` theorem.
///
/// This is the EXACT precondition of `validate_string_length_lemma`, so the
/// emitter in `ay-dpll` can only tag leaves strict mode will then accept — no
/// emitter/checker drift. Decision logic lives ONLY in this module.
#[must_use]
pub fn recognize_string_length_lemma(terms: &TermStore, clause: &[TermId]) -> bool {
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
        .any(|&lit| is_valid_str_len_theorem(terms, lit))
}

/// Whether `t` is one of the recognized universally-valid `str.len` theorems.
fn is_valid_str_len_theorem(terms: &TermStore, t: TermId) -> bool {
    is_concat_len_sum(terms, t)
        || is_empty_iff_zero_len(terms, t)
        || is_len_nonneg(terms, t)
        || is_const_len(terms, t)
        || is_str_eq_len_eq(terms, t)
        || containment::is_containment_len_bound(terms, t)
}

// ---------------------------------------------------------------------------
// Small structural helpers
// ---------------------------------------------------------------------------

/// The String-sorted argument `x` of `(str.len x)`, or `None`.
fn str_len_arg(terms: &TermStore, t: TermId) -> Option<TermId> {
    let TermData::App(Symbol::Named(sym), args) = terms.get(t) else {
        return None;
    };
    if sym == "str.len"
        && args.len() == 1
        && matches!(terms.sort(t), Sort::Int)
        && matches!(terms.sort(args[0]), Sort::String)
    {
        Some(args[0])
    } else {
        None
    }
}

/// The value of an integer constant term, or `None`.
fn int_const(terms: &TermStore, t: TermId) -> Option<&BigInt> {
    match (terms.get(t), terms.sort(t)) {
        (TermData::Const(Constant::Int(v)), Sort::Int) => Some(v),
        _ => None,
    }
}

/// The code-point length of a string-constant term, or `None`.
fn string_const_len(terms: &TermStore, t: TermId) -> Option<BigInt> {
    match (terms.get(t), terms.sort(t)) {
        (TermData::Const(Constant::String(s)), Sort::String) => {
            Some(BigInt::from(s.chars().count()))
        }
        _ => None,
    }
}

/// Whether `t` is the empty string constant `""`.
fn is_empty_string(terms: &TermStore, t: TermId) -> bool {
    matches!(
        (terms.get(t), terms.sort(t)),
        (TermData::Const(Constant::String(s)), Sort::String) if s.is_empty()
    )
}

/// Decompose `(op a b)` into `(a, b)` when the symbol name is `name`.
fn as_binary(terms: &TermStore, t: TermId, name: &str) -> Option<(TermId, TermId)> {
    let TermData::App(Symbol::Named(sym), args) = terms.get(t) else {
        return None;
    };
    if sym == name
        && args.len() == 2
        && matches!(terms.sort(t), Sort::Bool)
        && terms.sort(args[0]) == terms.sort(args[1])
    {
        Some((args[0], args[1]))
    } else {
        None
    }
}

// ---------------------------------------------------------------------------
// 1. Concat-length: len(a₁ ++ … ++ aₙ) = Σ len(aᵢ)
// ---------------------------------------------------------------------------

fn is_concat_len_sum(terms: &TermStore, t: TermId) -> bool {
    let Some((l, r)) = as_binary(terms, t, "=") else {
        return false;
    };
    check_concat_sum(terms, l, r) || check_concat_sum(terms, r, l)
}

/// `len_side = (str.len (str.++ …))` and `sum_side` sums the operand lengths.
fn check_concat_sum(terms: &TermStore, len_side: TermId, sum_side: TermId) -> bool {
    let Some(concat) = str_len_arg(terms, len_side) else {
        return false;
    };
    let TermData::App(Symbol::Named(csym), cargs) = terms.get(concat) else {
        return false;
    };
    if csym != "str.++"
        || cargs.is_empty()
        || !matches!(terms.sort(concat), Sort::String)
        || cargs
            .iter()
            .any(|&arg| !matches!(terms.sort(arg), Sort::String))
    {
        return false;
    }
    let cargs: Vec<TermId> = cargs.clone();

    // The summands: an explicit `(+ …)`, or a single length term for a 1-ary
    // concat whose sum collapsed to one operand.
    let sum_args: Vec<TermId> = match terms.get(sum_side) {
        TermData::App(Symbol::Named(ssym), sargs)
            if ssym == "+"
                && matches!(terms.sort(sum_side), Sort::Int)
                && sargs
                    .iter()
                    .all(|&arg| matches!(terms.sort(arg), Sort::Int)) =>
        {
            sargs.clone()
        }
        _ => vec![sum_side],
    };

    // Partition summands into `str.len(x)` operands and non-negative integer
    // constants (a folded string-constant length). Anything else (a product, a
    // fresh variable, a negative constant) fails closed.
    let mut len_args: Vec<TermId> = Vec::new();
    let mut const_lens: Vec<BigInt> = Vec::new();
    for &e in &sum_args {
        if let Some(x) = str_len_arg(terms, e) {
            len_args.push(x);
        } else if let Some(k) = int_const(terms, e) {
            if k.is_negative() {
                return false;
            }
            const_lens.push(k.clone());
        } else {
            return false;
        }
    }

    // Every `str.len(x)` summand must consume a distinct concat operand `x`.
    let mut remaining: Vec<TermId> = cargs;
    for &x in &len_args {
        let Some(pos) = remaining.iter().position(|&c| c == x) else {
            return false;
        };
        let _ = remaining.swap_remove(pos);
    }

    // Each leftover concat operand must be a string constant, and the multiset of
    // their code-point lengths must exactly equal the constant summands.
    let mut leftover_lens: Vec<BigInt> = Vec::with_capacity(remaining.len());
    for &c in &remaining {
        let Some(len) = string_const_len(terms, c) else {
            return false;
        };
        leftover_lens.push(len);
    }
    const_lens.sort_unstable();
    leftover_lens.sort_unstable();
    const_lens == leftover_lens
}

// ---------------------------------------------------------------------------
// 2. Empty ↔ zero length: stored as `(or ±(= x "") ∓(= (str.len x) 0))`
// ---------------------------------------------------------------------------

#[derive(PartialEq, Eq, Clone, Copy)]
enum LitKind {
    Empty,
    LenZero,
}

fn is_empty_iff_zero_len(terms: &TermStore, t: TermId) -> bool {
    let TermData::App(Symbol::Named(sym), args) = terms.get(t) else {
        return false;
    };
    if sym != "or"
        || args.len() != 2
        || !matches!(terms.sort(t), Sort::Bool)
        || args
            .iter()
            .any(|&arg| !matches!(terms.sort(arg), Sort::Bool))
    {
        return false;
    }
    let (Some((ka, pa, xa)), Some((kb, pb, xb))) = (
        classify_empty_or_zero_lit(terms, args[0]),
        classify_empty_or_zero_lit(terms, args[1]),
    ) else {
        return false;
    };
    // One `x = ""` literal and one `len(x) = 0` literal, over the SAME subject,
    // with OPPOSITE polarity — exactly the two valid implications. The two
    // same-polarity `or`s (`p ∨ p` and `¬p ∨ ¬p`) are not tautologies.
    ka != kb && xa == xb && pa != pb
}

/// Classify a literal as `(= x "")` or `(= (str.len x) 0)` (either argument
/// order), returning its kind, polarity (`true` = positive), and subject `x`.
fn classify_empty_or_zero_lit(terms: &TermStore, lit: TermId) -> Option<(LitKind, bool, TermId)> {
    let (atom, positive) = match terms.get(lit) {
        TermData::Not(inner) if matches!(terms.sort(*inner), Sort::Bool) => (*inner, false),
        TermData::Not(_) => return None,
        _ => (lit, true),
    };
    let (l, r) = as_binary(terms, atom, "=")?;

    // (= x "") / (= "" x)
    if is_empty_string(terms, l) && matches!(terms.sort(r), Sort::String) {
        return Some((LitKind::Empty, positive, r));
    }
    if is_empty_string(terms, r) && matches!(terms.sort(l), Sort::String) {
        return Some((LitKind::Empty, positive, l));
    }
    // (= (str.len x) 0) / (= 0 (str.len x))
    if let Some(x) = str_len_arg(terms, l) {
        if int_const(terms, r).is_some_and(BigInt::is_zero) {
            return Some((LitKind::LenZero, positive, x));
        }
    }
    if let Some(x) = str_len_arg(terms, r) {
        if int_const(terms, l).is_some_and(BigInt::is_zero) {
            return Some((LitKind::LenZero, positive, x));
        }
    }
    None
}

// ---------------------------------------------------------------------------
// 3. Non-negativity: (<= 0 (str.len x))
// ---------------------------------------------------------------------------

fn is_len_nonneg(terms: &TermStore, t: TermId) -> bool {
    let Some((lo, hi)) = as_binary(terms, t, "<=") else {
        return false;
    };
    int_const(terms, lo).is_some_and(BigInt::is_zero) && str_len_arg(terms, hi).is_some()
}

// ---------------------------------------------------------------------------
// 4. Constant length: (= k (str.len c)), c a string constant of length k
// ---------------------------------------------------------------------------

fn is_const_len(terms: &TermStore, t: TermId) -> bool {
    let Some((l, r)) = as_binary(terms, t, "=") else {
        return false;
    };
    check_const_len(terms, l, r) || check_const_len(terms, r, l)
}

fn check_const_len(terms: &TermStore, len_side: TermId, k_side: TermId) -> bool {
    let Some(x) = str_len_arg(terms, len_side) else {
        return false;
    };
    let Some(k) = int_const(terms, k_side) else {
        return false;
    };
    string_const_len(terms, x).is_some_and(|len| &len == k)
}

// ---------------------------------------------------------------------------
// 5. Equal length: s = t → len(s) = len(t)
//    Stored as `(or (not (= s t)) LENEQ)`.
// ---------------------------------------------------------------------------

fn is_str_eq_len_eq(terms: &TermStore, t: TermId) -> bool {
    let TermData::App(Symbol::Named(sym), args) = terms.get(t) else {
        return false;
    };
    if sym != "or"
        || args.len() != 2
        || !matches!(terms.sort(t), Sort::Bool)
        || args
            .iter()
            .any(|&arg| !matches!(terms.sort(arg), Sort::Bool))
    {
        return false;
    }
    check_eq_len_pair(terms, args[0], args[1]) || check_eq_len_pair(terms, args[1], args[0])
}

/// `neg_lit` must be `(not (= s t))` over String terms, and `len_lit` must be a
/// positive length consequence of `s = t`.
fn check_eq_len_pair(terms: &TermStore, neg_lit: TermId, len_lit: TermId) -> bool {
    let TermData::Not(inner) = terms.get(neg_lit) else {
        return false;
    };
    if !matches!(terms.sort(*inner), Sort::Bool) {
        return false;
    }
    let Some((s, t)) = as_binary(terms, *inner, "=") else {
        return false;
    };
    if !matches!(terms.sort(s), Sort::String) || !matches!(terms.sort(t), Sort::String) {
        return false;
    }
    let Some((l, r)) = as_binary(terms, len_lit, "=") else {
        return false;
    };

    // Both sides str.len: (= (str.len ?) (str.len ?)) with {args} == {s, t}.
    if let (Some(la), Some(lb)) = (str_len_arg(terms, l), str_len_arg(terms, r)) {
        return (la == s && lb == t) || (la == t && lb == s);
    }
    // One side str.len, other an int constant: (= (str.len x) k) with x ∈ {s, t}
    // and the OTHER of {s, t} a string constant of length k.
    if let Some(x) = str_len_arg(terms, l) {
        if let Some(k) = int_const(terms, r) {
            return eq_len_const_ok(terms, x, k, s, t);
        }
    }
    if let Some(x) = str_len_arg(terms, r) {
        if let Some(k) = int_const(terms, l) {
            return eq_len_const_ok(terms, x, k, s, t);
        }
    }
    false
}

/// `(= (str.len x) k)` is a valid consequence of `s = t` when `x` is one of
/// `{s, t}` and the OTHER is a string constant whose length is `k`.
fn eq_len_const_ok(terms: &TermStore, x: TermId, k: &BigInt, s: TermId, t: TermId) -> bool {
    let other = if x == s {
        t
    } else if x == t {
        s
    } else {
        return false;
    };
    string_const_len(terms, other).is_some_and(|len| &len == k)
}

#[cfg(test)]
#[path = "string_length_identity_tests.rs"]
mod string_length_identity_tests;
