// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Strict validation for the quantifier-negation De Morgan proof step.

use ay_core::{ProofId, Sort, TermData, TermId, TermStore};

use super::{invalid_rule, ProofCheckError};

fn invalid_qnt_neg_exists(step: ProofId, reason: impl Into<String>) -> ProofCheckError {
    invalid_rule(step, "qnt_neg_exists", reason)
}

fn validate_qnt_neg_exists_body_sort(
    terms: &TermStore,
    step: ProofId,
    body: TermId,
) -> Result<(), ProofCheckError> {
    if terms.sort(body) != &Sort::Bool {
        return Err(invalid_qnt_neg_exists(
            step,
            "exists body must have Bool sort",
        ));
    }
    Ok(())
}

/// Validate the quantifier-negation De Morgan step `¬∃x⃗.φ ≡ ∀x⃗.¬φ`.
///
/// # Shape
///
/// A premiseless, argument-free two-literal clause
/// `(cl (exists ((x1 S1) .. (xn Sn)) φ) (forall ((x1 S1) .. (xn Sn)) (not φ)))`.
/// The first literal is the existential `E = ∃x⃗.φ`; the second is the
/// universal `F = ∀x⃗.¬φ` over the SAME binder list, whose body is the exact
/// single negation of `E`'s body.
///
/// # Soundness argument
///
/// The clause denotes the disjunction `E ∨ F`. It is a tautology because `F`
/// is precisely the negation of `E`:
///
/// ```text
/// ¬F = ¬(∀x⃗.¬φ) = ∃x⃗.¬¬φ = ∃x⃗.φ = E
/// ```
///
/// so `E ∨ F = E ∨ ¬E`, valid in every model. The step-by-step identity
/// `¬(∀x⃗.¬φ) = ∃x⃗.¬¬φ` is the standard quantifier-negation duality and holds
/// for ANY body `φ` and ANY binder vector, because the negation is pushed
/// through exactly ONE quantifier level — nothing is substituted, so there is
/// no capture to avoid and `φ`'s internal structure (including nested binders)
/// is irrelevant.
///
/// The three structural preconditions the validator ENFORCES are exactly the
/// ones this identity needs, and each is load-bearing:
///
/// * **The quantified body is Boolean** — a release-mode caller can construct
///   raw quantifiers around a non-Boolean term despite the builders' debug
///   assertions. Such a malformed expression has no Boolean duality theorem.
/// * **The binder vectors of `E` and `F` are identical** — same names, same
///   sorts, same order, same length. The bound-variable NAMES matter: `φ`'s
///   free occurrences of `x⃗` are captured by `E`'s binders, and `¬φ`'s by
///   `F`'s. If `F` renamed a binder, that variable would fall FREE in `¬φ` and
///   `F` would no longer be `¬E`. Rejecting a mismatch is what keeps the clause
///   a genuine `A ∨ ¬A`.
/// * **`F`'s body is the single negation of `E`'s body** — `F.body = (not φ)`
///   with the very same interned `φ`. If it were some other formula the
///   disjunction would not be a tautology at all.
///
/// All three are re-derived here from the clause alone; nothing is taken from the
/// producer. A violated precondition makes the validator REJECT (mutation
/// tests `qnt_neg_exists_rejects_*` exercise each one), so a wrong step can
/// only cost completeness, never soundness.
pub(crate) fn validate_qnt_neg_exists(
    terms: &TermStore,
    step: ProofId,
    clause: &[TermId],
    premise_count: usize,
    args: &[TermId],
) -> Result<(), ProofCheckError> {
    if premise_count != 0 {
        return Err(invalid_qnt_neg_exists(step, "must not have premises"));
    }
    if !args.is_empty() {
        return Err(invalid_qnt_neg_exists(step, "must not have arguments"));
    }
    let [exists_lit, forall_lit] = clause else {
        return Err(invalid_qnt_neg_exists(
            step,
            "conclusion must be exactly (cl exists forall)",
        ));
    };
    let TermData::Exists(exists_vars, exists_body, _) = terms.get(*exists_lit) else {
        return Err(invalid_qnt_neg_exists(
            step,
            "first literal must be an exists",
        ));
    };
    let TermData::Forall(forall_vars, forall_body, _) = terms.get(*forall_lit) else {
        return Err(invalid_qnt_neg_exists(
            step,
            "second literal must be a forall",
        ));
    };
    validate_qnt_neg_exists_body_sort(terms, step, *exists_body)?;
    // Binder vectors must be identical: same names, sorts, order, and length.
    if exists_vars != forall_vars {
        return Err(invalid_qnt_neg_exists(
            step,
            "forall binders must match the exists binders exactly (name, sort, order)",
        ));
    }
    if exists_vars.is_empty() {
        return Err(invalid_qnt_neg_exists(
            step,
            "binder list must be non-empty",
        ));
    }
    // The universal's body must be the single negation of the existential's
    // body, over the same interned term. Terms are hash-consed, so this is an
    // exact identity check — no substitution and no approximation.
    let TermData::Not(negated_inner) = terms.get(*forall_body) else {
        return Err(invalid_qnt_neg_exists(
            step,
            "forall body must be a negation",
        ));
    };
    if *negated_inner != *exists_body {
        return Err(invalid_qnt_neg_exists(
            step,
            "forall body must be exactly (not <exists body>)",
        ));
    }
    Ok(())
}
