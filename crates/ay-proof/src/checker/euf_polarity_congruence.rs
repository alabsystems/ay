// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Sub-schema (P) of [`ay_core::TheoryLemmaKind::EufCongruenceExplanation`]:
//! a congruence explanation whose CONCLUSION is a PREDICATE application, not an
//! equality.
//!
//! # The clause
//!
//! ```text
//! (cl (not (= a_1 b_1)) .. (not (= a_n b_n))     hypothesis equalities
//!     (not A_1) .. (not A_j)                     atoms a refutation reads TRUE
//!     B_1 .. B_k)                                atoms it reads FALSE
//! ```
//!
//! at least one of which is NOT a (possibly negated) equality — that last
//! condition is the SCOPE guard, and it makes this schema and the equality
//! schema in [`super::euf_congruence_explanation`] disjoint by construction.
//! The measured population is B-method set membership over `mem`:
//!
//! ```text
//! (cl (not (= BOOL g179)) (not (= g179 g187)) (not (mem g222 (--> BOOL BOOL)))
//!     (not (mem g266 g187)) (not (= TRUE g266)) (not (= BOOL g404))
//!     (not (= TRUE (bool b794)))
//!     (mem (bool b794) g404))
//! ```
//!
//! `g266 = TRUE = bool(b794)` and `g187 = g179 = BOOL = g404` are two equality
//! CHAINS, so `mem(g266, g187)` and `mem(bool(b794), g404)` are congruent, and
//! the clause asserts one negatively and the other positively. The equality
//! schema declines it at "every literal must be a (possibly negated) equality";
//! `eq_congruent_pred` declines it because the argument equalities are not
//! stated directly.
//!
//! # Soundness
//!
//! The claim is that NO structure `M` falsifies the clause. Suppose one did.
//! Then, literal by literal, `M` makes every NEGATED literal's atom `true` and
//! every POSITIVE literal `false`. Hence in that `M`:
//!
//! * **(hypothesis)** the two sides of each negated equality are equal — the
//!   same merge the equality schema performs, and the reason a POSITIVE
//!   equality is never read as a hypothesis (`(cl (= a b) (= (f a) (f b)))` is
//!   false at `a := 0, b := 1, f(0) := 2, f(1) := 3`);
//! * **(true class)** all negated literals' atoms denote `true`, so they are
//!   pairwise equal as `Bool` terms;
//! * **(false class)** all positive literals denote `false`, so they too are
//!   pairwise equal;
//! * **(congruence)** two nodes with the same head and pairwise-merged children
//!   are equal, because every former the closure descends through denotes a
//!   total FUNCTION.
//!
//! Every merge the routine performs is therefore an equality that holds in that
//! `M`, so by induction every merged pair is equal in it. Acceptance requires a
//! node of the TRUE class to be merged with a node of the FALSE class — one
//! term that `M` must interpret as both `true` and `false`. No such `M` exists,
//! so the clause is valid. Nothing about the conflict that produced it, and no
//! problem context, is taken on trust: the clause structure IS the certificate.
//!
//! Completeness is neither claimed nor needed. A clause the closure does not
//! settle, one that trips a resource bound, and one outside the scope guards
//! are all REJECTED — the fail-closed direction.
//!
//! # Metering
//!
//! Shares the kind's `(0, 0)` precharge and debits its ACTUAL work through the
//! strict checker's progress callback, exactly as the equality schema does:
//! every interned node and every fixpoint node-visit is charged inside the
//! shared [`CongruenceClosure`].

use ay_core::{ProofId, TermData, TermId, TermStore};

use super::euf_congruence_explanation::CongruenceClosure;
use super::ProofCheckError;

/// Decode a term as an equality `(= lhs rhs)`.
fn decode_eq(terms: &TermStore, term: TermId) -> Option<(TermId, TermId)> {
    match terms.get(term) {
        TermData::App(ay_core::Symbol::Named(name), args) if name == "=" && args.len() == 2 => {
            Some((args[0], args[1]))
        }
        _ => None,
    }
}

/// Validate one predicate-conclusion congruence explanation. See the module
/// docs for the schema and its soundness argument.
pub(crate) fn validate_euf_polarity_congruence(
    terms: &TermStore,
    step_id: ProofId,
    clause: &[TermId],
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Result<(), ProofCheckError> {
    let reject = |reason: &str| ProofCheckError::InvalidTheoryLemma {
        step: step_id,
        reason: format!("EufPolarityCongruence: {reason}"),
    };
    let flattened = super::euf::flatten_or_clause(terms, clause);
    let literals = flattened.as_slice();
    if literals.len() < 2 {
        return Err(reject("clause must have at least 2 literals"));
    }

    let mut hypotheses: Vec<(TermId, TermId)> = Vec::with_capacity(literals.len());
    let mut true_atoms: Vec<TermId> = Vec::with_capacity(literals.len());
    let mut false_atoms: Vec<TermId> = Vec::with_capacity(literals.len());
    let mut non_equality = false;
    for &literal in literals {
        // `strip_not` counts the negation PARITY, so `(not (not (= a b)))` is a
        // POSITIVE literal and contributes no hypothesis — the same polarity
        // discipline the equality schema states.
        let (inner, negated) = super::euf::strip_not(terms, literal);
        let equality = decode_eq(terms, inner);
        non_equality |= equality.is_none();
        if negated {
            if let Some((lhs, rhs)) = equality {
                hypotheses.push((lhs, rhs));
            }
            true_atoms.push(inner);
        } else {
            false_atoms.push(inner);
        }
    }
    // SCOPE. An all-equality clause is the equality schema's business, and this
    // one must not silently take it: that schema's conclusion test is not
    // subsumed here (`(cl (not (= a b)) (= (f a) (f b)))` merges the
    // conclusion's SIDES without ever relating its atom to `(= a b)`), so the
    // two are kept disjoint rather than ordered.
    if !non_equality {
        return Err(reject(
            "every literal is an equality; that is the equality schema's clause shape",
        ));
    }
    if hypotheses.is_empty() {
        return Err(reject("clause has no hypothesis equality"));
    }
    if false_atoms.is_empty() {
        return Err(reject("clause has no positive literal to conclude"));
    }

    let mut closure = CongruenceClosure::new();
    let mut edges = Vec::with_capacity(hypotheses.len());
    for (lhs, rhs) in hypotheses {
        let lhs = closure.add(terms, lhs, step_id, progress)?;
        let rhs = closure.add(terms, rhs, step_id, progress)?;
        edges.push((lhs, rhs));
    }
    let mut true_nodes = Vec::with_capacity(true_atoms.len());
    for atom in true_atoms {
        true_nodes.push(closure.add(terms, atom, step_id, progress)?);
    }
    let mut false_nodes = Vec::with_capacity(false_atoms.len());
    for atom in false_atoms {
        false_nodes.push(closure.add(terms, atom, step_id, progress)?);
    }
    for (lhs, rhs) in edges {
        closure.union(lhs, rhs);
    }
    for window in true_nodes.windows(2) {
        closure.union(window[0], window[1]);
    }
    for window in false_nodes.windows(2) {
        closure.union(window[0], window[1]);
    }
    closure.close(step_id, progress)?;

    let false_root = closure.find(false_nodes[0]);
    for node in true_nodes {
        if closure.find(node) == false_root {
            return Ok(());
        }
    }
    Err(reject(
        "no negated literal's atom is congruent to a positive literal under the clause's own \
         equalities",
    ))
}

/// Recognize the exact predicate-conclusion congruence-explanation shape
/// [`validate_euf_polarity_congruence`] accepts.
///
/// Recognition IS the strict validator run on the clause exactly as recorded,
/// so classifier and checker cannot drift. Like the equality schema this one is
/// ORDER-FREE, so a caller may relabel a leaf IN PLACE without touching the
/// clause its consumers already reference, and the recognizer runs with an
/// UNLIMITED meter: the intrinsic bounds still apply and the strict checker
/// re-runs the same validation under the caller's real envelope.
#[must_use]
pub fn recognize_euf_polarity_congruence(terms: &TermStore, clause: &[TermId]) -> bool {
    validate_euf_polarity_congruence(terms, ProofId(0), clause, &mut |_, _| true).is_ok()
}

#[cfg(test)]
#[path = "euf_polarity_congruence_tests.rs"]
mod tests;
