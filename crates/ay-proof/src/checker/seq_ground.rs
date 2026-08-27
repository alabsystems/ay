// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact strict theorem for ground-sequence identities through one shared
//! symbolic anchor.
//!
//! The clause is exactly `(cl (not (= x S1)) (= x S2))` — either equality
//! orientation, either literal order — where `S1` and `S2` are GROUND
//! sequence terms (built only from `seq.empty`, `seq.unit` over constant
//! elements, and `seq.++`) whose concat-flattened, empty-dropped normal
//! forms are elementwise identical. `x = S1 ⊢ x = S2` is then the
//! substitution instance of the ground identity `S1 = S2`, so the clause is
//! a sequence tautology. The normalizer here is independent of the solver's
//! seq engine and fails closed on any non-ground leaf or unsupported
//! operator.

use ay_core::{ProofId, Symbol, TermData, TermId, TermStore};

use super::ProofCheckError;

/// Bound on the flattened element count, so a pathological concat tree
/// cannot make validation quadratic in adversarial input.
const MAX_GROUND_ELEMENTS: usize = 4096;

fn invalid(step: ProofId, reason: impl Into<String>) -> ProofCheckError {
    ProofCheckError::InvalidTheoryLemma {
        step,
        reason: format!("SeqGroundEval: {}", reason.into()),
    }
}

/// Flatten a single-literal `(cl (or L1 .. Ln))` clause into `[L1, .., Ln]`;
/// every other clause is returned unchanged (mirrors the array/euf lanes —
/// the packed `or` form denotes the same disjunction).
fn flatten_clause_literals(terms: &TermStore, clause: &[TermId]) -> Vec<TermId> {
    if clause.len() == 1 {
        if let TermData::App(Symbol::Named(sym), args) = terms.get(clause[0]) {
            if sym == "or" && args.len() >= 2 {
                return args.clone();
            }
        }
    }
    clause.to_vec()
}

fn strip_not(terms: &TermStore, term: TermId) -> (TermId, bool) {
    match terms.get(term) {
        TermData::Not(inner) => (*inner, true),
        _ => (term, false),
    }
}

fn decode_eq(terms: &TermStore, term: TermId) -> Option<(TermId, TermId)> {
    match terms.get(term) {
        TermData::App(Symbol::Named(name), args) if name == "=" && args.len() == 2 => {
            Some((args[0], args[1]))
        }
        _ => None,
    }
}

/// Flatten a ground sequence term into its unit-element argument list.
///
/// Returns `None` (fail closed) for anything that is not `seq.empty`,
/// `seq.unit` of a CONSTANT element, or `seq.++` of such terms.
fn ground_seq_elements(terms: &TermStore, term: TermId, out: &mut Vec<TermId>) -> Option<()> {
    match terms.get(term) {
        TermData::App(Symbol::Named(name), args) => match name.as_str() {
            "seq.empty" if args.is_empty() => Some(()),
            "seq.unit" if args.len() == 1 => {
                if !matches!(terms.get(args[0]), TermData::Const(_)) {
                    return None;
                }
                if out.len() >= MAX_GROUND_ELEMENTS {
                    return None;
                }
                out.push(args[0]);
                Some(())
            }
            "seq.++" if !args.is_empty() => {
                for &arg in args {
                    ground_seq_elements(terms, arg, out)?;
                }
                Some(())
            }
            _ => None,
        },
        _ => None,
    }
}

/// Validate a [`ay_core::TheoryLemmaKind::SeqGroundEval`] clause.
pub(crate) fn validate_seq_ground_eval(
    terms: &TermStore,
    step_id: ProofId,
    clause: &[TermId],
) -> Result<(), ProofCheckError> {
    let literals = flatten_clause_literals(terms, clause);
    // Shape (B): a UNIT positive equality between two ground sequence terms
    // with elementwise-identical normal forms — the pure ground identity
    // (`(= (seq.++ seq.empty (seq.unit 1)) (seq.unit 1))`), used by the
    // authored-source rebuild's trans chains exactly like the BV `evaluate`
    // leg.
    if let [only] = literals.as_slice() {
        let (eq, negated) = strip_not(terms, *only);
        if negated {
            return Err(invalid(step_id, "unit clause must be a positive equality"));
        }
        let (left, right) = decode_eq(terms, eq)
            .ok_or_else(|| invalid(step_id, "unit literal is not an equality"))?;
        let mut left_elements = Vec::new();
        let mut right_elements = Vec::new();
        if ground_seq_elements(terms, left, &mut left_elements).is_some()
            && ground_seq_elements(terms, right, &mut right_elements).is_some()
            && left_elements == right_elements
        {
            return Ok(());
        }
        return Err(invalid(
            step_id,
            "unit equality sides are not elementwise-identical ground sequences",
        ));
    }
    let [first, second] = literals.as_slice() else {
        return Err(invalid(step_id, "clause must have exactly 2 literals"));
    };

    let (first_eq, first_negated) = strip_not(terms, *first);
    let (second_eq, second_negated) = strip_not(terms, *second);
    let ((premise, _), (conclusion, _)) = match (first_negated, second_negated) {
        (true, false) => ((first_eq, first_negated), (second_eq, second_negated)),
        (false, true) => ((second_eq, second_negated), (first_eq, first_negated)),
        _ => {
            return Err(invalid(
                step_id,
                "clause must hold one negated and one positive equality",
            ));
        }
    };

    let (premise_left, premise_right) =
        decode_eq(terms, premise).ok_or_else(|| invalid(step_id, "premise is not an equality"))?;
    let (conclusion_left, conclusion_right) = decode_eq(terms, conclusion)
        .ok_or_else(|| invalid(step_id, "conclusion is not an equality"))?;

    // Find the shared symbolic anchor and the two ground sides.
    let candidates = [(premise_left, premise_right), (premise_right, premise_left)]
        .into_iter()
        .flat_map(|(anchor, premise_ground)| {
            [
                (anchor, premise_ground, conclusion_left, conclusion_right),
                (anchor, premise_ground, conclusion_right, conclusion_left),
            ]
        });
    for (anchor, premise_ground, conclusion_anchor, conclusion_ground) in candidates {
        if anchor != conclusion_anchor {
            continue;
        }
        let mut premise_elements = Vec::new();
        let mut conclusion_elements = Vec::new();
        if ground_seq_elements(terms, premise_ground, &mut premise_elements).is_some()
            && ground_seq_elements(terms, conclusion_ground, &mut conclusion_elements).is_some()
            && premise_elements == conclusion_elements
        {
            return Ok(());
        }
    }
    Err(invalid(
        step_id,
        "no shared anchor with elementwise-identical ground sequence sides",
    ))
}

/// Declaration-free recognizer used by proof producers: `true` exactly when
/// `validate_seq_ground_eval` accepts the clause.
#[must_use]
pub fn recognize_seq_ground_eval(terms: &TermStore, clause: &[TermId]) -> bool {
    validate_seq_ground_eval(terms, ProofId(0), clause).is_ok()
}
