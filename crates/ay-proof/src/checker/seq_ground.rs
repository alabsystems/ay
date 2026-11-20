// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact strict theorem for ground-sequence identities through one shared
//! symbolic anchor.
//!
//! The clause is exactly `(cl (not (= x S1)) (= x S2))` — either equality
//! orientation, either literal order — where `S1` and `S2` are GROUND
//! sequence terms whose concat-flattened, empty-dropped normal forms are
//! identical. A unit contributes its exact element term; any other well-typed
//! sequence contributes one opaque chunk. No commutation, element equality or
//! element inference is performed. This is the free-monoid identity `S1 = S2`,
//! so `x = S1 ⊢ x = S2` is also valid. The normalizer is independent of the
//! solver's sequence engine and rejects malformed native operators/sorts.
//! Unit sentences additionally admit the bounded exact length and singleton
//! membership laws in `sentences`; every conjunct must pass independently.
//!
//! Operator semantics: https://microsoft.github.io/z3guide/docs/theories/Sequences/

use ay_core::{ProofId, Sort, Symbol, TermData, TermId, TermStore};

use super::ProofCheckError;

/// Bound on the flattened element count, so a pathological concat tree
/// cannot make validation quadratic in adversarial input.
const MAX_GROUND_ELEMENTS: usize = 4096;
const MAX_NORMALIZATION_NODES: usize = MAX_GROUND_ELEMENTS * 4;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum WordPart {
    Unit(TermId),
    Opaque(TermId),
}

struct Work<'a> {
    remaining: usize,
    progress: &'a mut dyn FnMut(usize, usize) -> bool,
}

impl<'a> Work<'a> {
    fn new(progress: &'a mut dyn FnMut(usize, usize) -> bool) -> Option<Self> {
        progress(1, 4 * std::mem::size_of::<Vec<TermId>>()).then_some(Self {
            remaining: MAX_NORMALIZATION_NODES,
            progress,
        })
    }

    fn visit(&mut self) -> Option<()> {
        self.remaining = self.remaining.checked_sub(1)?;
        (self.progress)(1, 0).then_some(())
    }

    /// Before each push/extension, conservatively pay capacity growth, moved
    /// cells and eventual disposal. Vector doubling needs fewer than four
    /// cells of cumulative allocation/movement per inserted cell.
    fn scratch<T>(&mut self, count: usize) -> Option<()> {
        let bytes = count.checked_mul(4 * std::mem::size_of::<T>())?;
        (self.progress)(count.checked_mul(4)?, bytes).then_some(())
    }
}

mod sentences;

fn invalid(step: ProofId, reason: impl Into<String>) -> ProofCheckError {
    ProofCheckError::InvalidTheoryLemma {
        step,
        reason: format!("SeqGroundEval: {}", reason.into()),
    }
}

/// Flatten a single-literal `(cl (or L1 .. Ln))` clause into `[L1, .., Ln]`;
/// every other clause is returned unchanged (mirrors the array/euf lanes —
/// the packed `or` form denotes the same disjunction).
fn flatten_clause_literals(terms: &TermStore, clause: &[TermId]) -> Option<Vec<TermId>> {
    if clause.len() > 2 || clause.iter().any(|&term| terms.entry_stamp(term).is_none()) {
        return None;
    }
    if clause.len() == 1 {
        if let TermData::App(Symbol::Named(sym), args) = terms.get(clause[0]) {
            if sym == "or" {
                return (args.len() == 2
                    && !terms.is_declared_function(sym)
                    && terms.sort(clause[0]) == &Sort::Bool
                    && args.iter().all(|&term| {
                        terms.entry_stamp(term).is_some() && terms.sort(term) == &Sort::Bool
                    }))
                .then(|| args.clone());
            }
        }
    }
    Some(clause.to_vec())
}

fn strip_not(terms: &TermStore, term: TermId) -> (TermId, bool) {
    match terms.get(term) {
        TermData::Not(inner) => (*inner, true),
        _ => (term, false),
    }
}

fn decode_eq(terms: &TermStore, term: TermId) -> Option<(TermId, TermId)> {
    if terms.entry_stamp(term).is_none() || terms.sort(term) != &Sort::Bool {
        return None;
    }
    match terms.get(term) {
        TermData::App(Symbol::Named(name), args)
            if name == "="
                && !terms.is_declared_function(name)
                && args.len() == 2
                && args
                    .iter()
                    .all(|&argument| terms.entry_stamp(argument).is_some())
                && terms.sort(args[0]) == terms.sort(args[1]) =>
        {
            Some((args[0], args[1]))
        }
        _ => None,
    }
}

/// Normalize only the associative operation and its identity. Opaque chunks
/// and arbitrary unit elements keep exact, ordered term identities.
fn ground_seq_elements(
    terms: &TermStore,
    root: TermId,
    out: &mut Vec<WordPart>,
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Option<()> {
    let mut work = Work::new(progress)?;
    ground_seq_elements_with_budget(terms, root, out, &mut work)
}

fn ground_seq_elements_with_budget(
    terms: &TermStore,
    root: TermId,
    out: &mut Vec<WordPart>,
    work: &mut Work<'_>,
) -> Option<()> {
    if terms.entry_stamp(root).is_none() {
        return None;
    }
    let sort = terms.sort(root);
    let Sort::Seq(element) = sort else {
        return None;
    };
    work.scratch::<TermId>(1)?;
    let mut pending = vec![root];
    while let Some(term) = pending.pop() {
        work.visit()?;
        if terms.entry_stamp(term).is_none() || terms.sort(term) != sort {
            return None;
        }
        if let TermData::App(Symbol::Named(name), _) = terms.get(term) {
            if matches!(name.as_str(), "seq.empty" | "seq.unit" | "seq.++")
                && terms.is_declared_function(name)
            {
                return None;
            }
        }
        match terms.get(term) {
            TermData::App(Symbol::Named(name), args) if name == "seq.empty" => {
                if !args.is_empty() {
                    return None;
                }
            }
            TermData::App(Symbol::Named(name), args) if name == "seq.unit" => {
                let [value] = args.as_slice() else {
                    return None;
                };
                if terms.entry_stamp(*value).is_none() || terms.sort(*value) != element.as_ref() {
                    return None;
                }
                if out.len() >= MAX_GROUND_ELEMENTS {
                    return None;
                }
                work.scratch::<WordPart>(1)?;
                out.push(WordPart::Unit(*value));
            }
            TermData::App(Symbol::Named(name), args) if name == "seq.++" => {
                if args.is_empty() || pending.len().checked_add(args.len())? > work.remaining {
                    return None;
                }
                work.scratch::<TermId>(args.len())?;
                pending.extend(args.iter().rev().copied());
            }
            _ => {
                if out.len() >= MAX_GROUND_ELEMENTS {
                    return None;
                }
                work.scratch::<WordPart>(1)?;
                out.push(WordPart::Opaque(term));
            }
        }
    }
    Some(())
}

/// Validate a [`ay_core::TheoryLemmaKind::SeqGroundEval`] clause.
pub(crate) fn validate_seq_ground_eval(
    terms: &TermStore,
    step_id: ProofId,
    clause: &[TermId],
) -> Result<(), ProofCheckError> {
    validate_seq_ground_eval_with_progress(terms, step_id, clause, &mut |_, _| true)
}

pub(super) fn validate_seq_ground_eval_with_progress(
    terms: &TermStore,
    step_id: ProofId,
    clause: &[TermId],
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Result<(), ProofCheckError> {
    let mut refused = false;
    let mut original = |work, bytes| {
        if !refused && !progress(work, bytes) {
            refused = true;
        }
        !refused
    };
    let result = validate_seq_ground_eval_impl(terms, step_id, clause, &mut original);
    if result.is_ok() {
        let _ = original(0, 0);
    }
    if refused {
        return Err(ProofCheckError::ResourceLimit);
    }
    result
}

fn validate_seq_ground_eval_impl(
    terms: &TermStore,
    step_id: ProofId,
    clause: &[TermId],
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Result<(), ProofCheckError> {
    if !progress(4, 4 * std::mem::size_of::<TermId>()) {
        return Err(invalid(step_id, "original caller refused normalization"));
    }
    let literals = flatten_clause_literals(terms, clause)
        .ok_or_else(|| invalid(step_id, "malformed or oversized literal vector"))?;
    // Shape (B): a UNIT positive equality between two ground sequence terms
    // with elementwise-identical normal forms — the pure ground identity
    // (`(= (seq.++ seq.empty (seq.unit 1)) (seq.unit 1))`), used by the
    // authored-source rebuild's trans chains exactly like the BV `evaluate`
    // leg.
    if let [only] = literals.as_slice() {
        if sentences::valid(terms, *only, progress) {
            return Ok(());
        }
        let (eq, negated) = strip_not(terms, *only);
        if negated {
            return Err(invalid(step_id, "unit clause must be a positive equality"));
        }
        let (left, right) = decode_eq(terms, eq)
            .ok_or_else(|| invalid(step_id, "unit literal is not an equality"))?;
        let mut left_elements = Vec::new();
        let mut right_elements = Vec::new();
        if ground_seq_elements(terms, left, &mut left_elements, progress).is_some()
            && ground_seq_elements(terms, right, &mut right_elements, progress).is_some()
            && progress(left_elements.len().saturating_add(right_elements.len()), 0)
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
        if ground_seq_elements(terms, premise_ground, &mut premise_elements, progress).is_some()
            && ground_seq_elements(terms, conclusion_ground, &mut conclusion_elements, progress)
                .is_some()
            && progress(
                premise_elements
                    .len()
                    .saturating_add(conclusion_elements.len()),
                0,
            )
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

/// The same independent kernel, with refusal-only original work/storage
/// admission before traversal and scratch growth. Refusal supplies no lemma.
#[must_use]
pub fn recognize_seq_ground_eval_with_progress(
    terms: &TermStore,
    clause: &[TermId],
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> bool {
    validate_seq_ground_eval_with_progress(terms, ProofId(0), clause, progress).is_ok()
}

#[cfg(test)]
mod tests;
