// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bounded exact finite-word identities, with no candidate model or solver.
//! A conjunction is accepted only when every conjunct is independently valid.

use super::*;
use num_traits::ToPrimitive;

#[derive(Default, PartialEq, Eq)]
struct Length {
    constant: i64,
    // Every opaque sequence length is nonnegative. Repeated chunks retain
    // multiplicity; sorting uses only fixed-size native term identities.
    chunks: Vec<TermId>,
    sequence: bool,
}

fn app<'a>(terms: &'a TermStore, root: TermId, name: &str, arity: usize) -> Option<&'a [TermId]> {
    if terms.entry_stamp(root).is_none() || terms.is_declared_function(name) {
        return None;
    }
    match terms.get(root) {
        TermData::App(Symbol::Named(actual), arguments)
            if actual == name
                && arguments.len() == arity
                && arguments
                    .iter()
                    .all(|&argument| terms.entry_stamp(argument).is_some()) =>
        {
            Some(arguments)
        }
        _ => None,
    }
}

fn length(terms: &TermStore, root: TermId, work: &mut Work<'_>) -> Option<Length> {
    let mut output = Length::default();
    work.scratch::<TermId>(1)?;
    let mut pending = vec![root];
    while let Some(term) = pending.pop() {
        work.visit()?;
        if terms.entry_stamp(term).is_none() || terms.sort(term) != &Sort::Int {
            return None;
        }
        match terms.get(term) {
            TermData::Const(ay_core::Constant::Int(value)) => {
                output.constant = output.constant.checked_add(value.to_i64()?)?;
            }
            TermData::App(Symbol::Named(name), arguments) if name == "+" => {
                if terms.is_declared_function(name) {
                    return None;
                }
                if arguments.len() < 2
                    || pending.len().checked_add(arguments.len())? > work.remaining
                {
                    return None;
                }
                work.scratch::<TermId>(arguments.len())?;
                pending.extend(arguments.iter().rev().copied());
            }
            TermData::App(Symbol::Named(name), arguments) if name == "seq.len" => {
                if terms.is_declared_function(name) {
                    return None;
                }
                let [sequence] = arguments.as_slice() else {
                    return None;
                };
                let mut word = Vec::new();
                ground_seq_elements_with_budget(terms, *sequence, &mut word, work)?;
                output.sequence = true;
                for part in word {
                    work.visit()?;
                    match part {
                        WordPart::Unit(_) => output.constant = output.constant.checked_add(1)?,
                        WordPart::Opaque(chunk) => {
                            work.scratch::<TermId>(1)?;
                            output.chunks.push(chunk);
                        }
                    }
                }
            }
            _ => return None,
        }
    }
    // Bounded insertion sort polls each comparison and fixed-size swap. A
    // large descending chunk inventory consumes this SAME work allowance.
    for index in 1..output.chunks.len() {
        let mut current = index;
        while current > 0 {
            work.visit()?;
            if output.chunks[current - 1] <= output.chunks[current] {
                break;
            }
            output.chunks.swap(current - 1, current);
            current -= 1;
        }
    }
    Some(output)
}

fn contains<'a>(terms: &'a TermStore, root: TermId) -> Option<&'a [TermId]> {
    let arguments = app(terms, root, "seq.contains", 2)?;
    let [haystack, needle] = arguments else {
        return None;
    };
    (terms.sort(root) == &Sort::Bool
        && matches!(terms.sort(*haystack), Sort::Seq(_))
        && terms.sort(*haystack) == terms.sort(*needle))
    .then_some(arguments)
}

fn unit_element(terms: &TermStore, sequence: TermId) -> Option<TermId> {
    let arguments = app(terms, sequence, "seq.unit", 1)?;
    let [element] = arguments else {
        return None;
    };
    let Sort::Seq(sort) = terms.sort(sequence) else {
        return None;
    };
    (terms.sort(*element) == sort.as_ref()).then_some(*element)
}

/// Membership in a word with one appended unit is exactly membership in the
/// prefix or equality with the appended element. The singleton needle is
/// essential: the statement is false for arbitrary subsequence needles.
fn membership_recursion(terms: &TermStore, member: TermId, disjunction: TermId) -> Option<()> {
    let [word, needle] = contains(terms, member)? else {
        return None;
    };
    let element = unit_element(terms, *needle)?;
    let [prefix, last] = app(terms, *word, "seq.++", 2)? else {
        return None;
    };
    if terms.sort(*word) != terms.sort(*prefix) || terms.sort(*word) != terms.sort(*last) {
        return None;
    }
    let appended = unit_element(terms, *last)?;
    let pieces = app(terms, disjunction, "or", 2)?;
    if terms.sort(disjunction) != &Sort::Bool
        || pieces.len() != 2
        || pieces.iter().any(|&piece| terms.sort(piece) != &Sort::Bool)
    {
        return None;
    }
    for (equality, original) in [(pieces[0], pieces[1]), (pieces[1], pieces[0])] {
        let Some((a, b)) = decode_eq(terms, equality) else {
            continue;
        };
        if !((a == appended && b == element) || (b == appended && a == element)) {
            continue;
        }
        if contains(terms, original) == Some([*prefix, *needle].as_slice()) {
            return Some(());
        }
    }
    None
}

fn compare_lengths(
    terms: &TermStore,
    root: TermId,
    negated: bool,
    work: &mut Work<'_>,
) -> Option<bool> {
    let TermData::App(Symbol::Named(operator), arguments) = terms.get(root) else {
        return None;
    };
    if terms.is_declared_function(operator) {
        return None;
    }
    let [a, b] = arguments.as_slice() else {
        return None;
    };
    let (left, right, strict) = match (operator.as_str(), negated) {
        ("<=", false) | (">", true) => (*a, *b, false),
        ("<", false) | (">=", true) => (*a, *b, true),
        (">=", false) | ("<", true) => (*b, *a, false),
        (">", false) | ("<=", true) => (*b, *a, true),
        _ => return None,
    };
    let left = length(terms, left, work)?;
    let right = length(terms, right, work)?;
    let constants_suffice = if strict {
        left.constant < right.constant
    } else {
        left.constant <= right.constant
    };
    (work.progress)(left.chunks.len().saturating_add(right.chunks.len()), 0).then_some(())?;
    (constants_suffice && (left.chunks == right.chunks || left.chunks.is_empty()))
        .then_some(left.sequence || right.sequence)
}

pub(super) fn valid(
    terms: &TermStore,
    root: TermId,
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> bool {
    valid_bounded(terms, root, progress).unwrap_or(false)
}

fn valid_bounded(
    terms: &TermStore,
    root: TermId,
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Option<bool> {
    let mut work = Work::new(progress)?;
    work.scratch::<TermId>(1)?;
    let mut pending = vec![root];
    let mut sequence = false;
    while let Some(term) = pending.pop() {
        work.visit()?;
        if terms.entry_stamp(term).is_none() || terms.sort(term) != &Sort::Bool {
            return None;
        }
        match terms.get(term) {
            TermData::Const(ay_core::Constant::Bool(true)) => {}
            TermData::App(Symbol::Named(operator), arguments) if operator == "and" => {
                if terms.is_declared_function(operator) {
                    return None;
                }
                if arguments.is_empty()
                    || pending.len().checked_add(arguments.len())? > work.remaining
                {
                    return None;
                }
                work.scratch::<TermId>(arguments.len())?;
                pending.extend(arguments.iter().rev().copied());
            }
            TermData::App(Symbol::Named(operator), _) if operator == "=" => {
                let (left, right) = decode_eq(terms, term)?;
                match terms.sort(left) {
                    Sort::Seq(_) => {
                        let (mut a, mut b) = (Vec::new(), Vec::new());
                        ground_seq_elements_with_budget(terms, left, &mut a, &mut work)?;
                        ground_seq_elements_with_budget(terms, right, &mut b, &mut work)?;
                        (work.progress)(a.len().saturating_add(b.len()), 0).then_some(())?;
                        if a != b {
                            return None;
                        }
                        sequence = true;
                    }
                    Sort::Int => {
                        let a = length(terms, left, &mut work)?;
                        let b = length(terms, right, &mut work)?;
                        (work.progress)(a.chunks.len().saturating_add(b.chunks.len()), 0)
                            .then_some(())?;
                        if a.constant != b.constant || a.chunks != b.chunks {
                            return None;
                        }
                        sequence |= a.sequence || b.sequence;
                    }
                    Sort::Bool => {
                        (work.progress)(32, 0).then_some(())?;
                        if membership_recursion(terms, left, right).is_none()
                            && membership_recursion(terms, right, left).is_none()
                        {
                            return None;
                        }
                        sequence = true;
                    }
                    _ => return None,
                }
            }
            TermData::Not(inner) => {
                if terms.entry_stamp(*inner).is_none() || terms.sort(*inner) != &Sort::Bool {
                    return None;
                }
                if let Some([haystack, needle]) = contains(terms, *inner) {
                    unit_element(terms, *needle)?;
                    let mut word = Vec::new();
                    ground_seq_elements_with_budget(terms, *haystack, &mut word, &mut work)?;
                    if !word.is_empty() {
                        return None;
                    }
                    sequence = true;
                } else {
                    sequence |= compare_lengths(terms, *inner, true, &mut work)?;
                }
            }
            _ => sequence |= compare_lengths(terms, term, false, &mut work)?,
        }
    }
    Some(sequence)
}
