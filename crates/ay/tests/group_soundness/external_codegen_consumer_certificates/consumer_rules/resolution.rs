// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The consumer's `resolution` (Clean's Carcara `resolution.rs`, default
//! configuration). With `:args` it is `resolution_with_args`: resolve the
//! premises in order on the given pivots, as sets of literals, and compare
//! with the conclusion as a set; that is decided exactly. Without `:args` the
//! consumer accepts when its greedy pivot search succeeds AND a bounded
//! propositional search confirms entailment, or when reverse unit propagation
//! derives the conclusion. Reverse unit propagation is mirrored exactly, and a
//! counter-model found here refutes entailment (so both routes refuse); the
//! greedy route alone is not mirrored, so the rest is `Undetermined`.

use std::collections::{HashMap, HashSet, VecDeque};

use super::document::Document;
use super::{refuse, require, undecided, Checked, StepInput};

/// `remove_all_negations`: how many leading `not`s, and the term under them.
fn literal(document: &Document, mut term: u32) -> (u32, u32) {
    let mut negations = 0;
    while let Some([inner]) = document.op(term, "not").as_deref() {
        term = *inner;
        negations += 1;
    }
    (negations, term)
}

/// `remove_all_negations_with_polarity`.
fn signed(document: &Document, term: u32) -> (bool, u32) {
    let (negations, atom) = literal(document, term);
    (negations % 2 == 0, atom)
}

pub(super) fn resolution(document: &mut Document, input: &StepInput) -> Checked {
    if !input.args.is_empty() {
        return with_pivots(document, input);
    }
    if input.conclusion.is_empty() {
        if let [premise] = &input.premises[..] {
            if let [term] = premise[..] {
                if document.op(term, "not").is_some_and(
                    |inner| matches!(inner[..], [atom] if document.is_atom(atom, "true")),
                ) {
                    return Ok(());
                }
            }
        }
    }
    require(input.premises.len() >= 2, || {
        format!("{} premises, not two or more", input.premises.len())
    })?;
    if reverse_unit_propagation(document, input) {
        return Ok(());
    }
    if counter_model(document, input) {
        return refuse("the premises do not entail the conclusion (a counter-model exists)");
    }
    undecided("reverse unit propagation fails; the consumer's greedy pivot search is not mirrored")
}

/// `resolution_with_args`.
fn with_pivots(document: &mut Document, input: &StepInput) -> Checked {
    let steps = input
        .premises
        .len()
        .checked_sub(1)
        .filter(|&steps| steps >= 1);
    let Some(steps) = steps else {
        return refuse(format!(
            "{} premises, not two or more",
            input.premises.len()
        ));
    };
    require(input.args.len() == 2 * steps, || {
        format!("{} arguments, not {}", input.args.len(), 2 * steps)
    })?;
    let mut current: HashSet<(u32, u32)> = input.premises[0]
        .iter()
        .map(|&t| literal(document, t))
        .collect();
    for (next, pivot) in input.premises[1..].iter().zip(input.args.chunks(2)) {
        let (negations, atom) = literal(document, pivot[0]);
        let in_current = match document.atom_text(pivot[1]) {
            Some("true") => true,
            Some("false") => false,
            _ => return refuse("a pivot's polarity is not a Boolean constant"),
        };
        let negated = (negations + 1, atom);
        let (pivot_in_current, pivot_in_next) = if in_current {
            ((negations, atom), negated)
        } else {
            (negated, (negations, atom))
        };
        require(current.remove(&pivot_in_current), || {
            format!("pivot {} not found", document.show(atom))
        })?;
        let mut found = false;
        for &term in next {
            let lit = literal(document, term);
            if !found && lit == pivot_in_next {
                found = true;
            } else {
                current.insert(lit);
            }
        }
        require(found, || {
            format!(
                "pivot {} not found in the next premise",
                document.show(atom)
            )
        })?;
    }
    let conclusion: HashSet<(u32, u32)> = input
        .conclusion
        .iter()
        .map(|&t| literal(document, t))
        .collect();
    require(conclusion == current, || {
        "the conclusion is not the resolvent".to_string()
    })
}

/// Carcara's `rup`: unit propagation from the negated conclusion and the unit
/// premises reaches a conflict. Constants are opaque atoms here, as there.
fn reverse_unit_propagation(document: &Document, input: &StepInput) -> bool {
    let mut clauses: Vec<Option<HashSet<(bool, u32)>>> = input
        .premises
        .iter()
        .map(|clause| Some(clause.iter().map(|&t| signed(document, t)).collect()))
        .collect();
    let mut used_in: HashMap<u32, Vec<usize>> = HashMap::new();
    for (i, clause) in clauses.iter().enumerate() {
        for &(_, atom) in clause.iter().flatten() {
            used_in.entry(atom).or_default().push(i);
        }
    }
    let mut queue: VecDeque<(bool, u32)> = input
        .conclusion
        .iter()
        .map(|&t| {
            let (polarity, atom) = signed(document, t);
            (!polarity, atom)
        })
        .collect();
    queue.extend(
        clauses
            .iter()
            .flatten()
            .filter(|c| c.len() == 1)
            .flat_map(|c| c.iter().copied()),
    );
    let mut assignment: HashMap<u32, bool> = HashMap::new();
    while let Some((value, atom)) = queue.pop_front() {
        match assignment.get(&atom) {
            Some(&assigned) if assigned != value => return true,
            Some(_) => continue,
            None => assignment.insert(atom, value),
        };
        for &c in used_in.get(&atom).into_iter().flatten() {
            let Some(clause) = &mut clauses[c] else {
                continue;
            };
            if clause.contains(&(value, atom)) {
                clauses[c] = None;
            } else if clause.remove(&(!value, atom)) {
                if clause.is_empty() {
                    return true;
                }
                if clause.len() == 1 {
                    queue.extend(clause.iter().copied());
                }
            }
        }
    }
    false
}

/// A model of the premises that falsifies every conclusion literal, treating
/// `true`/`false` as constants and every other term up to negation as an
/// atom (the consumer's `propositionally_entailed`). Bounded; `false` when
/// none is found within the budget.
fn counter_model(document: &Document, input: &StepInput) -> bool {
    let constant = |(polarity, atom): (bool, u32)| match document.atom_text(atom) {
        Some("true") => Some(polarity),
        Some("false") => Some(!polarity),
        _ => None,
    };
    let mut clauses: Vec<Vec<(bool, u32)>> = Vec::new();
    for premise in &input.premises {
        let mut clause = Vec::new();
        let mut satisfied = false;
        for &term in premise {
            let lit = signed(document, term);
            match constant(lit) {
                Some(true) => satisfied = true,
                Some(false) => {}
                None => clause.push(lit),
            }
        }
        if !satisfied {
            clauses.push(clause);
        }
    }
    for &term in &input.conclusion {
        let (polarity, atom) = signed(document, term);
        match constant((!polarity, atom)) {
            Some(true) => {}
            Some(false) => return false,
            None => clauses.push(vec![(!polarity, atom)]),
        }
    }
    let mut budget = 2_000_000usize;
    satisfiable(&clauses, &mut HashMap::new(), &mut budget) == Some(true)
}

fn satisfiable(
    clauses: &[Vec<(bool, u32)>],
    assignment: &mut HashMap<u32, bool>,
    budget: &mut usize,
) -> Option<bool> {
    let mut trail = Vec::new();
    let result = loop {
        let mut changed = false;
        let mut choice = None;
        let mut all_satisfied = true;
        let mut conflict = false;
        for clause in clauses {
            *budget = budget.checked_sub(clause.len() + 1)?;
            let open: Vec<(bool, u32)> = clause
                .iter()
                .copied()
                .filter(|(_, a)| !assignment.contains_key(a))
                .collect();
            if clause.iter().any(|(p, a)| assignment.get(a) == Some(p)) {
                continue;
            }
            all_satisfied = false;
            match open[..] {
                [] => {
                    conflict = true;
                    break;
                }
                [(polarity, atom)] => {
                    assignment.insert(atom, polarity);
                    trail.push(atom);
                    changed = true;
                }
                [first, ..] => choice = choice.or(Some(first)),
            }
        }
        if conflict {
            break Some(false);
        }
        if all_satisfied {
            break Some(true);
        }
        if changed {
            continue;
        }
        let Some((polarity, atom)) = choice else {
            break Some(false);
        };
        let mut outcome = Some(false);
        for value in [polarity, !polarity] {
            assignment.insert(atom, value);
            match satisfiable(clauses, assignment, budget) {
                Some(false) => {}
                other => {
                    outcome = other;
                    break;
                }
            }
        }
        if outcome != Some(true) {
            assignment.remove(&atom);
        }
        break outcome;
    };
    if result != Some(true) {
        for atom in trail {
            assignment.remove(&atom);
        }
    }
    result
}

/// Carcara's DRUP `rup`: unit propagation over the clauses from the goal's
/// negated literals reaches a conflict; an empty clause is one at once.
fn drup_rup(clauses: &[&Vec<(bool, u32)>], units: Vec<(bool, u32)>) -> bool {
    if clauses.iter().any(|clause| clause.is_empty()) {
        return true;
    }
    let mut value: HashMap<u32, bool> = HashMap::new();
    let mut queue = units;
    loop {
        while let Some((polarity, atom)) = queue.pop() {
            match value.get(&atom) {
                Some(&assigned) if assigned != polarity => return true,
                Some(_) => {}
                None => {
                    value.insert(atom, polarity);
                }
            }
        }
        let mut changed = false;
        for clause in clauses {
            let mut open = None;
            let mut count = 0;
            if clause.iter().any(|(p, a)| value.get(a) == Some(p)) {
                continue;
            }
            for &(p, a) in clause.iter() {
                if !value.contains_key(&a) {
                    count += 1;
                    open = Some((p, a));
                }
            }
            match (count, open) {
                (0, _) => return true,
                (1, Some(unit)) => {
                    queue.push(unit);
                    changed = true;
                }
                _ => {}
            }
        }
        if !changed {
            return false;
        }
    }
}

/// The consumer's `drup` (`check_drup` without RAT): the premises are the
/// clause database, keyed by their literal lists; each `:args` clause must
/// follow by unit propagation and joins it (`(@d (cl …))` removes one); the
/// conclusion must then be one of its clauses, literal for literal.
pub(super) fn drup(document: &mut Document, input: &StepInput) -> Checked {
    let set = |clause: &[u32]| -> Vec<(bool, u32)> {
        let mut literals: Vec<(bool, u32)> = Vec::new();
        for &term in clause {
            let literal = signed(document, term);
            if !literals.contains(&literal) {
                literals.push(literal);
            }
        }
        literals
    };
    let mut database: HashMap<Vec<u32>, Vec<(bool, u32)>> = HashMap::new();
    for premise in &input.premises {
        database.insert(premise.clone(), set(premise));
    }
    for &arg in &input.args {
        if let Some([deleted]) = document.op(arg, "@d").as_deref() {
            if let Some(clause) = document.op(*deleted, "cl") {
                database.remove(&clause);
                continue;
            }
        }
        let Some(lemma) = document.op(arg, "cl") else {
            return refuse("an argument is not a clause");
        };
        let units = lemma
            .iter()
            .map(|&term| {
                let (polarity, atom) = signed(document, term);
                (!polarity, atom)
            })
            .collect();
        let clauses: Vec<&Vec<(bool, u32)>> = database.values().collect();
        require(drup_rup(&clauses, units), || {
            "a lemma does not follow by unit propagation".to_string()
        })?;
        let literals = set(&lemma);
        database.insert(lemma, literals);
    }
    require(database.contains_key(&input.conclusion), || {
        "the conclusion is not one of the clauses".to_string()
    })
}
