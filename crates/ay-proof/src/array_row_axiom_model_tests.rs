// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The INDEPENDENT array-model evaluator the read-over-write tests re-check
//! every ACCEPT with, and the fixture helpers both test files share.
//!
//! It shares NO code with `array_row_axiom.rs`: it re-derives the McCarthy
//! semantics from the term structure and enumerates every assignment over a
//! bounded index/element alphabet.
//! `congruence_derivation_sweep_tests::falsifies` cannot serve here — it treats
//! `select`/`store` as UNINTERPRETED functions, under which the read-over-write
//! axiom is not valid at all — so the array half of this campaign needs its own
//! evaluator, and this is it.

use crate::quality::check_proof_strict;
use ay_core::{
    AletheRule, ArraySort, Proof, ProofId, ProofStep, Sort, Symbol, TermData, TermId, TermStore,
    TheoryLemmaKind,
};

// ===== fixture helpers =====

pub(crate) fn index_sort() -> Sort {
    Sort::Uninterpreted("Index".to_string())
}

pub(crate) fn element_sort() -> Sort {
    Sort::Uninterpreted("Element".to_string())
}

pub(crate) fn array_sort() -> Sort {
    Sort::Array(Box::new(ArraySort::new(index_sort(), element_sort())))
}

pub(crate) fn array(terms: &mut TermStore, name: &str) -> TermId {
    terms.mk_var(name, array_sort())
}

pub(crate) fn index(terms: &mut TermStore, name: &str) -> TermId {
    terms.mk_var(name, index_sort())
}

pub(crate) fn element(terms: &mut TermStore, name: &str) -> TermId {
    terms.mk_var(name, element_sort())
}

/// A RAW `(store a i v)`, so a fixture controls the exact term.
pub(crate) fn store(terms: &mut TermStore, base: TermId, at: TermId, value: TermId) -> TermId {
    terms.mk_app(Symbol::named("store"), vec![base, at, value], array_sort())
}

/// A RAW `(select a i)`: `mk_select` FOLDS the read-over-write this file is
/// about, so the fixtures cannot use it either.
pub(crate) fn select(terms: &mut TermStore, base: TermId, at: TermId) -> TermId {
    terms.mk_app(Symbol::named("select"), vec![base, at], element_sort())
}

pub(crate) fn eq(terms: &mut TermStore, lhs: TermId, rhs: TermId) -> TermId {
    terms.mk_app(Symbol::named("="), vec![lhs, rhs], Sort::Bool)
}

// ===== the INDEPENDENT array-model evaluator =====

/// A value in the bounded model: an index, an element, or a total array.
#[derive(Clone, PartialEq, Eq, Debug)]
pub(crate) enum Value {
    Index(usize),
    Element(usize),
    Array(Vec<usize>),
}

/// The bounded alphabet: `indices` index values and `elements` element values.
/// An array value is any total function from the index universe to the element
/// universe, i.e. any `indices`-long vector over `0..elements`.
pub(crate) struct Alphabet {
    pub(crate) indices: usize,
    pub(crate) elements: usize,
}

impl Alphabet {
    /// How many values the ELEMENT universe of `sort` has. `Bool` is exactly
    /// two — `0 = false`, `1 = true` — and is never widened by `elements`, so an
    /// `(Array _ Bool)` cell can never hold a value that is neither Boolean
    /// constant. Widening it would let the enumeration report a "countermodel"
    /// in which a Bool cell is neither true nor false, which refutes nothing.
    fn element_universe(&self, sort: &Sort) -> usize {
        if matches!(sort, Sort::Bool) {
            2
        } else {
            self.elements
        }
    }

    fn values_for(&self, sort: &Sort) -> Vec<Value> {
        match sort {
            Sort::Array(array) => {
                let cells = self.element_universe(&array.element_sort);
                let mut out = vec![Vec::new()];
                for _ in 0..self.indices {
                    let mut next = Vec::new();
                    for prefix in &out {
                        for element in 0..cells {
                            let mut extended = prefix.clone();
                            extended.push(element);
                            next.push(extended);
                        }
                    }
                    out = next;
                }
                out.into_iter().map(Value::Array).collect()
            }
            sort if *sort == index_sort() => (0..self.indices).map(Value::Index).collect(),
            // `Bool` is BOTH a formula sort and (for an `(Array _ Bool)`) an
            // element sort, so it is represented as an `Element` over the fixed
            // two-value universe. That is what lets one array cell and one
            // Boolean literal share a representation.
            sort => (0..self.element_universe(sort))
                .map(Value::Element)
                .collect(),
        }
    }
}

/// Every ATOMIC sub-term (anything that is not an application, a negation, an
/// `ite` or an interpreted constant) reachable from `roots`, in a deterministic
/// first-seen order.
///
/// A `Const` is deliberately NOT an atom: binding `true`/`false` to an arbitrary
/// universe value would let the enumeration "falsify" a clause by reinterpreting
/// the constant, which is a countermodel to nothing. [`evaluate`] gives every
/// constant it understands its own fixed value instead, and returns `None` — a
/// FAILURE to refute — for every constant it does not.
fn atoms(terms: &TermStore, roots: &[TermId]) -> Vec<TermId> {
    let mut seen: Vec<TermId> = Vec::new();
    let mut out: Vec<TermId> = Vec::new();
    let mut stack: Vec<TermId> = roots.iter().rev().copied().collect();
    while let Some(term) = stack.pop() {
        if seen.contains(&term) {
            continue;
        }
        seen.push(term);
        match terms.get(term) {
            TermData::App(_, args) => {
                let args = args.clone();
                for arg in args.into_iter().rev() {
                    stack.push(arg);
                }
            }
            TermData::Not(inner) => stack.push(*inner),
            TermData::Ite(cond, then_branch, else_branch) => {
                stack.push(*else_branch);
                stack.push(*then_branch);
                stack.push(*cond);
            }
            TermData::Const(_) => {}
            _ => out.push(term),
        }
    }
    out
}

/// Evaluate `term` under `binding`, or `None` when the term uses an operator
/// this model does not interpret (which is a FAILURE to refute, never a proof).
///
/// The McCarthy semantics are re-derived from the term structure here and
/// nowhere else: `select` is application, `store` is point-update,
/// `const-array` is the constant function over the whole index universe, `ite`
/// picks a branch, `=` is value identity and `not` is complement. It shares no
/// code with any validator, minter or recognizer.
fn evaluate(
    terms: &TermStore,
    term: TermId,
    binding: &[(TermId, Value)],
    alphabet: &Alphabet,
) -> Option<Value> {
    if let Some((_, value)) = binding.iter().find(|(id, _)| *id == term) {
        return Some(value.clone());
    }
    match terms.get(term) {
        // `0 = false`, `1 = true`: the same representation an `(Array _ Bool)`
        // cell uses, so a Boolean read and a Boolean literal compare directly.
        TermData::Const(ay_core::Constant::Bool(value)) => {
            Some(Value::Element(usize::from(*value)))
        }
        TermData::Not(inner) => match evaluate(terms, *inner, binding, alphabet)? {
            Value::Element(0) => Some(Value::Element(1)),
            Value::Element(1) => Some(Value::Element(0)),
            _ => None,
        },
        TermData::Ite(cond, then_branch, else_branch) => {
            let branch = match evaluate(terms, *cond, binding, alphabet)? {
                Value::Element(1) => *then_branch,
                Value::Element(0) => *else_branch,
                _ => return None,
            };
            evaluate(terms, branch, binding, alphabet)
        }
        TermData::App(Symbol::Named(name), args) if name == "=" && args.len() == 2 => {
            let left = evaluate(terms, args[0], binding, alphabet)?;
            let right = evaluate(terms, args[1], binding, alphabet)?;
            Some(Value::Element(usize::from(left == right)))
        }
        TermData::App(Symbol::Named(name), args) if name == "or" && !args.is_empty() => {
            let mut any = false;
            for &arg in args {
                match evaluate(terms, arg, binding, alphabet)? {
                    Value::Element(1) => any = true,
                    Value::Element(0) => {}
                    _ => return None,
                }
            }
            Some(Value::Element(usize::from(any)))
        }
        TermData::App(Symbol::Named(name), args) if name == "and" && !args.is_empty() => {
            let mut all = true;
            for &arg in args {
                match evaluate(terms, arg, binding, alphabet)? {
                    Value::Element(1) => {}
                    Value::Element(0) => all = false,
                    _ => return None,
                }
            }
            Some(Value::Element(usize::from(all)))
        }
        TermData::App(Symbol::Named(name), args) if name == "select" && args.len() == 2 => {
            let Value::Array(cells) = evaluate(terms, args[0], binding, alphabet)? else {
                return None;
            };
            let Value::Index(at) = evaluate(terms, args[1], binding, alphabet)? else {
                return None;
            };
            cells.get(at).copied().map(Value::Element)
        }
        TermData::App(Symbol::Named(name), args) if name == "store" && args.len() == 3 => {
            let Value::Array(mut cells) = evaluate(terms, args[0], binding, alphabet)? else {
                return None;
            };
            let Value::Index(at) = evaluate(terms, args[1], binding, alphabet)? else {
                return None;
            };
            let Value::Element(value) = evaluate(terms, args[2], binding, alphabet)? else {
                return None;
            };
            *cells.get_mut(at)? = value;
            Some(Value::Array(cells))
        }
        TermData::App(Symbol::Named(name), args) if name == "const-array" && args.len() == 1 => {
            let Value::Element(fill) = evaluate(terms, args[0], binding, alphabet)? else {
                return None;
            };
            Some(Value::Array(vec![fill; alphabet.indices]))
        }
        _ => None,
    }
}

/// Whether the literal HOLDS under `binding`. `None` when the model cannot
/// decide it.
pub(crate) fn holds(
    terms: &TermStore,
    literal: TermId,
    binding: &[(TermId, Value)],
    alphabet: &Alphabet,
) -> Option<bool> {
    match evaluate(terms, literal, binding, alphabet)? {
        Value::Element(0) => Some(false),
        Value::Element(1) => Some(true),
        _ => None,
    }
}

/// An assignment over `alphabet` that falsifies EVERY literal of `clause`, or
/// `None` when the exhaustive enumeration finds none.
///
/// Shares no code with `array_row_axiom.rs`: it re-derives the McCarthy
/// semantics from the term structure directly.
pub(crate) fn falsify(
    terms: &TermStore,
    clause: &[TermId],
    alphabet: &Alphabet,
) -> Option<Vec<(TermId, Value)>> {
    let variables = atoms(terms, clause);
    let domains: Vec<Vec<Value>> = variables
        .iter()
        .map(|&variable| alphabet.values_for(terms.sort(variable)))
        .collect();
    let mut cursor = vec![0usize; variables.len()];
    loop {
        let binding: Vec<(TermId, Value)> = variables
            .iter()
            .zip(cursor.iter())
            .map(|(&variable, &choice)| {
                (
                    variable,
                    domains[variables
                        .iter()
                        .position(|&v| v == variable)
                        .expect("present")][choice]
                        .clone(),
                )
            })
            .collect();
        if clause
            .iter()
            .all(|&literal| holds(terms, literal, &binding, alphabet) == Some(false))
        {
            return Some(binding);
        }
        let mut position = 0;
        loop {
            if position == cursor.len() {
                return None;
            }
            cursor[position] += 1;
            if cursor[position] < domains[position].len() {
                break;
            }
            cursor[position] = 0;
            position += 1;
        }
    }
}

/// The default sweep box: two indices and two elements, i.e. four array values.
pub(crate) fn small() -> Alphabet {
    Alphabet {
        indices: 2,
        elements: 2,
    }
}

/// Whether the model can DECIDE every literal of `clause`.
///
/// [`falsify`] reports "no countermodel" both when the clause is valid and when
/// the model cannot interpret it, and those two are not the same answer. Every
/// caller that reads a `None` as EVIDENCE must assert this first, or a term the
/// evaluator silently does not understand would read as a clean bill of health.
pub(crate) fn decidable(terms: &TermStore, clause: &[TermId], alphabet: &Alphabet) -> bool {
    let variables = atoms(terms, clause);
    let binding: Vec<(TermId, Value)> = variables
        .iter()
        .map(|&variable| {
            (
                variable,
                alphabet.values_for(terms.sort(variable))[0].clone(),
            )
        })
        .collect();
    clause
        .iter()
        .all(|&literal| holds(terms, literal, &binding, alphabet).is_some())
}

/// The UNTOUCHED strict checker, on the axiom instance closed into a
/// self-contained refutation — exactly what the lane's Guard 7 runs.
pub(crate) fn strict_checks(terms: &mut TermStore, equality: TermId) -> bool {
    let negated = terms.mk_not(equality);
    let mut proof = Proof::new();
    proof.steps.push(ProofStep::TheoryLemma {
        theory: "ArrayEUF".to_string(),
        clause: vec![equality],
        farkas: None,
        kind: TheoryLemmaKind::ArraySelectStore { index_eq: true },
        lia: None,
    });
    proof.steps.push(ProofStep::Assume(negated));
    proof.steps.push(ProofStep::Step {
        rule: AletheRule::Resolution,
        clause: Vec::new(),
        premises: vec![ProofId(0), ProofId(1)],
        args: Vec::new(),
    });
    check_proof_strict(&proof, terms).is_ok()
}

/// Every layer of the bar at once, for one minted instance.
pub(crate) fn accept(terms: &mut TermStore, store_term: TermId) -> TermId {
    let equality =
        super::mint_row1_axiom(terms, store_term).expect("this store must yield an instance");
    assert!(
        decidable(terms, &[equality], &small()),
        "the array model could not interpret the instance, so its silence is not evidence"
    );
    assert!(
        falsify(terms, &[equality], &small()).is_none(),
        "the INDEPENDENT array model falsified an ACCEPTED read-over-write instance"
    );
    assert!(
        strict_checks(terms, equality),
        "the untouched strict checker refused an ACCEPTED instance"
    );
    assert_eq!(
        crate::recognize_array_select_store(terms, &[equality]),
        Some(true),
        "an accepted instance must be the index-EQUAL schema"
    );
    equality
}
