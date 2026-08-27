// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! The INDEPENDENT bounded model the constant-index row-chain tests re-check
//! every ACCEPT with.
//!
//! One universe `0..N` serves as BOTH the index and the element domain, which
//! is what an `(Array Int Int)` needs. It re-derives `select`/`store`/
//! `const-array` from the McCarthy axioms and shares no code with
//! `array_axiom.rs`.

use super::*;

// ===== the INDEPENDENT bounded model =====
//
// One universe `0..N` serves as BOTH the index and the element domain, which is
// what an `(Array Int Int)` needs. An array value is any total function from
// the universe to itself. It re-derives `select`/`store`/`const-array` from the
// McCarthy axioms and shares no code with `array_axiom.rs`.

pub(super) const UNIVERSE: usize = 3;

#[derive(Clone, PartialEq, Eq, Debug)]
pub(super) enum Val {
    Num(usize),
    Arr(Vec<usize>),
}

/// Every ATOM (variable) reachable from `roots`, first-seen order. A constant
/// is deliberately NOT an atom: binding `0` to an arbitrary universe value
/// would let the enumeration "refute" a clause by reinterpreting a numeral.
pub(super) fn atoms(terms: &TermStore, roots: &[TermId]) -> Vec<TermId> {
    let mut seen: Vec<TermId> = Vec::new();
    let mut out: Vec<TermId> = Vec::new();
    let mut stack: Vec<TermId> = roots.to_vec();
    while let Some(term) = stack.pop() {
        if seen.contains(&term) {
            continue;
        }
        seen.push(term);
        match terms.get(term) {
            TermData::App(_, args) => stack.extend(args.iter().copied()),
            TermData::Not(inner) => stack.push(*inner),
            TermData::Const(_) => {}
            _ => out.push(term),
        }
    }
    out
}

pub(super) fn domain(terms: &TermStore, atom: TermId) -> Vec<Val> {
    if matches!(terms.sort(atom), Sort::Array(_)) {
        let mut out = vec![Vec::new()];
        for _ in 0..UNIVERSE {
            let mut next = Vec::new();
            for prefix in &out {
                for cell in 0..UNIVERSE {
                    let mut extended = prefix.clone();
                    extended.push(cell);
                    next.push(extended);
                }
            }
            out = next;
        }
        out.into_iter().map(Val::Arr).collect()
    } else {
        (0..UNIVERSE).map(Val::Num).collect()
    }
}

/// `None` means the model does not interpret the term — a FAILURE to refute,
/// never a proof.
pub(super) fn evaluate(terms: &TermStore, term: TermId, binding: &[(TermId, Val)]) -> Option<Val> {
    if let Some((_, value)) = binding.iter().find(|(id, _)| *id == term) {
        return Some(value.clone());
    }
    match terms.get(term) {
        TermData::Const(Constant::Int(n)) => {
            let n = usize::try_from(i64::try_from(n).ok()?).ok()?;
            (n < UNIVERSE).then_some(Val::Num(n))
        }
        TermData::Const(Constant::Bool(b)) => Some(Val::Num(usize::from(*b))),
        TermData::Not(inner) => match evaluate(terms, *inner, binding)? {
            Val::Num(0) => Some(Val::Num(1)),
            Val::Num(1) => Some(Val::Num(0)),
            _ => None,
        },
        TermData::App(Symbol::Named(name), args) if name == "=" && args.len() == 2 => {
            let left = evaluate(terms, args[0], binding)?;
            let right = evaluate(terms, args[1], binding)?;
            Some(Val::Num(usize::from(left == right)))
        }
        TermData::App(Symbol::Named(name), args) if name == "or" && !args.is_empty() => {
            let mut any = false;
            for &arg in args {
                match evaluate(terms, arg, binding)? {
                    Val::Num(0) => {}
                    Val::Num(1) => any = true,
                    _ => return None,
                }
            }
            Some(Val::Num(usize::from(any)))
        }
        TermData::App(Symbol::Named(name), args) if name == "select" && args.len() == 2 => {
            let Val::Arr(cells) = evaluate(terms, args[0], binding)? else {
                return None;
            };
            let Val::Num(at) = evaluate(terms, args[1], binding)? else {
                return None;
            };
            cells.get(at).copied().map(Val::Num)
        }
        TermData::App(Symbol::Named(name), args) if name == "store" && args.len() == 3 => {
            let Val::Arr(mut cells) = evaluate(terms, args[0], binding)? else {
                return None;
            };
            let Val::Num(at) = evaluate(terms, args[1], binding)? else {
                return None;
            };
            let Val::Num(value) = evaluate(terms, args[2], binding)? else {
                return None;
            };
            *cells.get_mut(at)? = value;
            Some(Val::Arr(cells))
        }
        TermData::App(Symbol::Named(name), args) if name == "const-array" && args.len() == 1 => {
            let Val::Num(fill) = evaluate(terms, args[0], binding)? else {
                return None;
            };
            Some(Val::Arr(vec![fill; UNIVERSE]))
        }
        _ => None,
    }
}

pub(super) fn holds(terms: &TermStore, literal: TermId, binding: &[(TermId, Val)]) -> Option<bool> {
    match evaluate(terms, literal, binding)? {
        Val::Num(0) => Some(false),
        Val::Num(1) => Some(true),
        _ => None,
    }
}

/// An assignment falsifying EVERY literal, or `None` when none exists.
pub(super) fn falsify(terms: &TermStore, literals: &[TermId]) -> Option<Vec<(TermId, Val)>> {
    let variables = atoms(terms, literals);
    let domains: Vec<Vec<Val>> = variables.iter().map(|&v| domain(terms, v)).collect();
    let mut cursor = vec![0usize; variables.len()];
    loop {
        let binding: Vec<(TermId, Val)> = variables
            .iter()
            .enumerate()
            .map(|(slot, &variable)| (variable, domains[slot][cursor[slot]].clone()))
            .collect();
        if literals
            .iter()
            .all(|&lit| holds(terms, lit, &binding) == Some(false))
        {
            return Some(binding);
        }
        let mut slot = 0;
        loop {
            if slot == cursor.len() {
                return None;
            }
            cursor[slot] += 1;
            if cursor[slot] < domains[slot].len() {
                break;
            }
            cursor[slot] = 0;
            slot += 1;
        }
    }
}

/// Whether the model can DECIDE every literal. `falsify` returning `None` means
/// both "valid" and "not understood", and those are not the same answer.
pub(super) fn decidable(terms: &TermStore, literals: &[TermId]) -> bool {
    let variables = atoms(terms, literals);
    let binding: Vec<(TermId, Val)> = variables
        .iter()
        .map(|&v| (v, domain(terms, v)[0].clone()))
        .collect();
    literals
        .iter()
        .all(|&lit| holds(terms, lit, &binding).is_some())
}
