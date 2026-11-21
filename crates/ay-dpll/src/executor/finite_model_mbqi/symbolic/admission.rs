// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use ay_core::{term::Constant, TermStore};
use std::mem::size_of;

pub(super) fn text(value: &str, owner: &SymbolicAdmission) -> Option<String> {
    if value.len() > 256 || !owner.pay(value.len(), value.len().checked_add(size_of::<String>())?) {
        return None;
    }
    let mut output = String::new();
    output.try_reserve_exact(value.len()).ok()?;
    output.push_str(value);
    Some(output)
}

pub(super) fn sort(sort: &Sort, owner: &SymbolicAdmission, depth: usize) -> Option<usize> {
    if depth > 64 || !owner.pay(2, 0) {
        return None;
    }
    let mut cost = size_of::<Sort>();
    match sort {
        Sort::Bool | Sort::Int | Sort::Real => {}
        Sort::Array(array) => {
            cost = cost
                .checked_add(self::sort(&array.index_sort, owner, depth + 1)?)?
                .checked_add(self::sort(&array.element_sort, owner, depth + 1)?)?;
        }
        _ => return None,
    }
    Some(cost)
}

pub(super) fn copy_sort(value: &Sort, owner: &SymbolicAdmission) -> Option<Sort> {
    let cost = sort(value, owner, 0)?;
    owner.pay(cost, cost.checked_mul(2)?).then(|| value.clone())
}

pub(super) fn formal_head(
    terms: &TermStore,
    head: TermId,
    binders: &[(String, Sort)],
    owner: &SymbolicAdmission,
) -> Option<Option<(Symbol, Vec<String>, Vec<Sort>)>> {
    terms.entry_stamp(head)?;
    let TermData::App(Symbol::Named(symbol), args) = terms.get(head) else {
        return Some(None);
    };
    if args.len() != binders.len() || args.is_empty() || args.len() > MAX_TABLE_ROWS {
        return Some(None);
    }
    let mut names: Vec<String> = Vec::new();
    let mut sorts = Vec::new();
    owner.reserve(&mut names, args.len())?;
    owner.reserve(&mut sorts, args.len())?;
    for &argument in args {
        terms.entry_stamp(argument)?;
        let TermData::Var(name, _) = terms.get(argument) else {
            return Some(None);
        };
        if !owner.pay(
            binders
                .len()
                .checked_add(names.len())?
                .checked_mul(name.len().checked_add(256)?)?,
            0,
        ) {
            return None;
        }
        let Some((_, expected)) = binders.iter().find(|(binder, _)| binder == name) else {
            return Some(None);
        };
        let actual_cost = sort(terms.sort(argument), owner, 0)?;
        let expected_cost = sort(expected, owner, 0)?;
        if !owner.pay(actual_cost.checked_add(expected_cost)?, 0)
            || terms.sort(argument) != expected
            || names.contains(name)
        {
            return Some(None);
        }
        names.push(text(name, owner)?);
        sorts.push(copy_sort(expected, owner)?);
    }
    Some(Some((Symbol::named(text(symbol, owner)?), names, sorts)))
}

/// Every physical occurrence, including repeated shared children, is debited.
/// The source grammar deliberately refuses nested binders/lets and unsupported
/// sorts rather than treating unrepresented capture as a free model constant.
pub(super) fn source_body(
    terms: &TermStore,
    root: TermId,
    names: &[String],
    owner: &SymbolicAdmission,
) -> Option<()> {
    walk(terms, root, owner, |term| {
        let TermData::Var(name, _) = terms.get(term) else {
            return Some(());
        };
        owner
            .pay(names.len().checked_mul(name.len().checked_add(256)?)?, 0)
            .then_some(())?;
        names.iter().any(|bound| bound == name).then_some(())
    })
}

pub(super) fn body(
    terms: &TermStore,
    root: TermId,
    parameters: &[TermId],
    owner: &SymbolicAdmission,
) -> Option<()> {
    walk(terms, root, owner, |term| {
        if !matches!(terms.get(term), TermData::Var(..)) {
            return Some(());
        }
        owner.pay(parameters.len(), 0).then_some(())?;
        parameters.contains(&term).then_some(())
    })
}

pub(super) fn walk(
    terms: &TermStore,
    root: TermId,
    owner: &SymbolicAdmission,
    mut variable: impl FnMut(TermId) -> Option<()>,
) -> Option<()> {
    let mut pending = Vec::new();
    owner.reserve(&mut pending, 1)?;
    pending.push((root, 0usize));
    let mut occurrences = 0usize;
    while let Some((term, depth)) = pending.pop() {
        occurrences = occurrences.checked_add(1)?;
        if depth > 64 || occurrences > 4096 || !owner.pay(1, 0) {
            return None;
        }
        terms.entry_stamp(term)?;
        sort(terms.sort(term), owner, 0)?;
        let mut add = |children: &[TermId]| {
            owner.reserve(&mut pending, children.len())?;
            for &child in children {
                terms.entry_stamp(child)?;
                sort(terms.sort(child), owner, 0)?;
                pending.push((child, depth + 1));
            }
            Some(())
        };
        match terms.get(term) {
            TermData::Var(name, _) if name.len() <= 256 => {
                owner.pay(name.len(), 0).then_some(())?;
                variable(term)?;
            }
            TermData::Const(Constant::Bool(_)) if terms.sort(term) == &Sort::Bool => {}
            TermData::Const(Constant::Int(value)) if terms.sort(term) == &Sort::Int => {
                let bits = usize::try_from(value.bits()).ok()?;
                owner.pay(bits.checked_add(1)?, 0).then_some(())?;
            }
            TermData::Const(Constant::Rational(value)) if terms.sort(term) == &Sort::Real => {
                use num_traits::Signed;
                if !value.0.denom().is_positive() {
                    return None;
                }
                let bits =
                    usize::try_from(value.0.numer().bits().checked_add(value.0.denom().bits())?)
                        .ok()?;
                owner.pay(bits.checked_add(1)?, 0).then_some(())?;
            }
            TermData::App(Symbol::Named(name), args) if name.len() <= 256 && args.len() <= 256 => {
                owner
                    .pay(terms.declared_function_lookup_work(name.len())?, 0)
                    .then_some(())?;
                owner
                    .pay(name.len().checked_add(args.len())?, 0)
                    .then_some(())?;
                // Child IDs/sorts are admitted before the local operator's
                // signature checks inspect any child metadata.
                for &child in args {
                    terms.entry_stamp(child)?;
                    sort(terms.sort(child), owner, 0)?;
                }
                operator(terms, term, name, args)?;
                add(args)?;
            }
            TermData::Not(inner) => {
                terms.entry_stamp(*inner)?;
                if terms.sort(term) != &Sort::Bool || terms.sort(*inner) != &Sort::Bool {
                    return None;
                }
                add(std::slice::from_ref(inner))?;
            }
            TermData::Ite(c, t, e) => {
                for &child in [*c, *t, *e].iter() {
                    terms.entry_stamp(child)?;
                    sort(terms.sort(child), owner, 0)?;
                }
                if terms.sort(*c) != &Sort::Bool
                    || terms.sort(*t) != terms.sort(term)
                    || terms.sort(*e) != terms.sort(term)
                {
                    return None;
                }
                add(&[*c, *t, *e])?;
            }
            _ => return None,
        }
    }
    Some(())
}

/// Native operator typing is checked here, separately from structural interning.
/// Unknown ordinary function heads remain dependencies, never native operators.
fn operator(terms: &TermStore, term: TermId, name: &str, args: &[TermId]) -> Option<()> {
    if terms.is_declared_function(name) {
        return Some(());
    }
    let output = terms.sort(term);
    let same = |expected: &Sort| args.iter().all(|&arg| terms.sort(arg) == expected);
    let numeric = matches!(output, Sort::Int | Sort::Real);
    let valid = match name {
        "+" | "*" => numeric && !args.is_empty() && same(output),
        "-" => numeric && !args.is_empty() && same(output),
        "/" => output == &Sort::Real && args.len() == 2 && same(&Sort::Real),
        "div" | "mod" => output == &Sort::Int && args.len() == 2 && same(&Sort::Int),
        "abs" => numeric && args.len() == 1 && same(output),
        "to_int" => output == &Sort::Int && args.len() == 1 && same(&Sort::Real),
        "and" | "or" => output == &Sort::Bool && same(&Sort::Bool),
        "xor" => output == &Sort::Bool && args.len() >= 2 && same(&Sort::Bool),
        "=>" => output == &Sort::Bool && args.len() >= 2 && same(&Sort::Bool),
        "not" => output == &Sort::Bool && args.len() == 1 && same(&Sort::Bool),
        "=" | "distinct" => output == &Sort::Bool && args.len() >= 2 && same(terms.sort(args[0])),
        "<" | "<=" | ">" | ">=" => {
            output == &Sort::Bool
                && args.len() == 2
                && matches!(terms.sort(args[0]), Sort::Int | Sort::Real)
                && same(terms.sort(args[0]))
        }
        "to_real" => {
            !terms.to_real_is_shadowed()
                && output == &Sort::Real
                && args.len() == 1
                && same(&Sort::Int)
        }
        "is_int" => {
            !terms.is_int_is_shadowed()
                && output == &Sort::Bool
                && args.len() == 1
                && same(&Sort::Real)
        }
        "const-array" => {
            matches!(output, Sort::Array(array) if args.len() == 1 && terms.sort(args[0]) == &array.element_sort)
        }
        "select" => {
            args.len() == 2
                && matches!(terms.sort(args[0]), Sort::Array(array)
            if terms.sort(args[1]) == &array.index_sort && output == &array.element_sort)
        }
        "store" => {
            args.len() == 3
                && matches!(terms.sort(args[0]), Sort::Array(array)
            if terms.sort(args[1]) == &array.index_sort && terms.sort(args[2]) == &array.element_sort && output == terms.sort(args[0]))
        }
        // Only an independently source-checked definition may later interpret
        // this head. Readiness/closure rejects every unresolved dependency.
        _ => true,
    };
    valid.then_some(())
}

pub(super) fn render(terms: &TermStore, body: TermId, owner: &SymbolicAdmission) -> Option<String> {
    let mut bytes = 0usize;
    walk(terms, body, owner, |_| Some(()))?;
    let mut pending = Vec::new();
    owner.reserve(&mut pending, 1)?;
    pending.push(body);
    while let Some(term) = pending.pop() {
        let mut extra = 16usize;
        match terms.get(term) {
            TermData::Var(name, _) => extra = extra.checked_add(name.len().checked_mul(2)?)?,
            TermData::Const(Constant::Int(value)) => {
                extra = extra.checked_add(usize::try_from(value.bits()).ok()?.checked_add(1)?)?
            }
            TermData::Const(Constant::Rational(value)) => {
                extra = extra.checked_add(
                    usize::try_from(value.0.numer().bits().checked_add(value.0.denom().bits())?)
                        .ok()?
                        .checked_add(1)?,
                )?
            }
            TermData::App(Symbol::Named(name), args) => {
                extra = extra.checked_add(name.len())?;
                owner.reserve(&mut pending, args.len())?;
                pending.extend_from_slice(args);
            }
            TermData::Not(inner) => {
                owner.reserve(&mut pending, 1)?;
                pending.push(*inner);
            }
            TermData::Ite(c, t, e) => {
                owner.reserve(&mut pending, 3)?;
                pending.extend([*c, *t, *e]);
            }
            _ => {}
        }
        bytes = bytes.checked_add(extra)?;
        owner
            .pay(extra.checked_mul(extra)?, extra.checked_mul(2)?)
            .then_some(())?;
    }
    owner.pay(bytes, bytes.checked_mul(4)?).then_some(())?;
    Some(ay_proof::format_term_alethe(terms, body))
}
