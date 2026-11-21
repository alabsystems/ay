// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Borrowed occurrence census before the legacy substitution/emission helpers
//! can clone payload or reserve a work stack. This admits no semantic rule.

use crate::executor::Executor;
use ay_core::term::Constant;
use ay_core::{Sort, Symbol, TermData, TermId};

const OCCURRENCES: usize = 4096;
const DEPTH: usize = 64;
const PAYLOAD: usize = 65_536;

fn text(exec: &Executor, value: &str, payload: &mut usize) -> Option<()> {
    if value.len() > 4096 {
        return None;
    }
    *payload = payload.checked_add(value.len())?;
    (*payload <= PAYLOAD).then_some(())?;
    exec.charge_native_universal(value.len(), value.len())
}

fn sort(exec: &Executor, value: &Sort, depth: usize, payload: &mut usize) -> Option<()> {
    if depth > 32 {
        return None;
    }
    exec.charge_native_universal(1, std::mem::size_of::<Sort>())?;
    match value {
        Sort::Bool | Sort::Int | Sort::Real => Some(()),
        Sort::BitVec(bits) if (1..=4096).contains(&bits.width) => Some(()),
        Sort::Uninterpreted(name) => text(exec, name, payload),
        Sort::Array(array) => {
            sort(exec, &array.index_sort, depth + 1, payload)?;
            sort(exec, &array.element_sort, depth + 1, payload)
        }
        Sort::Seq(element) => sort(exec, element, depth + 1, payload),
        _ => None,
    }
}

pub(super) fn terms(exec: &Executor, roots: &[TermId]) -> Option<()> {
    if roots.len() > OCCURRENCES {
        return None;
    }
    exec.charge_native_universal(roots.len(), roots.len().checked_mul(32)?)?;
    let mut pending: Vec<_> = roots.iter().map(|&r| (r, 0usize)).collect();
    let mut left = OCCURRENCES;
    let mut payload = 0usize;
    while let Some((term, depth)) = pending.pop() {
        left = left.checked_sub(1)?;
        if depth > DEPTH {
            return None;
        }
        exec.charge_native_universal(1, std::mem::size_of::<TermData>())?;
        exec.ctx.terms.entry_stamp(term)?;
        sort(exec, exec.ctx.terms.sort(term), 0, &mut payload)?;
        let mut push = |child: TermId| -> Option<()> {
            if child.0 >= term.0 || pending.len() >= left {
                return None;
            }
            exec.charge_native_universal(1, 32)?;
            pending.push((child, depth + 1));
            Some(())
        };
        match exec.ctx.terms.get(term) {
            TermData::Const(Constant::Bool(_)) => {
                if exec.ctx.terms.sort(term) != &Sort::Bool {
                    return None;
                }
            }
            TermData::Const(Constant::Int(value)) => {
                if exec.ctx.terms.sort(term) != &Sort::Int || value.bits() > 4096 {
                    return None;
                }
                exec.charge_native_universal(value.bits() as usize + 64, 1024)?;
            }
            TermData::Const(Constant::BitVec { value, width }) => {
                if *width == 0
                    || *width > 4096
                    || value.bits() > u64::from(*width)
                    || value.sign() == num_bigint::Sign::Minus
                    || !matches!(exec.ctx.terms.sort(term), Sort::BitVec(bits) if bits.width == *width)
                {
                    return None;
                }
                exec.charge_native_universal(*width as usize + 64, 1024)?;
            }
            TermData::Const(Constant::Rational(value)) => {
                // Raw/checker snapshots need not have normalized Ratio data.
                // Inspect borrowed sign/kind before any legacy constructor or
                // equality/hash path could encounter a zero/negative divisor.
                if exec.ctx.terms.sort(term) != &Sort::Real
                    || value.0.denom().sign() != num_bigint::Sign::Plus
                {
                    return None;
                }
                let bits = value.0.numer().bits().checked_add(value.0.denom().bits())?;
                if bits > 4096 {
                    return None;
                }
                let bits = usize::try_from(bits).ok()?;
                exec.charge_native_universal(
                    bits.checked_mul(bits.checked_add(1)?)?.checked_add(128)?,
                    2048,
                )?;
            }
            TermData::Var(name, _) => text(exec, name, &mut payload)?,
            TermData::Not(inner) => {
                exec.ctx.terms.entry_stamp(*inner)?;
                if exec.ctx.terms.sort(term) != &Sort::Bool
                    || exec.ctx.terms.sort(*inner) != &Sort::Bool
                {
                    return None;
                }
                push(*inner)?;
            }
            TermData::Ite(c, t, e) => {
                for child in [c, t, e] {
                    exec.ctx.terms.entry_stamp(*child)?;
                    sort(exec, exec.ctx.terms.sort(*child), 0, &mut payload)?;
                }
                if exec.ctx.terms.sort(*c) != &Sort::Bool
                    || exec.ctx.terms.sort(*t) != exec.ctx.terms.sort(term)
                    || exec.ctx.terms.sort(*e) != exec.ctx.terms.sort(term)
                {
                    return None;
                }
                push(*c)?;
                push(*t)?;
                push(*e)?;
            }
            TermData::App(symbol, children) => {
                text(exec, symbol.name(), &mut payload)?;
                if let Symbol::Indexed(_, indices) = symbol {
                    if indices.len() > 64 {
                        return None;
                    }
                    exec.charge_native_universal(indices.len(), indices.len().checked_mul(4)?)?;
                }
                if children.len() > 64 || children.len() > left {
                    return None;
                }
                for &child in children {
                    push(child)?;
                }
            }
            TermData::Forall(bindings, body, triggers)
            | TermData::Exists(bindings, body, triggers) => {
                exec.ctx.terms.entry_stamp(*body)?;
                if exec.ctx.terms.sort(term) != &Sort::Bool
                    || exec.ctx.terms.sort(*body) != &Sort::Bool
                {
                    return None;
                }
                if bindings.is_empty() || bindings.len() > 16 || triggers.len() > 64 {
                    return None;
                }
                for (index, (name, ty)) in bindings.iter().enumerate() {
                    text(exec, name, &mut payload)?;
                    sort(exec, ty, 0, &mut payload)?;
                    exec.charge_native_universal(index.checked_mul(name.len() + 1)?, 0)?;
                    if bindings[..index].iter().any(|(other, _)| other == name) {
                        return None;
                    }
                }
                push(*body)?;
                exec.charge_native_universal(triggers.len(), triggers.len().checked_mul(24)?)?;
                for group in triggers {
                    if group.len() > left {
                        return None;
                    }
                    for &child in group {
                        push(child)?;
                    }
                }
            }
            // Let substitution and future payloads need their own admission.
            _ => return None,
        }
    }
    // Legacy structural substitution and tracker helpers use name/hash maps.
    // Prepay their worst-case comparisons/copies on this bounded expanded DAG,
    // rather than treating a hash operation as constant-time authority.
    let count = OCCURRENCES - left;
    let fee = count.checked_mul(count.checked_add(payload)?.checked_add(128)?)?;
    exec.charge_native_universal(
        fee,
        count
            .checked_mul(256)?
            .checked_add(payload.checked_mul(8)?)?,
    )?;
    for &root in roots {
        lexical_types(exec, root, &[], 0)?;
    }
    Some(())
}

fn lexical_types<'a>(
    exec: &'a Executor,
    term: TermId,
    bound: &[(&'a str, &'a Sort)],
    depth: usize,
) -> Option<()> {
    if depth > DEPTH {
        return None;
    }
    exec.charge_native_universal(1, 0)?;
    match exec.ctx.terms.get(term) {
        TermData::Var(name, _) => {
            // The occurrence's annotated sort cannot silently retype a native
            // binder. Name matching here follows the checker's lexical binding
            // semantics, with actual nested shadowing, never a source spelling
            // or global variable-name lookup.
            exec.charge_native_universal(bound.len().checked_mul(name.len().checked_add(1)?)?, 0)?;
            if let Some((_, expected)) = bound.iter().rev().find(|(n, _)| *n == name.as_str()) {
                if exec.ctx.terms.sort(term) != *expected {
                    return None;
                }
            }
        }
        TermData::App(_, args) => {
            for &child in args {
                lexical_types(exec, child, bound, depth + 1)?;
            }
        }
        TermData::Not(child) => lexical_types(exec, *child, bound, depth + 1)?,
        TermData::Ite(c, t, e) => {
            for child in [c, t, e] {
                lexical_types(exec, *child, bound, depth + 1)?;
            }
        }
        TermData::Forall(bindings, body, triggers) | TermData::Exists(bindings, body, triggers) => {
            let len = bound.len().checked_add(bindings.len())?;
            exec.charge_native_universal(
                len,
                len.checked_mul(std::mem::size_of::<(&str, &Sort)>())?,
            )?;
            let mut inner = Vec::with_capacity(len);
            inner.extend_from_slice(bound);
            inner.extend(bindings.iter().map(|(name, sort)| (name.as_str(), sort)));
            lexical_types(exec, *body, &inner, depth + 1)?;
            for group in triggers {
                for &child in group {
                    lexical_types(exec, child, &inner, depth + 1)?;
                }
            }
        }
        TermData::Const(_) => {}
        _ => return None,
    }
    Some(())
}
