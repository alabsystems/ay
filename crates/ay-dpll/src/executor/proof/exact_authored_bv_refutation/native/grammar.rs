// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Positive, metered Bool/BV closure for the native-only early proof route.
//! Free core Vars are UNIVERSALLY quantified leaves keyed by exact TermId,
//! as in the strict lowerer. Their display names grant no declaration, source,
//! assumption or model authority. Only the authenticated public roots may be
//! assumed; proving their negation for every free valuation is sufficient.

use super::*;
use crate::executor::proof::bool_bv_typing as typing;
use ay_core::kani_compat::{DetHashMap, DetHashSet};
use ay_frontend::DeclarationKind;

const MAX_NODES: usize = 1 << 16;
const MAX_EDGES: usize = 1 << 18;
const MAX_BINDINGS: usize = 1 << 14;
const MAX_NAME_BYTES: usize = 256;
const MAX_WIDTH: u32 = 128;

pub(super) fn accepts(executor: &Executor, roots: &[TermId], stop: &dyn Fn() -> bool) -> bool {
    accepts_inner(executor, roots, stop).unwrap_or(false)
}

fn accepts_inner(executor: &Executor, roots: &[TermId], stop: &dyn Fn() -> bool) -> Option<bool> {
    let ctx = &executor.ctx;
    let charge = |amount| !stop() && executor.proof_source_work.spend_canonical_scan_work(amount);
    if roots.is_empty() || roots.len() > 64 || !charge(roots.len()) {
        return None;
    }
    // A public alias must never let a non-theory declaration own a builtin's
    // core spelling. Scan all bindings once, pricing names BEFORE hashing or
    // cloning. A first-hit symbol_info lookup is not an ambiguity check.
    let mut foreign = DetHashSet::default();
    for (index, (surface, info)) in ctx.symbols_iter().enumerate() {
        if index >= MAX_BINDINGS || stop() {
            return None;
        }
        let identity = ctx.symbol_identity_name(surface, info);
        if surface.len() > MAX_NAME_BYTES
            || identity.len() > MAX_NAME_BYTES
            || !charge(surface.len().checked_add(identity.len())?.checked_add(1)?)
        {
            return None;
        }
        if info.declaration_kind() != DeclarationKind::Theory {
            foreign.insert(identity.to_string());
        }
    }
    for &root in roots {
        ctx.terms.entry_stamp(root)?;
        if ctx.terms.sort(root) != &Sort::Bool {
            return None;
        }
    }
    let mut states = DetHashMap::default();
    let mut pending: Vec<_> = roots.iter().rev().map(|&root| (root, false)).collect();
    let mut edges = 0usize;
    let mut mentions_bv = false;
    while let Some((term, exiting)) = pending.pop() {
        if !charge(1) {
            return None;
        }
        if exiting {
            states.insert(term, true);
            continue;
        }
        match states.get(&term) {
            Some(true) => continue,
            Some(false) => return None, // cyclic or forward-forged native DAG
            None => {}
        }
        if states.len() >= MAX_NODES {
            return None;
        }
        ctx.terms.entry_stamp(term)?;
        match typing::scalar(ctx, term)? {
            typing::Scalar::Word(width) if width <= MAX_WIDTH => mentions_bv = true,
            typing::Scalar::Bool => {}
            _ => return None,
        }
        let count = match ctx.terms.get(term) {
            TermData::App(symbol, args) => {
                if symbol.name().len() > MAX_NAME_BYTES
                    || matches!(symbol, Symbol::Indexed(_, indices) if indices.len() > 2)
                {
                    return None;
                }
                args.len()
            }
            TermData::Not(_) => 1,
            TermData::Ite(..) => 3,
            TermData::Const(_) | TermData::Var(..) => 0,
            _ => return None,
        };
        edges = edges.checked_add(count)?;
        if edges > MAX_EDGES
            || !charge(
                count
                    .checked_mul(4)?
                    .checked_add(typing::payload(ctx, term)?.checked_mul(8)?)?,
            )
        {
            return None;
        }
        // The typing helper reads child sorts. Authenticate each handle first
        // so malformed native edges cannot index the store during that gate.
        // Every edge must point backward: a frozen live root cannot retain an
        // unbound future child whose numeric slot could later be populated.
        match ctx.terms.get(term) {
            TermData::App(symbol, args) => {
                for &child in args {
                    if stop() {
                        return None;
                    }
                    if child.index() >= term.index() {
                        return None;
                    }
                    ctx.terms.entry_stamp(child)?;
                }
                let canonical = match symbol {
                    Symbol::Named(name) => ctx.canonical_operator_binding_is_unambiguous(name),
                    // Indexed-only builtins acquire their theory identity from
                    // their shape. The positive typing gate below checks the
                    // exact operator, indices, widths and arity.
                    Symbol::Indexed(..) => true,
                    _ => false,
                };
                if foreign.contains(symbol.name()) || !canonical {
                    return None;
                }
            }
            TermData::Not(child) => {
                if child.index() >= term.index() {
                    return None;
                }
                ctx.terms.entry_stamp(*child)?;
            }
            TermData::Ite(c, t, e) => {
                for child in [*c, *t, *e] {
                    if child.index() >= term.index() {
                        return None;
                    }
                    ctx.terms.entry_stamp(child)?;
                }
            }
            _ => {}
        }
        let children = typing::children(ctx, term)?;
        states.insert(term, false);
        pending.push((term, true));
        children.push_reversed(&mut pending);
    }
    Some(mentions_bv && !stop())
}
