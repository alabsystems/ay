// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Refutation-search advice, NEVER a SAT verdict or proof credential.
//!
//! A free definition x=t with x absent from a total, well-sorted Bool/BV t is
//! satisfiable by assigning x the value of t. This is the conservative
//! definitional-extension/occurs-check argument (SMT-LIB 2.6, §§5.3, 5.4):
//! https://smt-lib.org/papers/smt-lib-reference-v2.6-r2024-09-20.pdf
//! Skip only that singleton search; retain its root in the joint refutation.
//! Unsupported, malformed, cyclic, stopped or unaffordable input keeps the
//! legacy attempt. No model, premise, theorem or publication is produced.

use super::*;
use crate::executor::proof_repair::proof_trust_surgery_surface_audit::ProofSourceWorkEnvelope;
use ay_core::kani_compat::DetHashMap as HashMap;
use ay_frontend::Context;

mod affine_udiv;
#[cfg(test)]
mod tests;
use super::super::bool_bv_typing as typing;

const MAX_NODES: usize = 1 << 16;

/// Continue the same deny-only search while raw interning mutates the context
/// between roots. Retain refusals, not declaration lookup results: a changed
/// declaration universe must be authenticated again. Every probe still debits
/// the caller's original source envelope and polls its original stop closure.
#[derive(Default)]
pub(in crate::executor::proof) struct SingletonSearch {
    refused: bool,
}

impl SingletonSearch {
    pub(in crate::executor::proof) fn may_skip(
        &mut self,
        root: TermId,
        scope: &[TermId],
        ctx: &Context,
        work: &ProofSourceWorkEnvelope,
        stop: &dyn Fn() -> bool,
    ) -> bool {
        if self.refused {
            return false;
        }
        // Pre-arm across arbitrary stop callbacks, including unwinding. No
        // positive result or fresh work allowance survives a refused probe.
        self.refused = true;
        let mut screen = Screen::new(ctx, work, stop);
        let skip = screen.may_skip(root, scope);
        self.refused = screen.refused;
        skip
    }
}

pub(super) fn candidate_selections<'a>(
    roots: &[(TermId, &'a FrontendTerm)],
    scope: &[TermId],
    ctx: &Context,
    work: &ProofSourceWorkEnvelope,
    stop: &dyn Fn() -> bool,
) -> Vec<Vec<(TermId, &'a FrontendTerm)>> {
    let mut screen = Screen::new(ctx, work, stop);
    let mut attempts = Vec::new();
    for &pair in roots {
        if !screen.may_skip(pair.0, scope) {
            attempts.push(vec![pair]);
        }
    }
    if roots.len() > 1 {
        attempts.push(roots.to_vec());
    }
    attempts
}

struct Screen<'a> {
    ctx: &'a Context,
    work: &'a ProofSourceWorkEnvelope,
    stop: &'a dyn Fn() -> bool,
    refused: bool,
    inventory: Option<usize>,
}

impl<'a> Screen<'a> {
    fn new(
        ctx: &'a Context,
        work: &'a ProofSourceWorkEnvelope,
        stop: &'a dyn Fn() -> bool,
    ) -> Self {
        Self {
            ctx,
            work,
            stop,
            refused: false,
            inventory: None,
        }
    }

    fn charge(&mut self, units: usize) -> bool {
        if self.refused || (self.stop)() || !self.work.spend_canonical_scan_work(units) {
            self.refused = true;
            return false;
        }
        true
    }

    fn inventory_size(&mut self) -> Option<usize> {
        if let Some(count) = self.inventory {
            return Some(count);
        }
        let mut count = 0usize;
        let ctx = self.ctx;
        // The borrowed iterator's overload filter hashes names BEFORE yield.
        // Record debits below do not bound that opaque iterator/bucket work;
        // the original deadline/interrupt remains cooperative throughout.
        for (surface, info) in ctx.symbols_iter() {
            let identity = ctx.symbol_identity_name(surface, info);
            if count >= 16_384
                || surface.len() > 256
                || identity.len() > 256
                || !self.charge(
                    1usize
                        .checked_add(surface.len())?
                        .checked_add(identity.len())?,
                )
            {
                return None;
            }
            count = count.checked_add(1)?;
        }
        self.inventory = Some(count);
        Some(count)
    }

    fn free_variable(&mut self, id: TermId) -> Option<&'a str> {
        let ctx = self.ctx;
        ctx.terms.entry_stamp(id)?;
        let TermData::Var(name, _) = ctx.terms.get(id) else {
            return None;
        };
        let inventory = self.inventory_size()?;
        // Price the bounded overload scan and name hashing BEFORE lookup.
        if !self.charge(inventory.checked_add(name.len())?.checked_add(1)?) {
            return None;
        }
        let (declared, sort) = ctx.source_constant_for_value(name)?;
        if declared != id || sort != ctx.terms.sort(id) || typing::scalar(ctx, id).is_none() {
            return None;
        }
        Some(name)
    }

    fn may_skip(&mut self, root: TermId, scope: &[TermId]) -> bool {
        self.probe(root, scope).unwrap_or(false)
    }

    fn probe(&mut self, root: TermId, scope: &[TermId]) -> Option<bool> {
        if !self.charge(scope.len().checked_add(1)?) || !scope.contains(&root) {
            return None;
        }
        let ctx = self.ctx;
        ctx.terms.entry_stamp(root)?;
        let TermData::App(Symbol::Named(name), args) = ctx.terms.get(root) else {
            return None;
        };
        let [left, right] = args.as_slice() else {
            return None;
        };
        if name != "="
            || self.ctx.has_symbol_binding("=")
            || self.ctx.terms.sort(root) != &Sort::Bool
            || typing::scalar(self.ctx, *left)? != typing::scalar(self.ctx, *right)?
        {
            return None;
        }
        let (variable, value) = if matches!(self.ctx.terms.get(*left), TermData::Var(..)) {
            (*left, *right)
        } else if matches!(self.ctx.terms.get(*right), TermData::Var(..)) {
            (*right, *left)
        } else {
            affine_udiv::singleton_witness(self, *left, *right)?;
            return self.charge(1).then_some(true);
        };
        let variable_name = self.free_variable(variable)?;
        self.independent_total_value(value, variable, variable_name)?;
        self.charge(1).then_some(true)
    }

    fn independent_total_value(
        &mut self,
        root: TermId,
        variable: TermId,
        variable_name: &str,
    ) -> Option<()> {
        let ctx = self.ctx;
        let mut pending = Vec::new();
        pending.try_reserve(1).ok()?;
        pending.push((root, false));
        let mut states = HashMap::default();
        while let Some((term, exiting)) = pending.pop() {
            if !self.charge(1) {
                return None;
            }
            ctx.terms.entry_stamp(term)?;
            if exiting {
                states.insert(term, true);
                continue;
            }
            match states.get(&term) {
                Some(true) => continue,
                Some(false) => return None,
                None => {}
            }
            if states.len() >= MAX_NODES || term == variable {
                return None;
            }
            let arity = match ctx.terms.get(term) {
                TermData::App(_, args) => args.len(),
                TermData::Not(_) => 1,
                TermData::Ite(..) => 3,
                TermData::Const(_) | TermData::Var(..) => 0,
                _ => return None,
            };
            if arity > MAX_NODES || !self.charge(arity.checked_add(typing::payload(ctx, term)?)?) {
                return None;
            }
            let children = typing::children(ctx, term)?;
            if let TermData::Var(name, _) = ctx.terms.get(term) {
                if name == variable_name || self.free_variable(term).is_none() {
                    return None;
                }
            }
            let additional = children.len().checked_add(1)?;
            if pending.len().checked_add(additional)? > MAX_NODES {
                return None;
            }
            states.try_reserve(1).ok()?;
            pending.try_reserve(additional).ok()?;
            states.insert(term, false);
            pending.push((term, true));
            children.push_reversed(&mut pending);
        }
        Some(())
    }
}
