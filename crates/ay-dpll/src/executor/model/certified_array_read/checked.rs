// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

impl<'a> CertifiedArrayRead<'a> {
    pub(super) fn prepare(&mut self, exec: &'a Executor, model: &'a Model) -> bool {
        if !self.live(exec) {
            return false;
        }
        let Some(declarations) = exec.ctx.bounded_projection_declaration_inventory_size() else {
            self.refused = true;
            return false;
        };
        let entries = model.certified_const_interp_entries();
        if !self.charge(exec, declarations) || !self.charge(exec, entries.len()) {
            return false;
        }
        let mut inventory_work = 1usize;
        for (surface, info) in exec.ctx.symbol_iter() {
            let name = exec.ctx.symbol_identity_name(surface, info);
            let cost = surface.len().saturating_add(name.len()).saturating_add(3);
            if !self.charge(exec, cost) {
                return false;
            }
            inventory_work = inventory_work.saturating_add(cost);
            // Signature equality below visits at most each bounded expected
            // descriptor (a different length/constructor fails immediately).
            // Unrelated declaration sorts need no semantic interpretation.
        }
        let package = model.authenticate_const_interp_read(&exec.ctx, |entry| {
            let before = self.remaining;
            if !self.charge(exec, entry.name().map_or(1, str::len))
                || !self.charge(exec, entry.parameter_sorts().len())
                || !self.charge(exec, entry.value_graph_slots().len())
                || !self.same_sort(exec, entry.result_sort(), entry.result_sort())
            {
                return false;
            }
            for sort in entry.parameter_sorts() {
                if !self.same_sort(exec, sort, sort) {
                    return false;
                }
            }
            for &(term, _) in entry.value_graph_slots() {
                if !self.visit(exec, term, 0)
                    || !self.same_sort(exec, exec.ctx.terms.sort(term), exec.ctx.terms.sort(term))
                {
                    return false;
                }
            }
            if let Some(term) = entry.declaration_term() {
                if !self.visit(exec, term, 0)
                    || !self.same_sort(exec, exec.ctx.terms.sort(term), exec.ctx.terms.sort(term))
                {
                    return false;
                }
            }
            // Prepay this entry's established currentness check once: two
            // declaration-inventory walks plus its bounded graph/signatures.
            // The returned immutable borrow retains that result for this read;
            // every later lookup still pays and checks its actual signature.
            let cost = before
                .saturating_sub(self.remaining)
                .saturating_add(inventory_work.saturating_mul(2));
            self.lookup_work = self
                .lookup_work
                .saturating_add(entry.name().map_or(1, str::len).saturating_add(1));
            self.charge(exec, cost)
        });
        let Ok(package) = package else {
            self.refused = true;
            return false;
        };
        self.package = Some(package);
        true
    }

    pub(super) fn same_sort(&mut self, exec: &Executor, left: &Sort, right: &Sort) -> bool {
        let mut pending = vec![(left, right, 0)];
        while let Some((left, right, depth)) = pending.pop() {
            if !self.live(exec) || depth > MAX_READ_DEPTH || self.remaining == 0 {
                exec.record_evaluation_stop(UnknownOrigin::DeterministicResourceBudget);
                self.refused = true;
                return false;
            }
            self.remaining -= 1;
            match (left, right) {
                (Sort::Bool, Sort::Bool)
                | (Sort::Int, Sort::Int)
                | (Sort::Real, Sort::Real)
                | (Sort::String, Sort::String) => {}
                // A constant function does not inspect its arguments. Its
                // exact declaration/signature and scope stamp are checked by
                // the package reader; this bounded shape check must also admit
                // uninterpreted parameter carriers such as a Seq projection.
                (Sort::Uninterpreted(a), Sort::Uninterpreted(b)) => {
                    if a.is_empty() || !self.charge(exec, a.len().saturating_add(b.len())) || a != b
                    {
                        return false;
                    }
                }
                (Sort::BitVec(a), Sort::BitVec(b)) if a.width == b.width && a.width > 0 => {}
                (Sort::Array(a), Sort::Array(b)) => {
                    if !self.charge(exec, 2) {
                        return false;
                    }
                    pending.push((&a.index_sort, &b.index_sort, depth + 1));
                    pending.push((&a.element_sort, &b.element_sort, depth + 1));
                }
                (Sort::Seq(a), Sort::Seq(b)) => {
                    if !self.charge(exec, 1) {
                        return false;
                    }
                    pending.push((a, b, depth + 1));
                }
                _ => return false,
            }
        }
        true
    }

    pub(super) fn closed_value(&mut self, exec: &Executor, root: TermId) -> Option<ModelValue> {
        let mut current = root;
        for depth in 0..=MAX_READ_DEPTH {
            if !self.visit(exec, current, depth)
                || !self.same_sort(
                    exec,
                    exec.ctx.terms.sort(current),
                    exec.ctx.terms.sort(current),
                )
            {
                return None;
            }
            let charge = match exec.ctx.terms.get(current) {
                TermData::App(symbol, args)
                    if symbol.name() == "const-array" && args.len() == 1 =>
                {
                    current = args[0];
                    continue;
                }
                TermData::Const(Constant::Bool(_)) => 1,
                TermData::Const(Constant::BitVec { width, value }) => {
                    if value.sign() == num_bigint::Sign::Minus || value.bits() > u64::from(*width) {
                        return None;
                    }
                    u64::from(*width)
                        .div_ceil(4)
                        .saturating_add(value.bits().div_ceil(8))
                }
                TermData::Const(Constant::Int(value)) => value.bits().saturating_add(1),
                TermData::Const(Constant::Rational(value)) => value
                    .0
                    .numer()
                    .bits()
                    .saturating_add(value.0.denom().bits())
                    .saturating_add(2),
                TermData::Const(Constant::String(value)) => value.len() as u64,
                _ => return None,
            };
            let charge = usize::try_from(charge).ok()?;
            if charge > self.remaining {
                exec.record_evaluation_stop(UnknownOrigin::DeterministicResourceBudget);
                self.refused = true;
                return None;
            }
            self.remaining -= charge;
            let outcome = ay_model_check::evaluate_term(&exec.ctx.terms, &ClosedValue, root);
            return match outcome {
                EvalOutcome::Value(value) if self.live(exec) => Some(value),
                _ => None,
            };
        }
        exec.record_evaluation_stop(UnknownOrigin::DeterministicResourceBudget);
        self.refused = true;
        None
    }
}
