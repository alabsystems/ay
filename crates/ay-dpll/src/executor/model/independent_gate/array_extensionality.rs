// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Fail-closed model values for asserted array-equality classes.

use std::collections::HashSet;

use ay_core::term::TermData;
use ay_core::{Sort, TermId};
use ay_model_check::{ArrayValue, EvalOutcome, Evaluator, ModelValue, ModelView};

use super::{eval_value_to_model_value, values_equal, IndependentModelView};

impl IndependentModelView<'_> {
    /// Extensionality-covering shared value for `t`'s asserted-equality class.
    /// Returns `None` when `t` is not in a nontrivial array-`Var==Var` class,
    /// when the class carries an asserted read the model does not pin, or when
    /// any two pinned values disagree (fail closed).
    pub(super) fn array_extensionality_value(
        &self,
        t: TermId,
        index_sort: &Sort,
        element_sort: &Sort,
    ) -> Option<ModelValue> {
        let class = self.array_equality_class(t);
        if class.len() < 2 {
            return None; // not an extensionality case
        }
        if self.model.array_model.as_ref().is_some_and(|arrays| {
            class
                .iter()
                .any(|member| arrays.read_conflicted.contains(member))
        }) {
            return None;
        }
        let adopted = self.adopted_array_class_value(&class, index_sort, element_sort)?;

        // Merge the class's committed reads (fail-closed on a value conflict at
        // one index): (i) the array theory's per-member store entries; (ii)
        // every ASSERTED direct `select` over a class member
        // (#ext-class-read-cover), keyed by its model-evaluated index, with its
        // model-committed value. This enforces the soundness condition that the
        // shared default only sets indices in no committed read.
        let mut store: Vec<(ModelValue, ModelValue)> = Vec::new();
        for &m in &class {
            let Some(am) = self.model.array_model.as_ref() else {
                continue;
            };
            let Some(interp) = am.array_values.get(&m) else {
                continue;
            };
            let mut seen_member_keys: Vec<ModelValue> = Vec::new();
            for (k_s, v_s) in &interp.stores {
                let key = self.parse_leaf(k_s, index_sort)?;
                // Interpretation stores are authoritative/newest first. An
                // older duplicate is shadowed within this member and is not a
                // second committed read (nor a cross-member conflict).
                if seen_member_keys.iter().any(|seen| values_equal(seen, &key)) {
                    continue;
                }
                seen_member_keys.push(key.clone());
                let val = self.parse_leaf(v_s, element_sort)?;
                if let Some((_, prev)) = store.iter().find(|(k, _)| values_equal(k, &key)) {
                    if !values_equal(prev, &val) {
                        return None; // committed read conflict ⇒ fail closed
                    }
                } else {
                    store.push((key, val));
                }
            }
        }
        // Walk the assertions' subterms for direct reads of a member.
        let terms = &self.exec.ctx.terms;
        let mut stack: Vec<TermId> = self.exec.ctx.assertions.to_vec();
        let mut seen: HashSet<TermId> = HashSet::new();
        while let Some(cur) = stack.pop() {
            if !seen.insert(cur) {
                continue;
            }
            match terms.get(cur) {
                TermData::App(sym, args) => {
                    if sym.name() == "select" && args.len() == 2 && class.contains(&args[0]) {
                        let key = match Evaluator::new(&self.exec.ctx.terms, self).evaluate(args[1])
                        {
                            EvalOutcome::Value(value) => value,
                            _ => return None,
                        };
                        let val = self.committed_read_value(cur, element_sort)?;
                        if let Some((_, prev)) = store.iter().find(|(k, _)| values_equal(k, &key)) {
                            if !values_equal(prev, &val) {
                                return None; // committed read conflict ⇒ fail closed
                            }
                        } else {
                            store.push((key, val));
                        }
                    }
                    stack.extend(args.iter().copied());
                }
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(c, a, b) => {
                    stack.push(*c);
                    stack.push(*a);
                    stack.push(*b);
                }
                _ => {}
            }
        }
        // A total adopted entry must agree with every committed read.
        if let Some(ModelValue::Array(base)) = adopted {
            for (k, v) in &store {
                let at = base
                    .store
                    .iter()
                    .rev()
                    .find(|(bk, _)| values_equal(bk, k))
                    .map(|(_, bv)| bv)
                    .unwrap_or(&base.default);
                if !values_equal(at, v) {
                    return None;
                }
            }
            return Some(ModelValue::Array(base));
        }
        let default = self.canonical_model_value(element_sort)?;
        Some(ModelValue::Array(Box::new(ArrayValue { default, store })))
    }

    /// Adopt a complete emitted entry for the asserted-equal class. Two
    /// complete entries that disagree make the model internally inconsistent.
    /// The outer `Option` distinguishes that conflict from no emitted entry.
    fn adopted_array_class_value(
        &self,
        class: &[TermId],
        index_sort: &Sort,
        element_sort: &Sort,
    ) -> Option<Option<ModelValue>> {
        let mut adopted: Option<ModelValue> = None;
        for &member in class {
            if let Some(value) = self.array_from_model(member, index_sort, element_sort) {
                match &adopted {
                    Some(previous) if !values_equal(previous, &value) => return None,
                    Some(_) => {}
                    None => adopted = Some(value),
                }
            }
        }
        Some(adopted)
    }

    /// The model-committed value of one asserted read `sel = (select a i)`
    /// over an extensionality-class member. `None` means the model pins nothing
    /// or two model channels disagree, so the class fails closed.
    fn committed_read_value(&self, sel: TermId, element_sort: &Sort) -> Option<ModelValue> {
        if self.exec.datatype_sort_carries_array_field(element_sort) {
            // The generic whole-term evaluator may fall back to an opaque EUF
            // value. Hazardous datatype cells must instead come from the
            // emitted outer-array interpretation and authenticated inventory.
            return self.array_select_value(sel);
        }
        let structural = {
            let ev = self.exec.evaluate_term(self.model, sel);
            eval_value_to_model_value(&ev, element_sort)
        };
        let opaque = self
            .model
            .euf_model
            .as_ref()
            .and_then(|e| e.term_values.get(&sel))
            .and_then(|s| self.parse_leaf(s, element_sort))
            .or_else(|| match element_sort {
                Sort::Int => self
                    .model
                    .lia_model
                    .as_ref()
                    .and_then(|l| l.values.get(&sel))
                    .map(|v| ModelValue::Int(v.clone())),
                _ => None,
            });
        match (structural, opaque) {
            (Some(a), Some(b)) => values_equal(&a, &b).then_some(a),
            (Some(a), None) => Some(a),
            (None, Some(b)) => Some(b),
            (None, None) => None,
        }
    }

    /// The asserted array-`Var == Var` equality class of `t` (reflexive-
    /// transitive closure), joining only unconditional array-variable edges.
    fn array_equality_class(&self, t: TermId) -> Vec<TermId> {
        let terms = &self.exec.ctx.terms;
        let mut edges: Vec<(TermId, TermId)> = Vec::new();
        let mut stack: Vec<(TermId, u32)> = self
            .exec
            .ctx
            .assertions
            .iter()
            .map(|&a| (a, 32u32))
            .collect();
        while let Some((cand, depth)) = stack.pop() {
            if depth == 0 {
                continue;
            }
            match terms.get(cand) {
                TermData::App(sym, args) if sym.name() == "=" && args.len() == 2 => {
                    let (l, r) = (args[0], args[1]);
                    if l != r
                        && matches!(terms.sort(l), Sort::Array(_))
                        && matches!(terms.get(l), TermData::Var(_, _))
                        && matches!(terms.get(r), TermData::Var(_, _))
                    {
                        edges.push((l, r));
                    }
                }
                TermData::App(sym, args) if sym.name() == "and" => {
                    for &c in args {
                        stack.push((c, depth - 1));
                    }
                }
                _ => {}
            }
        }
        let mut class = vec![t];
        let mut i = 0;
        while i < class.len() {
            let cur = class[i];
            for &(a, b) in &edges {
                let other = if a == cur {
                    Some(b)
                } else if b == cur {
                    Some(a)
                } else {
                    None
                };
                if let Some(o) = other {
                    if !class.contains(&o) {
                        class.push(o);
                    }
                }
            }
            i += 1;
        }
        class
    }
}
