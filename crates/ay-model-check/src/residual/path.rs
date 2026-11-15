// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact selector/index paths, including authenticated read-over-store misses.

use super::*;

mod access;
pub(super) mod metadata;
mod stores;

use access::ReversePath;
pub(super) use stores::{is_store, StoreEdges};

pub(super) struct ParsedRead {
    pub(super) array: TermId,
    pub(super) index: TermId,
    pub(super) slot: Slot,
    pub(super) store_edges: Vec<(TermId, TermId)>,
}

impl Classifier<'_> {
    pub(super) fn parse_free_read(&mut self, term: TermId) -> Option<(TermId, TermId, Slot)> {
        let parsed = self.parse_read_with_stores(term)?;
        Some((parsed.array, parsed.index, parsed.slot))
    }

    pub(super) fn parse_read_with_stores(&mut self, mut term: TermId) -> Option<ParsedRead> {
        let mut path = ReversePath::default();
        let mut misses = stores::Misses::default();
        loop {
            if !self.spend_classify_work(1)
                || path.len().checked_add(misses.len())? > MAX_CLASSIFY_DEPTH
            {
                return None;
            }
            // Symbolic projections take precedence over ordinary named dispatch.
            if self.model.projection_argument(term).ok()?.is_some() {
                return None;
            }
            let TermData::App(symbol, args) = self.terms.get(term) else {
                return None;
            };
            if !self.spend_classify_work(symbol.name().len().div_ceil(64).max(1))
                || self.terms.is_declared_function(symbol.name())
            {
                return None;
            }
            if matches!(symbol, Symbol::Named(name) if name == "select") && args.len() == 2 {
                let (array, index) = (args[0], args[1]);
                let array = misses.peel(self, term, array, index, path.len())?;
                if matches!(self.terms.get(array), TermData::Var(_, _)) {
                    let Sort::Array(sort) = self.free_dt_array_var(array)? else {
                        return None;
                    };
                    for actual in [self.terms.sort(index), self.terms.sort(term)] {
                        if !metadata::sort_work(actual, 0, &mut |n| self.spend_classify_work(n)) {
                            return None;
                        }
                    }
                    if self.terms.sort(index) != &sort.index_sort
                        || self.terms.sort(term) != &sort.element_sort
                    {
                        return None;
                    }
                    return Some(ParsedRead {
                        array,
                        index,
                        slot: path.finish()?,
                        store_edges: misses.into_edges(),
                    });
                }
                if path.len().checked_add(misses.len())? == MAX_CLASSIFY_DEPTH {
                    return None;
                }
                let key = self.inner_index(term, array, index)?;
                path.push_index(key, &mut |n| self.spend_classify_work(n))?;
                term = array;
                continue;
            }
            let (Symbol::Named(name), [argument]) = (symbol, args.as_slice()) else {
                return None;
            };
            if path.len().checked_add(misses.len())? == MAX_CLASSIFY_DEPTH
                || !self.selector_step(term, *argument, name)
            {
                return None;
            }
            path.push_field(name, &mut |n| self.spend_classify_work(n))?;
            term = *argument;
        }
    }

    fn inner_index(&mut self, term: TermId, array: TermId, index: TermId) -> Option<ModelValue> {
        let Sort::Array(sort) = self.terms.sort(array) else {
            return None;
        };
        for actual in [
            self.terms.sort(array),
            self.terms.sort(index),
            self.terms.sort(term),
        ] {
            if !metadata::sort_work(actual, 0, &mut |n| self.spend_classify_work(n)) {
                return None;
            }
        }
        if self.terms.sort(index) != &sort.index_sort || self.terms.sort(term) != &sort.element_sort
        {
            return None;
        }
        self.typed_key(index, &sort.index_sort)
    }

    fn typed_key(&mut self, index: TermId, sort: &Sort) -> Option<ModelValue> {
        let EvalOutcome::Value(key) = self.ev.evaluate(index) else {
            return None;
        };
        // The evaluator owns its acquisition costs. Before this path retains
        // the result or recursively checks it, debit the complete payload.
        let previous_work = self.witness_value_work;
        if !witness::account_path_index(&mut self.witness_value_work, &key) {
            // A census must not mistake exhausted accounting for an ordinary
            // unsupported path and silently omit an uncommitted read site.
            self.spend_classify_work(MAX_CLASSIFY_WORK + 1);
            return None;
        }
        // Failed disjuncts roll back retained entries, not acquisition work.
        if !self.spend_classify_work(self.witness_value_work.checked_sub(previous_work)?) {
            return None;
        }
        self.ev.ensure_value_inhabits_sort(&key, sort).ok()?;
        Some(key)
    }

    fn selector_step(&mut self, term: TermId, argument: TermId, name: &str) -> bool {
        if !self.spend_classify_work(name.len()) || reserved(name) {
            return false;
        }
        let result = self.terms.sort(term);
        let Some(result_dt) =
            metadata::datatype_shape(result, self.resolve, &mut |n| self.spend_classify_work(n))
        else {
            return false;
        };
        if let Some(result_dt) = result_dt {
            if result_dt.constructors.iter().any(|ctor| ctor.name == name) {
                return false; // constructors precede selectors in normal dispatch
            }
        } else if !metadata::sort_work(result, 0, &mut |n| self.spend_classify_work(n)) {
            return false;
        }
        let Some(datatype) =
            metadata::datatype(self.terms.sort(argument), self.resolve, &mut |n| {
                self.spend_classify_work(n)
            })
        else {
            return false;
        };
        if name
            .strip_prefix("is-")
            .is_some_and(|target| datatype.constructors.iter().any(|ctor| ctor.name == target))
        {
            return false;
        }
        let mut fields = datatype
            .constructors
            .iter()
            .flat_map(|ctor| &ctor.fields)
            .filter(|field| field.name == name);
        let Some(field) = fields.next() else {
            return false;
        };
        fields.next().is_none() && &field.sort == result
    }
}

/// Ordinary evaluator dispatch before datatypes. Only fp./seq. claim their
/// entire namespace; an ordinary field named bv_payload or str.custom is valid.
fn reserved(name: &str) -> bool {
    ["fp.", "seq."]
        .iter()
        .any(|prefix| name.starts_with(prefix))
        || crate::strings::handles(name, 1)
        || crate::sets::handles(name, 1)
        || matches!(
            name,
            "and"
                | "or"
                | "=>"
                | "xor"
                | "not"
                | "ite"
                | "if"
                | "="
                | "distinct"
                | "+"
                | "-"
                | "*"
                | "/"
                | "div"
                | "mod"
                | "abs"
                | "to_real"
                | "to_int"
                | "is_int"
                | "<"
                | "<="
                | ">"
                | ">="
                | "select"
                | "store"
                | "const-array"
                | "lambda-array"
                | "default"
                | "concat"
                | "bvadd"
                | "bvsub"
                | "bvmul"
                | "bvudiv"
                | "bvurem"
                | "bvsdiv"
                | "bvsrem"
                | "bvsmod"
                | "bvand"
                | "bvor"
                | "bvxor"
                | "bvnot"
                | "bvnand"
                | "bvnor"
                | "bvxnor"
                | "bvneg"
                | "bvshl"
                | "bvlshr"
                | "bvashr"
                | "bvcomp"
                | "bv2nat"
                | "bvult"
                | "bvule"
                | "bvugt"
                | "bvuge"
                | "bvslt"
                | "bvsle"
                | "bvsgt"
                | "bvsge"
                | "str.++"
                | "str.len"
                | "str.at"
                | "str.in_re"
                | "str.in.re"
                | "str.replace_re"
                | "str.replace_re_all"
        )
}

#[cfg(test)]
mod tests;
