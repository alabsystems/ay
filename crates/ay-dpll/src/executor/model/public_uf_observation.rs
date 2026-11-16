// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Bounded, read-only observations of ALREADY-computed public UF decisions.
//! No value is evaluated, cloned or compared here. Complex values are omitted.

use std::fmt;

use crate::executor::Executor;
use ay_core::{Sort, Symbol, TermData, TermId};
use ay_model_check::ModelValue;

struct Text<'a>(&'a str);
impl fmt::Debug for Text<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // At most 96 BYTES, on a UTF-8 boundary, before Debug can escape it.
        let mut end = self.0.len().min(96);
        while !self.0.is_char_boundary(end) {
            end -= 1;
        }
        f.debug_struct("text")
            .field("bytes", &self.0.len())
            .field("prefix", &&self.0[..end])
            .field("truncated", &(end < self.0.len()))
            .finish()
    }
}
struct SortTag<'a>(Option<&'a Sort>);
impl fmt::Debug for SortTag<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.0 {
            Some(Sort::Bool) => f.write_str("Bool"),
            Some(Sort::Int) => f.write_str("Int"),
            Some(Sort::Uninterpreted(name)) => f.debug_tuple("carrier").field(&Text(name)).finish(),
            _ => f.write_str("omitted-sort"),
        }
    }
}
struct Value<'a> {
    value: Option<&'a ModelValue>,
    sort: Option<&'a Sort>,
}
impl fmt::Debug for Value<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match (self.value, self.sort) {
            (None, _) => f.write_str("absent"),
            (Some(ModelValue::Bool(value)), Some(Sort::Bool)) => {
                f.debug_tuple("Bool").field(value).finish()
            }
            (Some(ModelValue::Int(value)), Some(Sort::Int)) if value.bits() <= 128 => {
                f.debug_tuple("Int").field(value).finish()
            }
            (Some(ModelValue::Int(value)), Some(Sort::Int)) => f
                .debug_tuple("omitted-Int-bits")
                .field(&value.bits())
                .finish(),
            (Some(ModelValue::Uninterpreted(value)), Some(Sort::Uninterpreted(name))) => f
                .debug_struct("carrier")
                .field("sort", &Text(name))
                .field("token", &Text(value))
                .finish(),
            _ => f.write_str("omitted-complex-or-sort-mismatch"),
        }
    }
}
struct Head<'a>(&'a Symbol);
impl fmt::Debug for Head<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.0 {
            Symbol::Named(name) => f.debug_tuple("Named").field(&Text(name)).finish(),
            Symbol::Indexed(name, indices) => f
                .debug_struct("Indexed")
                .field("name", &Text(name))
                .field("indices", &&indices[..indices.len().min(8)])
                .field("indices_len", &indices.len())
                .field("truncated", &(indices.len() > 8))
                .finish(),
            _ => f.write_str("omitted-symbol"),
        }
    }
}
struct Argument<'a> {
    term: TermId,
    sort: Option<&'a Sort>,
    value: Option<&'a ModelValue>,
}
impl fmt::Debug for Argument<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("arg")
            .field("term", &self.term)
            .field("sort", &SortTag(self.sort))
            .field(
                "value",
                &Value {
                    value: self.value,
                    sort: self.sort,
                },
            )
            .finish()
    }
}
struct Arguments<'a> {
    exec: &'a Executor,
    terms: &'a [TermId],
    values: &'a [ModelValue],
}
impl fmt::Debug for Arguments<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut out = f.debug_list();
        for (index, &term) in self.terms.iter().take(8).enumerate() {
            let sort = if term.index() < self.exec.ctx.terms.len() {
                Some(self.exec.ctx.terms.sort(term))
            } else {
                None
            };
            out.entry(&Argument {
                term,
                sort,
                value: self.values.get(index),
            });
        }
        out.finish()
    }
}

impl Executor {
    pub(in crate::executor) fn observe_public_uf_read(
        &self,
        term: TermId,
        arguments: &[ModelValue],
        pin: Option<&ModelValue>,
        printed: &ModelValue,
        decision: &'static str,
        printed_arity: usize,
        printed_rows: usize,
    ) {
        if !ay_core::misc_cli_flags().model_reject_dump || term.index() >= self.ctx.terms.len() {
            return;
        }
        let TermData::App(symbol, native_args) = self.ctx.terms.get(term) else {
            return;
        };
        let sort = self.ctx.terms.sort(term);
        // Equal reads never call us. Missing-pin observations are limited to
        // scalar results, avoiding unrelated carrier reads before a divergence.
        if decision == "printed-without-pin" && !matches!(sort, Sort::Bool | Sort::Int) {
            return;
        }
        let Some((ticket, epoch)) = self.reserve_model_recovery_trace() else {
            return;
        };
        // Prefixes and bounded BigInt decimal formatting start AFTER reservation.
        // Both branches select `printed`; no extra lookup/comparison occurs.
        ay_core::safe_eprintln!(
            "[ay-public-uf] seq={} executor={:p} epoch=0x{:x} decision={} term={:?} symbol={:?} arity={} argument_values={} arguments_truncated={} arguments={:?} result_sort={:?} pin={:?} printed={:?} selected={:?} printed_arity={} printed_rows={}",
            ticket, std::ptr::from_ref(self), epoch, decision, term, Head(symbol), native_args.len(), arguments.len(), native_args.len() > 8 || arguments.len() > 8,
            Arguments { exec: self, terms: native_args, values: arguments }, SortTag(Some(sort)),
            Value { value: pin, sort: Some(sort) }, Value { value: Some(printed), sort: Some(sort) },
            Value { value: Some(printed), sort: Some(sort) }, printed_arity, printed_rows,
        );
    }

    pub(in crate::executor) fn observe_removed_uf_rows(
        &self,
        name: &str,
        before: usize,
        after: usize,
        first_removed: Option<TermId>,
        first_kept: Option<TermId>,
        reachable: usize,
        root_entries: usize,
    ) {
        if !ay_core::misc_cli_flags().model_reject_dump || first_removed.is_none() {
            return;
        }
        let Some((ticket, epoch)) = self.reserve_model_recovery_trace() else {
            return;
        };
        // Lengths only: no additional root walk or source-membership query.
        let assertions = self.ctx.assertions.len();
        let assumptions = self.last_assumptions.as_ref().map_or(0, Vec::len);
        let kernel = self.function_row_roots.len();
        ay_core::safe_eprintln!(
            "[ay-public-uf-rows] seq={} executor={:p} epoch=0x{:x} symbol={:?} before={} after={} first_removed={:?} first_kept={:?} root_entries={} working_root_list_counts={:?} reachable={}",
            ticket, std::ptr::from_ref(self), epoch, Text(name), before, after, first_removed, first_kept,
            root_entries, (assertions, assumptions, kernel), reachable,
        );
    }
}
