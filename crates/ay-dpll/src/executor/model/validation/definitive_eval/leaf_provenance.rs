// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Read-only provenance for leaves the strict oracle has ALREADY enumerated.
//! No evaluator, term traversal, model mutation or decision reads this output.

use std::fmt;
use std::sync::atomic::{AtomicUsize, Ordering};

use super::{Constant, Executor, Model, Sort, TermData, TermId};
use num_bigint::BigInt;

const LEAF_LIMIT: usize = 32;
const ROW_LIMIT: usize = 8;
const ARG_LIMIT: usize = 8;
const TEXT_CHARS: usize = 128;
const INTEGER_BITS: u64 = 256;
const SYMBOL_BYTES: usize = 256;
static LEAF_RECORDS: AtomicUsize = AtomicUsize::new(0);

struct Text<'a>(&'a str);

impl fmt::Debug for Text<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let end = self
            .0
            .char_indices()
            .nth(TEXT_CHARS)
            .map_or(self.0.len(), |(i, _)| i);
        f.debug_struct("text")
            .field("bytes", &self.0.len())
            .field("prefix", &&self.0[..end])
            .field("truncated", &(end != self.0.len()))
            .finish()
    }
}

struct Integer<'a>(&'a BigInt);

impl fmt::Debug for Integer<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let bits = self.0.bits();
        if bits <= INTEGER_BITS {
            write!(f, "{}", self.0)
        } else {
            write!(f, "<integer omitted: {bits} bits>")
        }
    }
}

struct Atoms<'a>(&'a [String]);

impl fmt::Debug for Atoms<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut list = f.debug_list();
        for atom in self.0.iter().take(ARG_LIMIT) {
            list.entry(&Text(atom));
        }
        list.finish()
    }
}

/// Exact raw map lookups at one already-known id. Describing native metadata
/// reads only this node; pin metadata is inspected once, never evaluated.
struct Point<'a> {
    executor: &'a Executor,
    model: &'a Model,
    term: TermId,
}

impl fmt::Debug for Point<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let terms = &self.executor.ctx.terms;
        let mut out = f.debug_struct("point");
        out.field("term", &self.term);
        if self.term.0 as usize >= terms.len() {
            return out.field("invalid_id", &true).finish();
        }
        let sort = terms.sort(self.term);
        let native = terms.get(self.term);
        out.field("sort_tag", &std::mem::discriminant(sort));
        let named_sort = match sort {
            Sort::Uninterpreted(name) => Some(Text(name)),
            _ => None,
        };
        out.field("named_sort", &named_sort);
        out.field("native_tag", &std::mem::discriminant(native));
        match native {
            TermData::Var(name, _) => {
                out.field("variable", &Text(name));
            }
            TermData::Const(Constant::Int(value)) => {
                out.field("literal_int", &Integer(value));
            }
            TermData::App(symbol, args) => {
                out.field("symbol", &Text(symbol.name()));
                out.field("arity", &args.len());
                out.field("argument_ids", &&args[..args.len().min(ARG_LIMIT)]);
                out.field("arguments_truncated", &(args.len() > ARG_LIMIT));
            }
            _ => {}
        }
        out.field(
            "lia",
            &self
                .model
                .lia_model
                .as_ref()
                .and_then(|model| model.values.get(&self.term))
                .map(Integer),
        );
        let euf = self.model.euf_model.as_ref();
        out.field(
            "euf_numeric",
            &euf.and_then(|model| model.int_values.get(&self.term))
                .map(Integer),
        );
        out.field(
            "euf_formatted",
            &euf.and_then(|model| model.term_values.get(&self.term))
                .map(|s| Text(s)),
        );
        out.field(
            "speculative",
            &euf.is_some_and(|model| model.speculative_int_terms.contains(&self.term)),
        );
        let pin = euf
            .and_then(|model| model.func_app_const_terms.get(&self.term))
            .copied();
        out.field("pin_id", &pin);
        let pin_literal = pin
            .filter(|term| (term.0 as usize) < terms.len())
            .and_then(|term| match terms.get(term) {
                TermData::Const(Constant::Int(value)) => Some(Integer(value)),
                _ => None,
            });
        out.field("pin_literal_int", &pin_literal);
        let sat_var = self.model.term_to_var.get(&self.term).copied();
        out.field("sat_var", &sat_var);
        out.field(
            "sat_assignment",
            &sat_var.and_then(|v| self.model.sat_model.get(v as usize).copied()),
        );
        out.finish()
    }
}

pub(super) fn observe(executor: &Executor, model: &Model, leaf: TermId) {
    if !ay_core::misc_cli_flags().debug_strict_oracle {
        return;
    }
    let ticket = match LEAF_RECORDS.fetch_update(Ordering::Relaxed, Ordering::Relaxed, |count| {
        if count <= LEAF_LIMIT {
            Some(count + 1)
        } else {
            None
        }
    }) {
        Ok(ticket) => ticket,
        Err(_) => return,
    };
    if ticket == LEAF_LIMIT {
        ay_core::safe_eprintln!(
            "[ite-uf-provenance] leaf-cap={} reached; further provenance omitted",
            LEAF_LIMIT
        );
        return;
    }
    ay_core::safe_eprintln!(
        "[ite-uf-provenance] seq={} executor={:p} epoch=0x{:x} leaf={:?}",
        ticket,
        executor as *const Executor,
        executor.query_authority_epoch.diagnostic_address(),
        Point {
            executor,
            model,
            term: leaf
        },
    );
    let terms = &executor.ctx.terms;
    if leaf.0 as usize >= terms.len() {
        return;
    }
    let TermData::App(symbol, _) = terms.get(leaf) else {
        return;
    };
    // Bound name hashing before table lookup, as well as printed text.
    if symbol.name().len() > SYMBOL_BYTES {
        ay_core::safe_eprintln!(
            "[ite-uf-provenance] seq={} rows-omitted oversized-symbol-bytes={}",
            ticket,
            symbol.name().len()
        );
        return;
    }
    let Some(euf) = model.euf_model.as_ref() else {
        return;
    };
    let Some(rows) = euf.function_tables.get(symbol.name()) else {
        return;
    };
    let sources = euf.function_table_terms.get(symbol.name());
    ay_core::safe_eprintln!(
        "[ite-uf-provenance] seq={} rows={} sources={:?} aligned={} rows_truncated={}",
        ticket,
        rows.len(),
        sources.map(|s| s.len()),
        sources.is_some_and(|s| s.len() == rows.len()),
        rows.len() > ROW_LIMIT,
    );
    for (index, (arguments, result)) in rows.iter().take(ROW_LIMIT).enumerate() {
        let source = sources.and_then(|terms| terms.get(index)).copied();
        ay_core::safe_eprintln!(
            "[ite-uf-provenance] seq={} row={} source={:?} is_leaf={} raw_arity={} raw_arguments={:?} arguments_truncated={} raw_result={:?}",
            ticket, index, source, source == Some(leaf), arguments.len(),
            Atoms(arguments), arguments.len() > ARG_LIMIT, Text(result),
        );
        let Some(source) = source.filter(|term| (term.0 as usize) < terms.len()) else {
            continue;
        };
        ay_core::safe_eprintln!(
            "[ite-uf-provenance] seq={} row={} source_point={:?}",
            ticket,
            index,
            Point {
                executor,
                model,
                term: source
            }
        );
        if let TermData::App(_, args) = terms.get(source) {
            for (argument_index, &term) in args.iter().take(ARG_LIMIT).enumerate() {
                ay_core::safe_eprintln!(
                    "[ite-uf-provenance] seq={} row={} argument={} point={:?}",
                    ticket,
                    index,
                    argument_index,
                    Point {
                        executor,
                        model,
                        term
                    },
                );
            }
        }
    }
}
