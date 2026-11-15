// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

//! Bounded borrowed source footprint, diagnostic-only and never a price.

use super::*;
use ay_core::{Constant, Sort, TermData, TermId};
use ay_dpll::api::SerializableProofBundle;
use num_traits::ToPrimitive;

pub(super) fn shape(snapshot: &SerializableProofBundle, clause: &[TermId]) -> Source {
    let mut result = EMPTY_SOURCE;
    result.literals = clause.len();
    result.singleton_not = clause.len() == 1
        && matches!(
            snapshot.term_entries.get(clause[0].index()),
            Some((TermData::Not(_), _))
        );
    let mut pending = [TermId::SENTINEL; EDGES];
    let mut seen = [TermId::SENTINEL; TERMS];
    let (mut queued, mut visited, mut edges) = (0, 0, 0);
    if clause.len() > EDGES {
        return result;
    }
    result.unique_roots = clause
        .iter()
        .enumerate()
        .filter(|(i, term)| !clause[..*i].contains(term))
        .count();
    pending[..clause.len()].copy_from_slice(clause);
    queued += clause.len();
    while queued > 0 {
        queued -= 1;
        let term = pending[queued];
        let Some((data, sort)) = snapshot.term_entries.get(term.index()) else {
            return result;
        };
        if let TermData::Var(name, _) = data {
            let Some(names) = result.raw_var_name_bytes.checked_add(name.len()) else {
                return result;
            };
            result.raw_var_name_bytes = names;
            result.max_var_name_bytes = result.max_var_name_bytes.max(name.len());
        }
        if seen[..visited].contains(&term) {
            continue;
        }
        if visited == TERMS {
            return result;
        }
        seen[visited] = term;
        visited += 1;
        result.unique_terms = visited;
        match data {
            TermData::Ite(..) => result.ite_nodes += 1,
            TermData::App(symbol, args) => {
                result.max_arity = result.max_arity.max(args.len());
                result.indexed_apps += usize::from(matches!(symbol, ay_core::Symbol::Indexed(..)));
            }
            _ => {}
        }
        result.bool_bv_only &= matches!(sort, Sort::Bool | Sort::BitVec(_));
        if let Sort::BitVec(width) = sort {
            result.max_bv_width = result.max_bv_width.max(width.width);
        }
        if !narrow(snapshot, data, sort) {
            result.narrow_typed_ops = false;
            if !record_head(&mut result, data) {
                return result;
            }
        }
        if let Sort::Array(array) = sort {
            result.array = true;
            result.small_array_keys &= match &array.index_sort {
                Sort::Bool => true,
                Sort::BitVec(width) => width.width <= 8 && width.width > 0,
                _ => false,
            };
            if let Sort::BitVec(width) = &array.index_sort {
                result.max_array_bv_key = result.max_array_bv_key.max(width.width);
            }
        }
        let local;
        let children = match data {
            TermData::Const(_) | TermData::Var(..) => &[][..],
            TermData::Not(inner) => std::slice::from_ref(inner),
            TermData::App(_, args) => args.as_slice(),
            TermData::Ite(a, b, c) => {
                local = [*a, *b, *c];
                &local[..]
            }
            _ => return result,
        };
        edges += children.len();
        result.raw_edges = edges;
        if edges > EDGES || queued + children.len() > EDGES {
            return result;
        }
        pending[queued..queued + children.len()].copy_from_slice(children);
        queued += children.len();
    }
    result.complete = true;
    result
}

fn scalar(sort: &Sort) -> bool {
    matches!(sort, Sort::Bool)
        || matches!(sort, Sort::BitVec(width) if (1..=128).contains(&width.width))
}

// Diagnostic syntax/typing only. Not a cycle/depth/value-cap proof or pricing
// prerequisite. The independent retained checker remains the sole verifier.
fn narrow(snapshot: &SerializableProofBundle, data: &TermData, sort: &Sort) -> bool {
    if !scalar(sort) {
        return false;
    }
    let child_sort = |term: &TermId| {
        snapshot
            .term_entries
            .get(term.index())
            .map(|entry| &entry.1)
    };
    let bools = |args: &[TermId]| {
        args.iter()
            .all(|term| child_sort(term) == Some(&Sort::Bool))
    };
    match data {
        TermData::Var(..) => true,
        TermData::Const(Constant::Bool(_)) => matches!(sort, Sort::Bool),
        TermData::Const(Constant::BitVec { value, width }) => {
            matches!(sort, Sort::BitVec(w) if w.width == *width)
                && value
                    .to_u128()
                    .is_some_and(|value| *width == 128 || value < (1u128 << *width))
        }
        TermData::Not(inner) => {
            matches!(sort, Sort::Bool) && child_sort(inner) == Some(&Sort::Bool)
        }
        TermData::App(ay_core::Symbol::Named(name), args) => {
            if args.len() > 128 {
                return false;
            }
            match name.as_str() {
                "not" => matches!(sort, Sort::Bool) && args.len() == 1 && bools(args),
                "and" | "or" => matches!(sort, Sort::Bool) && bools(args),
                "xor" | "=>" | "implies" => {
                    matches!(sort, Sort::Bool) && args.len() == 2 && bools(args)
                }
                "=" | "distinct" if args.len() == 2 && matches!(sort, Sort::Bool) => {
                    match (child_sort(&args[0]), child_sort(&args[1])) {
                        (Some(a), Some(b)) => a == b && scalar(a),
                        _ => false,
                    }
                }
                "bvadd" | "bvsub" | "bvand" | "bvor" | "bvxor" if args.len() == 2 => {
                    matches!(sort, Sort::BitVec(_))
                        && child_sort(&args[0]) == Some(sort)
                        && child_sort(&args[1]) == Some(sort)
                }
                "bvult" | "bvugt" | "bvule" | "bvuge"
                    if args.len() == 2 && matches!(sort, Sort::Bool) =>
                {
                    match (child_sort(&args[0]), child_sort(&args[1])) {
                        (Some(a @ Sort::BitVec(_)), Some(b)) => a == b && scalar(a),
                        _ => false,
                    }
                }
                _ => false,
            }
        }
        _ => false,
    }
}

fn record_head(source: &mut Source, data: &TermData) -> bool {
    let name = match data {
        TermData::App(symbol, _) => symbol.name(),
        TermData::Ite(..) => "ITE",
        TermData::Not(_) => "Not/wrong-sort",
        TermData::Var(..) => "Var/non-scalar",
        TermData::Const(_) => "Const/wrong-value-or-sort",
        _ => "unsupported-node",
    };
    let len = name.len().min(32);
    if let Some(head) = source.heads[..source.head_count]
        .iter_mut()
        .find(|head| head.len == len && head.bytes[..len] == name.as_bytes()[..len])
    {
        head.nodes += 1;
        return true;
    }
    if source.head_count == HEADS {
        return false;
    }
    let mut head = EMPTY_HEAD;
    head.bytes[..len].copy_from_slice(&name.as_bytes()[..len]);
    head.len = len;
    head.nodes = 1;
    head.clipped = name.len() > 32;
    source.heads[source.head_count] = head;
    source.head_count += 1;
    true
}
