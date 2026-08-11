// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Allocation preflight for canonical terms rendered by the surface audit.

use ay_core::kani_compat::DetHashSet as HashSet;
use ay_core::term::{Constant, TermData};
use ay_core::{Sort, Symbol, TermId, TermStore};

use super::{term_child_count, MAX_SURFACE_DEPTH};

fn decimal_bytes(value: &num_bigint::BigInt) -> Option<usize> {
    let bits = usize::try_from(value.bits()).ok()?;
    bits.checked_mul(30_103)?
        .checked_add(99_999)?
        .checked_div(100_000)?
        .checked_add(2)
}

fn sort_bytes(sort: &Sort, remaining_nodes: &mut usize) -> Option<usize> {
    let mut pending = vec![(sort, 0usize)];
    let mut bytes = 0usize;
    while let Some((sort, depth)) = pending.pop() {
        *remaining_nodes = remaining_nodes.checked_sub(1)?;
        if depth > MAX_SURFACE_DEPTH {
            return None;
        }
        let local = match sort {
            Sort::Bool | Sort::Int | Sort::Real | Sort::String | Sort::RegLan | Sort::Char => 8,
            Sort::BitVec(_) | Sort::FloatingPoint(..) => 32,
            Sort::Uninterpreted(name) | Sort::TypeVar(name) => name.len().checked_mul(2)?,
            Sort::FiniteDomain(name, _) => name.len().checked_mul(2)?.checked_add(24)?,
            Sort::Array(array) => {
                if *remaining_nodes < 2 {
                    return None;
                }
                pending.push((&array.index_sort, depth + 1));
                pending.push((&array.element_sort, depth + 1));
                10
            }
            Sort::Seq(element) => {
                if *remaining_nodes < 1 {
                    return None;
                }
                pending.push((element, depth + 1));
                6
            }
            Sort::Datatype(datatype) => {
                let field_count = datatype
                    .constructors
                    .iter()
                    .try_fold(0usize, |count, constructor| {
                        count.checked_add(constructor.fields.len())
                    })?;
                if datatype.constructors.len() > *remaining_nodes
                    || field_count > (*remaining_nodes).saturating_sub(datatype.constructors.len())
                {
                    return None;
                }
                *remaining_nodes -= datatype.constructors.len();
                let mut local = datatype.name.len().checked_mul(2)?;
                for constructor in &datatype.constructors {
                    local = local.checked_add(constructor.name.len().checked_mul(2)?)?;
                    for field in &constructor.fields {
                        local = local.checked_add(field.name.len().checked_mul(2)?)?;
                        pending.push((&field.sort, depth + 1));
                    }
                }
                local
            }
            _ => return None,
        };
        bytes = bytes.checked_add(local)?;
    }
    Some(bytes)
}

fn decimal_u32_bytes(mut value: u32) -> usize {
    let mut digits = 1usize;
    while value >= 10 {
        value /= 10;
        digits += 1;
    }
    digits
}

fn symbol_bytes(symbol: &Symbol, max_indices: usize) -> Option<usize> {
    match symbol {
        Symbol::Named(name) => name.len().checked_mul(2)?.checked_add(2),
        Symbol::Indexed(name, indices) => {
            if indices.len() > max_indices {
                return None;
            }
            indices.iter().try_fold(
                name.len().checked_mul(2)?.checked_add(6)?,
                |bytes, index| bytes.checked_add(decimal_u32_bytes(*index).saturating_add(1)),
            )
        }
        _ => None,
    }
}

/// Estimate every allocation-heavy atomic payload before invoking the
/// recursive Alethe formatter. The formatter memoizes canonical TermIds, so
/// shared subterms are charged once, while every binder sort is charged in
/// full because its formatting is embedded at each binder occurrence.
pub(in crate::executor) fn render_roots_have_bounded_payload(
    terms: &TermStore,
    roots: &[TermId],
    max_terms: usize,
    max_bytes: usize,
) -> bool {
    let mut pending: Vec<(TermId, usize)> = roots.iter().map(|&term| (term, 0usize)).collect();
    let mut seen = HashSet::default();
    let mut bytes = 0usize;
    let mut remaining_sort_nodes = max_terms;
    while let Some((term, depth)) = pending.pop() {
        if depth > MAX_SURFACE_DEPTH || !seen.insert(term) {
            if depth > MAX_SURFACE_DEPTH {
                return false;
            }
            continue;
        }
        if seen.len() > max_terms {
            return false;
        }
        let local = match terms.get(term) {
            TermData::Const(Constant::Bool(_)) => 5,
            TermData::Const(Constant::Int(value)) => match decimal_bytes(value) {
                Some(bytes) => bytes,
                None => return false,
            },
            TermData::Const(Constant::Rational(value)) => {
                let Some(numerator) = decimal_bytes(value.0.numer()) else {
                    return false;
                };
                let Some(denominator) = decimal_bytes(value.0.denom()) else {
                    return false;
                };
                match numerator
                    .checked_add(denominator)
                    .and_then(|n| n.checked_add(16))
                {
                    Some(bytes) => bytes,
                    None => return false,
                }
            }
            TermData::Const(Constant::BitVec { value, width }) => {
                let Some(value_bytes) = decimal_bytes(value) else {
                    return false;
                };
                let Ok(width) = usize::try_from(*width) else {
                    return false;
                };
                value_bytes.max(width).saturating_add(2)
            }
            TermData::Const(Constant::String(value)) => {
                match value.len().checked_mul(6).and_then(|n| n.checked_add(2)) {
                    Some(bytes) => bytes,
                    None => return false,
                }
            }
            TermData::Var(name, _) => {
                match name.len().checked_mul(2).and_then(|n| n.checked_add(2)) {
                    Some(bytes) => bytes,
                    None => return false,
                }
            }
            TermData::App(symbol, args) => {
                match symbol_bytes(symbol, max_terms.saturating_sub(seen.len()))
                    .and_then(|n| n.checked_add(args.len().saturating_add(2)))
                {
                    Some(bytes) => bytes,
                    None => return false,
                }
            }
            TermData::Let(bindings, _) => {
                if bindings.len().saturating_add(1)
                    > max_terms
                        .saturating_sub(seen.len())
                        .saturating_sub(pending.len())
                {
                    return false;
                }
                let mut local = 8usize;
                for (name, _) in bindings {
                    let Some(next) = name
                        .len()
                        .checked_mul(2)
                        .and_then(|n| n.checked_add(3))
                        .and_then(|n| local.checked_add(n))
                    else {
                        return false;
                    };
                    local = next;
                }
                local
            }
            TermData::Not(_) => 6,
            TermData::Ite(..) => 8,
            TermData::Forall(bindings, _, _) | TermData::Exists(bindings, _, _) => {
                if bindings.len().saturating_add(1)
                    > max_terms
                        .saturating_sub(seen.len())
                        .saturating_sub(pending.len())
                {
                    return false;
                }
                let mut local = 12usize;
                for (name, sort) in bindings {
                    let Some(sort_bytes) = sort_bytes(sort, &mut remaining_sort_nodes) else {
                        return false;
                    };
                    let Some(next) = name
                        .len()
                        .checked_mul(2)
                        .and_then(|n| n.checked_add(sort_bytes))
                        .and_then(|n| n.checked_add(3))
                        .and_then(|n| local.checked_add(n))
                    else {
                        return false;
                    };
                    local = next;
                }
                local
            }
            _ => return false,
        };
        let Some(next_bytes) = bytes.checked_add(local) else {
            return false;
        };
        if next_bytes > max_bytes {
            return false;
        }
        bytes = next_bytes;
        let Some(child_count) = term_child_count(terms, term) else {
            return false;
        };
        if child_count
            > max_terms
                .saturating_sub(seen.len())
                .saturating_sub(pending.len())
        {
            return false;
        }
        for child in terms.children(term) {
            pending.push((child, depth + 1));
        }
    }
    true
}

#[cfg(test)]
mod tests {
    use ay_core::{DatatypeConstructor, DatatypeField, DatatypeSort, Sort, Symbol, TermStore};
    use num_bigint::BigInt;

    use super::render_roots_have_bounded_payload;

    #[test]
    fn zero_bitvector_width_is_charged_before_formatting() {
        let mut terms = TermStore::new();
        let huge = terms.mk_bitvec(BigInt::from(0), 9_000_000);
        assert!(!render_roots_have_bounded_payload(
            &terms,
            &[huge],
            16,
            8 * 1024 * 1024,
        ));
        let small = terms.mk_var("small_payload", Sort::Bool);
        assert!(render_roots_have_bounded_payload(
            &terms,
            &[small],
            16,
            8 * 1024 * 1024,
        ));
    }

    #[test]
    fn indexed_symbol_vector_is_bounded_before_printer_string_collection() {
        let mut terms = TermStore::new();
        let app = terms.mk_app(
            Symbol::indexed("wide_indexed_symbol", vec![u32::MAX; 17_000]),
            Vec::<ay_core::TermId>::new(),
            Sort::Bool,
        );
        assert!(!render_roots_have_bounded_payload(
            &terms,
            &[app],
            16_384,
            8 * 1024 * 1024,
        ));

        let wide_sort = Sort::Datatype(DatatypeSort::new(
            "WidePayloadDatatype",
            vec![DatatypeConstructor::new(
                "wide",
                (0..17_000)
                    .map(|index| DatatypeField::new(format!("f{index}"), Sort::Int))
                    .collect(),
            )],
        ));
        let body = terms.mk_bool(true);
        let quantified = terms.mk_forall(vec![("x".to_string(), wide_sort)], body);
        assert!(!render_roots_have_bounded_payload(
            &terms,
            &[quantified],
            16_384,
            8 * 1024 * 1024,
        ));
    }
}
