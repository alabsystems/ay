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

fn application_bytes(
    terms: &TermStore,
    term: TermId,
    remaining_terms: usize,
    remaining_sort_nodes: &mut usize,
) -> Option<usize> {
    let TermData::App(symbol, args) = terms.get(term) else {
        return None;
    };
    let bytes = symbol_bytes(symbol, remaining_terms)?.checked_add(args.len().checked_add(2)?)?;
    // The constant-array printer may emit a result-sort annotation. Price it
    // before that printer even compares the recursive element/value sorts.
    let annotation = if matches!(symbol, Symbol::Named(name) if name == "const-array")
        && args.len() == 1
        && matches!(terms.sort(term), Sort::Array(_))
    {
        sort_bytes(terms.sort(term), remaining_sort_nodes)?
    } else {
        0
    };
    bytes.checked_add(annotation)
}

fn atomic_payload_bytes(
    terms: &TermStore,
    term: TermId,
    remaining_terms: usize,
    pending_terms: usize,
    remaining_sort_nodes: &mut usize,
) -> Option<usize> {
    Some(match terms.get(term) {
        TermData::Const(Constant::Bool(_)) => 5,
        TermData::Const(Constant::Int(value)) => decimal_bytes(value)?,
        TermData::Const(Constant::Rational(value)) => {
            let numerator = decimal_bytes(value.0.numer())?;
            let denominator = decimal_bytes(value.0.denom())?;
            numerator
                .checked_add(denominator)
                .and_then(|n| n.checked_add(16))?
        }
        TermData::Const(Constant::BitVec { value, width }) => {
            let value_bytes = decimal_bytes(value)?;
            let Ok(width) = usize::try_from(*width) else {
                return None;
            };
            value_bytes.max(width).saturating_add(2)
        }
        TermData::Const(Constant::String(value)) => {
            value.len().checked_mul(6).and_then(|n| n.checked_add(2))?
        }
        TermData::Var(name, _) => name.len().checked_mul(2).and_then(|n| n.checked_add(2))?,
        TermData::App(..) => application_bytes(terms, term, remaining_terms, remaining_sort_nodes)?,
        TermData::Let(bindings, _) => {
            if bindings.len().saturating_add(1) > remaining_terms.saturating_sub(pending_terms) {
                return None;
            }
            let mut local = 8usize;
            for (name, _) in bindings {
                let next = name
                    .len()
                    .checked_mul(2)
                    .and_then(|n| n.checked_add(3))
                    .and_then(|n| local.checked_add(n))?;
                local = next;
            }
            local
        }
        TermData::Not(_) => 6,
        TermData::Ite(..) => 8,
        TermData::Forall(bindings, _, _) | TermData::Exists(bindings, _, _) => {
            if bindings.len().saturating_add(1) > remaining_terms.saturating_sub(pending_terms) {
                return None;
            }
            let mut local = 12usize;
            for (name, sort) in bindings {
                let sort_bytes = sort_bytes(sort, remaining_sort_nodes)?;
                let next = name
                    .len()
                    .checked_mul(2)
                    .and_then(|n| n.checked_add(sort_bytes))
                    .and_then(|n| n.checked_add(3))
                    .and_then(|n| local.checked_add(n))?;
                local = next;
            }
            local
        }
        _ => return None,
    })
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
        let Some(local) = atomic_payload_bytes(
            terms,
            term,
            max_terms.saturating_sub(seen.len()),
            pending.len(),
            &mut remaining_sort_nodes,
        ) else {
            return false;
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

/// Bound aggregate expanded output before formatting, including every copy of
/// an override at every occurrence. Atomic DAG payload alone does not price
/// expansion. The returned bound is in the existing printer's COPY-work units,
/// separately from the output-byte cap: rendering every source subtree without
/// cache reuse copies each local payload at most once per ancestor. A cached
/// batch cannot do more work than that conservative unfolded bound.
pub(in crate::executor) fn expanded_render_work_bound(
    terms: &TermStore,
    roots: &[TermId],
    overrides: &ay_core::kani_compat::DetHashMap<TermId, String>,
    max_terms: usize,
    max_visits: usize,
    max_bytes: usize,
) -> Option<u64> {
    let mut pending: Vec<_> = roots.iter().map(|&term| (term, 0usize)).collect();
    let (mut visits, mut bytes, mut copy_work) = (0usize, 0usize, 0usize);
    let mut remaining_sort_nodes = max_visits;
    while let Some((term, depth)) = pending.pop() {
        visits = visits.checked_add(1)?;
        if visits > max_visits || depth > MAX_SURFACE_DEPTH {
            return None;
        }
        let override_text = overrides.get(&term);
        let local = match override_text {
            Some(text) => text.len(),
            None => {
                // This preflight covers the existing ground-source printer
                // fragment. Binders and other atomic spellings decline rather
                // than borrowing an incomplete length model.
                if !matches!(
                    terms.get(term),
                    TermData::Const(Constant::Bool(_) | Constant::BitVec { .. })
                        | TermData::Var(..)
                        | TermData::App(..)
                        | TermData::Not(_)
                        | TermData::Ite(..)
                ) {
                    return None;
                }
                let bytes =
                    atomic_payload_bytes(terms, term, max_terms, 0, &mut remaining_sort_nodes)?;
                // The tester printer resugars is-C to (_ is C), which adds
                // syntax beyond an ordinary named application's payload.
                let tester = matches!(terms.get(term), TermData::App(Symbol::Named(name), args)
                    if args.len() == 1 && name.starts_with("is-"));
                bytes.checked_add(if tester { 8 } else { 0 })?
            }
        };
        bytes = bytes
            .checked_add(local)
            .filter(|&bytes| bytes <= max_bytes)?;
        copy_work = copy_work.checked_add(local.checked_mul(depth.checked_add(1)?)?)?;
        if override_text.is_none() {
            let children = term_child_count(terms, term)?;
            if visits.checked_add(pending.len())?.checked_add(children)? > max_visits {
                return None;
            }
            pending.extend(
                terms
                    .children(term)
                    .into_iter()
                    .map(|child| (child, depth + 1)),
            );
        }
    }
    u64::try_from(copy_work).ok()
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
