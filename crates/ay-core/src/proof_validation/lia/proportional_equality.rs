// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

/// Exact data for `P = 0 => Q = 0`, with `Q = multiplier * P`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ArithProportionalEqualityWitness {
    /// The original negated premise literal, followed by the conclusion.
    pub ordered: [TermId; 2],
    /// Signed, nonzero rational scale between the RAW operand differences.
    pub multiplier: num_rational::BigRational,
}

/// Recheck an exact two-literal integer equality implication. No hint or
/// normalization supplied by the producer is consumed.
///
/// Integer-valued opaque applications can be shared atoms: proportional
/// forms over the identical atom imply the same equality without assuming
/// any property of that function. All coefficients and the affine constant
/// must scale together. Degenerate constant-only rows are outside this lane.
#[must_use]
pub fn arith_proportional_equality_witness(
    terms: &TermStore,
    clause: &[TermId],
) -> Option<ArithProportionalEqualityWitness> {
    use crate::{
        term::{Symbol, TermData},
        Sort,
    };
    use num_rational::BigRational;
    use num_traits::Zero;

    fn equality(terms: &TermStore, root: TermId) -> Option<(TermId, TermId)> {
        terms.entry_stamp(root)?;
        let TermData::App(Symbol::Named(name), args) = terms.get(root) else {
            return None;
        };
        let [left, right] = args.as_slice() else {
            return None;
        };
        terms.entry_stamp(*left)?;
        terms.entry_stamp(*right)?;
        (name == "="
            && terms.sort(root) == &Sort::Bool
            && terms.sort(*left) == &Sort::Int
            && terms.sort(*right) == &Sort::Int)
            .then_some((*left, *right))
    }
    let [a, b] = clause else {
        return None;
    };
    // Count OCCURRENCES, not distinct nodes: the normalizer recursively
    // expands repeated arithmetic children and does not memoize a DAG.
    if !proportional_equality_input_is_bounded(terms, clause) {
        return None;
    }
    for ordered in [[*a, *b], [*b, *a]] {
        let TermData::Not(premise) = terms.get(ordered[0]) else {
            continue;
        };
        if terms.sort(ordered[0]) != &Sort::Bool {
            continue;
        }
        let Some((pl, pr)) = equality(terms, *premise) else {
            continue;
        };
        let Some((ql, qr)) = equality(terms, ordered[1]) else {
            continue;
        };
        let (mut p, pc) = int_linear_diff(terms, pl, pr)?;
        let (mut q, qc) = int_linear_diff(terms, ql, qr)?;
        p.retain(|_, c| !c.is_zero());
        q.retain(|_, c| !c.is_zero());
        let (&pivot, coefficient) = p.first_key_value()?;
        let target = q.get(&pivot)?;
        if p.len() != q.len()
            || p.values()
                .chain(q.values())
                .chain([&pc, &qc])
                .any(|c| c.bits() > 4_096)
        {
            return None;
        }
        let multiplier = BigRational::new(target.clone(), coefficient.clone());
        if multiplier.is_zero()
            || BigRational::from_integer(pc) * &multiplier != BigRational::from_integer(qc)
        {
            return None;
        }
        if !p.iter().all(|(atom, value)| {
            q.get(atom).is_some_and(|target| {
                BigRational::from_integer(value.clone()) * &multiplier
                    == BigRational::from_integer(target.clone())
            })
        }) {
            return None;
        }
        return Some(ArithProportionalEqualityWitness {
            ordered,
            multiplier,
        });
    }
    None
}

fn proportional_equality_input_is_bounded(terms: &TermStore, roots: &[TermId]) -> bool {
    use crate::{
        term::{Constant, Symbol, TermData},
        Sort,
    };
    let mut pending: Vec<_> = roots.iter().map(|&root| (root, 0usize)).collect();
    let mut work = 256usize;
    let mut sort_work = 2_048usize;
    while let Some((term, depth)) = pending.pop() {
        let Some(remaining) = work.checked_sub(1) else {
            return false;
        };
        work = remaining;
        if depth > 32
            || terms.entry_stamp(term).is_none()
            || !proportional_equality_sort_is_bounded(terms.sort(term), &mut sort_work)
        {
            return false;
        }
        let children: &[TermId] = match terms.get(term) {
            TermData::Const(Constant::Bool(_)) => &[],
            TermData::Const(Constant::Int(value)) if value.bits() <= 512 => &[],
            TermData::Const(Constant::Rational(value))
                if value.0.numer().bits() <= 512 && value.0.denom().bits() <= 512 =>
            {
                &[]
            }
            TermData::Const(Constant::BitVec { value, width })
                if (1..=512).contains(width) && value.bits() <= 512 =>
            {
                &[]
            }
            TermData::Const(Constant::String(value)) if value.len() <= 1_024 => &[],
            TermData::Var(name, _) if name.len() <= 256 => &[],
            TermData::App(symbol, args) => {
                // Check borrowed metadata/counts before normalization or any
                // recursive formatter can copy an unbounded payload.
                let bounded_symbol = match symbol {
                    Symbol::Named(name) => name.len() <= 256,
                    Symbol::Indexed(name, indices) => name.len() <= 256 && indices.len() <= 8,
                };
                if !bounded_symbol
                    || args.len() > work.saturating_sub(pending.len())
                    || args.iter().any(|&arg| terms.entry_stamp(arg).is_none())
                {
                    return false;
                }
                // Canceled non-Int arithmetic must not disappear before the
                // normalizer's atom-sort check sees it.
                if matches!(symbol.name(), "+" | "-" | "*")
                    && (terms.sort(term) != &Sort::Int
                        || args.iter().any(|&arg| terms.sort(arg) != &Sort::Int))
                {
                    return false;
                }
                args
            }
            TermData::Not(inner) => {
                if terms.entry_stamp(*inner).is_none()
                    || terms.sort(term) != &Sort::Bool
                    || terms.sort(*inner) != &Sort::Bool
                {
                    return false;
                }
                std::slice::from_ref(inner)
            }
            TermData::Ite(c, t, e) => {
                if pending.len() + 3 > work {
                    return false;
                }
                pending.extend([(*c, depth + 1), (*t, depth + 1), (*e, depth + 1)]);
                continue;
            }
            // Includes binders, oversized literals and unknown future
            // variants: none may introduce unpriced owned payloads.
            _ => return false,
        };
        if pending.len() + children.len() > work {
            return false;
        }
        pending.extend(children.iter().map(|&child| (child, depth + 1)));
    }
    true
}

/// Opaque integer atoms may contain array, datatype or other sorted operands.
/// Bound their metadata without restricting the whole DAG to Int and Bool;
/// canonical constant-array rendering can itself visit these sort payloads.
fn proportional_equality_sort_is_bounded(sort: &crate::Sort, work: &mut usize) -> bool {
    use crate::Sort;

    let mut pending = vec![(sort, 0usize)];
    while let Some((sort, depth)) = pending.pop() {
        let Some(remaining) = work.checked_sub(1) else {
            return false;
        };
        *work = remaining;
        if depth > 32 {
            return false;
        }
        match sort {
            Sort::Bool
            | Sort::Int
            | Sort::Real
            | Sort::BitVec(_)
            | Sort::String
            | Sort::RegLan
            | Sort::FloatingPoint(..)
            | Sort::Char
            | Sort::Complex => {}
            // This bounded integer wire lane does not admit the newly
            // composed finite-field carrier without its own surface review.
            Sort::FiniteField(_) => return false,
            Sort::Uninterpreted(name) | Sort::TypeVar(name) | Sort::FiniteDomain(name, _) => {
                if name.len() > 256 {
                    return false;
                }
            }
            Sort::Array(array) => {
                if pending.len().saturating_add(2) > *work {
                    return false;
                }
                pending.push((&array.index_sort, depth + 1));
                pending.push((&array.element_sort, depth + 1));
            }
            Sort::Seq(element) => {
                if pending.len().saturating_add(1) > *work {
                    return false;
                }
                pending.push((element, depth + 1));
            }
            Sort::Datatype(datatype) => {
                if datatype.name.len() > 256 || datatype.constructors.len() > *work {
                    return false;
                }
                for constructor in &datatype.constructors {
                    let Some(remaining) = work.checked_sub(1) else {
                        return false;
                    };
                    *work = remaining;
                    if constructor.name.len() > 256 || constructor.fields.len() > *work {
                        return false;
                    }
                    for field in &constructor.fields {
                        let Some(remaining) = work.checked_sub(1) else {
                            return false;
                        };
                        *work = remaining;
                        if field.name.len() > 256 || pending.len().saturating_add(1) > *work {
                            return false;
                        }
                        pending.push((&field.sort, depth + 1));
                    }
                }
            }
        }
    }
    true
}
