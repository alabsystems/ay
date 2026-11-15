// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Validate every operand discarded by a proved local memory property.

use super::*;

/// The top-level requests [`property`] makes, in its order, for the census:
/// the traces of both reads, `outside`, and every lowered child. `None` when
/// the shape is malformed, which [`property`] refuses.
pub(super) fn requests(terms: &TermStore, shape: &Shape) -> Option<Vec<Request>> {
    for term in [shape.property, shape.equality] {
        terms.entry_stamp(term)?;
    }
    let TermData::App(Symbol::Named(_), reads) = terms.get(shape.equality) else {
        return None;
    };
    let [left, right] = reads.as_slice() else {
        return None;
    };
    let TermData::App(Symbol::Named(_), children) = terms.get(shape.property) else {
        return None;
    };
    let mut requests = vec![
        Request::OperandsOf(*left),
        Request::OperandsOf(*right),
        Request::Lower(shape.outside),
    ];
    for &child in children {
        terms.entry_stamp(child)?;
        if lowers_child(terms, shape, child) {
            requests.push(Request::Lower(child));
        }
    }
    Some(requests)
}

/// Whether [`property`] lowers `child` of the property connective: every
/// child except the equality it proves and that equality's negation.
fn lowers_child(terms: &TermStore, shape: &Shape, child: TermId) -> bool {
    child != shape.equality
        && !matches!(terms.get(child), TermData::Not(inner) if *inner == shape.equality)
}

pub(super) fn property(
    lowerer: &mut ProofProducingLowerer<'_, '_>,
    shape: &Shape,
) -> Result<(), String> {
    let terms = lowerer.terms;
    for term in [shape.property, shape.equality, shape.outside] {
        if terms.entry_stamp(term).is_none() || terms.sort(term) != &Sort::Bool {
            return Err("memory property must contain live Boolean terms".into());
        }
    }
    let TermData::App(Symbol::Named(op), reads) = terms.get(shape.equality) else {
        return Err("memory property requires equality".into());
    };
    let [left, right] = reads.as_slice() else {
        return Err("memory equality requires two reads".into());
    };
    if op != "=" {
        return Err("memory property requires equality".into());
    }
    lowerer.validate_sparse_read(*left)?;
    lowerer.validate_sparse_read(*right)?;
    if terms.sort(*left) != terms.sort(*right) {
        return Err("memory read sort mismatch".into());
    }
    lowerer.lower_bool(shape.outside)?;
    let TermData::App(Symbol::Named(op), children) = terms.get(shape.property) else {
        return Err("memory property requires a Boolean connective".into());
    };
    if (shape.property_value && (op != "or" || children.len() != 2))
        || (!shape.property_value && (op != "and" || children.len() > 128))
    {
        return Err("malformed memory property connective".into());
    }
    for &child in children {
        if terms.entry_stamp(child).is_none() || terms.sort(child) != &Sort::Bool {
            return Err("memory property child must be Boolean".into());
        }
        if lowers_child(terms, shape, child) {
            lowerer.lower_bool(child)?;
        }
    }
    Ok(())
}
