// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Comparison price/depth guard only; full sort semantics belong to preflight_sort.

use super::*;

pub(super) fn price(
    sort: &Sort,
    depth: usize,
    app: &mut App<'_, '_>,
) -> Result<(), ProofCheckError> {
    app.charge(2, 0)?; // This walk plus the ensuing equality visit.
    if depth > MAX_BUNDLE_SORT_DEPTH {
        return app.invalid("exceeds the maximum sort nesting depth");
    }
    match sort {
        Sort::Array(array) => {
            price(&array.index_sort, depth + 1, app)?;
            price(&array.element_sort, depth + 1, app)?;
        }
        Sort::Seq(element) => price(element, depth + 1, app)?,
        Sort::Uninterpreted(name) | Sort::TypeVar(name) | Sort::FiniteDomain(name, _) => {
            app.charge(mul(add(name.len(), 1)?, 2)?, 0)?;
        }
        Sort::Datatype(datatype) => {
            app.charge(mul(add(datatype.name.len(), 1)?, 2)?, 0)?;
            for constructor in &datatype.constructors {
                app.charge(mul(add(constructor.name.len(), 1)?, 2)?, 0)?;
                for field in &constructor.fields {
                    app.charge(mul(add(field.name.len(), 1)?, 2)?, 0)?;
                    price(&field.sort, depth + 1, app)?;
                }
            }
        }
        Sort::Bool
        | Sort::Int
        | Sort::Real
        | Sort::BitVec(_)
        | Sort::String
        | Sort::RegLan
        | Sort::FloatingPoint(..)
        | Sort::FiniteField(_)
        | Sort::Char => {}
        _ => return Err(ProofCheckError::ResourceLimit),
    }
    Ok(())
}
