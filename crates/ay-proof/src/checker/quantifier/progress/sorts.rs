// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bound all recursive sort equality before invoking its derived implementation.

use super::*;

const MAX_SORT_DEPTH: usize = 256;

pub(super) fn meter_sort(
    sort: &Sort,
    depth: usize,
    meter: &mut QuantifierMeter<'_, '_>,
) -> Result<(), ProofCheckError> {
    meter.charge(2, 0)?;
    if depth > MAX_SORT_DEPTH {
        return Err(ProofCheckError::ResourceLimit);
    }
    match sort {
        Sort::Array(array) => {
            meter_sort(&array.index_sort, depth + 1, meter)?;
            meter_sort(&array.element_sort, depth + 1, meter)?;
        }
        Sort::Seq(element) => meter_sort(element, depth + 1, meter)?,
        Sort::Datatype(datatype) => {
            meter.name(&datatype.name)?;
            for constructor in &datatype.constructors {
                meter.name(&constructor.name)?;
                for field in &constructor.fields {
                    meter.name(&field.name)?;
                    meter_sort(&field.sort, depth + 1, meter)?;
                }
            }
        }
        Sort::Uninterpreted(name) | Sort::TypeVar(name) | Sort::FiniteDomain(name, _) => {
            meter.name(name)?
        }
        Sort::Bool
        | Sort::Int
        | Sort::Real
        | Sort::BitVec(_)
        | Sort::String
        | Sort::RegLan
        | Sort::FloatingPoint(_, _)
        | Sort::Char => {}
        _ => return Err(ProofCheckError::ResourceLimit),
    }
    Ok(())
}
