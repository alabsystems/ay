// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Closed predicate admission only; descendants still undergo the full census.

use ay_core::term::{TermId, TermStore};
use ay_core::Sort;

use crate::fp_adapter::FpAdapterError;

pub(super) fn supports(
    terms: &TermStore,
    name: &str,
    args: &[TermId],
) -> Result<bool, FpAdapterError> {
    let relational = matches!(
        name,
        "bvult" | "bvule" | "bvugt" | "bvuge" | "bvslt" | "bvsle" | "bvsgt" | "bvsge"
    );
    let equality = matches!(name, "=" | "distinct")
        && args
            .first()
            .is_some_and(|&id| matches!(terms.sort(id), Sort::BitVec(_)));
    if !relational && !equality {
        return Ok(false);
    }
    if args.len() != 2
        || terms.sort(args[0]) != terms.sort(args[1])
        || !matches!(terms.sort(args[0]), Sort::BitVec(w) if (1..=64).contains(&w.width))
    {
        return Err(FpAdapterError::Invalid("closed BV predicate arity/sorts"));
    }
    // OTHER=4096's mixed-guard proof uses these COMPLETE payload ceilings.
    // Refuse a larger ABI rather than silently pricing only Bool variants.
    if std::mem::size_of::<usize>() > 8
        || std::mem::size_of::<crate::ChcExpr>() > 128
        || std::mem::size_of::<crate::ChcVar>() > 64
        || std::mem::size_of::<ay_fp::FpDecomposed>() > 128
        || std::mem::size_of::<ay_core::CnfClause>() > 32
        || std::mem::size_of::<TermId>() > 8
    {
        return Err(FpAdapterError::Unsupported(
            "closed BV guard layout envelope",
        ));
    }
    Ok(true)
}
