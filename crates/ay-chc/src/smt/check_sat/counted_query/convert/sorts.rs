// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use ay_core::original_query::CountedAdmission;
use ay_core::Sort;

use super::super::types::{Type, Types};
use super::{Error, Result};

// Inherited native owned-Sort copy safety, not a query-node/work ceiling.
// Both core term/snapshot.rs and the counted builder enforce this envelope.
const MAX_COPY_DEPTH: usize = 256;

pub(super) fn materialize(ty: Type, types: &Types, owner: &CountedAdmission) -> Result<Sort> {
    copy(ty, types, owner, 0)
}

fn copy(ty: Type, types: &Types, owner: &CountedAdmission, depth: usize) -> Result<Sort> {
    owner.admit(1, 0)?;
    if depth > MAX_COPY_DEPTH {
        return Err(Error::Unsupported);
    }
    match ty {
        Type::Bool => Ok(Sort::Bool),
        Type::BitVec(width) if width > 0 => Ok(Sort::bitvec(width)),
        Type::BitVec(_) => Err(Error::IllTyped),
        Type::Array(key, value) => {
            // Native Sort is a tree, unlike the census type DAG. Charge every
            // actual copied occurrence and allocation, not only each unique ID.
            // Recursion is bounded by the inherited representation depth above.
            owner.admit(2, std::mem::size_of::<ay_core::ArraySort>())?;
            let key = copy(types.get(key)?, types, owner, depth + 1)?;
            let value = copy(types.get(value)?, types, owner, depth + 1)?;
            Ok(Sort::array(key, value))
        }
    }
}
