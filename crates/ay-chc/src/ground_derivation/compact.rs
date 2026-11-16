// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Finite, complete ground values represented by shared constructor DAGs.
//! Node identity is structural, never a solver assertion. Acceptance replays
//! the original clauses, including every field and every positional premise.

use ay_core::kani_compat::DetHashMap;
use num_bigint::BigUint;

mod arena;
mod eval;
mod evidence;
mod owner;
mod source;
mod validate;

pub(crate) use arena::Arena;
pub(crate) use evidence::CompactEvidence;
pub(crate) use owner::Owner;
pub(crate) use validate::validate;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) struct ValueId(pub(crate) u32);

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) enum ValueNode {
    Bool(bool),
    BitVec {
        value: BigUint,
        width: u32,
    },
    Datatype {
        sort: String,
        constructor: String,
        fields: Vec<ValueId>,
    },
}

#[derive(Debug)]
pub(crate) struct CompactStep {
    pub(crate) clause_index: usize,
    pub(crate) env: DetHashMap<String, ValueId>,
    pub(crate) premises: Vec<usize>,
}

#[derive(Debug)]
pub(crate) struct CompactDerivation {
    pub(crate) arena: Arena,
    pub(crate) steps: Vec<CompactStep>,
    pub(crate) query_step: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, thiserror::Error)]
pub(crate) enum Error {
    #[error("original owner stopped")]
    Stopped,
    #[error("original resource allowance exhausted")]
    Resource,
    #[error("invalid original source")]
    InvalidSource,
    #[error("invalid complete ground value")]
    InvalidValue,
    #[error("original-clause derivation rejected")]
    InvalidDerivation,
    #[error("unsupported compact evidence fragment")]
    Unsupported,
}

pub(crate) type Result<T> = std::result::Result<T, Error>;

pub(crate) fn validate_source(problem: &crate::ChcProblem, owner: &mut Owner<'_>) -> Result<()> {
    let _scope = owner.enter();
    let result = source::Source::new(problem, owner).and_then(|mut source| source.validate(owner));
    if result == Err(Error::Resource) {
        return owner.refuse(Error::Resource);
    }
    result?;
    owner.poll()
}

#[cfg(test)]
mod tests;
