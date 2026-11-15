// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Source-preserving raw construction, NOT a solver or model admission.
//!
//! The already typed postorder and pointer table stay attached to the result.
//! Structural interning may merge terms, but never source-node identities or
//! same-spelling variables of different sorts. Every child comes from this
//! fresh store's earlier postorder slot; numeric handles from another store
//! cannot enter this path. Construction uses the original cumulative owner.

use ay_core::kani_compat::DetHashMap;
use ay_core::original_query::CountedAdmission;
use ay_core::term::{CountedTermBuilder, CountedTermError};
use ay_core::{TermId, TermStore};

use super::types::Type;
use super::{allocation, Census, Error, Query, Result};
use crate::{ChcExpr, ChcVar};

mod cnf;
mod operators;
mod scalar;
mod sorts;
#[cfg(test)]
mod tests;

/// Borrowed ORIGINAL declaration and its exact typed native variable.
/// This is deliberately not a String-keyed model or external assignment.
pub(in crate::smt::check_sat) struct Binding<'a> {
    pub(in crate::smt::check_sat) original: &'a ChcVar,
    pub(in crate::smt::check_sat) term: TermId,
}

pub(in crate::smt::check_sat) struct Converted<'a> {
    query: Query<'a>,
    store: TermStore,
    node_terms: Vec<TermId>,
    bindings: Vec<Binding<'a>>,
    root: TermId,
}

impl<'a> Query<'a> {
    pub(in crate::smt::check_sat) fn into_terms(self) -> Result<Converted<'a>> {
        let owner = self.owner.clone();
        owner.admit(1, 0)?;
        let result = construct(&self);
        match result {
            Ok((store, node_terms, bindings, root)) => {
                let converted = Converted {
                    query: self,
                    store,
                    node_terms,
                    bindings,
                    root,
                };
                if let Err(error) = owner.check() {
                    drop(converted);
                    return Err(error.into());
                }
                Ok(converted)
            }
            Err(error) => {
                drop(self);
                // All failed construction scratch/source tables are gone.
                owner.check()?;
                Err(error)
            }
        }
    }
}

impl<'a> Converted<'a> {
    pub(in crate::smt::check_sat) fn original(&self) -> &'a ChcExpr {
        self.query.original
    }

    pub(in crate::smt::check_sat) fn census(&self) -> Census {
        self.query.census
    }

    pub(in crate::smt::check_sat) fn terms(&self) -> &TermStore {
        &self.store
    }

    pub(in crate::smt::check_sat) fn root(&self) -> TermId {
        self.root
    }

    pub(in crate::smt::check_sat) fn bindings(&self) -> &[Binding<'a>] {
        &self.bindings
    }

    pub(in crate::smt::check_sat) fn term_for(&self, original: &ChcExpr) -> Result<TermId> {
        let index = self.query.node_index(original)?;
        self.node_terms.get(index).copied().ok_or(Error::IllTyped)
    }

    /// Terminal disposal fence, not a solve/model/proof acceptance gate.
    pub(in crate::smt::check_sat) fn finish(self) -> Result<()> {
        let owner = self.query.owner.clone();
        drop(self);
        owner.check()?;
        Ok(())
    }
}

type Parts<'a> = (TermStore, Vec<TermId>, Vec<Binding<'a>>, TermId);

fn construct<'a>(query: &Query<'a>) -> Result<Parts<'a>> {
    let owner = &query.owner;
    let mut store = TermStore::try_new_with_admission(owner).map_err(construction_error)?;
    let mut builder = CountedTermBuilder::new(&mut store, owner).map_err(construction_error)?;
    let mut node_terms = Vec::new();
    let mut bindings = Vec::new();
    let mut bound = DetHashMap::default();
    let mut args = Vec::new();
    allocation::vector(&mut node_terms, query.nodes.len(), owner)?;
    for &(node, ty) in &query.nodes {
        owner.admit(1, 0)?;
        args.clear();
        let children = crate::expr::dag::children(node);
        allocation::vector(&mut args, children.len(), owner)?;
        owner.admit(children.len(), 0)?;
        for child in children {
            let index = query.node_index(child)?;
            args.push(*node_terms.get(index).ok_or(Error::IllTyped)?);
        }
        let term = emit(node, ty, &args, query, &mut builder)?;
        if let ChcExpr::Var(var) = node {
            owner.admit(1, 0)?;
            if !bound.contains_key(&term) {
                allocation::map(&mut bound, 1, owner)?;
                allocation::vector(&mut bindings, 1, owner)?;
                owner.admit(1, 0)?;
                bound.insert(term, ());
                bindings.push(Binding {
                    original: var,
                    term,
                });
            }
        }
        node_terms.push(term);
    }
    let index = query.node_index(query.original)?;
    let root = *node_terms.get(index).ok_or(Error::IllTyped)?;
    builder.finish().map_err(construction_error)?;
    drop(args);
    drop(bound);
    owner.check()?;
    Ok((store, node_terms, bindings, root))
}

fn emit(
    node: &ChcExpr,
    ty: Type,
    args: &[TermId],
    query: &Query<'_>,
    builder: &mut CountedTermBuilder<'_, '_>,
) -> Result<TermId> {
    let owner = &query.owner;
    let term = match node {
        ChcExpr::Bool(value) => builder.boolean(*value),
        ChcExpr::BitVec(value, width) => {
            let value = bitvector_temporary(*value, owner)?;
            builder.bitvector(&value, *width)
        }
        ChcExpr::Var(var) => {
            let sort = sorts::materialize(ty, &query.types, owner)?;
            builder.variable(&var.name, &sort)
        }
        ChcExpr::Op(op, _) => builder.apply(operators::builtin(*op)?, args),
        ChcExpr::ConstArray(..) => {
            let (Type::Array(key, _), [value]) = (ty, args) else {
                return Err(Error::IllTyped);
            };
            owner.admit(1, 0)?;
            let index = sorts::materialize(query.types.get(key)?, &query.types, owner)?;
            builder.constant_array(&index, *value)
        }
        _ => return Err(Error::Unsupported),
    };
    // Temporary values/sorts are disposed before the original fence.
    owner.check()?;
    term.map_err(construction_error)
}

fn bitvector_temporary(value: u128, owner: &CountedAdmission) -> Result<num_bigint::BigInt> {
    // Pinned num-bigint 0.4.6 biguint/convert.rs From<u128> pushes at most
    // four u32 digits or two u64 digits. Vec's first nonzero growth has room
    // for four digits: reserve a fixed 32-byte envelope BEFORE conversion,
    // even for zero. One conversion plus four pushes is five logical units.
    // This temporary is distinct from the builder's separately charged clone.
    owner.admit(5, 4 * std::mem::size_of::<u64>())?;
    Ok(num_bigint::BigInt::from(value))
}

fn construction_error(error: CountedTermError) -> Error {
    match error {
        CountedTermError::Stopped(error) => Error::Stopped(error),
        CountedTermError::Unsupported => Error::Unsupported,
        CountedTermError::InvalidInput | CountedTermError::ReadOnlySnapshot => Error::IllTyped,
    }
}
