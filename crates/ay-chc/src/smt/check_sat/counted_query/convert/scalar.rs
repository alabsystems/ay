// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Actual paid Boolean/BV attachment, not a public counted solver.
//!
//! Both encoders retain one exact store and owner. Every canonical Boolean
//! variable is linked, including variables occurring inside BV ITEs and the
//! synthetic distinct bridge. Borrowed source and gate ledgers remain live;
//! neither imported numeric maps nor a mutable encoder escape is offered.

use super::cnf::Context;
use super::*;
use ay_bv::{CountedBvEncoder, CountedBvError};
use ay_core::CountedCnf;

mod arrays;
mod attachment;
mod candidate;
mod cleanup;
mod memory;
#[cfg(test)]
mod tests;

/// Exact allocation-free scalar data; wider replay is explicitly unsupported.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(in crate::smt::check_sat) enum ScalarValue {
    Bool(bool),
    BitVec(u128, u32),
}

/// Origin indexes name the retained encoders, not independently checked proofs.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(in crate::smt::check_sat) enum RowOrigin {
    Boolean(usize),
    Bitvector(usize),
    Link {
        index: usize,
        reverse: bool,
    },
    /// Exact closure step; still requires its native checked proof premises.
    ArrayRead(usize),
}

pub(in crate::smt::check_sat) struct AttachedRow {
    literals: Vec<i32>,
    origin: RowOrigin,
}

impl AttachedRow {
    pub(in crate::smt::check_sat) fn literals(&self) -> &[i32] {
        &self.literals
    }

    pub(in crate::smt::check_sat) fn origin(&self) -> RowOrigin {
        self.origin
    }
}

#[derive(Debug, Clone, Copy)]
struct Link {
    source: TermId,
    boolean: i32,
    bitvector: i32,
}

/// Only the private attachment constructor can bind these three namespaces.
/// Array rows keep their exact derivations and unresolved obligations. The
/// circuit itself never discharges proof premises or free-array completion.
pub(in crate::smt::check_sat) struct ScalarEncoding<'scope, 'source> {
    context: Context<'scope, 'source>,
    cnf: &'scope CountedCnf<'scope>,
    bv: CountedBvEncoder<'scope>,
    rows: Vec<AttachedRow>,
    links: Vec<Link>,
    offset: u32,
    num_vars: u32,
}

impl<'source> Converted<'source> {
    /// Execute with one authentic, immutable source/CNF/BV attachment.
    /// The callback cannot return a borrowed handle or replace its source.
    /// No SAT search, UNSAT certificate, or public model is returned here.
    pub(in crate::smt::check_sat) fn with_scalar_encoding<T>(
        &mut self,
        operation: impl for<'scope> FnOnce(&ScalarEncoding<'scope, 'source>) -> Result<T>,
    ) -> Result<T> {
        self.with_cnf(|context, cnf| {
            let attached = ScalarEncoding::attach(*context, cnf)?;
            // The encoder stays OUTSIDE the unwind boundary, so retained
            // callback destruction can only happen during explicit finish.
            let result = cleanup::invoke(context.admission(), || operation(&attached));
            if let Err(Error::Stopped(error)) = &result {
                context.admission().refuse(*error);
            }
            attached.finish()?;
            result
        })
    }
}

impl ScalarEncoding<'_, '_> {
    pub(in crate::smt::check_sat) fn rows(&self) -> &[AttachedRow] {
        &self.rows
    }

    pub(in crate::smt::check_sat) fn num_vars(&self) -> u32 {
        self.num_vars
    }

    pub(in crate::smt::check_sat) fn source_cnf(&self) -> &CountedCnf<'_> {
        self.cnf
    }

    /// Immutable gate records remain available to the later proof producer.
    pub(in crate::smt::check_sat) fn bitvector_encoding(&self) -> &CountedBvEncoder<'_> {
        &self.bv
    }

    pub(in crate::smt::check_sat) fn admission(&self) -> &CountedAdmission {
        self.context.admission()
    }

    /// Every attached array row still requires independently admitted premises.
    /// Includes const-select and ITE composition, never mislabeled raw axioms.
    pub(in crate::smt::check_sat) fn array_read_obligations(
        &self,
    ) -> Option<&ay_arrays::counted_reads::CountedArrayReadClosure> {
        self.bv.array_read_obligations()
    }

    fn finish(self) -> Result<()> {
        let owner = self.context.admission().clone();
        let Self {
            bv, rows, links, ..
        } = self;
        // Variable-length destruction was prepaid at allocation/insertion.
        drop(rows);
        drop(links);
        let result = bv.finish().map_err(bv_error);
        owner.check()?;
        result
    }
}

fn bv_error(error: CountedBvError) -> Error {
    match error {
        CountedBvError::Stopped(error) => Error::Stopped(error),
        CountedBvError::Unsupported(_) => Error::Unsupported,
        CountedBvError::Invalid => Error::IllTyped,
    }
}
