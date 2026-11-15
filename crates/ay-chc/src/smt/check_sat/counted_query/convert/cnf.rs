// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Original-source/CNF handoff, without a solver or evidence verdict.
//!
//! The callback borrows the sealed core ledger and the original source mapping
//! together. Neither can be replaced by a foreign store, a printed formula or
//! a new resource grant. Theory atoms remain obligations for that callback.

use super::*;
use ay_arrays::counted_reads::{CountedArrayReadClosure, Error as ArrayReadError};
use ay_core::{CountedCnf, CountedCnfError};

/// Source identity retained beside the sealed native CNF. Read-only metadata
/// is not model/proof authority; work on it must use `admission()`.
#[derive(Clone, Copy)]
pub(in crate::smt::check_sat) struct Context<'query, 'source> {
    pub(super) query: &'query Query<'source>,
    node_terms: &'query [TermId],
    bindings: &'query [Binding<'source>],
    root: TermId,
    array_reads: Option<&'query CountedArrayReadClosure>,
}

impl<'query, 'source> Context<'query, 'source> {
    pub(in crate::smt::check_sat) fn original(&self) -> &'source ChcExpr {
        self.query.original
    }

    pub(in crate::smt::check_sat) fn root(&self) -> TermId {
        self.root
    }

    pub(in crate::smt::check_sat) fn bindings(&self) -> &[Binding<'source>] {
        self.bindings
    }

    pub(in crate::smt::check_sat) fn census(&self) -> Census {
        self.query.census
    }

    pub(in crate::smt::check_sat) fn admission(&self) -> &CountedAdmission {
        &self.query.owner
    }

    /// Exact pre-seal derived clauses, never additional authored CNF roots.
    /// Free-array and equality obligations remain explicitly unresolved.
    pub(in crate::smt::check_sat) fn array_reads(&self) -> Option<&'query CountedArrayReadClosure> {
        self.array_reads
    }

    pub(in crate::smt::check_sat) fn term_for(&self, source: &ChcExpr) -> Result<TermId> {
        let index = self.query.node_index(source)?;
        self.node_terms.get(index).copied().ok_or(Error::IllTyped)
    }
}

impl<'source> Converted<'source> {
    /// Borrow one exact CNF and original mapping under their existing owner.
    ///
    /// The scope cannot return a borrow of its CNF or replace its store/owner.
    /// Semantic callback errors remain semantic; an observed resource refusal
    /// or caught unwind is terminal on the original owner. CNF scratch is
    /// disposed before the final fence, on both success and error. Returned
    /// data is not accepted evidence and its later disposal remains the
    /// caller's responsibility, followed by `Converted::finish`.
    pub(in crate::smt::check_sat) fn with_cnf<T>(
        &mut self,
        operation: impl for<'scope, 'store> FnOnce(
            &Context<'scope, 'source>,
            &CountedCnf<'store>,
        ) -> Result<T>,
    ) -> Result<T> {
        let owner = self.query.owner.clone();
        owner.admit(1, 0)?;
        // `with_work` shares the existing ledger and panic latch. Wrapping the
        // semantic result in Ok does not reinterpret Unsupported as exhaustion.
        let result = owner.with_work(|_| {
            let arrays = if self.query.census.has_arrays {
                match CountedArrayReadClosure::derive(&mut self.store, &[self.root], &owner) {
                    Ok(closure) => Some(closure),
                    Err(error) => return Ok(Err(Error::from(error))),
                }
            } else {
                None
            };
            let cnf =
                CountedCnf::encode(&mut self.store, &[self.root], &owner).map_err(Error::from);
            let result = match cnf {
                Ok(cnf) => {
                    let context = Context {
                        query: &self.query,
                        node_terms: &self.node_terms,
                        bindings: &self.bindings,
                        root: self.root,
                        array_reads: arrays.as_ref(),
                    };
                    let result = (|| {
                        if let Some(closure) = context.array_reads() {
                            closure.validate_source(cnf.terms())?;
                        }
                        operation(&context, &cnf)
                    })();
                    if let Err(Error::Stopped(error)) = &result {
                        owner.refuse(*error);
                    }
                    match cnf.finish().map_err(Error::from) {
                        Ok(()) => result,
                        Err(error) => Err(error),
                    }
                }
                Err(error) => Err(error),
            };
            // Derived axioms were NOT inserted as authored assertions. Their
            // ledger survives CNF sealing and is disposed only after the CNF.
            match arrays {
                Some(closure) => Ok(match closure.finish().map_err(Error::from) {
                    Ok(()) => result,
                    Err(error) => Err(error),
                }),
                None => Ok(result),
            }
        });
        // Callback captures and CNF storage have been destroyed; the original
        // owner, not a refreshed budget, decides whether anything can escape.
        owner.check()?;
        result.map_err(Error::from)?
    }
}

impl From<ArrayReadError> for Error {
    fn from(error: ArrayReadError) -> Self {
        match error {
            ArrayReadError::Stopped(error) => Self::Stopped(error),
            ArrayReadError::Unsupported => Self::Unsupported,
            ArrayReadError::Invalid => Self::IllTyped,
        }
    }
}

impl From<CountedCnfError> for Error {
    fn from(error: CountedCnfError) -> Self {
        match error {
            CountedCnfError::Stopped(error) => Self::Stopped(error),
            CountedCnfError::Unsupported => Self::Unsupported,
            CountedCnfError::Invalid => Self::IllTyped,
        }
    }
}
