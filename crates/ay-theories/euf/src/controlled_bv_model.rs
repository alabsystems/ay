// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Prepared, bounded EUF interpretation DATA under the caller's original ledger.

use crate::solver::EufSolver;
use crate::types::EufModel;
use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::original_query::{QueryError, WorkBudget};
use ay_core::term::{Constant, Symbol, TermData, TermId};
use ay_core::Sort;

mod classes;
mod literal;
mod owned;
mod shape;
mod tables;
#[cfg(test)]
mod tests;

impl EufSolver<'_> {
    /// Extract the prepared Bool/BV1..128/flat-array builtin cohort.
    ///
    /// Borrows the SAME supplied work/copy ledger. No closure rebuild, scope
    /// installation, grant, native solve or model-publication authority occurs.
    /// The complete live arena must be in this closed cohort; unsupported
    /// domains, pending closure and malformed graph state terminally refuse.
    /// Exact flat named store constructors retain legacy function-table DATA;
    /// they do not add array reasoning, preparation or publication authority.
    /// Known array function tables and tracked-value metadata are preserved.
    /// Output is ordinary DATA; its later consumption/clone/disposal is owned
    /// by the caller. Enclosing OriginalAdmission handles callback unwind.
    pub fn try_extract_prepared_bv_model_from_roots_with_budget(
        &self,
        roots: &[TermId],
        work: &mut WorkBudget<'_>,
    ) -> Result<EufModel, QueryError> {
        work.admit(128, 8 * std::mem::size_of::<EufModel>())?;
        shape::prepared(self, work)?;
        work.admit(
            64,
            16 * std::mem::size_of::<ay_core::term::TermStoreSnapshotStamp>(),
        )?;
        let stamp = self.terms.snapshot_stamp();
        let metadata = self.terms.checker_visible_metadata_generation();
        let result = build(self, roots, work);
        let checked = match result {
            Ok(model) => {
                let verified = work.charge(64).and_then(|()| {
                    let current = self.terms.snapshot_stamp();
                    let same = current == stamp
                        && metadata == self.terms.checker_visible_metadata_generation();
                    drop(current);
                    if same {
                        shape::prepared(self, work)
                    } else {
                        Err(work.refuse_exhaustion())
                    }
                });
                match verified {
                    Ok(()) => Ok(model),
                    Err(error) => {
                        drop(model);
                        Err(error)
                    }
                }
            }
            Err(error) => Err(error),
        };
        drop(stamp);
        owned::finish(checked, work)
    }
}

fn build(
    source: &EufSolver<'_>,
    roots: &[TermId],
    work: &mut WorkBudget<'_>,
) -> Result<EufModel, QueryError> {
    shape::arena(source, work)?;
    for &root in roots {
        shape::live(source, root, work)?;
    }
    let terms = source.try_model_terms_from_roots(roots, work)?;
    let result = (|| {
        let rows = classes::prepare(source, &terms, work)?;
        let mut model = EufModel::default();
        let buckets = owned::reserve_table::<(TermId, String)>(terms.len(), work)?;
        model
            .term_values
            .try_reserve(terms.len())
            .map_err(|_| work.refuse_exhaustion())?;
        for index in 0..terms.len() {
            work.charge(32)?;
            let term = terms[index];
            if let Sort::BitVec(bits) = source.terms.sort(term) {
                let rep = shape::representative(source, term, work)?;
                if let Some(value) = classes::value(&rows, bits.width, rep, work)? {
                    let text = literal::bitvector(value, bits.width, work)?;
                    owned::probe(buckets, work)?;
                    model.term_values.insert(term, text);
                }
            }
        }
        tables::build(source, &terms, &mut model, buckets, work)?;
        tables::tracked(source, &mut model, work)?;
        drop(rows);
        Ok(model)
    })();
    drop(terms);
    owned::finish(result, work)
}
