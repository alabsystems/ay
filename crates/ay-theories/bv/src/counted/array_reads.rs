// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Scalar leaves for authentic read requests, not unmetered numeric imports.

use super::*;
use ay_arrays::counted_reads::{CountedArrayReadClosure, Error as ArrayError, ScalarSort};

impl<'a> CountedBvEncoder<'a> {
    /// Bind fresh Bool/BV read leaves to this exact source closure and owner.
    ///
    /// This constructor does NOT assert the closure's theory clauses, discharge
    /// its unresolved congruence/extensionality obligations, or grant a checked
    /// proof/model credential. The retained closure must accompany later rows.
    /// Ordinary `new` continues to reject every array read.
    pub fn with_array_reads(
        terms: &'a TermStore,
        closure: &'a CountedArrayReadClosure,
    ) -> Result<Self> {
        closure.validate_source(terms).map_err(array_error)?;
        let owner = closure.admission().clone();
        let mut encoder = Self::new(terms, &owner)?;
        encoder.array_reads = Some(closure);
        // Retain ownership outside the entire with_work entry/seed/disposal
        // boundary: an opaque panic payload may itself panic during cleanup.
        let result = cleanup::caught(&owner, || {
            owner.with_work(|_| Ok(seed(&mut encoder, closure)))?
        });
        if let Err(error) = result {
            let error = encoder.refuse(error);
            return Err(encoder.finish().err().unwrap_or(error));
        }
        if let Err(error) = cleanup::check(&encoder) {
            return Err(encoder.finish().err().unwrap_or(error));
        }
        Ok(encoder)
    }

    /// Borrow the same source/derivation ledger, including all unresolved work.
    pub fn array_read_obligations(&self) -> Option<&'a CountedArrayReadClosure> {
        self.array_reads
    }
}

fn seed(encoder: &mut CountedBvEncoder<'_>, closure: &CountedArrayReadClosure) -> Result<()> {
    for read in closure.reads() {
        encoder.owner.admit(1, 0)?;
        match read.element_sort {
            ScalarSort::Bool => {
                let literal = encoder.solver.fresh_var();
                if !memory::map(&mut encoder.solver.bool_to_var, &encoder.solver.encoding) {
                    return stopped(encoder);
                }
                encoder.solver.bool_to_var.insert(read.select, literal);
            }
            ScalarSort::BitVec(width) => {
                let bits = encoder.solver.counted_fresh_bits(width as usize);
                encoder.check()?;
                if !memory::map(&mut encoder.solver.term_to_bits, &encoder.solver.encoding) {
                    return stopped(encoder);
                }
                encoder.solver.term_to_bits.insert(read.select, bits);
            }
        }
        // Only the closure's immutable exact select IDs bypass the scalar DAG
        // walk. An unlisted read, array equality, or declared lookalike refuses.
        if !memory::set(&mut encoder.prepared, &encoder.solver.encoding) {
            return stopped(encoder);
        }
        encoder.prepared.insert(read.select);
        encoder.check()?;
    }
    encoder.check()
}

fn stopped<T>(encoder: &CountedBvEncoder<'_>) -> Result<T> {
    encoder.owner.check()?;
    Err(CountedBvError::Invalid)
}

fn array_error(error: ArrayError) -> CountedBvError {
    match error {
        ArrayError::Stopped(error) => CountedBvError::Stopped(error),
        ArrayError::Unsupported => CountedBvError::Unsupported("array declaration provenance"),
        ArrayError::Invalid => CountedBvError::Invalid,
    }
}
