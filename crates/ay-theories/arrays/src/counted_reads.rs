// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Query-local McCarthy read closure over raw Bool/BV arrays.
//!
//! Uses the same ROW1/ROW2 semantics as the ordinary array kernel, without
//! assuming preprocessing removed identical-index stores. Both guards and
//! every source identity are retained. This is a paid theory-lemma producer,
//! NOT SAT, a checked proof, array-equality completion or a publishable model.
//! See McCarthy, "Towards a Mathematical Science of Computation" (1962).

use ay_core::kani_compat::DetHashMap;
use ay_core::original_query::{CountedAdmission, CountedAdmissionError};
use ay_core::term::{CountedBuiltin, CountedTermBuilder, CountedTermError, TermStoreSnapshotStamp};
use ay_core::{Sort, TermData, TermId, TermStore};

mod expand;
mod memory;
mod provenance;
mod scan;
#[cfg(test)]
mod tests;

/// Logical visits, dictionary operations, element moves and cumulative bytes.
/// This does not count opaque allocator instructions or individual hash probes.
pub const COUNTED_ARRAY_READ_WORK_VERSION: u32 = 3;

/// A refused closure is never source SAT/UNSAT authority.
#[derive(Clone, Copy, Debug, PartialEq, Eq, thiserror::Error)]
pub enum Error {
    /// The original owner has refused work, storage or external controls.
    #[error(transparent)]
    Stopped(#[from] CountedAdmissionError),
    /// This stage cannot account for the source representation.
    #[error("unsupported counted array-read representation")]
    Unsupported,
    /// A source identity or signature is invalid.
    #[error("invalid counted array-read source")]
    Invalid,
}
type Result<T> = std::result::Result<T, Error>;

impl From<CountedTermError> for Error {
    fn from(error: CountedTermError) -> Self {
        match error {
            CountedTermError::Stopped(error) => Self::Stopped(error),
            CountedTermError::Unsupported => Self::Unsupported,
            CountedTermError::InvalidInput | CountedTermError::ReadOnlySnapshot => Self::Invalid,
        }
    }
}

/// Exact nonrecursive scalar sort, without width truncation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ScalarSort {
    /// Boolean indices/elements retain their two-element domain.
    Bool,
    /// A positive native bitvector width.
    BitVec(u32),
}

/// One exact native read; the two IDs form the query-local memoization key.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Read {
    /// Original array expression.
    pub array: TermId,
    /// Exact original read index, never a sampled numeric index.
    pub index: TermId,
    /// Raw typed select, retained even at an identical store index.
    pub select: TermId,
    /// Source index sort.
    pub index_sort: ScalarSort,
    /// Source element sort.
    pub element_sort: ScalarSort,
}

/// Exact producer origin, not a request to trust an arbitrary axiom label.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Derivation {
    /// Same exact free array, with the index-equality guard retained.
    /// This is the ordinary select congruence law, not array extensionality.
    FreeReadCongruence {
        /// Exact free-array source identity shared by both reads.
        array: TermId,
        /// First exact read in deterministic discovery order.
        left_read: usize,
        /// Second exact read in that same closure.
        right_read: usize,
    },
    /// Guarded hit of a store, including syntactically identical indices.
    Row1 {
        /// Index of the exact source read.
        read: usize,
        /// Original store constructor.
        store: TermId,
        /// Original store index.
        write_index: TermId,
        /// Original stored value.
        value: TermId,
    },
    /// Guarded miss linked to the same base read at the same query index.
    Row2 {
        /// Index of the exact source read.
        read: usize,
        /// Original store constructor.
        store: TermId,
        /// Read of the store's base at the SAME query index.
        base_read: usize,
    },
    /// Select of a genuine constant-array constructor, not default(A).
    ConstFill {
        /// Index of the exact source read.
        read: usize,
        /// Original constant-array constructor.
        array: TermId,
        /// Exact fill value.
        fill: TermId,
    },
    /// Then branch of an array-valued ITE, preserving the source condition.
    IteThen {
        /// Index of the original array-ITE read.
        read: usize,
        /// Original array-ITE constructor.
        array: TermId,
        /// Original Boolean branch condition.
        condition: TermId,
        /// The then-array read at the SAME query index.
        branch_read: usize,
        /// Raw (= array then-array), for IteBranchProjection.
        array_equality: TermId,
        /// Raw negation of array_equality, for select congruence.
        not_array_equality: TermId,
    },
    /// Else branch of that same original array ITE.
    IteElse {
        /// Index of the original array-ITE read.
        read: usize,
        /// Original array-ITE constructor.
        array: TermId,
        /// Original Boolean branch condition.
        condition: TermId,
        /// The else-array read at the SAME query index.
        branch_read: usize,
        /// Raw (= array else-array), for IteBranchProjection.
        array_equality: TermId,
        /// Raw negation of array_equality, for select congruence.
        not_array_equality: TermId,
    },
}

/// Native Boolean clause and exact derivation. Never an authored root.
#[derive(Clone, Copy, Debug)]
pub struct Step {
    origin: Derivation,
    literals: [TermId; 2],
    len: usize,
}

impl Step {
    /// The exact source rule and its query-local read links.
    pub fn derivation(&self) -> Derivation {
        self.origin
    }
    /// One/two raw Boolean literal terms, retaining the original guard.
    pub fn literals(&self) -> &[TermId] {
        &self.literals[..self.len]
    }
}

/// Obligations intentionally NOT discharged by this read-closure stage.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Unresolved {
    /// Requires total model completion. Generated congruence is still DATA,
    /// not an independently checked proof or an accepted array model.
    FreeRead {
        /// Exact unresolved read index.
        read: usize,
    },
    /// Array equality/disequality needs its own equality/extensionality work.
    ArrayRelation {
        /// Exact original equality or distinct expression.
        source: TermId,
        /// Original left array operand.
        left: TermId,
        /// Original right array operand.
        right: TermId,
    },
}

/// Authentic append-only source-bound derivations under one sticky owner.
///
/// Numeric records are read-only data. Only this producer constructs the seal;
/// validate_source rejects foreign stores, rollback and compaction. Appending
/// later CNF proof terms is allowed. Relevant declaration-registry changes are
/// checked separately: the physical stamp does not cover their semantics.
/// No checked-proof/model credential exists.
#[must_use = "finish the closure under its original owner before publishing later results"]
pub struct CountedArrayReadClosure {
    owner: CountedAdmission,
    source: TermStoreSnapshotStamp,
    primitives: provenance::Primitives,
    roots: Vec<TermId>,
    reads: Vec<Read>,
    steps: Vec<Step>,
    unresolved: Vec<Unresolved>,
}

impl CountedArrayReadClosure {
    /// Materialize the actual reachable read closure before a CNF store seals.
    /// Partial failure may append terms, but never asserts or changes originals.
    pub fn derive(
        terms: &mut TermStore,
        roots: &[TermId],
        owner: &CountedAdmission,
    ) -> Result<Self> {
        owner.admit(1, 0)?;
        let result = owner.with_work(|_| Ok(derive(terms, roots, owner)));
        owner.check()?;
        result.map_err(Error::from)?
    }
    /// Exact authored roots, unchanged and never augmented with derived facts.
    pub fn roots(&self) -> &[TermId] {
        &self.roots
    }
    /// Memoized read requests, in deterministic first-discovery order.
    pub fn reads(&self) -> &[Read] {
        &self.reads
    }
    /// Actual emitted source clauses, awaiting independent proof admission.
    pub fn steps(&self) -> &[Step] {
        &self.steps
    }
    /// Explicitly incomplete obligations; emptiness is not solver authority.
    pub fn unresolved(&self) -> &[Unresolved] {
        &self.unresolved
    }
    /// Original cumulative owner, without a new grant or clock.
    pub fn admission(&self) -> &CountedAdmission {
        &self.owner
    }
    /// Authenticate the original physical source universe after append-only growth.
    pub fn validate_source(&self, terms: &TermStore) -> Result<()> {
        self.owner.admit(1, 0)?;
        if !self.source.is_append_only_prefix_of(terms) {
            return Err(Error::Invalid);
        }
        self.primitives.validate(terms, &self.owner)?;
        self.owner.check()?;
        Ok(())
    }
    /// Dispose every owned table/record before the original final fence.
    pub fn finish(self) -> Result<()> {
        let owner = self.owner.clone();
        drop(self);
        owner.check()?;
        Ok(())
    }
}

fn derive(
    terms: &mut TermStore,
    roots: &[TermId],
    owner: &CountedAdmission,
) -> Result<CountedArrayReadClosure> {
    let scanned = scan::source(terms, roots, owner)?;
    let mut copied_roots = Vec::new();
    memory::reserve(&mut copied_roots, roots.len(), owner)?;
    copied_roots.extend_from_slice(roots);
    let expanded = expand::run(terms, &scanned, owner)?;
    let scan::Source {
        unresolved,
        shapes,
        requests,
        primitives,
    } = scanned;
    drop(shapes);
    drop(requests);
    let expand::Expanded { reads, steps, free } = expanded;
    let mut unresolved = unresolved;
    for item in free {
        memory::push(&mut unresolved, item, owner)?;
    }
    owner.admit(1, 0)?;
    let closure = CountedArrayReadClosure {
        owner: owner.clone(),
        source: terms.snapshot_stamp(),
        primitives,
        roots: copied_roots,
        reads,
        steps,
        unresolved,
    };
    owner.check()?;
    Ok(closure)
}
