// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Exclusive, caller-owned typed construction without recursive rewriting.

use super::{checked_term_id, next_entry_stamp, StoreRole, NEXT_TERM_ENTRY_STAMP};
use crate::original_query::{CountedAdmission, CountedAdmissionError};
use crate::term::{Constant, Sort, Symbol, TermData, TermEntry, TermId, TermStore};
use std::mem::size_of;

mod index;
mod inspection;
mod literals;
mod numbers;
mod operators;
mod payload;
mod rebuild;
mod ring;
mod sequences;
mod sorts;
pub(super) mod storage;
#[cfg(test)]
mod tests;
mod variables;

pub use operators::CountedBuiltin;
pub use ring::CountedRingBuiltin;

/// Borrow an existing caller's construction ledger, never create an allowance.
///
/// Implementations admit before work/allocation and retain their first refusal
/// across every borrow and retry. This supplies no source, proof or machine
/// authority. Callback implementations must preserve their original controls
/// without holding a mutable borrow or lock across arbitrary callbacks.
pub trait TermConstructionAdmission {
    /// Charge logical work and storage against the original owner's ledger.
    fn admit(&self, work: usize, storage: usize) -> std::result::Result<(), CountedAdmissionError>;
    /// Retain the owner's first refusal and return the effective refusal.
    fn refuse(&self, error: CountedAdmissionError) -> CountedAdmissionError;
    /// Recheck the original owner without charging additional work or storage.
    fn check(&self) -> std::result::Result<(), CountedAdmissionError> {
        self.admit(0, 0)
    }
}

impl TermConstructionAdmission for CountedAdmission {
    fn admit(&self, work: usize, storage: usize) -> std::result::Result<(), CountedAdmissionError> {
        CountedAdmission::admit(self, work, storage)
    }
    fn refuse(&self, error: CountedAdmissionError) -> CountedAdmissionError {
        CountedAdmission::refuse(self, error)
    }
}

/// Versioned LOGICAL work, not a CPU-instruction/hash-probe runtime bound.
///
/// Units include dictionary operations, ordered-search comparisons, inspected
/// payload bytes/edges, actual collision-candidate comparisons and geometric
/// allocation/rehash copies. Opaque allocator and hashbrown probe instructions
/// are not individually counted. Original cancellation/memory remain separate.
pub const COUNTED_TERM_WORK_VERSION: u32 = 2;

/// Closed prime-field operators, separate from the existing BV vocabulary.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CountedFieldBuiltin {
    /// Prime-field addition over two or more operands.
    Add,
    /// Prime-field multiplication over two or more operands.
    Mul,
    /// Prime-field additive negation of one operand.
    Neg,
    /// Prime-field weighted bit sum over two or more operands.
    BitSum,
}

/// Construction refusal is data, never SAT/UNSAT or proof authority.
#[derive(Clone, Copy, Debug, PartialEq, Eq, thiserror::Error)]
pub enum CountedTermError {
    /// The original admission owner retained a terminal refusal.
    #[error(transparent)]
    Stopped(#[from] CountedAdmissionError),
    /// The requested representation is outside the constructor vocabulary.
    #[error("term construction requires a supported Bool/BV/FP/prime-field/array representation")]
    Unsupported,
    /// A sort, operand or identifier is inconsistent with the live arena.
    #[error("term construction received an invalid sort, operand or identity")]
    InvalidInput,
    /// A checker snapshot was supplied where a producer store is required.
    #[error("checker-only snapshots cannot construct producer terms")]
    ReadOnlySnapshot,
}

type Result<T> = std::result::Result<T, CountedTermError>;

/// Reuse the native counted geometric buffer reservation: full replacement
/// capacity and copied prefix are prepaid against the SAME borrowed ledger.
pub fn reserve_counted<T>(
    values: &mut Vec<T>,
    additional: usize,
    owner: &dyn TermConstructionAdmission,
) -> Result<()> {
    owner.check()?;
    storage::reserve(values, additional, owner)?;
    owner.check()?;
    Ok(())
}

/// Reserve native fixed-hasher map storage before allocation/rehash copies.
/// Payload hashing (for example String bytes) remains the caller's borrowed
/// inspection work. This creates no allowance or source/semantic permission.
pub fn reserve_map_counted<K: Eq + std::hash::Hash, V>(
    values: &mut crate::kani_compat::DetHashMap<K, V>,
    additional: usize,
    owner: &dyn TermConstructionAdmission,
) -> Result<()> {
    owner.check()?;
    let needed = values
        .len()
        .checked_add(additional)
        .ok_or_else(|| storage::storage(owner))?;
    if needed > values.capacity() {
        // Native hashbrown replacement buckets/controls plus alignment; the
        // existing counted registry envelope also covers in-place rehash.
        let old = values.allocation_size();
        let added = additional
            .checked_mul(size_of::<(K, V)>().max(1))
            .and_then(|n| n.checked_mul(8))
            .ok_or_else(|| storage::storage(owner))?;
        let bytes = old
            .checked_mul(4)
            .and_then(|n| n.checked_add(added))
            .and_then(|n| n.checked_add(4096))
            .ok_or_else(|| storage::storage(owner))?;
        owner.admit(
            old.checked_add(additional)
                .ok_or_else(|| storage::work(owner))?,
            bytes,
        )?;
        values
            .try_reserve(additional)
            .map_err(|_| storage::storage(owner))?;
    }
    owner.check()?;
    Ok(())
}

/// The SAME native growth plan for UTF-8 storage, without exposing its bytes.
pub fn reserve_string_counted(
    value: &mut String,
    additional: usize,
    owner: &dyn TermConstructionAdmission,
) -> Result<()> {
    owner.check()?;
    storage::reserve_string(value, additional, owner)?;
    owner.check()?;
    Ok(())
}

#[derive(Clone, Copy)]
enum PayloadUse {
    Inspect,
    Copy,
}

impl PayloadUse {
    fn bytes(self, bytes: usize) -> usize {
        match self {
            Self::Inspect => 0,
            Self::Copy => bytes,
        }
    }
}

/// One exclusive construction session, retaining the SAME caller's ledger.
///
/// The one-time ordered index cannot become stale: ordinary store mutation is
/// excluded for this borrow. Every insertion also maintains the native hash
/// buckets/name registry, so dropping this session leaves a normal producer.
/// No preprocessing, folding, query clock, local grant or source/proof authority
/// is introduced. Existing child semantics must still be source-authenticated
/// by the caller; this builder checks live IDs and each new operator's signature.
///
/// Bool/BV/FP data sorts are supported; BV widths are positive u32 values. Nested Bool/BV array sorts use the
/// native snapshot's depth-256 copy-safety envelope; deeper sorts explicitly
/// decline. This is NOT a query-node ceiling. Allocator abort/RSS and caller-owned
/// returned-data disposal are not logical-work guarantees. Use a fresh store
/// when query-only deterministic effort, independent of prior history, is needed.
pub struct CountedTermBuilder<'store, 'owner, O: TermConstructionAdmission = CountedAdmission> {
    store: &'store mut TermStore,
    owner: &'owner O,
    variables: index::Index,
    registry_name_bytes: usize,
}

impl TermStore {
    /// Admit the fixed native bootstrap BEFORE its first allocation. This
    /// creates exactly the normal producer with true/false and one identity
    /// Arc; empty metadata maps allocate nothing. It creates no new grant.
    /// Allocator internals are outside the versioned logical unit definition.
    pub fn try_new_with_admission(owner: &CountedAdmission) -> Result<Self> {
        let bytes = size_of::<Self>()
            .checked_add(32 * size_of::<TermEntry>())
            .and_then(|n| n.checked_add(8192))
            .ok_or_else(|| storage::storage(owner))?;
        owner.admit(1024, bytes)?;
        let store = Self::new();
        owner.check()?;
        Ok(store)
    }
}

impl<'store, 'owner> CountedTermBuilder<'store, 'owner> {
    /// Borrow a live producer using the caller's same counted admission.
    pub fn new(store: &'store mut TermStore, owner: &'owner CountedAdmission) -> Result<Self> {
        Self::with_admission(store, owner)
    }
}

impl<'store, 'owner, O: TermConstructionAdmission> CountedTermBuilder<'store, 'owner, O> {
    /// Immutable native data; this borrow does not create a source/grant owner.
    pub fn terms(&self) -> &TermStore {
        self.store
    }

    /// Intern a canonical residue of the supplied prime-field sort.
    pub fn finite_field(&mut self, value: u32, field: crate::FiniteFieldSort) -> Result<TermId> {
        self.owner.admit(1, 0)?;
        if value >= field.modulus() {
            return Err(CountedTermError::InvalidInput);
        }
        self.publish(
            TermData::Const(Constant::FiniteField { value, field }),
            Sort::FiniteField(field),
        )
    }

    /// Construct a canonical prime-field application after checking arity and sorts.
    pub fn field_apply(
        &mut self,
        operation: CountedFieldBuiltin,
        args: &[TermId],
    ) -> Result<TermId> {
        self.owner.admit(args.len().saturating_add(1), 0)?;
        let Some(first) = args.first().and_then(|id| self.store.terms.get(id.index())) else {
            return Err(CountedTermError::InvalidInput);
        };
        let Sort::FiniteField(field) = first.sort else {
            return Err(CountedTermError::InvalidInput);
        };
        let arity = match operation {
            CountedFieldBuiltin::Neg => args.len() == 1,
            _ => args.len() >= 2,
        };
        if !arity
            || args.iter().any(|id| {
                self.store
                    .terms
                    .get(id.index())
                    .is_none_or(|entry| entry.sort != Sort::FiniteField(field))
            })
        {
            return Err(CountedTermError::InvalidInput);
        }
        let name = match operation {
            CountedFieldBuiltin::Add => "ff.add",
            CountedFieldBuiltin::Mul => "ff.mul",
            CountedFieldBuiltin::Neg => "ff.neg",
            CountedFieldBuiltin::BitSum => "ff.bitsum",
        };
        let term = payload::named(name, args, self.owner)?;
        self.publish(term, Sort::FiniteField(field))
    }
    /// Reuse a borrowed original owner. No balance, deadline or refusal is
    /// copied or reset. The adapter itself is a borrowed pointer, not a grant.
    pub fn with_admission(store: &'store mut TermStore, owner: &'owner O) -> Result<Self> {
        owner.admit(1, 0)?;
        if store.store_role != StoreRole::Producer {
            return Err(CountedTermError::ReadOnlySnapshot);
        }
        let mut builder = Self {
            store,
            owner,
            variables: index::Index::default(),
            registry_name_bytes: 0,
        };
        let result = builder.initialize();
        if let Err(error) = result {
            drop(builder);
            owner.check()?;
            return Err(error);
        }
        owner.check()?;
        Ok(builder)
    }

    fn initialize(&mut self) -> Result<()> {
        // Term dedup reads the store's native hash-cons directly (see
        // `indexed_ids`): every Producer growth path maintains it, so
        // re-inspecting and re-indexing the whole store here only
        // duplicated it at whole-store admission cost. The typed
        // variable side-index has no native equivalent (the names
        // table is last-binding), so it is still seeded per name.
        for (name, (id, _)) in &self.store.names {
            self.owner.admit(
                name.len()
                    .checked_add(1)
                    .ok_or_else(|| storage::work(self.owner))?,
                0,
            )?;
            self.registry_name_bytes = self
                .registry_name_bytes
                .checked_add(name.len())
                .ok_or_else(|| storage::work(self.owner))?;
            self.variables
                .insert(index::name_hash(name), *id, self.owner)?;
        }
        Ok(())
    }

    /// Intern a Boolean constant under the same original admission.
    pub fn boolean(&mut self, value: bool) -> Result<TermId> {
        self.publish(TermData::Const(Constant::Bool(value)), Sort::Bool)
    }

    /// The value must already be canonical unsigned BV data; no modular folding.
    pub fn bitvector(&mut self, value: &num_bigint::BigInt, width: u32) -> Result<TermId> {
        self.owner.admit(1, 0)?;
        if width == 0 || value.sign() == num_bigint::Sign::Minus || value.bits() > u64::from(width)
        {
            return Err(CountedTermError::InvalidInput);
        }
        payload::bigint(value, self.owner, PayloadUse::Copy)?;
        self.publish(
            TermData::Const(Constant::BitVec {
                value: value.clone(),
                width,
            }),
            Sort::bitvec(width),
        )
    }

    /// Copy canonical unsigned data only AFTER the original owner admits its
    /// occupied limbs. No unsigned-to-signed temporary is required from callers.
    pub fn bitvector_unsigned(
        &mut self,
        value: &num_bigint::BigUint,
        width: u32,
    ) -> Result<TermId> {
        self.owner.admit(1, 0)?;
        if width == 0 || value.bits() > u64::from(width) {
            return Err(CountedTermError::InvalidInput);
        }
        payload::unsigned(value, self.owner, PayloadUse::Copy)?;
        self.publish(
            TermData::Const(Constant::BitVec {
                value: num_bigint::BigInt::from(value.clone()),
                width,
            }),
            Sort::bitvec(width),
        )
    }

    /// Assemble FP data from live sign/exponent/trailing-fraction BV terms.
    /// This checks representation only; solver admission remains caller-owned.
    pub fn floating_point_fields(
        &mut self,
        sign: TermId,
        exponent: TermId,
        fraction: TermId,
    ) -> Result<TermId> {
        self.owner.admit(1, 0)?;
        let args = [sign, exponent, fraction];
        let sort = operators::fp_fields(self.store, &args, self.owner)?;
        let term = payload::named("fp", &args, self.owner)?;
        self.publish(term, sort)
    }

    /// Check the closed operator signature and intern its original arguments.
    pub fn apply(&mut self, op: CountedBuiltin, args: &[TermId]) -> Result<TermId> {
        self.owner.admit(1, 0)?;
        let sort = operators::infer(self.store, op, args, self.owner)?;
        let term = operators::term(op, args, self.owner)?;
        self.publish(term, sort)
    }

    /// Intern an array with the supplied index sort and one repeated live value.
    pub fn constant_array(&mut self, index: &Sort, value: TermId) -> Result<TermId> {
        self.owner.admit(1, 0)?;
        let value_sort = self
            .store
            .terms
            .get(value.index())
            .ok_or(CountedTermError::InvalidInput)?;
        let index = sorts::copy(index, self.owner)?;
        let element = sorts::copy(&value_sort.sort, self.owner)?;
        self.owner.admit(1, size_of::<crate::sort::ArraySort>())?;
        let sort = Sort::array(index, element);
        let term = payload::named("const-array", &[value], self.owner)?;
        self.publish(term, sort)
    }

    /// Dispose the session's scratch before the original terminal fence.
    pub fn finish(self) -> Result<()> {
        let owner = self.owner;
        drop(self);
        owner.check()?;
        Ok(())
    }

    fn publish(&mut self, term: TermData, sort: Sort) -> Result<TermId> {
        self.check_generated_head(&term)?;
        let result = self.intern(&term, &sort);
        drop(term);
        drop(sort);
        self.owner.check()?;
        result
    }

    fn check_generated_head(&self, term: &TermData) -> Result<()> {
        // Closed builtin enums do not make an ambiguous Named application a
        // builtin when this store has registered that spelling as a function.
        // Existing opaque source nodes are handled by source-preserving
        // rebuilding, never through this new-builtin publication path.
        if let TermData::App(Symbol::Named(name), _) = term {
            self.owner.admit(name.len(), 0)?;
            if self.store.is_declared_function(name) {
                self.owner.check()?;
                return Err(CountedTermError::InvalidInput);
            }
        }
        Ok(())
    }

    /// Candidate ids for `hash` from the store's native hash-cons,
    /// charged as one admitted bucket probe. Every Producer growth
    /// path (native builders, counted commit, compaction rebuild)
    /// maintains that map, and counted commits insert into it, so it
    /// stays exact for the builder's whole session. Candidates are
    /// still inspected and compared exactly by the callers; the map
    /// only nominates them.
    fn indexed_ids(&self, hash: u64) -> Result<Option<&[TermId]>> {
        self.owner.admit(1, 0)?;
        Ok(self.store.hash_cons.get(&hash).map(Vec::as_slice))
    }

    fn intern(&mut self, term: &TermData, sort: &Sort) -> Result<TermId> {
        payload::visit(term, sort, self.owner, PayloadUse::Inspect)?;
        let hash = TermStore::compute_hash(term);
        if let Some(ids) = self.indexed_ids(hash)? {
            for id in ids {
                self.owner.admit(1, 0)?;
                let entry = self
                    .store
                    .terms
                    .get(id.index())
                    .ok_or(CountedTermError::InvalidInput)?;
                inspection::entry(&entry.term, &entry.sort, self.owner)?;
                payload::visit(term, sort, self.owner, PayloadUse::Inspect)?;
                if &entry.term == term && &entry.sort == sort {
                    return Ok(*id);
                }
            }
        }
        self.insert(hash, term, sort)
    }

    fn insert(&mut self, hash: u64, term: &TermData, sort: &Sort) -> Result<TermId> {
        let id = checked_term_id(self.store.terms.len()).map_err(|_| storage::work(self.owner))?;
        let plan = self.store.counted_bucket_plan(hash, self.owner)?;
        let prepared = self.store.counted_reserve(hash, &plan, self.owner)?;
        payload::visit(term, sort, self.owner, PayloadUse::Copy)?;
        let owned = payload::copy(term, self.owner)?;
        let (owned_sort, sort_has_field) = sorts::copy_with_presence(sort, self.owner)?;
        let heap = TermStore::heap_size(&owned);
        let credit = self
            .store
            .counted_credit(heap, plan.bucket_bytes, self.owner)?;
        self.store
            .controlled_settle(credit, heap, prepared.growth)
            .map_err(|_| storage::storage(self.owner))?;
        let stamp =
            next_entry_stamp(&NEXT_TERM_ENTRY_STAMP).map_err(|_| storage::work(self.owner))?;
        let children = match &owned {
            TermData::App(_, args) => args.len(),
            TermData::Ite(..) => 3,
            TermData::Not(_) => 1,
            _ => 0,
        };
        self.owner.admit(
            children
                .checked_add(1)
                .ok_or_else(|| storage::work(self.owner))?,
            0,
        )?;
        let field_presence = self
            .store
            .entry_field_presence_from_sort(&owned, Some(sort_has_field));
        self.owner.admit(1, 0)?;
        self.store
            .controlled_commit_bucket(
                hash,
                id,
                TermEntry {
                    field_presence,
                    term: owned,
                    sort: owned_sort,
                    stamp,
                },
                prepared,
            )
            .map_err(|_| storage::storage(self.owner))?;
        Ok(id)
    }
}
