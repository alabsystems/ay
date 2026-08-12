// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Capacity-based memory accounting for term stores.

use std::mem::size_of;

use super::*;

const MAX_ACCOUNTED_SORT_DEPTH: usize = 128;
const CLONED_ROLLBACK_IDENTITY_BYTES: usize = 64;

impl TermStore {
    /// Per-instance term memory usage in bytes (approximate).
    ///
    /// Unlike `global_term_bytes()`, this counts only terms interned by THIS
    /// `TermStore` instance. Use this for per-solver memory budgets that must
    /// not interfere with other concurrent solver instances (#6563).
    pub fn instance_term_bytes(&self) -> usize {
        self.instance_term_bytes
    }

    /// Accurate memory footprint of THIS `TermStore` instance (bytes).
    ///
    /// Unlike `instance_term_bytes()`, which incrementally tracks per-element
    /// allocations and can undercount by up to 2x (missing Vec spare capacity,
    /// HashMap table overhead, and BTreeMap node overhead), this method queries
    /// actual container capacities to compute a more precise estimate.
    pub fn true_memory_bytes(&self) -> usize {
        let terms_heap = self.terms.capacity() * size_of::<TermEntry>();
        #[cfg(not(kani))]
        let hash_cons_table = self.hash_cons.allocation_size();
        #[cfg(kani)]
        let hash_cons_table = self.hash_cons.len() * 64;
        #[cfg(not(kani))]
        let names_table = self.names.allocation_size();
        #[cfg(kani)]
        let names_table = self.names.len() * 64;

        terms_heap
            + hash_cons_table
            + self.bucket_capacity_bytes
            + names_table
            + self.heap_data_bytes
    }

    /// Upper-bound the heap allocations duplicated by [`Self::clone`].
    ///
    /// Unlike [`Self::true_memory_bytes`], this includes every cloned owning
    /// side table and all nested [`Sort`] payloads. Arithmetic and traversal
    /// are bounded by `limit`; `None` means the clone must be declined.
    #[must_use]
    pub fn diagnostic_clone_memory_bytes(&self, limit: usize) -> Option<usize> {
        #[cfg(kani)]
        {
            let _ = limit;
            None
        }
        #[cfg(not(kani))]
        {
            self.diagnostic_clone_memory_bytes_native(limit)
        }
    }

    #[cfg(not(kani))]
    fn diagnostic_clone_memory_bytes_native(&self, limit: usize) -> Option<usize> {
        let mut bytes = 0;
        add_product(
            &mut bytes,
            self.terms.capacity(),
            size_of::<TermEntry>(),
            limit,
        )?;
        for allocation in [
            self.hash_cons.allocation_size(),
            self.bucket_capacity_bytes,
            self.names.allocation_size(),
            self.not_cache.allocation_size(),
            self.no_mbqi.allocation_size(),
            self.skolem_symbols.allocation_size(),
            self.skolem_choice.allocation_size(),
            self.quantifier_id.allocation_size(),
            self.skolem_id.allocation_size(),
            self.quantifier_weight.allocation_size(),
            self.quantifier_no_patterns.allocation_size(),
            CLONED_ROLLBACK_IDENTITY_BYTES,
        ] {
            add(&mut bytes, allocation, limit)?;
        }
        self.add_clone_payload_bytes(&mut bytes, limit)?;
        Some(bytes)
    }

    #[cfg(not(kani))]
    fn add_clone_payload_bytes(&self, bytes: &mut usize, limit: usize) -> Option<()> {
        for entry in &self.terms {
            // Do not trust the incremental heap ledger here: checker-only
            // stores built by `from_entries` deliberately leave it at zero.
            add(bytes, Self::heap_size(&entry.term), limit)?;
            add_sort(&entry.sort, bytes, limit, 0)?;
            if let TermData::Forall(vars, ..) | TermData::Exists(vars, ..) = &entry.term {
                for (_, sort) in vars {
                    add_sort(sort, bytes, limit, 0)?;
                }
            }
        }
        for (name, (_, sort)) in &self.names {
            add(bytes, name.capacity(), limit)?;
            add_sort(sort, bytes, limit, 0)?;
        }
        for name in &self.skolem_symbols {
            add(bytes, name.capacity(), limit)?;
        }
        for choice in self.skolem_choice.values() {
            add(bytes, choice.binder.capacity(), limit)?;
            add_sort(&choice.sort, bytes, limit, 0)?;
        }
        for name in self.quantifier_id.values().chain(self.skolem_id.values()) {
            add(bytes, name.capacity(), limit)?;
        }
        for patterns in self.quantifier_no_patterns.values() {
            add_product(bytes, patterns.capacity(), size_of::<TermId>(), limit)?;
        }
        Some(())
    }

    /// Check if THIS instance has exceeded a given memory budget.
    pub fn instance_memory_exceeded(&self, limit: usize) -> bool {
        let cached_at = self.true_memory_cache_at.get();
        let delta = self.instance_term_bytes.saturating_sub(cached_at);
        if delta >= TRUE_MEMORY_RECOMPUTE_DELTA || self.true_memory_cache.get() == 0 {
            let fresh = self.true_memory_bytes();
            self.true_memory_cache.set(fresh);
            self.true_memory_cache_at.set(self.instance_term_bytes);
            fresh > limit
        } else {
            self.true_memory_cache.get() > limit
        }
    }
}

fn add_sort(sort: &Sort, bytes: &mut usize, limit: usize, depth: usize) -> Option<()> {
    if depth > MAX_ACCOUNTED_SORT_DEPTH {
        return None;
    }
    match sort {
        Sort::Array(array) => {
            add(bytes, size_of::<crate::sort::ArraySort>(), limit)?;
            add_sort(&array.index_sort, bytes, limit, depth + 1)?;
            add_sort(&array.element_sort, bytes, limit, depth + 1)
        }
        Sort::Seq(element) => {
            add(bytes, size_of::<Sort>(), limit)?;
            add_sort(element, bytes, limit, depth + 1)
        }
        Sort::Uninterpreted(name) | Sort::TypeVar(name) | Sort::FiniteDomain(name, _) => {
            add(bytes, name.capacity(), limit)
        }
        Sort::Datatype(datatype) => {
            add(bytes, datatype.name.capacity(), limit)?;
            add_product(
                bytes,
                datatype.constructors.capacity(),
                size_of::<crate::sort::DatatypeConstructor>(),
                limit,
            )?;
            for constructor in &datatype.constructors {
                add(bytes, constructor.name.capacity(), limit)?;
                add_product(
                    bytes,
                    constructor.fields.capacity(),
                    size_of::<crate::sort::DatatypeField>(),
                    limit,
                )?;
                for field in &constructor.fields {
                    add(bytes, field.name.capacity(), limit)?;
                    add_sort(&field.sort, bytes, limit, depth + 1)?;
                }
            }
            Some(())
        }
        Sort::Bool
        | Sort::Int
        | Sort::Real
        | Sort::BitVec(_)
        | Sort::String
        | Sort::RegLan
        | Sort::FloatingPoint(..)
        | Sort::Char => Some(()),
    }
}

fn add(bytes: &mut usize, amount: usize, limit: usize) -> Option<()> {
    *bytes = bytes.checked_add(amount)?;
    (*bytes <= limit).then_some(())
}

fn add_product(bytes: &mut usize, count: usize, width: usize, limit: usize) -> Option<()> {
    add(bytes, count.checked_mul(width)?, limit)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn clone_bound(store: &TermStore) -> usize {
        store
            .diagnostic_clone_memory_bytes(usize::MAX)
            .expect("small populated store has a bounded clone")
    }

    fn assert_bound_grows(store: &mut TermStore, mutate: impl FnOnce(&mut TermStore)) {
        let before = clone_bound(store);
        mutate(store);
        assert!(clone_bound(store) > before);
    }

    #[test]
    fn diagnostic_clone_accounting_covers_every_side_table_and_nested_sort() {
        let mut store = TermStore::new();
        let nested = Sort::Array(Box::new(crate::sort::ArraySort::new(
            Sort::Uninterpreted("index-sort-with-owned-storage".repeat(8)),
            Sort::Seq(Box::new(Sort::TypeVar("element-sort".repeat(8)))),
        )));
        let id = store.mk_var("clone-accounting-witness", nested.clone());
        let legacy = store.true_memory_bytes();
        assert!(clone_bound(&store) > legacy);

        assert_bound_grows(&mut store, |store| {
            store.not_cache.insert(id, id);
        });
        assert_bound_grows(&mut store, |store| {
            store.no_mbqi.insert(id);
        });
        assert_bound_grows(&mut store, |store| {
            store.skolem_symbols.insert("skolem-symbol".repeat(256));
        });
        assert_bound_grows(&mut store, |store| {
            store.skolem_choice.insert(
                id,
                SkolemChoice {
                    binder: "choice-binder".repeat(256),
                    sort: nested,
                    body: id,
                },
            );
        });
        assert_bound_grows(&mut store, |store| {
            store.quantifier_id.insert(id, "qid".repeat(1024));
        });
        assert_bound_grows(&mut store, |store| {
            store.skolem_id.insert(id, "skid".repeat(1024));
        });
        assert_bound_grows(&mut store, |store| {
            store.quantifier_weight.insert(id, 42);
        });
        assert_bound_grows(&mut store, |store| {
            store.quantifier_no_patterns.insert(id, vec![id; 1024]);
        });

        let bound = clone_bound(&store);
        assert_eq!(store.diagnostic_clone_memory_bytes(bound), Some(bound));
        assert_eq!(store.diagnostic_clone_memory_bytes(bound - 1), None);
    }

    #[test]
    fn diagnostic_clone_accounting_scans_from_entries_payload() {
        let payload = "checker-only-owned-payload".repeat(16 * 1024);
        let payload_bytes = payload.capacity();
        let store = TermStore::from_entries(
            vec![(TermData::Const(Constant::String(payload)), Sort::String)],
            None,
            None,
            0,
        );
        assert_eq!(store.heap_data_bytes, 0);
        let bound = clone_bound(&store);
        assert!(bound >= payload_bytes);
        assert_eq!(store.diagnostic_clone_memory_bytes(bound - 1), None);
    }

    #[test]
    fn diagnostic_clone_accounting_declines_overdeep_sort() {
        let mut sort = Sort::Bool;
        for _ in 0..=MAX_ACCOUNTED_SORT_DEPTH {
            sort = Sort::Seq(Box::new(sort));
        }
        let mut store = TermStore::new();
        let _ = store.mk_var("deep-sort", sort);
        assert_eq!(store.diagnostic_clone_memory_bytes(usize::MAX), None);
    }
}
