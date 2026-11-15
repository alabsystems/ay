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
        let terms_heap = self.terms.capacity().saturating_mul(size_of::<TermEntry>());
        let hash_cons_table = self.hash_cons.allocation_size();
        let names_table = self.names.allocation_size();

        terms_heap
            .saturating_add(hash_cons_table)
            .saturating_add(self.bucket_capacity_bytes)
            .saturating_add(names_table)
            .saturating_add(self.heap_data_bytes)
    }

    /// Upper-bound the heap allocations duplicated by [`Self::clone`].
    ///
    /// Unlike [`Self::true_memory_bytes`], this includes every cloned owning
    /// side table and all nested [`Sort`] payloads. Arithmetic and traversal
    /// are bounded by `limit`; `None` means the clone must be declined.
    #[must_use]
    pub fn diagnostic_clone_memory_bytes(&self, limit: usize) -> Option<usize> {
        self.clone_memory_bytes(limit, None).map(|plan| plan.bytes)
    }

    /// Clone the complete store under the caller's cumulative envelope.
    ///
    /// Reuses the full clone accountant, including owning side tables and
    /// nested sorts. Every inspection and allocation is charged before the
    /// ordinary clone begins. The callback supplies no fresh allowance and
    /// must retain its first refusal across this and later operations.
    pub fn clone_with_progress(
        &self,
        progress: &mut dyn FnMut(usize, usize) -> bool,
    ) -> Result<Self, TermSnapshotError> {
        let plan = self
            .clone_memory_bytes(usize::MAX, Some(&mut *progress))
            .ok_or(TermSnapshotError::ResourceLimit)?;
        if !progress(0, 0) {
            return Err(TermSnapshotError::ResourceLimit);
        }
        let (_, memo_bytes) = self
            .strict_bv_semantics
            .clone_memory_usage(plan.memo_entries)
            .ok_or(TermSnapshotError::ResourceLimit)?;
        if memo_bytes > plan.memo_bytes {
            return Err(TermSnapshotError::ResourceLimit);
        }
        let cloned = self.clone();
        if !progress(0, 0) {
            return Err(TermSnapshotError::ResourceLimit);
        }
        Ok(cloned)
    }

    fn clone_memory_bytes(
        &self,
        limit: usize,
        progress: Option<&mut dyn FnMut(usize, usize) -> bool>,
    ) -> Option<ClonePlan> {
        let mut account = CloneAccounting {
            bytes: 0,
            limit,
            progress,
        };
        account.add_product(self.terms.capacity(), size_of::<TermEntry>())?;
        for allocation in [
            self.hash_cons.allocation_size(),
            self.names.allocation_size(),
            self.not_cache.allocation_size(),
            self.no_mbqi.allocation_size(),
            self.skolem_symbols.allocation_size(),
            self.skolem_choice.allocation_size(),
            self.divmod_purification.allocation_size(),
            self.quantifier_id.allocation_size(),
            self.skolem_id.allocation_size(),
            self.quantifier_weight.allocation_size(),
            self.quantifier_no_patterns.allocation_size(),
            self.constructor_fields.allocation_size(),
            self.datatype_field_sorts.allocation_size(),
            self.declared_functions.allocation_size(),
            CLONED_ROLLBACK_IDENTITY_BYTES,
        ] {
            account.add(allocation)?;
        }
        self.add_clone_payload_bytes(&mut account)?;
        let count = self.strict_bv_semantics.clone_entry_count()?;
        // Pay both this census and the final pre-clone validation now. The
        // final validation has no callback between its guard and cloning.
        account.work(count.checked_mul(2)?)?;
        let (memo_entries, memo_bytes) = self.strict_bv_semantics.clone_memory_usage(count)?;
        account.add(memo_bytes)?;
        Some(ClonePlan {
            bytes: account.bytes,
            memo_entries,
            memo_bytes,
        })
    }

    fn add_clone_payload_bytes(&self, account: &mut CloneAccounting<'_>) -> Option<()> {
        for bucket in self.hash_cons.values() {
            account.add_product(bucket.capacity(), size_of::<TermId>())?;
        }
        for entry in &self.terms {
            if let Some(progress) = account.progress.as_mut() {
                // Prepay the existing payload inspector before heap_size's
                // binder/trigger walks; storage is charged by the accountant.
                snapshot::meter_entry(&entry.term, &entry.sort, &mut |work, _| progress(work, 0))
                    .ok()?;
            }
            // Do not trust the incremental heap ledger here: checker-only
            // stores built by `from_entries` deliberately leave it at zero.
            account.add(Self::heap_size(&entry.term))?;
            account.add_sort(&entry.sort, MAX_ACCOUNTED_SORT_DEPTH)?;
            if let TermData::Forall(vars, ..) | TermData::Exists(vars, ..) = &entry.term {
                for (_, sort) in vars {
                    account.add_sort(sort, MAX_ACCOUNTED_SORT_DEPTH)?;
                }
            }
        }
        for (name, (_, sort)) in &self.names {
            account.add(name.capacity())?;
            account.add_sort(sort, MAX_ACCOUNTED_SORT_DEPTH)?;
        }
        for name in &self.skolem_symbols {
            account.add(name.capacity())?;
        }
        for choice in self.skolem_choice.values() {
            account.add(choice.binder.capacity())?;
            account.add_sort(&choice.sort, MAX_ACCOUNTED_SORT_DEPTH)?;
        }
        for name in self.quantifier_id.values().chain(self.skolem_id.values()) {
            account.add(name.capacity())?;
        }
        for patterns in self.quantifier_no_patterns.values() {
            account.add_product(patterns.capacity(), size_of::<TermId>())?;
        }
        for (name, fields) in &self.constructor_fields {
            account.add(name.capacity())?;
            account.add_product(fields.capacity(), size_of::<String>())?;
            for field in fields {
                account.add(field.capacity())?;
            }
        }
        for (name, sorts) in &self.datatype_field_sorts {
            account.add(name.capacity())?;
            account.add_product(sorts.capacity(), size_of::<Sort>())?;
            for sort in sorts {
                account.add_sort(sort, MAX_ACCOUNTED_SORT_DEPTH)?;
            }
        }
        for name in &self.declared_functions {
            account.add(name.capacity())?;
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

struct ClonePlan {
    bytes: usize,
    memo_entries: usize,
    memo_bytes: usize,
}

struct CloneAccounting<'a> {
    bytes: usize,
    limit: usize,
    progress: Option<&'a mut dyn FnMut(usize, usize) -> bool>,
}

impl CloneAccounting<'_> {
    fn work(&mut self, work: usize) -> Option<()> {
        if let Some(progress) = self.progress.as_mut() {
            if !progress(work, 0) {
                return None;
            }
        }
        Some(())
    }

    // Retain the existing diagnostic copy-safety depth bound.
    fn add_sort(&mut self, sort: &Sort, depth_left: usize) -> Option<()> {
        if let Some(progress) = self.progress.as_mut() {
            if !progress(1, 0) {
                return None;
            }
        }
        match sort {
            Sort::Array(array) => {
                self.add(size_of::<crate::sort::ArraySort>())?;
                let depth_left = depth_left.checked_sub(1)?;
                self.add_sort(&array.index_sort, depth_left)?;
                self.add_sort(&array.element_sort, depth_left)
            }
            Sort::Seq(element) => {
                self.add(size_of::<Sort>())?;
                let depth_left = depth_left.checked_sub(1)?;
                self.add_sort(element, depth_left)
            }
            Sort::Uninterpreted(name) | Sort::TypeVar(name) | Sort::FiniteDomain(name, _) => {
                self.add(name.capacity())
            }
            Sort::Datatype(datatype) => {
                self.add(datatype.name.capacity())?;
                self.add_product(
                    datatype.constructors.capacity(),
                    size_of::<crate::sort::DatatypeConstructor>(),
                )?;
                for constructor in &datatype.constructors {
                    self.add(constructor.name.capacity())?;
                    self.add_product(
                        constructor.fields.capacity(),
                        size_of::<crate::sort::DatatypeField>(),
                    )?;
                    for field in &constructor.fields {
                        self.add(field.name.capacity())?;
                        self.add_sort(&field.sort, depth_left.checked_sub(1)?)?;
                    }
                }
                Some(())
            }
            Sort::Bool
            | Sort::Int
            | Sort::Real
            | Sort::Complex
            | Sort::BitVec(_)
            | Sort::String
            | Sort::RegLan
            | Sort::FloatingPoint(..)
            | Sort::FiniteField(_)
            | Sort::Char => Some(()),
        }
    }

    fn add(&mut self, amount: usize) -> Option<()> {
        let next = self.bytes.checked_add(amount)?;
        if next > self.limit {
            return None;
        }
        if let Some(progress) = self.progress.as_mut() {
            if !progress(amount.checked_add(1)?, amount) {
                return None;
            }
        }
        self.bytes = next;
        Some(())
    }

    fn add_product(&mut self, count: usize, width: usize) -> Option<()> {
        self.add(count.checked_mul(width)?)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn admitted_clone_preserves_nested_sorts_and_owning_side_tables() {
        let mut store = TermStore::new();
        let sort = Sort::Seq(Box::new(Sort::Uninterpreted("owned-element".repeat(16))));
        let id = store.mk_var("original-name", sort.clone());
        store.no_mbqi.insert(id);
        store.skolem_choice.insert(
            id,
            SkolemChoice {
                binder: "owning-binder".repeat(256),
                sort,
                body: id,
            },
        );
        store.quantifier_no_patterns.insert(id, vec![id; 64]);
        store
            .constructor_fields
            .insert("constructor".into(), vec!["field".repeat(256)]);
        store
            .datatype_field_sorts
            .insert("carrier".into(), vec![Sort::Seq(Box::new(Sort::Int))]);
        store
            .declared_functions
            .insert("private-function".repeat(64));
        store.record_strict_bv_semantics_refusal(7, &[id], "retained refusal");
        let bound = store.diagnostic_clone_memory_bytes(usize::MAX).unwrap();
        let mut charged = 0usize;
        let cloned = store
            .clone_with_progress(&mut |_, bytes| {
                charged += bytes;
                charged <= bound
            })
            .unwrap();
        assert_eq!(cloned.get(id), store.get(id));
        assert_eq!(cloned.sort(id), store.sort(id));
        assert!(cloned.no_mbqi.contains(&id));
        assert_eq!(cloned.skolem_choice.get(&id), store.skolem_choice.get(&id));
        assert_eq!(
            cloned.quantifier_no_patterns.get(&id),
            store.quantifier_no_patterns.get(&id)
        );
        assert_eq!(charged, bound);
        assert_eq!(cloned.constructor_fields, store.constructor_fields);
        assert_eq!(cloned.datatype_field_sorts, store.datatype_field_sorts);
        assert_eq!(cloned.declared_functions, store.declared_functions);
        assert_eq!(
            cloned.strict_bv_semantics_refusal(7, &[id]).as_deref(),
            Some("retained refusal")
        );
    }

    #[test]
    fn admitted_clone_declines_a_late_growing_refusal_memo_without_borrowing_across_callback() {
        let store = TermStore::new();
        store.record_strict_bv_semantics_refusal(1, &[], "first");
        let mut changed = false;
        assert!(store
            .clone_with_progress(&mut |work, bytes| {
                if work == 0 && bytes == 0 && !changed {
                    // This must not panic on a RefCell guard held across callback,
                    // or copy a larger memo under its previously priced footprint.
                    changed = true;
                    store.record_strict_bv_semantics_refusal(2, &[], "second");
                }
                true
            })
            .is_err());
        assert!(changed);
        let cloned = store.clone_with_progress(&mut |_, _| true).unwrap();
        assert_eq!(
            cloned.strict_bv_semantics_refusal(2, &[]).as_deref(),
            Some("second")
        );
    }

    #[test]
    fn admitted_clone_refuses_hidden_payload_without_reentering_after_refusal() {
        let payload = "not-in-the-incremental-ledger".repeat(2048);
        let payload_bytes = payload.len();
        let store = TermStore::from_entries(
            vec![(TermData::Const(Constant::String(payload)), Sort::String)],
            None,
            None,
            0,
        );
        assert_eq!(store.heap_data_bytes, 0);
        assert!(store.true_memory_bytes() < payload_bytes);
        let stamp = store.snapshot_stamp();
        let mut charged = 0usize;
        let mut refused = false;
        assert!(store
            .clone_with_progress(&mut |_, bytes| {
                assert!(!refused, "no callback after the first refusal");
                charged += bytes;
                refused = charged >= payload_bytes;
                !refused
            })
            .is_err());
        assert!(refused);
        assert_eq!(store.snapshot_stamp(), stamp);
        let mut charged = 0usize;
        let fresh = store
            .clone_with_progress(&mut |_, bytes| {
                charged += bytes;
                charged <= payload_bytes * 2
            })
            .unwrap();
        assert_eq!(fresh.get(TermId(0)), store.get(TermId(0)));
        assert_eq!(store.snapshot_stamp(), stamp);
    }

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
            store.divmod_purification.insert(
                id,
                DivModPurification {
                    quotient: id,
                    remainder: id,
                    dividend: id,
                    divisor: id,
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
        assert_bound_grows(&mut store, |store| {
            store
                .constructor_fields
                .insert("ctor".repeat(64), vec!["field".repeat(256)]);
        });
        assert_bound_grows(&mut store, |store| {
            store.datatype_field_sorts.insert(
                "carrier".repeat(64),
                vec![Sort::TypeVar("owned".repeat(256))],
            );
        });
        assert_bound_grows(&mut store, |store| {
            store.declared_functions.insert("function".repeat(256));
        });
        assert_bound_grows(&mut store, |store| {
            store.record_strict_bv_semantics_refusal(1, &[id], &"reason".repeat(1024));
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
