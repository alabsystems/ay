// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Real store spines and shared DAGs on a 2 MiB thread stack, including drop.

use super::*;
use num_bigint::BigInt;

#[derive(Clone, Copy)]
enum Domain {
    Int,
    Bv64ToBv32,
}

impl Domain {
    fn index_sort(self) -> Sort {
        match self {
            Self::Int => Sort::Int,
            Self::Bv64ToBv32 => Sort::bitvec(64),
        }
    }

    fn index(self, store: &mut TermStore, value: usize) -> TermId {
        match self {
            Self::Int => store.mk_int(BigInt::from(value)),
            Self::Bv64ToBv32 => store.mk_bitvec(BigInt::from(value), 64),
        }
    }

    fn value(self, store: &mut TermStore, value: usize) -> TermId {
        match self {
            Self::Int => store.mk_int(BigInt::from(value)),
            Self::Bv64ToBv32 => store.mk_bitvec(BigInt::from(value), 32),
        }
    }
}

fn store_lifecycle(domain: Domain, depth: usize) {
    let mut store = TermStore::new();
    let zero = domain.value(&mut store, 0);
    let mut array = store.mk_const_array(domain.index_sort(), zero);
    let sort = store.sort(array).clone();
    // Int indices and values share a sort and therefore numeral identities.
    // Keep their ranges separate so this replacement changes only a value.
    // BV64/BV32 retains the original index i / value i+100 recipe exactly.
    let value_offset = match domain {
        Domain::Int => 100_000,
        Domain::Bv64ToBv32 => 100,
    };
    // Ascending indices retain the original bottom-read shape and do not
    // exercise the separate recursively commuting descending-store rewrite.
    for index in 0..depth {
        let key = domain.index(&mut store, index);
        let value = domain.value(&mut store, index + value_offset);
        array = raw(&mut store, "store", vec![array, key, value], sort.clone());
    }
    let key = domain.index(&mut store, 1);
    let old = domain.value(&mut store, value_offset + 1);
    let replacement = domain.value(&mut store, value_offset + depth + 1000);
    let value_sort = store.sort(old).clone();
    let raw_read = raw(&mut store, "select", vec![array, key], value_sort);
    assert_eq!(store.simplify(array), array);
    assert_eq!(store.simplify(raw_read), old);
    let rewritten = store.substitute(array, &[old], &[replacement]);
    assert_ne!(rewritten, array);
    assert_eq!(store.mk_select(rewritten, key), replacement);
    assert_eq!(
        store.substitute(raw_read, &[old], &[replacement]),
        replacement
    );
    let next_key = domain.index(&mut store, 2);
    let next_value = domain.value(&mut store, value_offset + 2);
    assert_eq!(store.mk_select(rewritten, next_key), next_value);
    let beyond = domain.index(&mut store, depth + 1);
    assert_eq!(store.mk_select(rewritten, beyond), zero);
    let actual = store.mk_select(rewritten, key);
    let equal = store.mk_eq(actual, replacement);
    let different = store.mk_eq(actual, old);
    assert_eq!(equal, store.mk_bool(true));
    assert_eq!(different, store.mk_bool(false));
    // The complete core construction/walk/read/comparison/drop happens on
    // this same fixed stack. This is not a proof or bindings qualification.
    drop(store);
}

#[test]
fn deep_16384_store_simplify_substitute_reads_and_drop_use_two_mib_stack() {
    std::thread::Builder::new()
        .name("core-postorder-stores-2mib".into())
        .stack_size(2 * 1024 * 1024)
        .spawn(|| {
            for domain in [Domain::Int, Domain::Bv64ToBv32] {
                for depth in [1024, 16_384] {
                    store_lifecycle(domain, depth);
                }
            }
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn deep_shared_dag_rebuilds_once_per_node_and_drops_on_two_mib_stack() {
    std::thread::Builder::new()
        .name("core-postorder-shared-2mib".into())
        .stack_size(2 * 1024 * 1024)
        .spawn(|| {
            let mut store = TermStore::new();
            let x = store.mk_var("x", Sort::Int);
            let y = store.mk_var("y", Sort::Int);
            let depth = 16_384;
            let mut root = x;
            for _ in 0..depth {
                root = raw(&mut store, "opaque", vec![root, root], Sort::Int);
            }
            let before_len = store.len();
            let mut cache = crate::kani_compat::det_hash_map_new();
            assert_eq!(store.simplify_inner(root, &mut cache), root);
            assert_eq!(cache.len(), depth + 1);
            assert_eq!(store.len(), before_len);
            cache.clear();
            let mut rewritten = store.substitute_inner(root, &[x], &[y], &mut cache);
            assert_eq!(cache.len(), depth + 1);
            assert_eq!(store.len(), before_len + depth);
            for _ in 0..depth {
                match store.get(rewritten) {
                    TermData::App(_, args) => {
                        assert_eq!(args.len(), 2);
                        assert_eq!(args[0], args[1]);
                        rewritten = args[0];
                    }
                    _ => unreachable!("all rebuilt parents retain the opaque application"),
                }
            }
            assert_eq!(rewritten, y);
            drop(cache);
            drop(store);
        })
        .unwrap()
        .join()
        .unwrap();
}
