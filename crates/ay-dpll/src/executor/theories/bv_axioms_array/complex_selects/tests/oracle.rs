// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Frozen original membership walk. The live collector is unchanged; this
//! oracle deliberately retains its redundant per-store suffix navigation.

use super::*;

pub(super) fn membership(terms: &ay_core::TermStore, stores: &[Store]) -> (HashSet<TermId>, usize) {
    let mut store_arrays = HashSet::default();
    let mut links = 0;
    for &(store_term, base_array, _, _) in stores {
        store_arrays.insert(store_term);
        store_arrays.insert(base_array);
        let mut current = base_array;
        loop {
            match terms.get(current) {
                TermData::App(Symbol::Named(name), args)
                    if name.as_str() == "store" && args.len() == 3 =>
                {
                    store_arrays.insert(args[0]);
                    current = args[0];
                    links += 1;
                }
                _ => break,
            }
        }
    }
    (store_arrays, links)
}
