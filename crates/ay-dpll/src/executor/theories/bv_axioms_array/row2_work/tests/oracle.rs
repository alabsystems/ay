// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

//! Frozen f788a4208 whole-root closure and recursive discovery. The only
//! algorithmic substitution is the private root cap supplied by the test.
//! The existing live mk_select/carrier handles folding, independently of the
//! new work scheduler. This oracle never calls the production DFS/worklist.

use super::*;

pub(super) fn materialize(
    executor: &mut Executor,
    extra_roots: &mut Vec<TermId>,
    root_limit: usize,
) -> LateArrayReads {
    let mut known_roots: HashSet<TermId> = extra_roots.iter().copied().collect();
    let mut seen_obligations: HashSet<(TermId, TermId)> = HashSet::default();
    let mut reads = LateArrayReads::default();
    loop {
        let mut selects = Vec::new();
        let mut stores = Vec::new();
        let mut visited = HashSet::default();
        for &assertion in &executor.ctx.assertions {
            collect(
                &executor.ctx.terms,
                assertion,
                &mut selects,
                &mut stores,
                &mut visited,
            );
        }
        for &root in extra_roots.iter() {
            collect(
                &executor.ctx.terms,
                root,
                &mut selects,
                &mut stores,
                &mut visited,
            );
        }
        if selects.is_empty() {
            break;
        }
        let mut selects_by_array: HashMap<TermId, Vec<TermId>> = HashMap::default();
        for &(_, array, index) in &selects {
            selects_by_array.entry(array).or_default().push(index);
        }
        let mut progress = false;
        for &(_, array, index) in &selects {
            let TermData::Ite(_, then_array, else_array) = executor.ctx.terms.get(array) else {
                continue;
            };
            for branch in [*then_array, *else_array] {
                if !matches!(executor.ctx.terms.sort(branch), Sort::Array(_)) {
                    continue;
                }
                if !seen_obligations.insert((branch, index)) {
                    continue;
                }
                let read = reads.materialize_read(&mut executor.ctx.terms, branch, index);
                if known_roots.insert(read) {
                    extra_roots.push(read);
                    reads.note_added_root();
                    progress = true;
                    if reads.added_roots() >= root_limit {
                        return reads;
                    }
                }
            }
        }
        for &(store, base, store_index, _) in &stores {
            let Some(indices) = selects_by_array.get(&store) else {
                continue;
            };
            for &index in indices {
                if store_index == index {
                    continue;
                }
                if !seen_obligations.insert((base, index)) {
                    continue;
                }
                let read = reads.materialize_read(&mut executor.ctx.terms, base, index);
                if known_roots.insert(read) {
                    extra_roots.push(read);
                    reads.note_added_root();
                    progress = true;
                    if reads.added_roots() >= root_limit {
                        return reads;
                    }
                }
            }
        }
        if !progress {
            break;
        }
    }
    reads
}

fn collect(
    terms: &TermStore,
    term: TermId,
    selects: &mut Vec<(TermId, TermId, TermId)>,
    stores: &mut Vec<(TermId, TermId, TermId, TermId)>,
    visited: &mut HashSet<TermId>,
) {
    if visited.contains(&term) {
        return;
    }
    visited.insert(term);
    match terms.get(term) {
        TermData::App(symbol, args) => match symbol.name() {
            "select" if args.len() == 2 => {
                selects.push((term, args[0], args[1]));
                collect(terms, args[0], selects, stores, visited);
                collect(terms, args[1], selects, stores, visited);
            }
            "store" if args.len() == 3 => {
                stores.push((term, args[0], args[1], args[2]));
                collect(terms, args[0], selects, stores, visited);
                collect(terms, args[1], selects, stores, visited);
                collect(terms, args[2], selects, stores, visited);
            }
            _ => {
                for &arg in args {
                    collect(terms, arg, selects, stores, visited);
                }
            }
        },
        TermData::Not(inner) => collect(terms, *inner, selects, stores, visited),
        TermData::Ite(c, t, e) => {
            collect(terms, *c, selects, stores, visited);
            collect(terms, *t, selects, stores, visited);
            collect(terms, *e, selects, stores, visited);
        }
        _ => {}
    }
}
