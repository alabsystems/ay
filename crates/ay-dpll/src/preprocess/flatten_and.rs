// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! FlattenAnd preprocessing pass
//!
//! Flattens nested AND terms into individual assertions.
//! For example:
//!   `(and (and a b) (and c d))` becomes `[a, b, c, d]`
//!
//! This simplifies downstream processing and exposes individual
//! constraints for other passes (like variable substitution).
//!
//! # Reference
//! - `reference/bitwuzla/src/preprocess/pass/flatten_and.cpp`

use super::PreprocessingPass;
// #8529: Use deterministic hash sets in all builds.
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::TermData;
use ay_core::{TermId, TermStore};

/// Flattens nested AND terms into individual assertions.
pub(crate) struct FlattenAnd {
    /// Cache of terms we've already processed to avoid duplicates
    processed: HashSet<TermId>,
}

impl FlattenAnd {
    /// Create a new FlattenAnd pass.
    pub(crate) fn new() -> Self {
        Self {
            processed: HashSet::default(),
        }
    }
}

impl Default for FlattenAnd {
    fn default() -> Self {
        Self::new()
    }
}

impl PreprocessingPass for FlattenAnd {
    fn apply(&mut self, terms: &mut TermStore, assertions: &mut Vec<TermId>) -> bool {
        let mut modified = false;
        let mut new_assertions = Vec::new();
        let mut work_stack = Vec::new();

        for &assertion in assertions.iter() {
            work_stack.push(assertion);

            while let Some(term) = work_stack.pop() {
                // Skip if already processed to avoid duplicates
                if !self.processed.insert(term) {
                    continue;
                }

                match terms.get(term) {
                    // Flatten AND: push children onto work stack
                    TermData::App(sym, args) if sym.name() == "and" && args.len() >= 2 => {
                        modified = true;
                        // Push in reverse order so first child is processed first
                        for &arg in args.iter().rev() {
                            work_stack.push(arg);
                        }
                    }
                    // Not an AND: keep as individual assertion
                    _ => {
                        new_assertions.push(term);
                    }
                }
            }
        }

        if modified {
            *assertions = new_assertions;
        }

        modified
    }

    fn apply_with_sources(
        &mut self,
        terms: &mut TermStore,
        assertions: &mut Vec<TermId>,
        source_sets: &mut Vec<Vec<TermId>>,
    ) -> bool {
        debug_assert_eq!(assertions.len(), source_sets.len());
        let mut modified = false;
        let mut new_assertions = Vec::new();
        let mut new_source_sets: Vec<Vec<TermId>> = Vec::new();
        let mut work_stack = Vec::new();
        let mut source_index: HashMap<TermId, usize> = HashMap::default();

        for (&assertion, source_set) in assertions.iter().zip(source_sets.iter()) {
            work_stack.push((assertion, source_set.clone()));
            // Per-assertion dedup of the `and`-skeleton walk: the term store is
            // a hash-consed DAG, so a shared `and` node reachable through
            // several parents would otherwise be re-expanded once per PATH
            // (exponential — the DAG→tree pathology). Within one assertion the
            // `sources` vector is IDENTICAL along every path (it is only cloned
            // down, never extended), so skipping a revisited `and` node loses
            // nothing: its conjuncts were already emitted with the same sources.
            // The set must not span assertions — their source sets differ; the
            // leaf-level `source_index` merge below handles cross-assertion dedup.
            let mut and_visited: HashSet<TermId> = HashSet::default();

            while let Some((term, sources)) = work_stack.pop() {
                match terms.get(term) {
                    TermData::App(sym, args) if sym.name() == "and" && args.len() >= 2 => {
                        modified = true;
                        if !and_visited.insert(term) {
                            continue;
                        }
                        for &arg in args.iter().rev() {
                            work_stack.push((arg, sources.clone()));
                        }
                    }
                    _ => {
                        if let Some(&index) = source_index.get(&term) {
                            for source in sources {
                                if !new_source_sets[index].contains(&source) {
                                    new_source_sets[index].push(source);
                                }
                            }
                        } else {
                            source_index.insert(term, new_assertions.len());
                            new_assertions.push(term);
                            new_source_sets.push(sources);
                        }
                    }
                }
            }
        }

        if modified {
            *assertions = new_assertions;
            *source_sets = new_source_sets;
        }

        debug_assert_eq!(assertions.len(), source_sets.len());
        modified
    }

    fn reset(&mut self) {
        self.processed.clear();
    }
}

#[cfg(test)]
#[path = "flatten_and_tests.rs"]
mod tests;
