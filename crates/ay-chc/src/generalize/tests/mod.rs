// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::expr::{ChcOp, ChcSort, ChcVar};
use ay_core::kani_compat::DetHashSet as HashSet;
use std::cell::RefCell;
use std::sync::Arc;

/// Mock transition system that returns configurable inductiveness results.
///
/// This allows testing generalizer behavior without a real CHC solver.
pub(crate) struct MockTransitionSystem {
    pub(crate) init_bounds_map: HashMap<String, InitBounds>,
    /// Set of lemma hashes for which check_inductive returns true
    pub(crate) inductive_lemmas: RefCell<HashSet<String>>,
    /// Record of all inductiveness queries for verification
    pub(crate) queries: RefCell<Vec<String>>,
}

impl MockTransitionSystem {
    pub(crate) fn new() -> Self {
        Self {
            init_bounds_map: HashMap::default(),
            inductive_lemmas: RefCell::new(HashSet::default()),
            queries: RefCell::new(Vec::new()),
        }
    }

    pub(crate) fn with_init_bounds(mut self, bounds: HashMap<String, InitBounds>) -> Self {
        self.init_bounds_map = bounds;
        self
    }

    /// Mark a lemma as inductive (hash-based matching).
    pub(crate) fn mark_inductive(&self, lemma_repr: &str) {
        self.inductive_lemmas
            .borrow_mut()
            .insert(lemma_repr.to_string());
    }
}

impl TransitionSystemRef for MockTransitionSystem {
    fn check_inductive(&mut self, formula: &ChcExpr, _level: u32) -> bool {
        let repr = format!("{formula:?}");
        self.queries.borrow_mut().push(repr.clone());
        self.inductive_lemmas.borrow().contains(&repr)
    }

    fn check_inductive_with_core(
        &mut self,
        conjuncts: &[ChcExpr],
        level: u32,
    ) -> Option<Vec<ChcExpr>> {
        let formula = if conjuncts.is_empty() {
            ChcExpr::Bool(true)
        } else if conjuncts.len() == 1 {
            conjuncts[0].clone()
        } else {
            conjuncts.iter().cloned().reduce(ChcExpr::and).unwrap()
        };

        if self.check_inductive(&formula, level) {
            let core_size = conjuncts.len().div_ceil(2);
            Some(conjuncts.iter().take(core_size).cloned().collect())
        } else {
            None
        }
    }

    fn init_bounds(&self) -> HashMap<String, InitBounds> {
        self.init_bounds_map.clone()
    }
}

mod integration_bv;
mod integration_lia;
mod integration_template;
mod unit_tests;
