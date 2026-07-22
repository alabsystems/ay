// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Array-select index generalization for CHC PDR lemmas.
//!
//! This is a lightweight adaptation of Z3 Spacer's quantifier generalizer in
//! `spacer_quant_generalizer.cpp`. Spacer abstracts concrete array indices into
//! quantified variables; this pass uses a simpler weakening strategy:
//! identify `select(arr, idx) = val` conjuncts, drop them, and keep the weaker
//! lemma only if `TransitionSystemRef::check_inductive` still succeeds.

use super::{LemmaGeneralizer, TransitionSystemRef};
use crate::expr::{ChcExpr, ChcOp, ChcSort};

/// Drops array-select equality conjuncts when the remaining lemma is inductive.
pub(crate) struct ArraySelectIndexGeneralizer;

impl Default for ArraySelectIndexGeneralizer {
    fn default() -> Self {
        Self::new()
    }
}

impl ArraySelectIndexGeneralizer {
    pub(crate) fn new() -> Self {
        Self
    }

    fn is_array_select(expr: &ChcExpr) -> bool {
        let ChcExpr::Op(ChcOp::Select, args) = expr else {
            return false;
        };
        if args.len() != 2 {
            return false;
        }
        matches!(args[0].as_ref().sort(), ChcSort::Array(_, _))
            && !matches!(args[1].as_ref().sort(), ChcSort::Array(_, _))
            && !args[1].as_ref().contains_array_ops()
    }

    fn is_select_equality(expr: &ChcExpr) -> bool {
        let ChcExpr::Op(ChcOp::Eq, args) = expr else {
            return false;
        };
        if args.len() != 2 {
            return false;
        }
        Self::is_array_select(args[0].as_ref()) || Self::is_array_select(args[1].as_ref())
    }

    fn build_candidate(
        conjuncts: &[ChcExpr],
        kept: &[bool],
        drop_idx: Option<usize>,
    ) -> Vec<ChcExpr> {
        conjuncts
            .iter()
            .enumerate()
            .filter(|(i, _)| kept[*i] && Some(*i) != drop_idx)
            .map(|(_, conjunct)| conjunct.clone())
            .collect()
    }

    fn is_inductive(
        conjuncts: &[ChcExpr],
        level: u32,
        system: &mut dyn TransitionSystemRef,
    ) -> bool {
        !conjuncts.is_empty()
            && system.check_inductive(&ChcExpr::and_all(conjuncts.to_vec()), level)
    }
}

impl LemmaGeneralizer for ArraySelectIndexGeneralizer {
    fn generalize(
        &self,
        formula: &ChcExpr,
        level: u32,
        system: &mut dyn TransitionSystemRef,
    ) -> ChcExpr {
        if !formula.contains_array_ops() {
            return formula.clone();
        }

        let conjuncts = formula.collect_conjuncts();
        if conjuncts.len() <= 1 {
            return formula.clone();
        }

        let array_indices: Vec<usize> = conjuncts
            .iter()
            .enumerate()
            .filter_map(|(i, conjunct)| Self::is_select_equality(conjunct).then_some(i))
            .collect();
        if array_indices.is_empty() {
            return formula.clone();
        }

        let mut kept = vec![true; conjuncts.len()];
        for &idx in &array_indices {
            kept[idx] = false;
        }
        let scalar_only = Self::build_candidate(&conjuncts, &kept, None);
        if Self::is_inductive(&scalar_only, level, system) {
            return ChcExpr::and_all(scalar_only);
        }

        for &idx in &array_indices {
            kept[idx] = true;
        }

        let mut changed = false;
        for &idx in &array_indices {
            let candidate = Self::build_candidate(&conjuncts, &kept, Some(idx));
            if Self::is_inductive(&candidate, level, system) {
                kept[idx] = false;
                changed = true;
            }
        }

        if !changed {
            return formula.clone();
        }

        let generalized = Self::build_candidate(&conjuncts, &kept, None);
        if generalized.is_empty() {
            formula.clone()
        } else {
            ChcExpr::and_all(generalized)
        }
    }

    fn name(&self) -> &'static str {
        "array-select-index"
    }
}
