// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Narrow BV flag-guard generalizer for direct-IUC clauses (#5877).
//!
//! This packet preserves compact `x = 0` guards and only tries one weakening:
//! `x = 1` to `((_ extract 0 0) x) = #b1`, accepting the rewrite only when the
//! rewritten conjunction remains inductive.

use crate::expr::{ChcExpr, ChcOp, ChcSort, ChcVar};
use std::sync::Arc;

use super::{LemmaGeneralizer, TransitionSystemRef};

/// Direct-IUC-only generalizer for BV 0/1 flag guards.
pub(crate) struct BvFlagGuardGeneralizer;

impl BvFlagGuardGeneralizer {
    pub(crate) fn new() -> Self {
        Self
    }

    /// Recognize `(= var #x0)` / `(= var #x1)` and the reversed operand order.
    fn extract_flag_equality(conjunct: &ChcExpr) -> Option<(ChcVar, u32, u128)> {
        match conjunct {
            ChcExpr::Op(ChcOp::Eq, args) if args.len() == 2 => {
                match (args[0].as_ref(), args[1].as_ref()) {
                    (ChcExpr::Var(v), ChcExpr::BitVec(value, width))
                    | (ChcExpr::BitVec(value, width), ChcExpr::Var(v))
                        if matches!(v.sort, ChcSort::BitVec(var_width) if var_width == *width)
                            && (*value == 0 || *value == 1) =>
                    {
                        Some((v.clone(), *width, *value))
                    }
                    _ => None,
                }
            }
            _ => None,
        }
    }

    fn rewrite_one_to_lsb(var: &ChcVar) -> ChcExpr {
        let extract = ChcExpr::Op(
            ChcOp::BvExtract(0, 0),
            vec![Arc::new(ChcExpr::Var(var.clone()))],
        );
        ChcExpr::eq(extract, ChcExpr::BitVec(1, 1))
    }
}

impl LemmaGeneralizer for BvFlagGuardGeneralizer {
    fn generalize(&self, lemma: &ChcExpr, level: u32, ts: &mut dyn TransitionSystemRef) -> ChcExpr {
        let mut conjuncts = lemma.collect_conjuncts();
        let mut changed = false;

        for idx in 0..conjuncts.len() {
            let Some((var, _width, value)) = Self::extract_flag_equality(&conjuncts[idx]) else {
                continue;
            };

            // Keep `= 0` whole; only `= 1` gets a candidate weakening.
            if value != 1 {
                continue;
            }

            let rewritten = Self::rewrite_one_to_lsb(&var);
            let mut candidate_conjuncts = conjuncts.clone();
            candidate_conjuncts[idx] = rewritten.clone();
            let candidate = ChcExpr::and_all(candidate_conjuncts.iter().cloned());

            if ts.check_inductive(&candidate, level) {
                conjuncts[idx] = rewritten;
                changed = true;
            }
        }

        if changed {
            ChcExpr::and_all(conjuncts)
        } else {
            lemma.clone()
        }
    }

    fn name(&self) -> &'static str {
        "bv-flag-guards"
    }
}
