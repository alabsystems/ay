// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Boolean<->modular-parity coupling hint provider.
//!
//! Loop bodies that fold a GF(2) / parity bit alongside an integer counter
//! produce the relational invariant `b <=> (x mod 2 == r)`: a Boolean state
//! variable equals the parity of an integer state variable. The canonical case
//! is the congruence XOR-collapse fold `acc = acc ^ bit` with a popcount counter
//! (`acc <=> (count mod 2 == 1)`). The existing `discover_parity_invariants`
//! pass only finds `x mod k == const` (a *fixed* residue), which never holds
//! here because the counter's parity flips every iteration — what is invariant
//! is the *coupling* to the Boolean.
//!
//! This provider enumerates the small candidate space `b <=> (x mod 2 == r)`
//! for each (Bool, Int) state-variable pair and residue `r in {0,1}`. Like every
//! `LemmaHintProvider`, the candidates are NEVER trusted: PDR validates each via
//! its init / self-inductiveness / entry-inductiveness SMT checks and discards
//! any that are not genuinely inductive. The provider only proposes; soundness
//! rests entirely on PDR's validation.

use super::*;

pub(crate) struct BoolModParityHintProvider;

impl BoolModParityHintProvider {
    const SOURCE: &'static str = "bool-mod-parity-v1";
    const PRIORITY: u16 = 60;
    /// Cap candidates per predicate. Each Bool/Int pair yields 2 candidates;
    /// loop parity invariants have very few Boolean state vars, so this is ample.
    const MAX_HINTS_PER_PRED: usize = 32;
    const MODULUS: i64 = 2;
}

impl LemmaHintProvider for BoolModParityHintProvider {
    fn collect(&self, req: &HintRequest<'_>, out: &mut Vec<LemmaHint>) {
        if req.stage != HintStage::Startup {
            return;
        }
        for pred_info in req.problem.predicates() {
            let pred_id = pred_info.id;
            let Some(canonical_vars) = req.canonical_vars(pred_id) else {
                continue;
            };
            let bool_vars: Vec<&ChcVar> = canonical_vars
                .iter()
                .filter(|v| matches!(v.sort, crate::ChcSort::Bool))
                .collect();
            // Int and BitVec counters both carry a low-bit parity. Rust `usize`
            // counters lower to BitVec (e.g. `set_count % 2` -> `bvurem _ 2`), so
            // the real congruence obligation needs BitVec candidates too.
            let int_vars: Vec<&ChcVar> = canonical_vars
                .iter()
                .filter(|v| matches!(v.sort, crate::ChcSort::Int))
                .collect();
            let bv_vars: Vec<&ChcVar> = canonical_vars
                .iter()
                .filter(|v| matches!(v.sort, crate::ChcSort::BitVec(_)))
                .collect();
            if bool_vars.is_empty() || (int_vars.is_empty() && bv_vars.is_empty()) {
                continue;
            }
            let mut hint_count = 0usize;
            'pairs: for b in &bool_vars {
                let bexpr = ChcExpr::var((*b).clone());
                for x in &int_vars {
                    for r in 0..Self::MODULUS {
                        if hint_count >= Self::MAX_HINTS_PER_PRED {
                            break 'pairs;
                        }
                        // b <=> (x mod 2 == r)   (Bool equality is iff)
                        let residue_eq = ChcExpr::eq(
                            ChcExpr::mod_op(
                                ChcExpr::var((*x).clone()),
                                ChcExpr::int(Self::MODULUS),
                            ),
                            ChcExpr::int(r),
                        );
                        let formula = ChcExpr::eq(bexpr.clone(), residue_eq);
                        out.push(LemmaHint::new(
                            pred_id,
                            formula,
                            Self::PRIORITY,
                            Self::SOURCE,
                        ));
                        hint_count += 1;
                    }
                }
                for x in &bv_vars {
                    let crate::ChcSort::BitVec(width) = x.sort else {
                        continue;
                    };
                    let two = ChcExpr::BitVec(Self::MODULUS as u128, width);
                    for r in 0..Self::MODULUS {
                        if hint_count >= Self::MAX_HINTS_PER_PRED {
                            break 'pairs;
                        }
                        // b <=> (bvurem x 2 == r)
                        let residue_eq = ChcExpr::eq(
                            ChcExpr::Op(
                                ChcOp::BvURem,
                                vec![
                                    std::sync::Arc::new(ChcExpr::var((*x).clone())),
                                    std::sync::Arc::new(two.clone()),
                                ],
                            ),
                            ChcExpr::BitVec(r as u128, width),
                        );
                        let formula = ChcExpr::eq(bexpr.clone(), residue_eq);
                        out.push(LemmaHint::new(
                            pred_id,
                            formula,
                            Self::PRIORITY,
                            Self::SOURCE,
                        ));
                        hint_count += 1;
                    }
                }
            }
        }
    }
}

pub(super) static BOOL_MOD_PARITY_PROVIDER: BoolModParityHintProvider = BoolModParityHintProvider;
