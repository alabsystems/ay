// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use std::sync::Arc;

use ay_core::kani_compat::DetHashMap as FxHashMap;

use crate::{ChcExpr, ChcOp, ChcSort, ChcVar, InvariantModel, PredicateInterpretation};

use super::super::{BackTranslator, InvalidityWitness, TransformMemoryReport, ValidityWitness};
use super::BvBoolMap;

pub(super) fn boxed(map: BvBoolMap) -> Box<dyn BackTranslator> {
    Box::new(BvBoolBackTranslator { map })
}

// ── Back-translation ────────────────────────────────────────────────────────

struct BvBoolBackTranslator {
    map: BvBoolMap,
}

impl BackTranslator for BvBoolBackTranslator {
    fn translate_validity(&self, witness: ValidityWitness) -> ValidityWitness {
        reconstruct_bv_invariant(&witness, &self.map)
    }

    fn translate_invalidity(&self, witness: InvalidityWitness) -> InvalidityWitness {
        // Bool counterexamples are valid — reconstruct BV values from bit groups.
        reconstruct_bv_counterexample(witness, &self.map)
    }

    fn transform_memory(&self) -> TransformMemoryReport {
        TransformMemoryReport::reversible("bv_to_bool")
    }
}

/// Reconstruct BV-sorted invariant model from Bool-expanded model.
///
/// Handles selective bit-blasting (#7006/#7019): only arguments marked as
/// bit-blasted in `pred_arg_bitblasted` are reconstructed from Bool groups.
/// Non-bit-blasted arguments (e.g., BV64 left for BvToInt) are passed through.
pub(super) fn reconstruct_bv_invariant(inv: &InvariantModel, map: &BvBoolMap) -> InvariantModel {
    let mut result = InvariantModel::new();
    for (pid, interp) in inv.iter() {
        let Some(orig_sorts) = map.pred_original_sorts.get(pid) else {
            result.set(*pid, interp.clone());
            continue;
        };

        let bitblasted = map.pred_arg_bitblasted.get(pid);

        // Reconstruct variables: group consecutive Bool vars back into BV vars
        // for bit-blasted arguments; pass through non-bit-blasted arguments.
        let mut new_vars = Vec::new();
        let mut new_formula = interp.formula.clone();
        let mut bool_idx = 0;
        for (arg_idx, sort) in orig_sorts.iter().enumerate() {
            let was_bitblasted = bitblasted
                .and_then(|b| b.get(arg_idx))
                .copied()
                .unwrap_or_else(|| matches!(sort, ChcSort::BitVec(_)));

            if was_bitblasted {
                if let ChcSort::BitVec(w) = sort {
                    let w = *w as usize;
                    // Create BV variable with original name.
                    let bv_var_name = format!("x{arg_idx}");
                    new_vars.push(ChcVar::new(&bv_var_name, sort.clone()));

                    // Build reconstruction expression: bv_val = Σ bit_i * 2^i
                    // In the formula, replace references to individual bit vars
                    // with extract expressions on the BV variable.
                    let bv_var = ChcExpr::var(ChcVar::new(&bv_var_name, sort.clone()));
                    for bit_i in 0..w {
                        if bool_idx + bit_i < interp.vars.len() {
                            let bit_var_name = interp.vars[bool_idx + bit_i].name.clone();
                            let extract = ChcExpr::Op(
                                ChcOp::BvExtract(bit_i as u32, bit_i as u32),
                                vec![Arc::new(bv_var.clone())],
                            );
                            // Replace bit_var_name with extract in formula.
                            new_formula = substitute_var_in_expr(
                                &new_formula,
                                &bit_var_name,
                                &ChcExpr::eq(extract, ChcExpr::BitVec(1, 1)),
                            );
                        }
                    }
                    bool_idx += w;
                } else {
                    // Non-BV arg that was somehow marked as bitblasted (shouldn't happen)
                    if bool_idx < interp.vars.len() {
                        new_vars.push(interp.vars[bool_idx].clone());
                    }
                    bool_idx += 1;
                }
            } else {
                // Not bit-blasted: pass through as-is.
                if bool_idx < interp.vars.len() {
                    new_vars.push(interp.vars[bool_idx].clone());
                }
                bool_idx += 1;
            }
        }

        result.set(*pid, PredicateInterpretation::new(new_vars, new_formula));
    }
    result
}

/// Reconstruct BV counterexample from Bool-expanded counterexample.
///
/// Handles selective bit-blasting (#7006/#7019): only arguments that were
/// actually bit-blasted get reconstructed from individual bit assignments.
fn reconstruct_bv_counterexample(mut cex: InvalidityWitness, map: &BvBoolMap) -> InvalidityWitness {
    for step in &mut cex.steps {
        let Some(orig_sorts) = map.pred_original_sorts.get(&step.predicate) else {
            continue;
        };

        let bitblasted = map.pred_arg_bitblasted.get(&step.predicate);

        let mut new_assignments = FxHashMap::default();
        for (arg_idx, sort) in orig_sorts.iter().enumerate() {
            let was_bitblasted = bitblasted
                .and_then(|b| b.get(arg_idx))
                .copied()
                .unwrap_or_else(|| matches!(sort, ChcSort::BitVec(_)));

            if was_bitblasted {
                if let ChcSort::BitVec(w) = sort {
                    let w = *w as usize;
                    // Reconstruct BV value from individual bit assignments.
                    let mut bv_val: i64 = 0;
                    for bit_i in 0..w {
                        let bit_name = format!("x{arg_idx}_b{bit_i}");
                        if let Some(&val) = step.assignments.get(&bit_name) {
                            if val != 0 {
                                bv_val |= 1i64 << bit_i;
                            }
                        }
                    }
                    let orig_var_name = format!("x{arg_idx}");
                    new_assignments.insert(orig_var_name, bv_val);
                } else {
                    // Non-BV that was somehow marked as bitblasted — pass through.
                    let name = format!("x{arg_idx}");
                    if let Some(&val) = step.assignments.get(&name) {
                        new_assignments.insert(name, val);
                    }
                }
            } else {
                // Not bit-blasted: copy assignment as-is.
                let name = format!("x{arg_idx}");
                if let Some(&val) = step.assignments.get(&name) {
                    new_assignments.insert(name, val);
                }
            }
        }
        step.assignments = new_assignments;
    }
    cex
}

/// Substitute all occurrences of a variable name in an expression with a
/// replacement expression. Used for invariant back-translation.
fn substitute_var_in_expr(expr: &ChcExpr, var_name: &str, replacement: &ChcExpr) -> ChcExpr {
    crate::expr::maybe_grow_expr_stack(|| match expr {
        ChcExpr::Var(v) if v.name == var_name => replacement.clone(),
        ChcExpr::Op(op, args) => {
            let new_args: Vec<Arc<ChcExpr>> = args
                .iter()
                .map(|a| Arc::new(substitute_var_in_expr(a, var_name, replacement)))
                .collect();
            ChcExpr::Op(*op, new_args)
        }
        ChcExpr::PredicateApp(name, id, args) => ChcExpr::PredicateApp(
            name.clone(),
            *id,
            args.iter()
                .map(|a| Arc::new(substitute_var_in_expr(a, var_name, replacement)))
                .collect(),
        ),
        ChcExpr::FuncApp(name, sort, args) => ChcExpr::FuncApp(
            name.clone(),
            sort.clone(),
            args.iter()
                .map(|a| Arc::new(substitute_var_in_expr(a, var_name, replacement)))
                .collect(),
        ),
        _ => expr.clone(),
    })
}
