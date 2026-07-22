// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! BV-to-Bool bit-blast transformation for CHC problems (#5877).
//!
//! Converts BV-sorted predicate arguments to individual Bool parameters (one
//! per bit) and bit-blasts BV operations into Boolean circuits. The resulting
//! problem is pure Bool+Int CHC, solvable by standard PDR with natural Boolean
//! generalization (drop individual bits).
//!
//! This is the AY analogue of Z3's `dl_mk_bit_blast.cpp` transformation.
//!
//! Soundness: exact encoding — all BV operations are fully precise as Boolean
//! circuits. No over-approximation (unlike BvToInt which uses UFs for bitwise ops).
//!
//! # Selective bit-blasting (#7006/#7019)
//!
//! BV arguments with width <= `max_width` (default 64) are bit-blasted to
//! individual Bool parameters. BV arguments exceeding the threshold (e.g.,
//! BV128) are left as-is for BvToInt to handle downstream. The 64-bit
//! threshold covers all standard Rust pointer/usize widths (#7975), enabling
//! exact Boolean reasoning for BV64 harnesses from model-checker-consumer/verification-consumer.
//!
//! # Limitations
//!
//! - Array sorts with BV indices are left unchanged (BvToInt handles those).

mod ops;

use std::sync::Arc;

use ay_core::kani_compat::DetHashMap as FxHashMap;

use crate::{
    ChcExpr, ChcOp, ChcProblem, ChcSort, ChcVar, ClauseBody, ClauseHead, HornClause,
    InvariantModel, PredicateId, PredicateInterpretation,
};

use super::{
    BackTranslator, IdentityBackTranslator, InvalidityWitness, TransformMemoryReport,
    TransformationResult, Transformer, ValidityWitness,
};

/// Tracks BV→Bool mapping for back-translation.
struct BvBoolMap {
    /// Per-predicate: original argument sorts (before expansion).
    /// Used to reconstruct BV values from Bool groups during back-translation.
    pred_original_sorts: FxHashMap<PredicateId, Vec<ChcSort>>,
    /// Per-predicate: which original arguments were bit-blasted (true) vs
    /// left as-is (false). Used by selective bit-blasting (#7006/#7019) to
    /// correctly back-translate only the arguments that were expanded to Bools.
    pred_arg_bitblasted: FxHashMap<PredicateId, Vec<bool>>,
}

impl BvBoolMap {
    fn new() -> Self {
        Self {
            pred_original_sorts: FxHashMap::default(),
            pred_arg_bitblasted: FxHashMap::default(),
        }
    }
}

/// BV-to-Bool bit-blast transformer.
///
/// No-op for non-BV problems. For problems with mixed BV widths, selectively
/// bit-blasts arguments with width <= `max_width` (default 64) while leaving
/// wider BV arguments (e.g., BV128) unchanged for BvToInt (#7006/#7019/#7975).
pub(crate) struct BvToBoolBitBlaster {
    verbose: bool,
    max_width: u32,
}

impl BvToBoolBitBlaster {
    pub(crate) fn new() -> Self {
        Self {
            verbose: false,
            max_width: 64,
        }
    }

    pub(crate) fn with_verbose(mut self, verbose: bool) -> Self {
        self.verbose = verbose;
        self
    }
}

impl Transformer for BvToBoolBitBlaster {
    fn transform(self: Box<Self>, problem: ChcProblem) -> TransformationResult {
        if !problem.has_bv_sorts() {
            return TransformationResult {
                problem,
                back_translator: Box::new(IdentityBackTranslator),
            };
        }

        // Check whether any BV predicate arguments are eligible for
        // bit-blasting (width <= threshold). Wide BV arguments (e.g., BV64)
        // are left as-is for BvToInt to handle downstream (#7006/#7019).
        let has_eligible_bv = problem
            .predicates()
            .iter()
            .flat_map(|p| p.arg_sorts.iter())
            .any(|s| matches!(s, ChcSort::BitVec(w) if *w <= self.max_width));

        if !has_eligible_bv {
            if self.verbose {
                tracing::info!(
                    threshold = self.max_width,
                    "BvToBool: no BV args within threshold, skipping"
                );
            }
            return TransformationResult {
                problem,
                back_translator: Box::new(IdentityBackTranslator),
            };
        }

        let mut map = BvBoolMap::new();
        let transformed =
            bitblast_problem_selective(&problem, &mut map, self.max_width, self.verbose);
        TransformationResult {
            problem: transformed,
            back_translator: Box::new(BvBoolBackTranslator { map }),
        }
    }
}

// ── Core bit-blast transformation ───────────────────────────────────────────

/// Whether a BV sort should be bit-blasted given the width threshold.
fn should_bitblast_sort(sort: &ChcSort, max_width: u32) -> bool {
    matches!(sort, ChcSort::BitVec(w) if *w <= max_width)
}

fn analyze_predicate_arg_bitblasting(
    problem: &ChcProblem,
    max_width: u32,
) -> FxHashMap<PredicateId, Vec<bool>> {
    let mut pred_arg_bitblasted: FxHashMap<PredicateId, Vec<bool>> = problem
        .predicates()
        .iter()
        .map(|pred| {
            (
                pred.id,
                pred.arg_sorts
                    .iter()
                    .map(|sort| should_bitblast_sort(sort, max_width))
                    .collect(),
            )
        })
        .collect();

    let mut note_occurrence = |pid: PredicateId, args: &[ChcExpr]| {
        let original_sorts = &problem.predicates()[pid.index()].arg_sorts;
        let Some(arg_bitblasted) = pred_arg_bitblasted.get_mut(&pid) else {
            return;
        };
        for ((can_bitblast, sort), arg) in arg_bitblasted
            .iter_mut()
            .zip(original_sorts.iter())
            .zip(args.iter())
        {
            if *can_bitblast
                && matches!(sort, ChcSort::BitVec(_))
                && !ops::can_expand_predicate_arg(arg)
            {
                *can_bitblast = false;
            }
        }
    };

    for clause in problem.clauses() {
        for (pid, args) in &clause.body.predicates {
            note_occurrence(*pid, args);
        }
        if let ClauseHead::Predicate(pid, args) = &clause.head {
            note_occurrence(*pid, args);
        }
    }

    pred_arg_bitblasted
}

/// Selective bit-blast transformation (#7006/#7019).
///
/// Bit-blasts BV arguments with width <= `max_width` to individual Bool
/// parameters. BV arguments exceeding the threshold are preserved as-is
/// (their BV sort is unchanged) for BvToInt to handle downstream.
///
/// This enables the BvToBool lane to fire on problems containing BV64
/// (e.g., all 149 model-checker-consumer harnesses) by selectively bit-blasting any BV8/BV16/BV32
/// arguments while leaving BV64 untouched.
fn bitblast_problem_selective(
    problem: &ChcProblem,
    map: &mut BvBoolMap,
    max_width: u32,
    verbose: bool,
) -> ChcProblem {
    let mut result = ChcProblem::new();
    let pred_arg_bitblasted = analyze_predicate_arg_bitblasting(problem, max_width);

    // Phase 1: Convert predicate signatures.
    // BitVec(w) with w <= max_width becomes w Bool arguments.
    // BitVec(w) with w > max_width is preserved as-is.
    for pred in problem.predicates() {
        map.pred_original_sorts
            .insert(pred.id, pred.arg_sorts.clone());
        let mut new_sorts = Vec::new();
        let arg_bitblasted = pred_arg_bitblasted
            .get(&pred.id)
            .cloned()
            .unwrap_or_else(|| vec![false; pred.arg_sorts.len()]);
        for (sort, should_bitblast_arg) in pred.arg_sorts.iter().zip(arg_bitblasted.iter()) {
            if *should_bitblast_arg {
                let w = match sort {
                    ChcSort::BitVec(w) => *w,
                    _ => unreachable!(),
                };
                for _ in 0..w {
                    new_sorts.push(ChcSort::Bool);
                }
            } else {
                new_sorts.push(sort.clone());
            }
        }
        map.pred_arg_bitblasted.insert(pred.id, arg_bitblasted);
        result.declare_predicate(&pred.name, new_sorts);
    }

    if verbose {
        for (i, pred) in result.predicates().iter().enumerate() {
            let orig = &problem.predicates()[i];
            if pred.arity() != orig.arity() {
                tracing::info!(
                    predicate = %pred.name,
                    orig_arity = orig.arity(),
                    new_arity = pred.arity(),
                    "BvToBool: expanded predicate (selective)"
                );
            }
        }
    }

    // Phase 2: Transform each clause.
    for clause in problem.clauses() {
        let new_clause = bitblast_clause_selective(clause, problem, &map.pred_arg_bitblasted);
        result.add_clause(new_clause);
    }

    result
}

/// Selectively expand predicate arguments: bit-blast BV args within the
/// threshold, leave wider BV args unchanged (#7006/#7019).
fn expand_pred_args_selective(
    args: &[ChcExpr],
    original_sorts: &[ChcSort],
    arg_bitblasted: &[bool],
) -> Vec<ChcExpr> {
    let mut expanded = Vec::new();
    for (arg_idx, (arg, sort)) in args.iter().zip(original_sorts.iter()).enumerate() {
        if arg_bitblasted.get(arg_idx).copied().unwrap_or(false) {
            let w = match sort {
                ChcSort::BitVec(w) => *w,
                _ => unreachable!(),
            };
            // Extract bits from the argument expression.
            let bits = ops::expr_to_bits(arg, w);
            expanded.extend(bits);
        } else if matches!(sort, ChcSort::BitVec(_)) {
            // Preserve deferred BV arguments intact so later abstraction can
            // reason about opaque reads/conversions without sort corruption.
            expanded.push(arg.clone());
        } else {
            // Non-BV arguments keep their top-level sort, but can still
            // recursively bit-blast nested BV subexpressions in-place.
            expanded.push(ops::bitblast_expr(arg));
        }
    }
    expanded
}

fn bitblast_clause_selective(
    clause: &HornClause,
    orig_problem: &ChcProblem,
    pred_arg_bitblasted: &FxHashMap<PredicateId, Vec<bool>>,
) -> HornClause {
    // Transform body predicates.
    let body_preds: Vec<(PredicateId, Vec<ChcExpr>)> = clause
        .body
        .predicates
        .iter()
        .map(|(pid, args)| {
            let orig_sorts = &orig_problem.predicates()[pid.index()].arg_sorts;
            let arg_bitblasted = pred_arg_bitblasted
                .get(pid)
                .map(Vec::as_slice)
                .unwrap_or(&[]);
            let expanded = expand_pred_args_selective(args, orig_sorts, arg_bitblasted);
            (*pid, expanded)
        })
        .collect();

    // Transform body constraint (may contain BV operations).
    let body_constraint = clause.body.constraint.as_ref().map(ops::bitblast_expr);

    // Transform head.
    let head = match &clause.head {
        ClauseHead::Predicate(pid, args) => {
            let orig_sorts = &orig_problem.predicates()[pid.index()].arg_sorts;
            let arg_bitblasted = pred_arg_bitblasted
                .get(pid)
                .map(Vec::as_slice)
                .unwrap_or(&[]);
            let expanded = expand_pred_args_selective(args, orig_sorts, arg_bitblasted);
            ClauseHead::Predicate(*pid, expanded)
        }
        ClauseHead::False => ClauseHead::False,
    };

    let body = ClauseBody::new(body_preds, body_constraint);
    HornClause::new(body, head)
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
fn reconstruct_bv_invariant(inv: &InvariantModel, map: &BvBoolMap) -> InvariantModel {
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

#[allow(clippy::unwrap_used)]
#[cfg(test)]
mod tests;
