// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! BV bit-level don't-care generalization for PDR lemmas (#7968).
//!
//! Ports Z3 Spacer's `expand_literals` technique (reference/z3/src/muz/spacer/spacer_util.cpp:357-370):
//! For a BV equality `(= var #bvN)` with width `w`, expand into `w` individual bit constraints:
//!   - bit j is 1: `(= (extract j j var) #b1)`
//!   - bit j is 0: `(= (extract j j var) #b0)`
//!
//! Then try dropping individual bit constraints. Bits that can be dropped are "don't-cares" --
//! they are irrelevant to the invariant and removing them produces a more general lemma that
//! blocks more states.
//!
//! This is critical for HWMCC benchmarks where state variables are 1-64 bit bitvectors.

use super::*;

/// Maximum BV width for bit-level expansion. Wider BVs create too many constraints
/// and the SMT solver overhead outweighs the generalization benefit.
const MAX_BV_WIDTH_FOR_BIT_EXPANSION: u32 = 64;

/// Extract (variable, value, width) from a BV equality `(= var #bvN)` or `(= #bvN var)`.
pub(super) fn extract_bv_equality(expr: &ChcExpr) -> Option<(ChcVar, u128, u32)> {
    if let ChcExpr::Op(ChcOp::Eq, args) = expr {
        if args.len() == 2 {
            match (args[0].as_ref(), args[1].as_ref()) {
                (ChcExpr::Var(v), ChcExpr::BitVec(val, w))
                | (ChcExpr::BitVec(val, w), ChcExpr::Var(v))
                    if matches!(v.sort, ChcSort::BitVec(_)) =>
                {
                    Some((v.clone(), *val, *w))
                }
                _ => None,
            }
        } else {
            None
        }
    } else {
        None
    }
}

/// Expand a BV equality `(= var #bvN)` into per-bit constraints.
///
/// For each bit position j in 0..width:
/// - If bit j of value is 1: `(= ((_ extract j j) var) #b1)`
/// - If bit j of value is 0: `(= ((_ extract j j) var) #b0)`
fn expand_bv_equality_to_bits(var: &ChcVar, value: u128, width: u32) -> Vec<ChcExpr> {
    let mut bits = Vec::with_capacity(width as usize);
    for j in 0..width {
        let bit_val = (value >> j) & 1;
        let extract = ChcExpr::Op(
            ChcOp::BvExtract(j, j),
            vec![Arc::new(ChcExpr::Var(var.clone()))],
        );
        let bit_const = ChcExpr::BitVec(bit_val, 1);
        bits.push(ChcExpr::eq(extract, bit_const));
    }
    bits
}

/// BV bit-level don't-care generalization.
///
/// Given a cube (conjunction of literals), expand BV equalities into per-bit constraints,
/// then try dropping individual bits. Returns `Some(minimized_conjuncts)` if any bits
/// were dropped, `None` otherwise.
pub(super) fn generalize_bv_bit_level(
    solver: &mut PdrSolver,
    conjuncts: &[ChcExpr],
    predicate: PredicateId,
    level: usize,
) -> Option<Vec<ChcExpr>> {
    // Check if there are any BV equalities worth expanding
    let has_bv_equalities = conjuncts.iter().any(|c| {
        extract_bv_equality(c)
            .map(|(_, _, w)| w <= MAX_BV_WIDTH_FOR_BIT_EXPANSION)
            .unwrap_or(false)
    });

    if !has_bv_equalities {
        return None;
    }

    // Phase 1: Expand BV equalities into per-bit constraints.
    // Non-BV-equality conjuncts are kept as-is.
    let mut expanded: Vec<ChcExpr> = Vec::new();
    let mut is_bit_constraint: Vec<bool> = Vec::new();
    let mut total_expanded_bits: usize = 0;

    for conj in conjuncts {
        if let Some((var, value, width)) = extract_bv_equality(conj) {
            if width <= MAX_BV_WIDTH_FOR_BIT_EXPANSION {
                let bits = expand_bv_equality_to_bits(&var, value, width);
                total_expanded_bits += bits.len();
                for bit in bits {
                    is_bit_constraint.push(true);
                    expanded.push(bit);
                }
            } else {
                is_bit_constraint.push(false);
                expanded.push(conj.clone());
            }
        } else {
            is_bit_constraint.push(false);
            expanded.push(conj.clone());
        }
    }

    if total_expanded_bits == 0 {
        return None;
    }

    // Verify the expanded form is still a valid blocking formula
    let expanded_formula = PdrSolver::build_conjunction(&expanded);
    if !solver.is_inductive_blocking(&expanded_formula, predicate, level) {
        if solver.config.verbose {
            safe_eprintln!(
                "PDR: #7968 BV bit expansion: expanded form not inductive (unexpected), skipping"
            );
        }
        return None;
    }

    if solver.config.verbose {
        safe_eprintln!(
            "PDR: #7968 BV bit expansion: {} conjuncts -> {} expanded ({} bit constraints)",
            conjuncts.len(),
            expanded.len(),
            total_expanded_bits,
        );
    }

    // Phase 2: Don't-care minimization.
    // Try dropping individual bit constraints in reverse order (high bits first).
    let use_self_ind = level <= 1;
    let mut current = expanded;
    let mut current_is_bit = is_bit_constraint;
    let mut dropped_count: usize = 0;

    let mut i = current.len();
    while i > 0 {
        i -= 1;
        if !current_is_bit[i] {
            continue;
        }
        if current.len() <= 1 {
            break;
        }

        let mut candidate: Vec<ChcExpr> = Vec::with_capacity(current.len() - 1);
        let mut candidate_is_bit: Vec<bool> = Vec::with_capacity(current.len() - 1);
        for (j, c) in current.iter().enumerate() {
            if j != i {
                candidate.push(c.clone());
                candidate_is_bit.push(current_is_bit[j]);
            }
        }

        let blocking = PdrSolver::build_conjunction(&candidate);
        let check = if use_self_ind {
            solver.is_inductive_blocking(&blocking, predicate, level)
                && solver.is_self_inductive_blocking(&blocking, predicate)
        } else {
            solver.is_inductive_blocking(&blocking, predicate, level)
        };

        if check {
            if solver.config.verbose {
                safe_eprintln!(
                    "PDR: #7968 BV bit don't-care: dropped bit constraint {}",
                    current[i]
                );
            }
            current = candidate;
            current_is_bit = candidate_is_bit;
            dropped_count += 1;
        }
    }

    if dropped_count == 0 {
        if solver.config.verbose {
            safe_eprintln!("PDR: #7968 BV bit expansion: no don't-care bits found");
        }
        return None;
    }

    if solver.config.verbose {
        safe_eprintln!(
            "PDR: #7968 BV bit don't-care minimization: dropped {} of {} bit constraints, {} conjuncts remain",
            dropped_count,
            total_expanded_bits,
            current.len(),
        );
    }

    // Phase 3: Re-compact surviving bit constraints.
    let result = compact_bit_constraints(conjuncts, &current);

    Some(result)
}

/// Re-compact surviving bit constraints back into BV equalities where possible.
fn compact_bit_constraints(original_conjuncts: &[ChcExpr], expanded: &[ChcExpr]) -> Vec<ChcExpr> {
    use std::collections::BTreeMap;

    let mut var_bits: BTreeMap<String, BTreeMap<u32, (u128, ChcExpr)>> = BTreeMap::new();
    let mut non_bit_conjuncts: Vec<ChcExpr> = Vec::new();

    for expr in expanded {
        if let Some((var_name, bit_pos, bit_val)) = parse_bit_extract_info(expr) {
            var_bits
                .entry(var_name)
                .or_default()
                .insert(bit_pos, (bit_val, expr.clone()));
        } else {
            non_bit_conjuncts.push(expr.clone());
        }
    }

    let mut result = non_bit_conjuncts;

    for (var_name, bits) in &var_bits {
        let original = original_conjuncts.iter().find_map(|c| {
            if let Some((v, val, w)) = extract_bv_equality(c) {
                if v.name == *var_name {
                    return Some((v, val, w));
                }
            }
            None
        });

        if let Some((var, original_val, width)) = original {
            if bits.len() == width as usize {
                result.push(ChcExpr::eq(
                    ChcExpr::Var(var),
                    ChcExpr::BitVec(original_val, width),
                ));
            } else {
                for (_, expr) in bits.values() {
                    result.push(expr.clone());
                }
            }
        } else {
            for (_, expr) in bits.values() {
                result.push(expr.clone());
            }
        }
    }

    result
}

/// Parse bit-extract info from `(= (extract j j var) #bK)`.
fn parse_bit_extract_info(expr: &ChcExpr) -> Option<(String, u32, u128)> {
    if let ChcExpr::Op(ChcOp::Eq, args) = expr {
        if args.len() != 2 {
            return None;
        }

        let (extract_arg, bv_arg) =
            if matches!(args[0].as_ref(), ChcExpr::Op(ChcOp::BvExtract(_, _), _)) {
                (args[0].as_ref(), args[1].as_ref())
            } else if matches!(args[1].as_ref(), ChcExpr::Op(ChcOp::BvExtract(_, _), _)) {
                (args[1].as_ref(), args[0].as_ref())
            } else {
                return None;
            };

        if let ChcExpr::Op(ChcOp::BvExtract(high, low), extract_args) = extract_arg {
            if high != low || extract_args.len() != 1 {
                return None;
            }
            if let ChcExpr::Var(v) = extract_args[0].as_ref() {
                if let ChcExpr::BitVec(bit_val, 1) = bv_arg {
                    return Some((v.name.clone(), *high, *bit_val));
                }
            }
        }
    }
    None
}

#[allow(clippy::unwrap_used)]
#[cfg(test)]
mod tests {
    use super::*;

    fn bv_var(name: &str, width: u32) -> ChcVar {
        ChcVar::new(name, ChcSort::BitVec(width))
    }

    #[test]
    fn test_extract_bv_equality_basic() {
        let var = bv_var("x", 8);
        let eq = ChcExpr::eq(ChcExpr::Var(var.clone()), ChcExpr::BitVec(42, 8));
        let result = extract_bv_equality(&eq);
        assert!(result.is_some());
        let (v, val, w) = result.unwrap();
        assert_eq!(v.name, "x");
        assert_eq!(val, 42);
        assert_eq!(w, 8);
    }

    #[test]
    fn test_extract_bv_equality_reversed() {
        let var = bv_var("y", 16);
        let eq = ChcExpr::eq(ChcExpr::BitVec(0xFF, 16), ChcExpr::Var(var.clone()));
        let result = extract_bv_equality(&eq);
        assert!(result.is_some());
        let (v, val, w) = result.unwrap();
        assert_eq!(v.name, "y");
        assert_eq!(val, 0xFF);
        assert_eq!(w, 16);
    }

    #[test]
    fn test_extract_bv_equality_not_bv() {
        let var = ChcVar::new("z", ChcSort::Int);
        let eq = ChcExpr::eq(ChcExpr::Var(var), ChcExpr::Int(5));
        assert!(extract_bv_equality(&eq).is_none());
    }

    #[test]
    fn test_expand_bv_equality_to_bits_4bit() {
        let var = bv_var("s", 4);
        let bits = expand_bv_equality_to_bits(&var, 0b1010, 4);
        assert_eq!(bits.len(), 4);

        let info = parse_bit_extract_info(&bits[0]).unwrap();
        assert_eq!(info, ("s".to_string(), 0, 0));

        let info = parse_bit_extract_info(&bits[1]).unwrap();
        assert_eq!(info, ("s".to_string(), 1, 1));

        let info = parse_bit_extract_info(&bits[2]).unwrap();
        assert_eq!(info, ("s".to_string(), 2, 0));

        let info = parse_bit_extract_info(&bits[3]).unwrap();
        assert_eq!(info, ("s".to_string(), 3, 1));
    }

    #[test]
    fn test_compact_preserves_full_variable() {
        let var = bv_var("x", 4);
        let original = vec![ChcExpr::eq(
            ChcExpr::Var(var.clone()),
            ChcExpr::BitVec(0b1010, 4),
        )];
        let expanded = expand_bv_equality_to_bits(&var, 0b1010, 4);
        let compacted = compact_bit_constraints(&original, &expanded);
        assert_eq!(compacted.len(), 1);
    }

    #[test]
    fn test_compact_keeps_partial_bits() {
        let var = bv_var("x", 4);
        let original = vec![ChcExpr::eq(
            ChcExpr::Var(var.clone()),
            ChcExpr::BitVec(0b1010, 4),
        )];
        let mut expanded = expand_bv_equality_to_bits(&var, 0b1010, 4);
        expanded.remove(2);
        let compacted = compact_bit_constraints(&original, &expanded);
        assert_eq!(compacted.len(), 3);
    }
}
