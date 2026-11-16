// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Upper bounds on the variables one expression node can allocate — leaf
//! inputs and gate outputs — before any structural cache savings.
//!
//! The preflight charges these per DISTINCT node, reserves the encoder's
//! stores from their sum and refuses a sum above `max_estimated_gate_work`;
//! the encoder's actual gate count is checked against the same cap after
//! construction (`cnf::admit_shape`). Each bound is the node's own worst
//! case, so the preflight neither admits an encoding it cannot hold nor
//! refuses one far inside the cap. Measured 2026-09-29 on external-codegen's
//! integer-to-`f64` round trips: the charges these replaced (a width's worth
//! per rewiring node, 2-8 per bit elsewhere) estimated 119,000-199,000 gates
//! for encodings of 13,057 and 28,872.

/// A leaf allocates its input bits, once per name.
pub(super) fn leaf(width: usize) -> usize {
    width
}

/// A constant's bits are the encoder's two shared constant gates.
pub(super) fn constant(width: usize) -> usize {
    width.min(2)
}

/// Sign extension repeats the sign wire; zero extension adds the shared zero.
pub(super) fn extension(zero_padded: bool) -> usize {
    usize::from(zero_padded)
}

/// A slice selects existing wires.
pub(super) const EXTRACT: usize = 0;

/// A shift by a literal rewires its operand and may add the shared zero.
pub(super) const LITERAL_SHIFT: usize = 1;

/// One gate per bit: `bvnot`, `bvand`, `bvor`, `bvxor`.
pub(super) fn bitwise(width: usize) -> usize {
    width
}

/// A ripple-carry chain — `bvadd`, `bvsub` or a carry-out: at most `width`
/// complements of the subtrahend, the carry-in constant, `width` sums or
/// carries and `width - 1` further carries.
pub(super) fn ripple(width: usize) -> usize {
    width.saturating_mul(3)
}

/// `bvult`: per bit a complement, a less-than, a bit equality, a carried
/// equality and their disjunction.
pub(super) fn compare(width: usize) -> usize {
    width.saturating_mul(5)
}

/// `=`: a bit equality per bit and the conjunction chain over them.
pub(super) fn equality(width: usize) -> usize {
    width.saturating_mul(2)
}

pub(super) fn shift(width: usize) -> usize {
    // Each of ceil(log2(width)) stages and the final saturation layer uses
    // width four-gate multiplexers. One zero gate and at most width-1 OR
    // gates cover the complete high-count reduction, including width one.
    let stages = width.saturating_sub(1).bit_width();
    width
        .saturating_mul(4)
        .saturating_mul(stages as usize + 1)
        .saturating_add(width)
}

pub(super) fn multiply(width: usize) -> usize {
    // The truncated partial-product triangle has width*(width+1)/2 ANDs.
    // Each of width-1 subsequent rows adds width sums and width-1 carries.
    // Include the shared zero even when another expression already made it.
    let products = width.saturating_mul(width.saturating_add(1)) / 2;
    let adders = width
        .saturating_sub(1)
        .saturating_mul(width.saturating_mul(2).saturating_sub(1));
    products.saturating_add(adders).saturating_add(1)
}

pub(super) fn divide(width: usize) -> usize {
    // `width` complements of the divisor, the two shared constants, and per
    // step `width + 1` sums and carries, one negated quotient bit and a
    // three-gate multiplexer per remainder bit (`divide.rs`).
    let per_step = width
        .saturating_add(1)
        .saturating_mul(2)
        .saturating_add(1)
        .saturating_add(width.saturating_mul(3));
    width
        .saturating_mul(per_step)
        .saturating_add(width)
        .saturating_add(2)
}

#[cfg(test)]
mod tests {
    use crate::bv_blast_solver::*;

    #[test]
    fn topology_bounds_cover_constructed_graphs_at_every_internal_width() {
        for width in 1..=128 {
            for op in 0..6 {
                let a = BvExpr::leaf("a", width);
                let b = BvExpr::leaf("b", width);
                let expression = match op {
                    0 => BvExpr::shl(a, b),
                    1 => BvExpr::lshr(a, b),
                    2 => BvExpr::ashr(a, b),
                    3 => BvExpr::mul(a, b),
                    4 => BvExpr::udiv(a, b),
                    _ => BvExpr::urem(a, b),
                };
                let bound = match op {
                    3 => super::multiply(width as usize),
                    4 | 5 => super::divide(width as usize),
                    _ => super::shift(width as usize),
                };
                let mut vars = VarTable::default();
                let mut gates = Vec::new();
                let mut clauses = Vec::new();
                let output = ExprBlaster::new(None, &mut || true)
                    .blast(&expression, &mut vars, &mut gates, &mut clauses)
                    .unwrap();
                assert_eq!(output.len(), width as usize);
                assert!(
                    gates.len() <= bound,
                    "width {width}, op {op}: {} > {bound}",
                    gates.len()
                );
                let mut limits = BvExprProofLimits::conservative_external(
                    Instant::now() + Duration::from_secs(30),
                    1000,
                );
                let mut census = BvExprPreflight::default();
                preflight_bv_expr(&expression, &limits, &mut census, 1).unwrap();
                limits.max_estimated_gate_work = census.estimated_gate_work - 1;
                assert!(matches!(
                    preflight_bv_expr(&expression, &limits, &mut BvExprPreflight::default(), 1),
                    Err(BvExprExportError::ResourceLimit {
                        resource: "estimated bit-blast gates",
                        ..
                    })
                ));
            }
        }
    }

    /// Every node kind the tight bounds cover, over two leaves (or one), at
    /// every internal width: the preflight's estimate of the whole expression
    /// covers the variables and gates a fresh encoder actually allocates.
    #[test]
    fn node_bounds_cover_allocated_variables_at_every_internal_width() {
        for width in 1..=128_u32 {
            let low = u128::from(width > 1) << (width - 1) | 1;
            for op in 0..16 {
                let a = BvExpr::leaf("a", width);
                let b = BvExpr::leaf("b", width);
                let expression = match op {
                    0 => BvExpr::const_val(low, width),
                    1 => BvExpr::zero_ext(BvExpr::extract(a, 0, 0), width - 1),
                    2 => BvExpr::sign_ext(BvExpr::extract(a, 0, 0), width - 1),
                    3 => BvExpr::extract(a, width - 1, 0),
                    4 => BvExpr::not(a),
                    5 => BvExpr::and(a, b),
                    6 => BvExpr::or(a, b),
                    7 => BvExpr::xor(a, b),
                    8 => BvExpr::add(a, b),
                    9 => BvExpr::sub(a, b),
                    10 => BvExpr::Ult(Box::new(a), Box::new(b)),
                    11 => BvExpr::eq(a, b),
                    12 => BvExpr::carry_out_add(a, b),
                    13 => BvExpr::carry_out_sub(a, b),
                    14 => BvExpr::shl(a, BvExpr::const_val(1, width)),
                    _ => BvExpr::lshr(a, BvExpr::const_val(u128::from(width), width)),
                };
                let mut vars = VarTable::default();
                let mut gates = Vec::new();
                let mut clauses = Vec::new();
                ExprBlaster::new(None, &mut || true)
                    .blast(&expression, &mut vars, &mut gates, &mut clauses)
                    .unwrap();
                let limits = BvExprProofLimits::conservative_external(
                    Instant::now() + Duration::from_secs(30),
                    1000,
                );
                let mut census = BvExprPreflight::default();
                preflight_bv_expr(&expression, &limits, &mut census, 1).unwrap();
                assert!(
                    vars.len() <= census.estimated_gate_work
                        && gates.len() <= census.estimated_gate_work,
                    "width {width}, op {op}: {} vars, {} gates > {}",
                    vars.len(),
                    gates.len(),
                    census.estimated_gate_work
                );
            }
        }
    }

    /// The shape of external-codegen's integer-to-`f64` lowering: a 54-deep `ite`
    /// chain on the leading one of a 64-bit word, each branch a literal
    /// shift of it, lowered as the checker lowers `ite` (a sign-extended
    /// condition masking both branches). Its 4,467 variables are estimated
    /// at 14,052 (the encoder's constant folding is not credited); the
    /// charges these bounds replaced estimated 58,934.
    #[test]
    fn an_ite_chain_of_shifted_words_is_estimated_near_its_encoding() {
        let a = BvExpr::leaf("a", 64);
        let mut chain = BvExpr::const_val(0, 64);
        for bit in 0..54 {
            let mask = BvExpr::sign_ext(BvExpr::extract(a.clone(), bit, bit), 63);
            let branch = BvExpr::shl(a.clone(), BvExpr::const_val(u128::from(63 - bit), 64));
            chain = BvExpr::or(
                BvExpr::and(mask.clone(), branch),
                BvExpr::and(BvExpr::not(mask), chain),
            );
        }
        let mut vars = VarTable::default();
        ExprBlaster::new(None, &mut || true)
            .blast(&chain, &mut vars, &mut Vec::new(), &mut Vec::new())
            .unwrap();
        let limits = BvExprProofLimits::conservative_external(
            Instant::now() + Duration::from_secs(30),
            1000,
        );
        let mut census = BvExprPreflight::default();
        preflight_bv_expr(&chain, &limits, &mut census, 1).unwrap();
        assert!(
            vars.len() <= census.estimated_gate_work
                && census.estimated_gate_work <= 4 * vars.len(),
            "{} variables estimated at {}",
            vars.len(),
            census.estimated_gate_work
        );
    }
}
