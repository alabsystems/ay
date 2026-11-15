// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Unsigned bit-vector order in the ground `evaluate` fragment.
//!
//! Admitted because pinned carcara 1.1.0 (git 9a352ee) evaluates
//! `bvult`/`bvule`/`bvugt`/`bvuge` over the stored unsigned value
//! (`bitvec_comparison_op!` over `as_bitvec`), exactly as SMT-LIB defines
//! them, so an internally accepted step is one carcara re-derives.
//!
//! Only two LITERAL operands are admitted. Carcara misevaluates operators an
//! operand could nest (`bvsub` and the signed family read a negative operand
//! as its magnitude, `extract` drops its top bit), and this admission must not
//! let an `evaluate` step rest on one of them. The signed comparisons stay out
//! of the fragment for the same reason.

use super::*;

/// The admitted heads, in the order of the arithmetic comparison each maps to.
pub(super) const UNSIGNED_ORDERS: [&str; 4] = ["bvult", "bvule", "bvugt", "bvuge"];
const ARITHMETIC_ORDERS: [&str; 4] = ["<", "<=", ">", ">="];

impl Evaluator<'_> {
    /// The value of `(name a b)` for an unsigned order `name` over two
    /// same-width bit-vector literals, or `None` for any other head or shape
    /// (it is the last arm of `eval_app`).
    pub(super) fn eval_unsigned_order(
        &mut self,
        name: &str,
        args: &[TermId],
        depth: usize,
    ) -> Option<Value> {
        let order = UNSIGNED_ORDERS.iter().position(|&order| order == name)?;
        let literal = |arg: &TermId| {
            matches!(
                self.terms.get(*arg),
                TermData::Const(Constant::BitVec { .. })
            )
        };
        if args.len() != 2 || !args.iter().all(literal) {
            return None;
        }
        let (_, values) = self.eval_bit_vectors(args, depth)?;
        compare(ARITHMETIC_ORDERS[order], &values[0], &values[1]).map(Value::Bool)
    }
}

#[cfg(test)]
mod tests;
