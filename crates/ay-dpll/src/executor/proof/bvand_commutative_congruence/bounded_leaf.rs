// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Pure-syntax admission for the walker's GENERAL leaf: a differing pair small
//! enough, and free enough of arithmetic, to hand the recognizer whole.
//!
//! The walker lifts equalities through identical application heads with
//! `cong`. Where the heads differ (or a lockstep descent finds no proof), the
//! pair is a leaf. The named leaf shapes in `leaf_shapes` cover specific gate
//! rewrites; this predicate covers every other leaf whose bit-blast is pure
//! wiring and Boolean gates — slices, extensions, concatenation, bitwise
//! logic, `ite` and equality, over a bounded DAG on each side. Any adder,
//! comparator, shifter, multiplier or divider keeps the pair out: a miter over
//! two differently shaped arithmetic circuits is exactly the refutation the
//! walker exists to avoid, and an arithmetic identity such as
//! `7x + 21 = 7(x + 3)` belongs to the polynomial lanes the caller tries next,
//! not to a bit-blast.
//!
//! That bound is what makes the leaf worth taking: a collapse such as
//! `(bvmul (concat (ite (= ((_ extract 31 31) w) #b1) ones zeros) w) ..) =
//! (bvmul ((_ sign_extend 32) w) ..)` differs only below the multiplier, so
//! proving the two sign-extension spellings equal and lifting that through the
//! shared `bvmul` with `cong` replaces a 64-bit multiplier miter — which the
//! recognizer's bit-blast/SAT refutation cannot close in a solve budget — by
//! two wiring identities it closes at once.
//!
//! Shape selection is not authorization. Like every leaf predicate, this one
//! decides only WHICH crux the walker hands `ay_proof::recognize_bv_bitblast`,
//! the independent semantic authority; a false pair is refused there. Nothing
//! here mints a term or a proof step.

use super::*;

/// Distinct DAG nodes one side of a general leaf may have. The recognizer's
/// own limits still apply; this keeps the walker from handing it large cruxes
/// it would only refuse after paying for the attempt.
const MAX_BOUNDED_LEAF_NODES: usize = 512;

/// Operators whose bit-blast is wiring or a per-bit Boolean gate (equality is
/// an AND over per-bit XNORs). Everything else is refused, including every
/// arithmetic, comparison and shift operator.
const WIRING_OPERATORS: &[&str] = &[
    "concat",
    "extract",
    "zero_extend",
    "sign_extend",
    "repeat",
    "rotate_left",
    "rotate_right",
    "bvnot",
    "bvand",
    "bvor",
    "bvxor",
    "bvnand",
    "bvnor",
    "bvxnor",
    "bvcomp",
    "=",
    "distinct",
    "not",
    "and",
    "or",
    "xor",
    "=>",
    "ite",
];

/// Is the `left`/`right` pair an admissible general leaf: the same Boolean or
/// bit-vector sort, and each side a bounded wiring-only DAG?
pub(super) fn is_bounded_wiring_leaf_pair(terms: &TermStore, left: TermId, right: TermId) -> bool {
    let sort = terms.sort(left);
    if sort != terms.sort(right) || !matches!(sort, Sort::Bool | Sort::BitVec(_)) {
        return false;
    }
    is_bounded_wiring_dag(terms, left) && is_bounded_wiring_dag(terms, right)
}

fn is_bounded_wiring_dag(terms: &TermStore, root: TermId) -> bool {
    let mut seen = DetHashSet::default();
    let mut stack = vec![root];
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        if seen.len() > MAX_BOUNDED_LEAF_NODES {
            return false;
        }
        match terms.get(term) {
            TermData::Const(_) | TermData::Var(_, _) => {}
            TermData::Not(inner) => stack.push(*inner),
            TermData::Ite(condition, then_term, else_term) => {
                stack.extend([*condition, *then_term, *else_term]);
            }
            TermData::App(symbol, args) => {
                if !WIRING_OPERATORS.contains(&symbol.name()) {
                    return false;
                }
                stack.extend(args.iter().copied());
            }
            // Binders, lets and any future node kind are outside the QF_BV
            // fragment the recognizer decides; refuse them here rather than
            // hand them over.
            _ => return false,
        }
    }
    true
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sign_bit_spelling(terms: &mut TermStore, word: TermId, width: u32) -> TermId {
        let msb = terms.mk_app(
            Symbol::indexed("extract", vec![width - 1, width - 1]),
            [word],
            Sort::bitvec(1),
        );
        let one = terms.mk_bitvec(1u32.into(), 1);
        let is_negative = terms.mk_app(Symbol::named("="), [msb, one], Sort::Bool);
        let ones = terms.mk_bitvec((num_bigint::BigInt::from(1) << width) - 1, width);
        let zeros = terms.mk_bitvec(0u32.into(), width);
        let fill = terms.mk_ite_raw(is_negative, ones, zeros);
        terms.mk_app(
            Symbol::named("concat"),
            [fill, word],
            Sort::bitvec(2 * width),
        )
    }

    /// Wiring-only pairs are admitted; any arithmetic on either side is not,
    /// including a product by a constant and an addition.
    #[test]
    fn admits_wiring_and_refuses_arithmetic() {
        let mut terms = TermStore::new();
        let w = terms.mk_var("w", Sort::bitvec(32));
        let v = terms.mk_var("v", Sort::bitvec(64));
        let spelled = sign_bit_spelling(&mut terms, w, 32);
        let sext = terms.mk_app(
            Symbol::indexed("sign_extend", vec![32]),
            [w],
            Sort::bitvec(64),
        );
        assert!(is_bounded_wiring_leaf_pair(&terms, spelled, sext));

        let product = terms.mk_app(Symbol::named("bvmul"), [sext, v], Sort::bitvec(64));
        assert!(!is_bounded_wiring_leaf_pair(&terms, spelled, product));
        assert!(!is_bounded_wiring_leaf_pair(&terms, product, spelled));

        let three = terms.mk_bitvec(3u32.into(), 64);
        let scaled = terms.mk_app(Symbol::named("bvmul"), [v, three], Sort::bitvec(64));
        assert!(!is_bounded_wiring_leaf_pair(&terms, scaled, v));
        let sum = terms.mk_app(Symbol::named("bvadd"), [v, three], Sort::bitvec(64));
        assert!(!is_bounded_wiring_leaf_pair(&terms, sum, v));
        let below = terms.mk_app(Symbol::named("bvult"), [v, three], Sort::Bool);
        let bit = terms.mk_app(
            Symbol::indexed("extract", vec![63, 63]),
            [v],
            Sort::bitvec(1),
        );
        let one = terms.mk_bitvec(1u32.into(), 1);
        let is_set = terms.mk_app(Symbol::named("="), [bit, one], Sort::Bool);
        assert!(!is_bounded_wiring_leaf_pair(&terms, below, is_set));

        let flipped = terms.mk_app(Symbol::named("bvxor"), [v, three], Sort::bitvec(64));
        let flipped_back = terms.mk_app(Symbol::named("bvxor"), [three, v], Sort::bitvec(64));
        assert!(is_bounded_wiring_leaf_pair(&terms, flipped, flipped_back));

        let quotient = terms.mk_app(Symbol::named("bvudiv"), [v, sext], Sort::bitvec(64));
        assert!(!is_bounded_wiring_leaf_pair(&terms, quotient, v));
    }

    /// Sort mismatches and non-BV sorts never reach the recognizer.
    #[test]
    fn refuses_mismatched_and_non_bv_sorts() {
        let mut terms = TermStore::new();
        let a = terms.mk_var("a", Sort::bitvec(8));
        let b = terms.mk_var("b", Sort::bitvec(16));
        let x = terms.mk_var("x", Sort::Int);
        let y = terms.mk_var("y", Sort::Int);
        assert!(!is_bounded_wiring_leaf_pair(&terms, a, b));
        assert!(!is_bounded_wiring_leaf_pair(&terms, x, y));
    }

    /// A side over the node budget is refused even when it is wiring-only.
    #[test]
    fn refuses_sides_over_the_node_budget() {
        let mut terms = TermStore::new();
        let sort = Sort::bitvec(8);
        let mut chain = terms.mk_var("x0", sort.clone());
        for index in 1..=MAX_BOUNDED_LEAF_NODES {
            let next = terms.mk_var(format!("x{index}"), sort.clone());
            chain = terms.mk_app(Symbol::named("bvxor"), [chain, next], sort.clone());
        }
        let other = terms.mk_var("y", sort);
        assert!(!is_bounded_wiring_leaf_pair(&terms, chain, other));
    }
}
