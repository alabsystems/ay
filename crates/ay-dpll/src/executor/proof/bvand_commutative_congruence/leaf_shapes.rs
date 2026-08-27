// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Pure-syntax LEAF SHAPE predicates: WHICH crux to hand the recognizer.
//!
//! The boundary this module draws is the one the walker's own comments keep
//! restating: shape selection is not authorization. Every predicate here
//! decides only whether two terms are an instance of one of the local
//! bit-vector rewrite leaves the walker admits — never whether the resulting
//! equality is TRUE. The walker in the parent module gates each pair these
//! select through `ay_proof::recognize_bv_bitblast`, the independent semantic
//! authority, so nothing in this file can authorize a step: no `mk_app`, no
//! proof step, and no recognizer call appears below.
//!
//! `TermStore` is hash-consed, so `TermId` equality IS syntactic identity and
//! each of these is O(1): no assignment is enumerated and no bounded-width
//! budget is consumed. Each predicate's admissible set is pinned in lock-step
//! with a specific `ay_proof::alethe_printer` lowering, named in its own doc.
//!
//! The unit tests that pin these predicates live with them — both the syntax
//! gate in the negative direction and the authorisation lane that shows the
//! semantic recognizer, not the predicate, is what decides the crux.

use super::*;

/// Is `gate` the bit-wise idempotent application `(bvand t t)` / `(bvor t t)`
/// whose repeated operand is exactly `operand`?
///
/// PURE SYNTAX, and deliberately so — this decides only which small crux to
/// hand the recognizer, never whether that crux is true. `TermStore` is
/// hash-consed, so `TermId` equality IS syntactic identity, and the whole
/// side condition is O(1): no assignment is enumerated and no bounded-width
/// budget is consumed.
///
/// The operator list is exactly the printer's `decode_idempotent_bv_gate`
/// (`ay_proof::alethe_printer`) and must stay in lock-step with it, since a
/// leaf this admits but the printer cannot lower falls back to the honest
/// `hole`. `bvxor` must NEVER be added: `(bvxor t t)` is zero rather than `t`,
/// and even that true identity has no one-step `*_simplify` discharge.
pub(super) fn is_idempotent_bv_gate_of(terms: &TermStore, gate: TermId, operand: TermId) -> bool {
    let TermData::App(Symbol::Named(op), args) = terms.get(gate) else {
        return false;
    };
    if !matches!(op.as_str(), "bvand" | "bvor") {
        return false;
    }
    let [first, second] = args.as_slice() else {
        return false;
    };
    *first == *second && *first == operand && matches!(terms.sort(gate), Sort::BitVec(_))
}

/// The STRICT unsigned comparison whose negation is exactly `op`, for the ONE
/// operand order this walker admits (`(bvuge a b)` is `(not (bvult a b))`, NOT
/// `(not (bvugt b a))` — same fact, different printed operand order, and the
/// printer's derivation is per-operand-position).
///
/// The table is exactly the printer's `decode_unsigned_compare_duality`
/// (`ay_proof::alethe_printer`) and must stay in lock-step with it: a leaf this
/// admits but the printer cannot lower falls back to the honest `hole`.
///
/// SIGNED comparisons (`bvsge`/`bvslt`, `bvsle`/`bvsgt`) are deliberately
/// ABSENT. The identity holds for them too, but Carcara's pseudo-Boolean
/// lowering for a signed comparison carries a separate negative-weight sign
/// term, so it is a DIFFERENT derivation that would need its own
/// machine-checked witness. Admitting it here without that would relocate the
/// hole rather than close it.
fn unsigned_strict_dual(op: &str) -> Option<&'static str> {
    match op {
        "bvuge" => Some("bvult"),
        "bvule" => Some("bvugt"),
        _ => None,
    }
}

/// Strip one negation, in either spelling the store can hold.
fn decode_not(terms: &TermStore, term: TermId) -> Option<TermId> {
    match terms.get(term) {
        TermData::Not(inner) => Some(*inner),
        TermData::App(Symbol::Named(name), args) if name == "not" && args.len() == 1 => {
            Some(args[0])
        }
        _ => None,
    }
}

/// Is `non_strict` an unsigned comparison `(bvuge a b)` / `(bvule a b)` whose
/// exact negated strict dual — `(not (bvult a b))` / `(not (bvugt a b))` over
/// the SAME two operands in the SAME order — is `negated_strict`?
///
/// PURE SYNTAX, exactly like [`is_idempotent_bv_gate_of`], and for the same
/// reason: this decides only which small crux to hand the recognizer, never
/// whether that crux is true. `TermStore` is hash-consed, so the operand
/// comparisons are `TermId` identity and the whole side condition is O(1) — no
/// assignment is enumerated and no bounded-width budget is consumed.
pub(super) fn is_unsigned_compare_duality_of(
    terms: &TermStore,
    non_strict: TermId,
    negated_strict: TermId,
) -> bool {
    let TermData::App(Symbol::Named(op), args) = terms.get(non_strict) else {
        return false;
    };
    let Some(strict) = unsigned_strict_dual(op.as_str()) else {
        return false;
    };
    let [left_operand, right_operand] = args.as_slice() else {
        return false;
    };
    let (left_operand, right_operand) = (*left_operand, *right_operand);
    let Some(inner) = decode_not(terms, negated_strict) else {
        return false;
    };
    let TermData::App(Symbol::Named(inner_op), inner_args) = terms.get(inner) else {
        return false;
    };
    inner_op.as_str() == strict
        && inner_args.as_slice() == [left_operand, right_operand]
        && matches!(terms.sort(left_operand), Sort::BitVec(_))
        && terms.sort(left_operand) == terms.sort(right_operand)
}

/// True iff `term` is the bit-vector constant `value` at any width matching
/// `expected_width`.
fn is_bv_const(terms: &TermStore, term: TermId, value: u64, expected_width: u32) -> bool {
    matches!(
        terms.get(term),
        TermData::Const(Constant::BitVec { value: v, width })
            if *width == expected_width && *v == value.into()
    )
}

/// Is the pair `(bvult v ONE)` / `(= z ZERO)` the ZERO-TEST duality — the
/// unsigned `x < 1  <=>  x = 0` identity — over the SAME `v`, where the
/// equality's subject `z` is either `v` itself or an idempotent gate collapse
/// of it (`(bvand v v)` / `(bvor v v)`)?
///
/// This is the DivZero/NullIfZero guard-carrier shape a verified code
/// generator emits since its guards were re-phrased uniformly over `bvult`:
/// the INTENDED trap set is spelled `(bvult lhs (_ bv1 w))` while the EMITTED
/// x86 `E` condition code tests `(= (bvand lhs lhs) (_ bv0 w))`. Neither the
/// idempotency leaf (different top symbols: `bvult` against `=`) nor the
/// comparison-duality leaf (no negation involved) can reach it, so it needs
/// its own leaf or the whole rewrite spine is refused and the emitted Alethe
/// keeps a hole — which, downstream, is the difference between a code
/// generator's guard canary discharging and 18 of 18 programs failing closed
/// at -O0 on any host without a matching DRAT cert.
///
/// The admissible set is exactly what the printer's
/// `format_bv_ult_one_zero_equiv` lowers (constant literal ONE on the `bvult`
/// side, constant literal ZERO on the equality side, same width, `z` equal to
/// `v` or its idempotent collapse) and must stay in lock-step with it: a leaf
/// this admits but the printer cannot lower falls back to the honest `hole`.
///
/// Nothing is authorized here: like every leaf in this walker, the caller
/// still gates the pair through `ay_proof::recognize_bv_bitblast`, so a false
/// pair (e.g. `bvult v 2`, or a ZERO of the wrong width) is refused by the
/// independent semantic recognizer even if a future edit widened this match.
pub(super) fn is_ult_one_eq_zero_of(terms: &TermStore, ult_side: TermId, eq_side: TermId) -> bool {
    let TermData::App(Symbol::Named(ult_op), ult_args) = terms.get(ult_side) else {
        return false;
    };
    if ult_op.as_str() != "bvult" {
        return false;
    }
    let [subject, one] = ult_args.as_slice() else {
        return false;
    };
    let (subject, one) = (*subject, *one);
    let Sort::BitVec(bits) = terms.sort(subject) else {
        return false;
    };
    let width = bits.width;
    if !is_bv_const(terms, one, 1, width) {
        return false;
    }
    let TermData::App(Symbol::Named(eq_op), eq_args) = terms.get(eq_side) else {
        return false;
    };
    if eq_op.as_str() != "=" {
        return false;
    }
    let [zero_subject, zero] = eq_args.as_slice() else {
        return false;
    };
    let (zero_subject, zero) = (*zero_subject, *zero);
    if !is_bv_const(terms, zero, 0, width) {
        return false;
    }
    zero_subject == subject || is_idempotent_bv_gate_of(terms, zero_subject, subject)
}

#[cfg(test)]
mod unsigned_compare_duality_tests {
    use super::*;

    /// Build `(<op> lhs rhs)` and `(not (<dual> <a> <b>))` over fresh width-`w`
    /// variables, returning both plus the store.
    fn pair(width: u32, op: &str, dual: &str, dual_swapped: bool) -> (TermStore, TermId, TermId) {
        let mut terms = TermStore::new();
        let sort = Sort::bitvec(width);
        let lhs = terms.mk_var("lhs", sort.clone());
        let rhs = terms.mk_var("rhs", sort);
        let non_strict = terms.mk_app(Symbol::named(op), [lhs, rhs], Sort::Bool);
        let strict_args = if dual_swapped { [rhs, lhs] } else { [lhs, rhs] };
        let strict = terms.mk_app(Symbol::named(dual), strict_args, Sort::Bool);
        let negated = terms.mk_not(strict);
        (terms, non_strict, negated)
    }

    /// The two admitted pairs are recognized in BOTH argument orders.
    #[test]
    fn admits_exactly_the_two_unsigned_dual_pairs() {
        for (op, dual) in [("bvuge", "bvult"), ("bvule", "bvugt")] {
            let (terms, non_strict, negated) = pair(32, op, dual, false);
            assert!(
                is_unsigned_compare_duality_of(&terms, non_strict, negated),
                "{op}/{dual} must be recognized"
            );
            assert!(
                !is_unsigned_compare_duality_of(&terms, negated, non_strict),
                "{op}/{dual}: the predicate is oriented; the caller tries both orders"
            );
        }
    }

    /// SYNTAX GATE, negative direction. Every one of these must be refused by
    /// the predicate itself, so the recognizer is never even consulted.
    #[test]
    fn refuses_wrong_operator_wrong_order_and_signed() {
        // A genuinely FALSE pair: `bvugt` and `not bvult` differ at lhs == rhs.
        let (terms, non_strict, negated) = pair(32, "bvugt", "bvult", false);
        assert!(!is_unsigned_compare_duality_of(&terms, non_strict, negated));
        // Right fact, WRONG printed operand order — the printer's derivation is
        // per-operand-position, so this must not reach it.
        let (terms, non_strict, negated) = pair(32, "bvuge", "bvult", true);
        assert!(!is_unsigned_compare_duality_of(&terms, non_strict, negated));
        // Crossed duals: `bvuge` against `not bvugt` is false at lhs == rhs.
        let (terms, non_strict, negated) = pair(32, "bvuge", "bvugt", false);
        assert!(!is_unsigned_compare_duality_of(&terms, non_strict, negated));
        // SIGNED: true, but out of the printer's lane, so it must stay a hole.
        for (op, dual) in [("bvsge", "bvslt"), ("bvsle", "bvsgt")] {
            let (terms, non_strict, negated) = pair(32, op, dual, false);
            assert!(
                !is_unsigned_compare_duality_of(&terms, non_strict, negated),
                "{op}/{dual} has no printer lowering, so the leaf must decline"
            );
        }
    }

    /// AUTHORISATION LANE. The predicate only SELECTS a crux; this pins that the
    /// independent semantic gate actually decides it — accepting the true pairs
    /// at every width the guard-carrier canary asks for (8/32/64), and REFUSING
    /// the false `bvugt` variant. A regression here would turn the new leaf into
    /// a relocated hole, never into a false authorisation.
    #[test]
    fn recognizer_authorizes_true_pairs_and_refuses_false_ones() {
        for width in [8_u32, 16, 32, 64] {
            for (op, dual) in [("bvuge", "bvult"), ("bvule", "bvugt")] {
                let (mut terms, non_strict, negated) = pair(width, op, dual, false);
                let crux = terms.mk_app(Symbol::named("="), [non_strict, negated], Sort::Bool);
                assert!(
                    ay_proof::recognize_bv_bitblast(&terms, &[crux]),
                    "w={width} {op}/{dual}: the semantic gate must decide the crux"
                );
            }
            let (mut terms, non_strict, negated) = pair(width, "bvugt", "bvult", false);
            let crux = terms.mk_app(Symbol::named("="), [non_strict, negated], Sort::Bool);
            assert!(
                !ay_proof::recognize_bv_bitblast(&terms, &[crux]),
                "w={width}: a FALSE pair must be refused by the semantic gate"
            );
        }
    }
}

#[cfg(test)]
mod ult_one_eq_zero_tests {
    use super::*;

    /// Build `(bvult v 1)` and `(= z 0)` over a fresh width-`w` variable,
    /// with `z` either the variable itself or its `(bvand v v)` collapse.
    fn zero_test_pair(width: u32, gate: bool) -> (TermStore, TermId, TermId) {
        let mut terms = TermStore::new();
        let sort = Sort::bitvec(width);
        let v = terms.mk_var("v", sort.clone());
        let one = terms.mk_bitvec(1u32.into(), width);
        let zero = terms.mk_bitvec(0u32.into(), width);
        let ult = terms.mk_app(Symbol::named("bvult"), [v, one], Sort::Bool);
        let z = if gate {
            terms.mk_app(Symbol::named("bvand"), [v, v], sort)
        } else {
            v
        };
        let eqz = terms.mk_app(Symbol::named("="), [z, zero], Sort::Bool);
        (terms, ult, eqz)
    }

    /// Both the pure and the idempotent-gate forms are recognized, in the one
    /// orientation the predicate is written for (the caller tries both).
    #[test]
    fn admits_pure_and_gate_forms() {
        for gate in [false, true] {
            let (terms, ult, eqz) = zero_test_pair(32, gate);
            assert!(
                is_ult_one_eq_zero_of(&terms, ult, eqz),
                "gate={gate}: the zero-test duality must be recognized"
            );
        }
    }

    /// SYNTAX GATE, negative direction: wrong bound, wrong comparand, width
    /// mismatch, and a gate over a DIFFERENT variable are all refused by the
    /// predicate itself.
    #[test]
    fn refuses_wrong_constant_width_and_subject() {
        let mut terms = TermStore::new();
        let sort = Sort::bitvec(32);
        let v = terms.mk_var("v", sort.clone());
        let w = terms.mk_var("w", sort.clone());
        let one = terms.mk_bitvec(1u32.into(), 32);
        let two = terms.mk_bitvec(2u32.into(), 32);
        let zero = terms.mk_bitvec(0u32.into(), 32);
        let zero64 = terms.mk_bitvec(0u32.into(), 64);
        let ult_one = terms.mk_app(Symbol::named("bvult"), [v, one], Sort::Bool);
        let ult_two = terms.mk_app(Symbol::named("bvult"), [v, two], Sort::Bool);
        let eq_zero = terms.mk_app(Symbol::named("="), [v, zero], Sort::Bool);
        let eq_one = terms.mk_app(Symbol::named("="), [v, one], Sort::Bool);
        let eq_zero64 = terms.mk_app(Symbol::named("="), [v, zero64], Sort::Bool);
        let wgate = terms.mk_app(Symbol::named("bvand"), [w, w], sort);
        let eq_other = terms.mk_app(Symbol::named("="), [wgate, zero], Sort::Bool);
        assert!(
            !is_ult_one_eq_zero_of(&terms, ult_two, eq_zero),
            "bvult v 2 is not a zero test"
        );
        assert!(
            !is_ult_one_eq_zero_of(&terms, ult_one, eq_one),
            "(= v 1) is not a zero test"
        );
        assert!(
            !is_ult_one_eq_zero_of(&terms, ult_one, eq_zero64),
            "width-mismatched zero must be refused"
        );
        assert!(
            !is_ult_one_eq_zero_of(&terms, ult_one, eq_other),
            "a gate over a DIFFERENT variable must be refused"
        );
    }

    /// AUTHORISATION LANE: the independent semantic gate decides the crux for
    /// both forms at the widths the guard-carrier canary asks for, and refuses
    /// the false `bvult v 2` variant.
    #[test]
    fn recognizer_authorizes_zero_test_and_refuses_false_bound() {
        for width in [8_u32, 32, 64] {
            for gate in [false, true] {
                let (mut terms, ult, eqz) = zero_test_pair(width, gate);
                let crux = terms.mk_app(Symbol::named("="), [ult, eqz], Sort::Bool);
                assert!(
                    ay_proof::recognize_bv_bitblast(&terms, &[crux]),
                    "w={width} gate={gate}: the semantic gate must decide the zero test"
                );
            }
            let mut terms = TermStore::new();
            let sort = Sort::bitvec(width);
            let v = terms.mk_var("v", sort);
            let two = terms.mk_bitvec(2u32.into(), width);
            let zero = terms.mk_bitvec(0u32.into(), width);
            let ult_two = terms.mk_app(Symbol::named("bvult"), [v, two], Sort::Bool);
            let eq_zero = terms.mk_app(Symbol::named("="), [v, zero], Sort::Bool);
            let crux = terms.mk_app(Symbol::named("="), [ult_two, eq_zero], Sort::Bool);
            assert!(
                !ay_proof::recognize_bv_bitblast(&terms, &[crux]),
                "w={width}: bvult v 2 against a zero test must be refused"
            );
        }
    }

    /// END-TO-END through the walker: the pair must produce a proof step, in
    /// both orientations, for both forms.
    #[test]
    fn walker_produces_a_step_for_both_forms_and_orders() {
        for gate in [false, true] {
            for reversed in [false, true] {
                let (mut terms, ult, eqz) = zero_test_pair(32, gate);
                let (l, r) = if reversed { (eqz, ult) } else { (ult, eqz) };
                let mut proof = Proof::default();
                assert!(
                    add_bvand_commutative_congruence_proof(&mut terms, &mut proof, l, r).is_some(),
                    "gate={gate} reversed={reversed}: the walker must produce a step"
                );
            }
        }
    }
}
