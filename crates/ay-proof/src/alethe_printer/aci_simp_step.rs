// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The one way the printer spells an `aci_simp` step.
//!
//! Pinned carcara 1.1.0 (git 9a352ee) drops a repeated argument of every
//! operator its `aci_simp` flattens, idempotent or not, so it accepts false
//! conclusions such as `(= (bvmul a a) a)` or `(= (+ x x) x)`
//! (`ay_core::pinned_carcara::aci_simp`, measured there). Its `valid` on such
//! a step is no evidence, and every gate refuses a document carrying one. So
//! every `aci_simp` the printer emits goes through [`ac_identity_step`], which
//! prints it only for an AC identity, true whatever its operands denote
//! (`aci_simp_equality_is_ac_identity`), and otherwise refuses: the caller
//! keeps its own fallback, never a step that rests on the checker's defect.

/// `(step {id} (cl (= {left} {right})) :rule aci_simp)`, or `None` when
/// `(= {left} {right})` is not an AC identity.
pub(super) fn ac_identity_step(
    id: impl std::fmt::Display,
    left: &str,
    right: &str,
) -> Option<String> {
    ay_core::pinned_carcara::aci_simp::aci_simp_equality_is_ac_identity(left, right)
        .then(|| format!("(step {id} (cl (= {left} {right})) :rule aci_simp)"))
}

#[cfg(test)]
mod tests {
    use super::ac_identity_step;

    /// The operand swaps the printer lowers print exactly as before.
    #[test]
    fn an_operand_swap_prints_its_aci_simp_step() {
        assert_eq!(
            ac_identity_step("t0.ac", "(* 16 c)", "(* c 16)").as_deref(),
            Some("(step t0.ac (cl (= (* 16 c) (* c 16))) :rule aci_simp)")
        );
        assert_eq!(
            ac_identity_step("t3", "(bvand x (bvnot y))", "(bvand (bvnot y) x)").as_deref(),
            Some("(step t3 (cl (= (bvand x (bvnot y)) (bvand (bvnot y) x))) :rule aci_simp)")
        );
        // A repeated operand is no reason to refuse a TRUE swap.
        assert!(ac_identity_step("t4", "(* (* x y) x)", "(* x (* x y))").is_some());
    }

    /// NEGATIVE twin: a conclusion pinned Carcara accepts only by dropping a
    /// repeat of a non-idempotent operator is never printed, nor anything else
    /// that is not an AC identity.
    #[test]
    fn a_conclusion_resting_on_carcaras_deduplication_is_refused() {
        for (left, right) in [
            ("(bvmul a a)", "a"),
            ("(bvadd a a)", "a"),
            ("(bvxor a a)", "a"),
            ("(+ x x)", "x"),
            ("(* x x)", "x"),
            ("a", "(bvadd a a)"),
            ("(bvmul a b a)", "(bvmul a b)"),
            ("(bvmul a (bvmul a b))", "(bvmul a b)"),
            ("(concat a a b)", "(concat a b b)"),
            ("(concat a b)", "(concat b a)"),
            // `|#x02|` is a symbol, `#x02` a literal: no AC identity.
            ("(bvmul |#x02| |#x02| #x02 a)", "(bvmul |#x02| #x02 #x02 a)"),
            ("(* 16 c)", "(* c 17)"),
        ] {
            assert_eq!(
                ac_identity_step("t0", left, right),
                None,
                "{left} = {right}"
            );
        }
    }
}
