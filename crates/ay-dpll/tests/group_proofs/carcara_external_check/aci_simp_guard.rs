// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// The negative controls behind the `aci_simp` guard, against the real checker.
// The scan itself, `aci_simp_steps_pinned_carcara_misjudges`, and its unit
// tests live in `ay_core::pinned_carcara::aci_simp`, shared by every Carcara
// runner in the workspace.

/// A refutation of the SATISFIABLE `(not (= left right))` resting on the one
/// false step `(= left right)` by `aci_simp`.
#[cfg(test)]
fn one_step_aci_simp_refutation(declarations: &str, left: &str, right: &str) -> (String, String) {
    let problem = format!(
        "(set-logic ALL)\n{declarations}\n(assert (not (= {left} {right})))\n(check-sat)\n"
    );
    let proof = format!(
        "(assume h1 (not (= {left} {right})))\n\
         (step t1 (cl (= {left} {right})) :rule aci_simp)\n\
         (step t2 (cl) :rule resolution :premises (h1 t1))\n"
    );
    (problem, proof)
}

/// The negative controls behind the guard, end to end against the REAL
/// checker: every problem below is SATISFIABLE (each equality is false at
/// `a = #x02` and `b = #x03`, `x = 2`, `r = 2.0`; z3 `sat`), yet pinned
/// Carcara prints `valid` for its one-step `aci_simp` refutation in both gate
/// invocations, because it drops a repeated argument of a non-idempotent
/// operator. Both shared verdict helpers must refuse each before the checker
/// runs, so no assertion in either direction passes on it.
///
/// `non_ascii_space`, `glued_literal` and `glued_label` are spelled so that
/// Carcara's lexer reads apart what a reader splitting only at ASCII spaces
/// and parentheses reads as one atom (a U+00A0 space, a literal glued to its
/// operator, a numeral glued to a `:named` label over `+`; `2 = 4` is false
/// outright): the guard's shared lexer must split them the same way, or it
/// sees no operator or name to flag. `quoted_literal` repeats the constant
/// `|#x02|` and the literal `#x02` (false at `|#x02| = #x01`): read as one
/// spelling, its two sides would pass for an AC identity, which the guard
/// exempts.
///
/// The first row is `ay_core::pinned_carcara::FALSE_VALID_ACI_SIMP_CONTROL_*`'s
/// equality: if pinned Carcara stops printing `valid` here, the guard and that
/// control no longer demonstrate anything and must be re-measured.
#[test]
#[timeout(120_000)]
fn a_valid_verdict_resting_on_a_misjudged_aci_simp_is_not_evidence() {
    let Some(carcara) = require_carcara_or_skip() else {
        return;
    };
    let bv = "(declare-const a (_ BitVec 8))\n(declare-const b (_ BitVec 8))";
    let int = "(declare-const x Int)";
    let real = "(declare-const r Real)";
    let mut rows = vec![(
        "shared_control".to_string(),
        ay_core::pinned_carcara::FALSE_VALID_ACI_SIMP_CONTROL_PROBLEM.to_string(),
        ay_core::pinned_carcara::FALSE_VALID_ACI_SIMP_CONTROL_PROOF.to_string(),
    )];
    for (name, declarations, left, right) in [
        ("bvadd", bv, "(bvadd a a)", "a"),
        ("bvxor", bv, "(bvxor a a)", "a"),
        ("int_plus", int, "(+ x x)", "x"),
        ("int_times", int, "(* x x)", "x"),
        ("real_plus", real, "(+ r r)", "r"),
        ("concat", bv, "(concat a a b)", "(concat a b b)"),
        ("non_adjacent_repeat", bv, "(bvmul a b a)", "(bvmul a b)"),
        (
            "cross_side_cache",
            bv,
            "(bvadd a #x00)",
            "(bvmul a (bvadd a #x00))",
        ),
        (
            "spelled_apart",
            bv,
            "(bvmul a #x02 (_ bv2 8))",
            "(bvmul a #x02)",
        ),
        ("non_ascii_space", bv, "(bvmul\u{a0}a\u{a0}a)", "a"),
        ("glued_literal", bv, "(bvmul#x03 #x03 a)", "(bvmul#x03 a)"),
        (
            "quoted_literal",
            "(declare-const |#x02| (_ BitVec 8))",
            "(bvmul #x02 #x02 |#x02|)",
            "(bvmul |#x02| |#x02| #x02)",
        ),
    ] {
        let (problem, proof) = one_step_aci_simp_refutation(declarations, left, right);
        rows.push((name.to_string(), problem, proof));
    }
    rows.push((
        "glued_label".to_string(),
        "(set-logic QF_LIA)\n(assert (not (= 2 (! (+ 2 2) :named m))))\n(check-sat)\n".to_string(),
        "(assume h1 (not (= 2 m)))\n(step t1 (cl (= 2m)) :rule aci_simp)\n\
         (step t2 (cl) :rule resolution :premises (h1 t1))\n"
            .to_string(),
    ));
    for (name, problem, proof) in &rows {
        let label = format!("misjudged_aci_simp_{name}");
        assert_eq!(
            unguarded_carcara_verdict(&carcara, problem, proof),
            CarcaraVerdict::Valid,
            "{label}: pinned carcara no longer accepts this refutation of a satisfiable \
             problem under --expand-let-bindings; re-measure the aci_simp guard"
        );
        let plain = unguarded_plain_carcara_output(&carcara, problem, proof);
        assert!(
            plain.starts_with("Valid"),
            "{label}: pinned carcara no longer accepts it in its plain invocation either; \
             re-measure the aci_simp guard: {plain}"
        );
        assert_refused_as_not_evidence(&format!("{label}: no-allowance helper"), || {
            carcara_verdict_without_allowances(&carcara, &label, problem, proof);
        });
        assert_refused_as_not_evidence(&format!("{label}: exact-verdict helper"), || {
            exact_carcara_verdict(&carcara, problem, proof);
        });
    }
}

/// POSITIVE twin: the `aci_simp` conclusions AY prints (an operand swap, here
/// of `bvmul` and of numeric `*`) and an idempotent repeat are TRUE, so the
/// guard lets them through and the shared helper reads Carcara's own `valid`.
/// `spaced_swap` is a `bvmul` swap spelled with a U+00A0 and a vertical-tab
/// space and a literal glued to a variable: Carcara reading it `valid` pins
/// that it splits those tokens exactly where the guard's lexer does.
#[test]
#[timeout(60_000)]
fn a_true_aci_simp_refutation_is_still_judged() {
    let Some(carcara) = require_carcara_or_skip() else {
        return;
    };
    let bv = "(declare-const a (_ BitVec 8))\n(declare-const b (_ BitVec 8))";
    let int = "(declare-const x Int)";
    for (name, declarations, left, right) in [
        ("bvmul_swap", bv, "(bvmul a b)", "(bvmul b a)"),
        ("times_swap", int, "(* 16 x)", "(* x 16)"),
        ("bvand_repeat", bv, "(bvand a a)", "a"),
        (
            "spaced_swap",
            bv,
            "(bvmul\u{a0}a#x02)",
            "(bvmul #x02\u{b}a)",
        ),
    ] {
        let (problem, proof) = one_step_aci_simp_refutation(declarations, left, right);
        assert_eq!(
            ay_core::pinned_carcara::pinned_carcara_can_judge(&problem, &proof),
            Ok(()),
            "{name}"
        );
        assert_eq!(
            carcara_verdict_without_allowances(
                &carcara,
                &format!("true_aci_simp_{name}"),
                &problem,
                &proof
            ),
            CarcaraVerdict::Valid,
            "{name}"
        );
    }
}
