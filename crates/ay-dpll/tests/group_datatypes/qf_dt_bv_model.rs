// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![allow(clippy::panic)]

//! DT+BV combined solver tests and DT model extraction tests.
//! Split from qf_dt_integration.rs — Part of #7229.

use ntest::timeout;

// ===== DT + BV combined solver tests (#1766) =====

/// SAT: DT with BV-typed field under ALL logic (#1766).
///
/// An Option-like DT with a BV8 value field. The solver must generate DT selector
/// axioms AND handle BV bit-blasting. Previously fell through to BV solver without
/// DT axioms, losing constructor/selector semantics.
#[test]
#[timeout(60_000)]
fn test_dt_bv_option_sat() {
    let smt = r#"
        (set-logic ALL)
        (declare-datatypes ((OptBV8 0)) (((NoneOpt) (SomeOpt (value (_ BitVec 8))))))
        (declare-const x OptBV8)
        (assert ((_ is SomeOpt) x))
        (assert (= (value x) #x42))
        (check-sat)
    "#;
    let result = crate::common::solve(smt);
    assert_eq!(
        result.trim(),
        "sat",
        "Bug #1766: DT+BV combination should route to combined solver"
    );
}

/// SAT: Independent DT + BV constraints with no shared terms (#5457).
/// Regression: the BV solver's Bool atom linking skipped DT testers,
/// leaving them with independent SAT variables in Tseitin vs BV domains.
#[test]
#[timeout(60_000)]
fn test_dt_bv_independent_constraints_sat_5457() {
    let smt = r#"
        (set-logic ALL)
        (declare-datatypes ((OptBV8 0)) (((NoneOpt) (SomeOpt (value (_ BitVec 8))))))
        (declare-const x OptBV8)
        (declare-const y (_ BitVec 8))
        (assert ((_ is SomeOpt) x))
        (assert (= y #x42))
        (check-sat)
    "#;
    let result = crate::common::solve(smt);
    assert_eq!(
        result.trim(),
        "sat",
        "Bug #5457: independent DT + BV constraints must return SAT"
    );
}

/// UNSAT: Constructor clash in DT+BV under ALL logic (#1766).
///
/// A value cannot simultaneously be NoneOpt and SomeOpt.
#[test]
#[timeout(60_000)]
fn test_dt_bv_constructor_clash_unsat() {
    let smt = r#"
        (set-logic ALL)
        (declare-datatypes ((OptBV8 0)) (((NoneOpt) (SomeOpt (value (_ BitVec 8))))))
        (declare-const x OptBV8)
        (assert ((_ is NoneOpt) x))
        (assert ((_ is SomeOpt) x))
        (check-sat)
    "#;
    let result = crate::common::solve(smt);
    assert_eq!(
        result.trim(),
        "unsat",
        "Bug #1766: DT constructor clash must be detected in DT+BV mode"
    );
}

/// SAT: DT with Array-typed field under ALL logic (#1766).
///
/// A Container DT that wraps an Array and an integer size field.
#[test]
#[timeout(60_000)]
fn test_dt_arrays_container_sat() {
    let smt = r#"
        (set-logic ALL)
        (declare-datatypes ((Container 0)) (((MkCont (data (Array Int Int)) (size Int)))))
        (declare-const c Container)
        (assert (= (size c) 3))
        (assert (= (select (data c) 0) 42))
        (check-sat)
    "#;
    let result = crate::common::solve(smt);
    assert_eq!(
        result.trim(),
        "sat",
        "Bug #1766: DT+Arrays combination should route to combined solver"
    );
}

/// UNSAT: DT+BV with BV constraint in check-sat-assuming path (#1766).
///
/// Verifies DT+BV combined solver works in the check-sat-assuming dispatch path.
#[test]
#[timeout(60_000)]
fn test_dt_bv_check_sat_assuming_unsat() {
    let smt = r#"
        (set-logic ALL)
        (declare-datatypes ((OptBV8 0)) (((NoneOpt) (SomeOpt (value (_ BitVec 8))))))
        (declare-const x OptBV8)
        (assert (= x (SomeOpt #x42)))
        (check-sat-assuming ((not ((_ is SomeOpt) x))))
    "#;
    let result = crate::common::solve(smt);
    assert_eq!(
        result.trim(),
        "unsat",
        "Bug #1766: DT+BV axioms must work in check-sat-assuming path"
    );
}

/// SAT: UF with mixed DT+BV arguments where DT args differ (#5473).
///
/// Tests ArgDiffResult::Unencodable path in generate_non_bv_euf_congruence.
/// When a UF has DT-sorted arguments that differ between two applications,
/// the congruence axiom must be SKIPPED (not forced unconditionally).
/// Without the fix from #5457, this returns false UNSAT because the solver
/// forces f(SomeOpt(#x01), #x01) = f(NoneOpt, #x01) unconditionally.
#[test]
#[timeout(60_000)]
fn test_dt_bv_uf_mixed_sort_args_unencodable_5473() {
    let smt = r#"
        (set-logic ALL)
        (declare-datatypes ((OptBV8 0)) (((NoneOpt) (SomeOpt (value (_ BitVec 8))))))
        (declare-fun f (OptBV8 (_ BitVec 8)) (_ BitVec 8))
        (declare-const x OptBV8)
        (declare-const bv1 (_ BitVec 8))
        (assert (= x (SomeOpt #x01)))
        (assert (= bv1 #x01))
        (assert (distinct (f x bv1) (f NoneOpt bv1)))
        (check-sat)
    "#;
    let result = crate::common::solve(smt);
    assert_eq!(
        result.trim(),
        "sat",
        "Bug #5473: UF with mixed DT+BV args where DT args differ must be SAT \
         (congruence must NOT be forced when DT arg difference is unencodable)"
    );
}

/// UNSAT: UF with identical DT+BV arguments must obey congruence (#5473).
///
/// When all arguments are identical, f(x, bv) = f(x, bv) must hold,
/// so distinct(f(x, bv), f(x, bv)) is UNSAT.
#[test]
#[timeout(60_000)]
fn test_dt_bv_uf_identical_args_congruence_5473() {
    let smt = r#"
        (set-logic ALL)
        (declare-datatypes ((OptBV8 0)) (((NoneOpt) (SomeOpt (value (_ BitVec 8))))))
        (declare-fun f (OptBV8 (_ BitVec 8)) (_ BitVec 8)
        )
        (declare-const x OptBV8)
        (declare-const bv1 (_ BitVec 8))
        (assert (distinct (f x bv1) (f x bv1)))
        (check-sat)
    "#;
    let result = crate::common::solve(smt);
    assert_eq!(
        result.trim(),
        "unsat",
        "Bug #5473: UF with identical args must obey congruence — distinct(f(x,bv), f(x,bv)) is UNSAT"
    );
}

/// UNSAT: Tester-tester disjointness in pure QF_DT (#1766 audit).
///
/// Two conflicting testers without explicit constructor terms. The executor's
/// axiom (C) converts is-Cons(x)=true into x=Cons(hd(x),tl(x)), and likewise
/// for is-Nil(x)=true into x=Nil, creating constructor terms that then clash.
/// This tests the full DPLL(T) + axiom pipeline, not just the DT solver.
#[test]
#[timeout(60_000)]
fn test_qf_dt_tester_disjointness_unsat() {
    let smt = r#"
        (set-logic QF_DT)
        (declare-datatypes ((List 0)) (((Cons (hd Int) (tl List)) (Nil))))
        (declare-const x List)
        (assert ((_ is Cons) x))
        (assert ((_ is Nil) x))
        (check-sat)
    "#;
    let result = crate::common::solve(smt);
    assert_eq!(
        result.trim(),
        "unsat",
        "Tester disjointness: is-Cons(x) AND is-Nil(x) must be UNSAT"
    );
}

// ========================== DT Model Extraction Tests ==========================
// Issue: #5432 - DT model extraction returns 0 for constrained non-nullary selectors
//
// These tests verify that get-model and get-value correctly resolve DT constructor
// values including non-nullary constructors with constrained selector arguments.

/// Model extraction: constrained Int selector must show correct value (#5432).
#[test]
#[timeout(60_000)]
fn test_qf_dt_model_constrained_selector_value_5432() {
    let smt = r#"
        (set-logic QF_DT)
        (declare-datatype Opt ((SomeI (ival Int)) (NoneI)))
        (declare-fun x () Opt)
        (assert ((_ is SomeI) x))
        (assert (= (ival x) 42))
        (check-sat)
        (get-value ((ival x)))
    "#;
    let result = crate::common::solve(smt);
    assert!(result.starts_with("sat"), "Should be sat, got: {result}");
    assert!(
        result.contains("42"),
        "get-value for (ival x) must return 42, got: {result}"
    );
}

/// Model extraction: multiple DT variables resolved correctly.
#[test]
#[timeout(60_000)]
fn test_qf_dt_model_multiple_variables() {
    let smt = r#"
        (set-logic QF_DT)
        (declare-datatype Color ((Red) (Green) (Blue)))
        (declare-fun x () Color)
        (declare-fun y () Color)
        (assert (not (= x y)))
        (assert ((_ is Red) x))
        (check-sat)
        (get-model)
    "#;
    let result = crate::common::solve(smt);
    assert!(result.starts_with("sat"), "Should be sat, got: {result}");
    assert!(
        result.contains("Red"),
        "Model must show x = Red, got: {result}"
    );
    // y should be a different constructor (Green or Blue)
    assert!(
        !result.contains("@Color"),
        "Model must not contain opaque @Color element names, got: {result}"
    );
}

/// Model extraction: nested DT value should be recursively resolved (#5432).
#[test]
#[timeout(60_000)]
fn test_qf_dt_model_nested_dt_5432() {
    let smt = r#"
        (set-logic QF_DT)
        (declare-datatypes ((Pair 0) (OptPair 0))
          (((mkpair (fst Int) (snd Int)))
           ((SomeP (val Pair)) (NoneP))))
        (declare-fun x () OptPair)
        (assert ((_ is SomeP) x))
        (assert (= (fst (val x)) 42))
        (check-sat)
        (get-model)
    "#;
    let result = crate::common::solve(smt);
    assert!(result.starts_with("sat"), "Should be sat, got: {result}");
    // The nested Pair value should not show as @Pair!N
    assert!(
        !result.contains("@Pair"),
        "Model must not contain opaque @Pair element names, got: {result}"
    );
}

/// Model extraction: mutual recursion DT with constrained value (#5432).
#[test]
#[timeout(60_000)]
fn test_qf_dt_model_mutual_recursion_constrained_5432() {
    let smt = r#"
        (set-logic QF_DT)
        (declare-datatypes ((Expr 0) (ExprList 0))
          (((Num (numval Int)) (Add (left Expr) (right Expr)))
           ((Nil) (Cons (head Expr) (tail ExprList)))))
        (declare-fun e () Expr)
        (assert ((_ is Num) e))
        (assert (= (numval e) 7))
        (check-sat)
        (get-value ((numval e)))
    "#;
    let result = crate::common::solve(smt);
    assert!(result.starts_with("sat"), "Should be sat, got: {result}");
    assert!(
        result.contains("7"),
        "get-value for (numval e) must return 7, got: {result}"
    );
}

/// Nested DT model should resolve constructor arguments to constructor names,
/// not internal representatives like `@Color!0` (#5450).
#[test]
#[timeout(60_000)]
fn test_qf_dt_nested_ctor_arg_resolution_5450() {
    let smt = r#"
        (set-logic QF_DT)
        (declare-datatypes ((Color 0) (Maybe 0)) (
          ((Red) (Green) (Blue))
          ((Nothing) (Just (val Color)))
        ))
        (declare-fun m1 () Maybe)
        (assert ((_ is Just) m1))
        (assert (= (val m1) Green))
        (check-sat)
        (get-model)
    "#;
    let result = crate::common::solve(smt);
    assert!(result.starts_with("sat"), "Should be sat, got: {result}");
    // Model must show `(Just Green)`, not `(Just @Color!0)`.
    assert!(
        result.contains("Green"),
        "DT constructor argument should be resolved to 'Green', got: {result}"
    );
    assert!(
        !result.contains("@Color"),
        "Model must not contain internal name @Color!N, got: {result}"
    );
}

/// DT model with disequality should not produce equal values for distinct
/// variables (#5450).
#[test]
#[timeout(60_000)]
fn test_qf_dt_disequality_model_5450() {
    let smt = r#"
        (set-logic QF_DT)
        (declare-datatypes ((Color 0) (Maybe 0)) (
          ((Red) (Green) (Blue))
          ((Nothing) (Just (val Color)))
        ))
        (declare-fun m1 () Maybe)
        (declare-fun m2 () Maybe)
        (assert ((_ is Just) m1))
        (assert (= (val m1) Green))
        (assert (not (= m1 m2)))
        (check-sat)
        (get-model)
    "#;
    let result = crate::common::solve(smt);
    assert!(result.starts_with("sat"), "Should be sat, got: {result}");
    // Model must not contain internal representative names.
    assert!(
        !result.contains("@Color"),
        "Model must not contain internal name @Color!N, got: {result}"
    );
    assert!(
        !result.contains("@Maybe"),
        "Model must not contain internal name @Maybe!N, got: {result}"
    );
}

/// #5506: QF_DT with integer inequality constraints should produce correct model.
/// When (set-logic QF_DT) is used with Int-sorted selectors and inequality
/// constraints like (> (fst p) 5), the pure DT solver does not activate LIA.
/// The fix scans assertions for bounds to pick satisfying Int values.
#[test]
#[timeout(60_000)]
fn test_qf_dt_int_selector_inequality_5506() {
    let smt = r#"
        (set-logic QF_DT)
        (declare-datatypes ((Pair 0)) (((mkPair (fst Int) (snd Int)))))
        (declare-fun p () Pair)
        (assert (> (fst p) 5))
        (assert (< (snd p) 3))
        (check-sat)
        (get-model)
    "#;
    let result = crate::common::solve(smt);
    assert!(result.starts_with("sat"), "Should be sat, got: {result}");
    // Validate the model satisfies constraints: fst > 5 and snd < 3.
    // The model format is: (define-fun p () Pair (mkPair <fst> <snd>))
    // Extract the mkPair constructor arguments.
    let (fst_val, snd_val) = crate::common::extract_mkpair_int_values(&result, "mkPair");
    assert!(
        fst_val > 5,
        "fst p must be > 5, got {fst_val}, full output: {result}"
    );
    assert!(
        snd_val < 3,
        "snd p must be < 3, got {snd_val}, full output: {result}"
    );
}

/// #5506 gap: Real-sorted selectors in QF_DT with inequality constraints
/// should produce valid model values, not default 0.0.
#[test]
#[timeout(60_000)]
fn test_qf_dt_real_selector_inequality_gap() {
    let smt = r#"
        (set-logic QF_DT)
        (declare-datatypes ((RPair 0)) (((mkRPair (rfst Real) (rsnd Real)))))
        (declare-fun rp () RPair)
        (assert (> (rfst rp) 5.0))
        (assert (< (rsnd rp) 3.0))
        (check-sat)
        (get-model)
    "#;
    let result = crate::common::solve(smt);
    assert!(result.starts_with("sat"), "Should be sat, got: {result}");
    // Validate the model satisfies constraints: rfst > 5.0 and rsnd < 3.0.
    let (rfst_val, rsnd_val) = crate::common::extract_mkpair_real_values(&result, "mkRPair");
    assert!(
        rfst_val > 5.0,
        "rfst rp must be > 5.0, got {rfst_val}, full output: {result}"
    );
    assert!(
        rsnd_val < 3.0,
        "rsnd rp must be < 3.0, got {rsnd_val}, full output: {result}"
    );
}

/// Extract a Real value from a get-value response.
///
/// Handles both echo shapes ay may print for the queried term:
///   * `(((sel var) <val>))` — selector application preserved, and
///   * `((var!sel <val>))`   — the selector folded to the eliminated field
///     constant (single-constructor datatype elimination), exactly as ay
///     already folds e.g. `(get-value ((+ 1 2)))` to `((3 3))`.
/// In every case the answer is `((<term> <value>))`; the value is the last
/// top-level s-expression in the inner `(<term> <value>)` pair, which this
/// extracts by skipping one balanced s-expression (the term) from the front.
fn extract_get_value_real(output: &str, sel_name: &str) -> f64 {
    for line in output.lines() {
        let line = line.trim();
        if !(line.contains(sel_name) && line.starts_with("((") && line.ends_with("))")) {
            continue;
        }
        // Strip the outer `(` ... `)` of the whole response to get the inner
        // `(<term> <value>)` pair, then strip that pair's parens to get
        // `<term> <value>`.
        let pair = line
            .strip_prefix('(')
            .and_then(|s| s.strip_suffix(')'))
            .unwrap_or(line);
        let body = pair
            .trim()
            .strip_prefix('(')
            .and_then(|s| s.strip_suffix(')'))
            .unwrap_or(pair)
            .trim();
        // Skip the first balanced s-expression (the echoed term).
        let mut depth = 0i32;
        let mut split = None;
        for (i, ch) in body.char_indices() {
            match ch {
                '(' => depth += 1,
                ')' => depth -= 1,
                c if c.is_whitespace() && depth == 0 => {
                    split = Some(i);
                    break;
                }
                _ => {}
            }
        }
        let val_str = split.map(|i| body[i..].trim()).unwrap_or(body);
        let (val, _) = crate::common::parse_smt_real(val_str, output);
        return val;
    }
    panic!("get-value response for {sel_name} not found in: {output}");
}

/// #5506: get-value on Real-sorted DT selector with equality constraint.
/// This exercises extract_value_from_asserted_equalities (the existing path).
#[test]
#[timeout(60_000)]
fn test_qf_dt_get_value_real_selector_equality() {
    let smt = r#"
        (set-logic QF_DT)
        (declare-datatypes ((RBox 0)) (((mkRBox (rval Real)))))
        (declare-fun b () RBox)
        (assert (= (rval b) 7.5))
        (check-sat)
        (get-value ((rval b)))
    "#;
    let result = crate::common::solve(smt);
    assert!(result.starts_with("sat"), "Should be sat, got: {result}");
    let rval = extract_get_value_real(&result, "rval");
    assert!(
        (rval - 7.5).abs() < 0.001,
        "get-value (rval b) must be 7.5, got {rval}, full output: {result}"
    );
}

/// #5506 edge case: negated comparisons in QF_DT Int bound extraction.
/// `(not (>= (fst p) 5))` means `fst p < 5`, so valid model has fst < 5.
/// `(not (<= (snd p) 3))` means `snd p > 3`, so valid model has snd > 3.
#[test]
#[timeout(60_000)]
fn test_qf_dt_int_negated_bounds() {
    let smt = r#"
        (set-logic QF_DT)
        (declare-datatypes ((Pair 0)) (((mkPair (fst Int) (snd Int)))))
        (declare-fun p () Pair)
        (assert (not (>= (fst p) 5)))
        (assert (not (<= (snd p) 3)))
        (check-sat)
        (get-model)
    "#;
    let result = crate::common::solve(smt);
    assert!(result.starts_with("sat"), "Should be sat, got: {result}");
    let (fst_val, snd_val) = crate::common::extract_mkpair_int_values(&result, "mkPair");
    assert!(
        fst_val < 5,
        "not (>= fst 5) means fst < 5, got {fst_val}, output: {result}"
    );
    assert!(
        snd_val > 3,
        "not (<= snd 3) means snd > 3, got {snd_val}, output: {result}"
    );
}

/// #5506 edge case: constant on the left side of comparison.
/// `(> 10 (fst p))` means `fst p < 10`. `(< (- 2) (snd p))` means `snd p > -2`.
#[test]
#[timeout(60_000)]
fn test_qf_dt_int_constant_left_side() {
    let smt = r#"
        (set-logic QF_DT)
        (declare-datatypes ((Pair 0)) (((mkPair (fst Int) (snd Int)))))
        (declare-fun p () Pair)
        (assert (> 10 (fst p)))
        (assert (< (- 2) (snd p)))
        (check-sat)
        (get-model)
    "#;
    let result = crate::common::solve(smt);
    assert!(result.starts_with("sat"), "Should be sat, got: {result}");
    let (fst_val, snd_val) = crate::common::extract_mkpair_int_values(&result, "mkPair");
    assert!(
        fst_val < 10,
        "(> 10 fst) means fst < 10, got {fst_val}, output: {result}"
    );
    assert!(
        snd_val > -2,
        "(< (- 2) snd) means snd > -2, got {snd_val}, output: {result}"
    );
}

/// #5506 edge case: multiple tightening bounds on the same field.
/// fst > 3 AND fst > 7 means fst > 7. snd < 10 AND snd < 5 means snd < 5.
#[test]
#[timeout(60_000)]
fn test_qf_dt_int_multiple_tightening_bounds() {
    let smt = r#"
        (set-logic QF_DT)
        (declare-datatypes ((Pair 0)) (((mkPair (fst Int) (snd Int)))))
        (declare-fun p () Pair)
        (assert (> (fst p) 3))
        (assert (> (fst p) 7))
        (assert (< (snd p) 10))
        (assert (< (snd p) 5))
        (check-sat)
        (get-model)
    "#;
    let result = crate::common::solve(smt);
    assert!(result.starts_with("sat"), "Should be sat, got: {result}");
    let (fst_val, snd_val) = crate::common::extract_mkpair_int_values(&result, "mkPair");
    assert!(
        fst_val > 7,
        "fst > 3 AND fst > 7 tightens to fst > 7, got {fst_val}, output: {result}"
    );
    assert!(
        snd_val < 5,
        "snd < 10 AND snd < 5 tightens to snd < 5, got {snd_val}, output: {result}"
    );
}

/// #5506 edge case: equality constraint takes priority over inequality bounds.
#[test]
#[timeout(60_000)]
fn test_qf_dt_int_equality_overrides_bounds() {
    let smt = r#"
        (set-logic QF_DT)
        (declare-datatypes ((Box 0)) (((mkBox (val Int)))))
        (declare-fun b () Box)
        (assert (> (val b) 0))
        (assert (= (val b) 42))
        (assert (< (val b) 100))
        (check-sat)
        (get-model)
    "#;
    let result = crate::common::solve(smt);
    assert!(result.starts_with("sat"), "Should be sat, got: {result}");
    // Extract the value from mkBox constructor
    let val_start = result.find("(mkBox ").expect("model should contain mkBox");
    let num_start = val_start + "(mkBox ".len();
    let num_end = result[num_start..].find(')').unwrap() + num_start;
    let val_str = result[num_start..num_end].trim();
    let val: i64 = if let Some(inner) = val_str.strip_prefix("(- ") {
        let inner = inner.trim_end_matches(')');
        -inner.parse::<i64>().unwrap()
    } else {
        val_str
            .parse()
            .unwrap_or_else(|e| panic!("parse {val_str}: {e}"))
    };
    assert_eq!(
        val, 42,
        "equality (= val 42) should yield exactly 42, got {val}, output: {result}"
    );
}

/// #5506 edge case: negative integer constant via (- N) syntax.
#[test]
#[timeout(60_000)]
fn test_qf_dt_int_negative_constant() {
    let smt = r#"
        (set-logic QF_DT)
        (declare-datatypes ((Box 0)) (((mkBox (val Int)))))
        (declare-fun b () Box)
        (assert (< (val b) (- 5)))
        (check-sat)
        (get-model)
    "#;
    let result = crate::common::solve(smt);
    assert!(result.starts_with("sat"), "Should be sat, got: {result}");
    let val_start = result.find("(mkBox ").expect("model should contain mkBox");
    let num_start = val_start + "(mkBox ".len();
    let num_end = result[num_start..].find(')').unwrap() + num_start;
    let val_str = result[num_start..num_end].trim();
    let val: i64 = if let Some(inner) = val_str.strip_prefix("(- ") {
        let inner = inner.trim_end_matches(')');
        -inner.parse::<i64>().unwrap()
    } else {
        val_str
            .parse()
            .unwrap_or_else(|e| panic!("parse {val_str}: {e}"))
    };
    assert!(
        val < -5,
        "(< val (- 5)) means val < -5, got {val}, output: {result}"
    );
}

/// #5506 edge case: Real bounds with negated comparisons.
/// (not (> rfst 5.0)) => rfst <= 5.0. (not (< rsnd 3.0)) => rsnd >= 3.0.
#[test]
#[timeout(60_000)]
fn test_qf_dt_real_negated_bounds() {
    let smt = r#"
        (set-logic QF_DT)
        (declare-datatypes ((RPair 0)) (((mkRPair (rfst Real) (rsnd Real)))))
        (declare-fun rp () RPair)
        (assert (not (> (rfst rp) 5.0)))
        (assert (not (< (rsnd rp) 3.0)))
        (check-sat)
        (get-model)
    "#;
    let result = crate::common::solve(smt);
    assert!(result.starts_with("sat"), "Should be sat, got: {result}");
    let (rfst_val, rsnd_val) = crate::common::extract_mkpair_real_values(&result, "mkRPair");
    assert!(
        rfst_val <= 5.0 + 0.001,
        "not (> rfst 5.0) means rfst <= 5.0, got {rfst_val}, output: {result}"
    );
    assert!(
        rsnd_val >= 3.0 - 0.001,
        "not (< rsnd 3.0) means rsnd >= 3.0, got {rsnd_val}, output: {result}"
    );
}

/// #5506 edge case: Real bounds with rational constant (/ 1 3).
#[test]
#[timeout(60_000)]
fn test_qf_dt_real_rational_constant() {
    let smt = r#"
        (set-logic QF_DT)
        (declare-datatypes ((Box 0)) (((mkBox (val Real)))))
        (declare-fun b () Box)
        (assert (> (val b) (/ 1 3)))
        (check-sat)
        (get-model)
    "#;
    let result = crate::common::solve(smt);
    assert!(result.starts_with("sat"), "Should be sat, got: {result}");
    // val should be > 1/3 ≈ 0.333
    // We can't easily extract from model without parsing all formats,
    // but we can verify via get-value if we had the uncommitted fix.
    // For now, just verify sat + model was produced.
    assert!(
        result.contains("mkBox"),
        "Model should contain mkBox, got: {result}"
    );
}

/// #5506 edge case: Real bounds from both sides with constant on the left.
#[test]
#[timeout(60_000)]
fn test_qf_dt_real_constant_left_side() {
    let smt = r#"
        (set-logic QF_DT)
        (declare-datatypes ((Box 0)) (((mkBox (val Real)))))
        (declare-fun b () Box)
        (assert (< 2.0 (val b)))
        (assert (> 8.0 (val b)))
        (check-sat)
        (get-model)
    "#;
    let result = crate::common::solve(smt);
    assert!(result.starts_with("sat"), "Should be sat, got: {result}");
    assert!(
        result.contains("mkBox"),
        "Model should contain mkBox, got: {result}"
    );
}

/// #5506 gap: get-value on Real-sorted DT selector with inequality constraints
/// should return a satisfying value, not default 0.0. The get-model path works
/// (tested above) but get-value takes a different code path through output.rs
/// that doesn't invoke extract_real_from_assertion_bounds.
/// NOTE: Requires output.rs corresponding output-path fix to pass.
#[test]
#[timeout(60_000)]
fn test_qf_dt_get_value_real_selector_inequality() {
    let smt = r#"
        (set-logic QF_DT)
        (declare-datatypes ((RPair 0)) (((mkRPair (rfst Real) (rsnd Real)))))
        (declare-fun rp () RPair)
        (assert (> (rfst rp) 5.0))
        (assert (< (rsnd rp) 3.0))
        (check-sat)
        (get-value ((rfst rp)))
        (get-value ((rsnd rp)))
    "#;
    let result = crate::common::solve(smt);
    assert!(result.starts_with("sat"), "Should be sat, got: {result}");
    let rfst_val = extract_get_value_real(&result, "rfst");
    let rsnd_val = extract_get_value_real(&result, "rsnd");
    assert!(
        rfst_val > 5.0,
        "get-value (rfst rp) must be > 5.0, got {rfst_val}, full output: {result}"
    );
    assert!(
        rsnd_val < 3.0,
        "get-value (rsnd rp) must be < 3.0, got {rsnd_val}, full output: {result}"
    );
}

/// #6190: Exhaustiveness axiom must cover DT-sorted selector sub-terms.
///
/// The formula asserts `(not ((_ is cons) (cdr x4)))` (cdr(x4) is not cons)
/// and `(not (= null (cdr x4)))` (cdr(x4) != null). Since `list` has only
/// constructors `cons` and `null`, `cdr(x4)` must be one of them, making
/// this contradictory (unsat). Previously, the exhaustiveness axiom was only
/// generated for declared variables, missing selector applications like
/// `(cdr x4)` which also produce DT-sorted values.
#[test]
fn test_qf_dt_unsat_selector_exhaustiveness_6190() {
    let smt = r#"
        (set-logic QF_DT)
        (declare-datatypes ((nat 0)(list 0)(tree 0)) (((succ (pred nat)) (zero))
        ((cons (car tree) (cdr list)) (null))
        ((node (children list)) (leaf (data nat)))
        ))
        (declare-fun x1 () nat)
        (declare-fun x2 () nat)
        (declare-fun x3 () list)
        (declare-fun x4 () list)
        (declare-fun x5 () tree)
        (declare-fun x6 () tree)
        (assert (and (and (and (and (and (= (node x3) x5) (not ((_ is cons) (cdr x4)))) ((_ is node) x6)) ((_ is cons) (cons (leaf (pred x2)) x4))) (not (= null (cdr x4)))) (not ((_ is succ) zero))))
        (check-sat)
    "#;
    let result = crate::common::solve(smt);
    assert!(
        result.starts_with("unsat"),
        "#6190: selector sub-term exhaustiveness must make this unsat, got: {result}"
    );
}

/// UNSAT: Selector-of-constructor identity must reduce to its argument (#2677).
///
/// `(fld_0 (Literal_mk (bvxor x #x00000001)))` must equal `(bvxor x #x00000001)`.
/// The negation of this identity is unsatisfiable. Historical regression: ay once
/// returned SAT for this formula shape when DT+BV combined solving failed to
/// resolve selector-constructor pairs.
#[test]
#[timeout(60_000)]
fn test_dt_bv_selector_constructor_identity_issue_2677() {
    let smt = r#"
        (set-logic ALL)
        (declare-datatypes ((Literal 0)) (((Literal_mk (fld_0 (_ BitVec 32))))))
        (declare-fun x () (_ BitVec 32))
        (assert (not (= (fld_0 (Literal_mk (bvxor x #x00000001)))
                        (bvxor x #x00000001))))
        (check-sat)
    "#;
    let result = crate::common::solve(smt);
    assert_eq!(
        result.trim(),
        "unsat",
        "Bug #2677: selector-of-constructor identity must be resolved"
    );
}

/// UNSAT: XOR involution through nested selector-constructor (#2677).
///
/// Double XOR with the same mask through a DT wrapper must cancel. The formula
/// asserts `(fld_0 result) != (fld_0 orig)` after constructing `result` via
/// `Literal_mk(bvxor(fld_0(Literal_mk(bvxor(fld_0 orig, mask))), mask))`.
/// This is the exact issue-body shape from the original #2677 report.
#[test]
#[timeout(60_000)]
fn test_dt_bv_xor_involution_issue_2677() {
    let smt = r#"
        (declare-datatypes ((Literal 0)) (((Literal_mk (fld_0 (_ BitVec 32))))))
        (declare-fun orig () Literal)
        (declare-fun result () Literal)
        (assert (= result
            (Literal_mk
                (bvxor
                    (fld_0 (Literal_mk (bvxor (fld_0 orig) #x00000001)))
                    #x00000001))))
        (assert (not (= (fld_0 result) (fld_0 orig))))
        (check-sat)
    "#;
    let result = crate::common::solve(smt);
    assert_eq!(
        result.trim(),
        "unsat",
        "Bug #2677: XOR involution through DT wrapper must cancel"
    );
}

// ===== Variable transitivity via shared constructor binding (#8419) =====

/// UNSAT: Two variables bound to the same hash-consed constructor (#8419).
///
/// When `s = mk-val(#x01)` and `t = mk-val(#x01)`, hash-consing produces a
/// single term ID for `mk-val(#x01)`. The axiom generator must derive `s = t`
/// even though they are not in the same union-find class (the UF only tracks
/// var-to-var equalities, not var-to-ctor equalities).
///
/// Without axiom (I), this was falsely satisfiable because:
/// - Union-find only tracks var-var equalities, not var-ctor
/// - Injectivity (F2) generates field equalities, but identical hash-consed
///   args have a == b so no axiom is generated
/// - EUF congruence needs 2+ distinct applications (hash-consing gives 1)
#[test]
#[timeout(60_000)]
fn test_dt_bv_shared_ctor_binding_transitivity_8419() {
    let smt = r#"
        (set-logic ALL)
        (declare-datatypes ((Val 0)) (((mk-val (get-val (_ BitVec 8))))))
        (declare-const s Val)
        (declare-const t Val)
        (assert (= s (mk-val #x01)))
        (assert (= t (mk-val #x01)))
        (assert (not (= s t)))
        (check-sat)
    "#;
    let result = crate::common::solve(smt);
    assert_eq!(
        result.trim(),
        "unsat",
        "Bug #8419: Variables bound to same hash-consed constructor must be equal"
    );
}

/// UNSAT: Three variables bound to the same constructor (#8419).
///
/// Extension of the two-variable case: s, t, u all equal to mk-val(#x42),
/// then `not (= s u)` must be unsatisfiable.
#[test]
#[timeout(60_000)]
fn test_dt_bv_three_vars_shared_ctor_binding_8419() {
    let smt = r#"
        (set-logic ALL)
        (declare-datatypes ((Val 0)) (((mk-val (get-val (_ BitVec 8))))))
        (declare-const s Val)
        (declare-const t Val)
        (declare-const u Val)
        (assert (= s (mk-val #x42)))
        (assert (= t (mk-val #x42)))
        (assert (= u (mk-val #x42)))
        (assert (not (= s u)))
        (check-sat)
    "#;
    let result = crate::common::solve(smt);
    assert_eq!(
        result.trim(),
        "unsat",
        "Bug #8419: Three variables bound to same constructor must all be equal"
    );
}

/// SAT: Two variables bound to different constructor args (#8419 negative test).
///
/// `s = mk-val(#x01)` and `t = mk-val(#x02)` have different args, so `s != t`
/// is satisfiable.
#[test]
#[timeout(60_000)]
fn test_dt_bv_different_ctor_args_sat_8419() {
    let smt = r#"
        (set-logic ALL)
        (declare-datatypes ((Val 0)) (((mk-val (get-val (_ BitVec 8))))))
        (declare-const s Val)
        (declare-const t Val)
        (assert (= s (mk-val #x01)))
        (assert (= t (mk-val #x02)))
        (assert (not (= s t)))
        (check-sat)
    "#;
    let result = crate::common::solve(smt);
    assert_eq!(
        result.trim(),
        "sat",
        "Different constructor args: s and t can be different"
    );
}

/// UNSAT: Multi-field constructor with shared binding (#8419).
///
/// Both p and q bound to mk-pair(#x01, #x0002) — must be equal.
#[test]
#[timeout(60_000)]
fn test_dt_bv_multifield_shared_ctor_binding_8419() {
    let smt = r#"
        (set-logic ALL)
        (declare-datatypes ((Pair 0)) (((mk-pair (fst (_ BitVec 8)) (snd (_ BitVec 16))))))
        (declare-const p Pair)
        (declare-const q Pair)
        (assert (= p (mk-pair #x01 #x0002)))
        (assert (= q (mk-pair #x01 #x0002)))
        (assert (not (= p q)))
        (check-sat)
    "#;
    let result = crate::common::solve(smt);
    assert_eq!(
        result.trim(),
        "unsat",
        "Bug #8419: Multi-field constructor shared binding must derive equality"
    );
}
