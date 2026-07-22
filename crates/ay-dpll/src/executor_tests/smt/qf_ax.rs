// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_executor_qf_ax_basic_sat() {
    // Basic array operations that should be SAT
    let input = r#"
        (set-logic QF_AX)
        (declare-const a (Array Int Int))
        (declare-const i Int)
        (declare-const v Int)
        (assert (= (select (store a i v) i) v))
        (check-sat)
    "#;

    let commands = parse(input).expect("parse double-check-sat ROW2 regression");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("execute double-check-sat ROW2 regression");

    assert_eq!(outputs, vec!["sat"]);
}
#[test]
fn test_executor_qf_ax_row1_conflict() {
    // ROW1 violation: select(store(a, i, v), i) must equal v
    // This asserts the negation, which should be UNSAT
    let input = r#"
        (set-logic QF_AX)
        (declare-const a (Array Int Int))
        (declare-const i Int)
        (declare-const j Int)
        (declare-const v Int)
        (assert (= i j))
        (assert (not (= (select (store a i v) j) v)))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["unsat"]);
}
#[test]
fn test_executor_qf_ax_row2_sat() {
    // ROW2: When i ≠ j, select(store(a, i, v), j) = select(a, j)
    // This is consistent, so SAT
    let input = r#"
        (set-logic QF_AX)
        (declare-const a (Array Int Int))
        (declare-const i Int)
        (declare-const j Int)
        (declare-const v Int)
        (assert (not (= i j)))
        (assert (= (select (store a i v) j) (select a j)))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat"]);
}
#[test]
fn test_executor_qf_ax_row2_sat_recheck_6717() {
    let input = r#"
        (set-logic QF_AX)
        (declare-const a (Array Int Int))
        (declare-const i Int)
        (declare-const j Int)
        (declare-const v Int)
        (assert (not (= i j)))
        (assert (= (select (store a i v) j) (select a j)))
        (check-sat)
        (check-sat)
    "#;

    let commands = parse(input).expect("parse ROW2 recheck regression");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("execute ROW2 recheck regression");

    assert_eq!(outputs, vec!["sat", "sat"]);
}
#[test]
fn test_executor_qf_ax_row2_conflict() {
    // ROW2 violation: When i ≠ j, select(store(a, i, v), j) must equal select(a, j)
    // Asserting they differ should be UNSAT
    let input = r#"
        (set-logic QF_AX)
        (declare-const a (Array Int Int))
        (declare-const i Int)
        (declare-const j Int)
        (declare-const v Int)
        (assert (not (= i j)))
        (assert (not (= (select (store a i v) j) (select a j))))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["unsat"]);
}
#[test]
fn test_executor_qf_ax_row2_sat_no_split_incremental_6717() {
    let input = r#"
        (set-logic QF_AX)
        (declare-const a (Array Int Int))
        (declare-const i Int)
        (declare-const j Int)
        (declare-const v Int)
        (assert (not (= i j)))
        (assert (= (select (store a i v) j) (select a j)))
    "#;

    let commands = parse(input).expect("parse QF_AX input");
    let mut exec = Executor::new();
    for command in &commands {
        let output = exec.execute(command).expect("execute setup command");
        assert!(output.is_none(), "setup commands should not emit output");
    }

    let result = exec.solve_array_euf().expect("incremental solve");
    assert_eq!(result, SolveResult::Sat);
}
/// Exercises the NeedLemmas path in `solve_incremental_theory_pipeline!`.
///
/// The formula negates the ROW2 consequence: `i != j` but
/// `select(store(a,i,v), j) != select(a, j)`. This is UNSAT.
///
/// Without the eager axiom fixpoint (which the incremental pipeline
/// skips), the SAT solver first finds a propositional model. The array theory
/// then discovers the ROW2 violation and returns `NeedLemmas` with the clause
/// `(= i j) OR (= (select (store a i v) j) (select a j))`. The pipeline adds
/// the lemma and re-solves, yielding UNSAT.
#[test]
fn test_executor_qf_ax_row2_unsat_needlemmas_incremental() {
    let input = r#"
        (set-logic QF_AX)
        (declare-const a (Array Int Int))
        (declare-const i Int)
        (declare-const j Int)
        (declare-const v Int)
        (assert (not (= i j)))
        (assert (not (= (select (store a i v) j) (select a j))))
    "#;

    let commands = parse(input).expect("parse QF_AX input");
    let mut exec = Executor::new();
    for command in &commands {
        let output = exec.execute(command).expect("execute setup command");
        assert!(output.is_none(), "setup commands should not emit output");
    }

    let result = exec
        .solve_array_euf()
        .expect("incremental solve should not error");
    assert_eq!(
        result,
        SolveResult::unsat(),
        "ROW2 violation must be UNSAT after NeedLemmas adds the axiom clause"
    );
}
#[test]
fn test_executor_qf_ax_array_equality_conflict() {
    // Array equality: If a = b, then select(a, i) = select(b, i)
    // Asserting a = b and select(a, i) ≠ select(b, i) should be UNSAT
    let input = r#"
        (set-logic QF_AX)
        (declare-const a (Array Int Int))
        (declare-const b (Array Int Int))
        (declare-const i Int)
        (assert (= a b))
        (assert (not (= (select a i) (select b i))))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["unsat"]);
}
#[test]
fn test_executor_qf_ax_array_with_euf() {
    // Combined array + EUF reasoning
    // f(a) = f(b) when a = b (congruence), and arrays interact with EUF
    let input = r#"
        (set-logic QF_AX)
        (declare-sort U 0)
        (declare-const a (Array Int U))
        (declare-const b (Array Int U))
        (declare-const i Int)
        (declare-fun f ((Array Int U)) Bool)
        (assert (= a b))
        (assert (f a))
        (assert (not (f b)))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    // Should be UNSAT due to EUF congruence: a = b implies f(a) = f(b)
    assert_eq!(outputs, vec!["unsat"]);
}
#[test]
fn test_executor_qf_ax_check_sat_assuming() {
    // Test check-sat-assuming with QF_AX
    let input = r#"
        (set-logic QF_AX)
        (declare-const a (Array Int Int))
        (declare-const i Int)
        (declare-const v Int)
        (declare-const p Bool)
        (assert (=> p (= (select (store a i v) i) v)))
        (check-sat-assuming (p))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat"]);
}
#[test]
fn test_executor_qf_ax_get_model() {
    // Test get-model with array values
    let input = r#"
        (set-logic QF_AX)
        (set-option :produce-models true)
        (declare-const a (Array Int Int))
        (declare-const i Int)
        (declare-const v Int)
        (assert (= (select a i) v))
        (check-sat)
        (get-model)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    // Should return sat and a model
    assert_eq!(outputs.len(), 2);
    assert_eq!(outputs[0], "sat");
    // Model should contain array definition
    assert!(outputs[1].contains("(model"), "Expected model output");
    assert!(
        outputs[1].contains("define-fun a"),
        "Expected array 'a' in model"
    );
    // Array value should be formatted with const/store
    assert!(
        outputs[1].contains("(Array Int Int)"),
        "Expected array sort in model"
    );
}
#[test]
fn test_executor_qf_ax_get_model_with_store() {
    // Test get-model with explicit store operations.
    // This formula is SAT: b = store(a, 1, 42), select(b, 1) = 42 is trivially
    // satisfiable. However, the model evaluator may lack full array model data,
    // so model validation can degrade to "unknown" (#4304). Either "sat" or
    // "unknown" is acceptable; only "unsat" would be wrong.
    let input = r#"
        (set-logic QF_AX)
        (set-option :produce-models true)
        (declare-const a (Array Int Int))
        (declare-const b (Array Int Int))
        (assert (= b (store a 1 42)))
        (assert (= (select b 1) 42))
        (check-sat)
        (get-model)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    // Formula is SAT. Model validation may degrade to "unknown" when the array
    // evaluator cannot fully verify the model (#4304). "unsat" is wrong.
    assert_ne!(outputs[0], "unsat", "SAT formula must not return unsat");
    if outputs[0] == "sat" {
        assert_eq!(outputs.len(), 2);
        assert!(outputs[1].contains("(model"), "Expected model output");
    }
}
#[test]
fn test_executor_qf_ax_get_value_array() {
    let input = r#"
        (set-logic QF_AX)
        (declare-const a (Array Int Int))
        (assert (= (select a 1) 42))
        (check-sat)
        (get-value (a))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 2);
    assert_eq!(outputs[0], "sat");
    // Array model can be represented as store(...) or (as const ...).
    // Both are valid SMT-LIB representations.
    assert!(
        outputs[1].contains("store") || outputs[1].contains("as const"),
        "Expected store or as-const in output: {}",
        outputs[1]
    );
    assert!(
        outputs[1].contains("42"),
        "Expected 42 in output: {}",
        outputs[1]
    );
    assert!(
        outputs[1].contains("Array Int Int"),
        "Expected array sort in output: {}",
        outputs[1]
    );
}
#[test]
fn test_executor_qf_ax_get_value_select() {
    // Regression test for #386: get-value on select expression should return
    // the stored value, not a placeholder
    let input = r#"
        (set-logic QF_AX)
        (declare-const a (Array Int Int))
        (assert (= (select a 1) 42))
        (check-sat)
        (get-value ((select a 1)))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 2);
    assert_eq!(outputs[0], "sat");
    // The select expression should evaluate to 42, not 0
    assert!(
        outputs[1].contains("42"),
        "Expected 42 in get-value output: {}",
        outputs[1]
    );
    // Should NOT contain 0 as the value
    assert!(
        !outputs[1].contains("(select a 1) 0)"),
        "Should not return placeholder 0: {}",
        outputs[1]
    );
}

// Lambda array tests (#8535)
// ==========================

#[test]
fn test_executor_qf_ax_lambda_array_sat() {
    // Lambda array: select(lambda(x) (+ x 1), 5) = 6
    // Uses QF_ALIA because lambda body contains arithmetic
    let input = r#"
        (set-logic QF_ALIA)
        (assert (= (select (lambda ((x Int)) (+ x 1)) 5) 6))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat"]);
}

#[test]
fn test_executor_qf_ax_lambda_array_unsat() {
    // Lambda array with constant body: select(lambda(x) 42, i) must be 42.
    // Asserting it equals something else is UNSAT.
    // Beta reduction makes this: 42 != 42 which is false.
    let input = r#"
        (set-logic QF_AX)
        (declare-const i Int)
        (assert (not (= (select (lambda ((x Int)) 42) i) 42)))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["unsat"]);
}

#[test]
fn test_executor_qf_ax_lambda_array_with_lia_body() {
    // Lambda array with arithmetic body: select(lambda(x)(+ x 1), 5) = 6
    // The beta reduction creates (+ 5 1) which the LIA theory evaluates.
    let input = r#"
        (set-logic QF_ALIA)
        (assert (= (select (lambda ((x Int)) (+ x 1)) 5) 6))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat"]);
}

#[test]
fn test_executor_qf_ax_lambda_array_store() {
    // Store on lambda array overrides at specific index
    let input = r#"
        (set-logic QF_ALIA)
        (declare-const arr (Array Int Int))
        (assert (= arr (store (lambda ((x Int)) 0) 5 42)))
        (assert (= (select arr 5) 42))
        (assert (= (select arr 3) 0))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat"]);
}

#[test]
fn test_executor_qf_ax_lambda_array_direct_select() {
    // Direct select on lambda array: beta reduction at term construction.
    // select(lambda(x) 42, i) is eager-reduced to 42 by mk_select.
    // This tests the direct syntactic beta reduction path.
    let input = r#"
        (set-logic QF_AX)
        (declare-const i Int)
        (declare-const j Int)
        (assert (= (select (lambda ((x Int)) 42) i) (select (lambda ((y Int)) 42) j)))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    // Both selects beta-reduce to 42, so (= 42 42) is trivially SAT
    assert_eq!(outputs, vec!["sat"]);
}

#[test]
fn test_executor_qf_ax_uninterpreted_sort_model_keeps_point_writes() {
    // #qfax-universe-collapse regression: with UNINTERPRETED index/element
    // sorts, every array cell value is an internal `@Sort!n` universe atom.
    // The printer's blanket `@`-skolem skip (#model-witness-no-skolem, aimed
    // at datatype representatives) also erased these — every select-derived
    // point write was dropped and the printed array collapsed to a bare
    // const-array that FALSIFIED the asserted reads, even though the verdict
    // was correct and the independent gate had validated the (richer)
    // internal interpretation. 21/100 of the 2026-07-20 skeptic-3 QF_AX
    // corpus printed such invalid models.
    //
    // This formula forces b to hold TWO DISTINCT values (b[k] = g, b[j] = f,
    // with e, f, g pairwise distinct forcing k != i and j != i), so NO
    // const-only rendering of `b` can satisfy it: a sound printed model MUST
    // contain at least one `store` point write on `b`.
    let input = r#"
        (set-logic QF_AX)
        (set-option :produce-models true)
        (declare-sort I 0)
        (declare-sort E 0)
        (declare-const b (Array I E))
        (declare-const i I)
        (declare-const j I)
        (declare-const k I)
        (declare-const e E)
        (declare-const f E)
        (declare-const g E)
        (assert (= (select (store b i e) k) g))
        (assert (= (select (store b i e) j) f))
        (assert (not (= e g)))
        (assert (not (= f g)))
        (assert (not (= f e)))
        (check-sat)
        (get-model)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs[0], "sat", "gate-confirmed sat expected");
    let model = &outputs[1];
    let b_def_start = model
        .find("(define-fun b ")
        .expect("array 'b' must be in the model");
    // The next define-fun (or the model's closing paren) ends b's definition.
    let b_def_end = model[b_def_start + 1..]
        .find("(define-fun ")
        .map_or(model.len(), |off| b_def_start + 1 + off);
    let b_def = &model[b_def_start..b_def_end];
    assert!(
        b_def.contains("(store "),
        "b holds two distinct cell values, so its printed model value must \
         carry a point write, not collapse to a bare const-array: {b_def}"
    );
    // The cells are universe atoms and must print sort-ascribed, never as a
    // bare internal `@` token (which validators reject as unbound).
    assert!(
        b_def.contains("(as @"),
        "expected sort-ascribed universe atoms in b's store chain: {b_def}"
    );
}

// QF_UFLIA get-value Tests
// ========================
