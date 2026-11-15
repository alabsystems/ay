// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! QF_AUFBV arrays of arrays take their model from their nested reads
//! (`theories/bv_model/nested_reads.rs`), and model completion merges an
//! array-valued cell as an array (`executor_format/array_cell.rs`):
//!
//! * a forced row copy `(= m (store m0 #x1 (select m0 #x2)))` over a free
//!   `m0` builds once `m0` has the row its read pins, so the forced read of
//!   `m` validates (it answered `unknown`);
//! * a free `m0` with one nested read keeps its model through completion,
//!   whose candidate folds the read into the row's else-value;
//! * a forced write of one byte into a row, `(store m0 k (store (select m0
//!   k) off v))`, builds from `m0`'s row parsed back from its cell
//!   (`nested_cells.rs`), so the model validates (it answered `unknown`);
//! * and a satisfiable formula (z3 5.1.0) whose property is model validity,
//!   not the verdict: a nested definition whose atom the SAT assignment set
//!   false. Released on its atom alone while acceptance still counted
//!   bit-blast coverage as evidence, AY answered `sat` with a printed model
//!   that falsified `(= (select (select m0 x) #x5) (select u #x5))`; since
//!   #bv-array-delegation the gate judges the printed arrays, and nothing
//!   defined only under a nested equality is withheld (`live_definitions.rs`).
//!
//! The fuzz reproducers below (z3 5.1.0: sat) answered `sat` with a valid
//! model at fd4e00f75 and lost it once arrays of arrays got their nested
//! reads: a withheld nested-only array left a round unevaluable or a
//! confirmed round unprintable (n7001_086, t9101_004), and one cell of an
//! array of arrays read through two row terms held two values that the FC
//! audit never compared (q8002_035, `bv_cegar_array/nested_fc.rs`).

use super::*;

fn run(input: &str) -> Vec<String> {
    let commands = parse(input).expect("invariant: valid SMT-LIB input");
    let mut exec = Executor::new();
    exec.execute_all(&commands)
        .expect("invariant: execute succeeds")
}

/// The model-checker-consumer memory row copy, forced by `(select a #x..42)`.
const ROW_COPY: &str = r#"
    (set-logic QF_AUFBV)
    (set-option :produce-models true)
    (declare-const a (Array (_ BitVec 64) Bool))
    (declare-const m (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 8))))
    (declare-const m0 (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 8))))
    (assert (select a #x0000000000000042))
    (assert (= (select (select m0 #x0000000000000002) #x0000000000000003) #x09))
    (assert (or (not (select a #x0000000000000042))
                (= m (store m0 #x0000000000000001 (select m0 #x0000000000000002)))))
"#;

#[test]
fn test_forced_row_copy_of_a_free_array_of_arrays_is_sat() {
    let input = format!(
        "{ROW_COPY} (assert (= (select (select m #x0000000000000001) #x0000000000000003) #x09))
         (check-sat)
         (get-value ((select (select m #x0000000000000001) #x0000000000000003)))"
    );
    let out = run(&input);
    assert_eq!(out[0], "sat", "{out:?}");
    assert_eq!(
        out[1], "(((select (select m #x0000000000000001) #x0000000000000003) #x09))",
        "{out:?}"
    );
}

#[test]
fn test_forced_row_copy_contradiction_is_not_sat() {
    let input = format!(
        "{ROW_COPY}
         (assert (not (= (select (select m #x0000000000000001) #x0000000000000003) #x09)))
         (check-sat)"
    );
    let out = run(&input);
    assert_ne!(out[0], "sat", "the copied row pins the cell: {out:?}");
}

/// A free `m0` read once at `[x][5]`, `x < 3`.
const ONE_NESTED_READ: &str = r#"
    (set-logic QF_AUFBV)
    (set-option :produce-models true)
    (declare-const u (Array (_ BitVec 4) (_ BitVec 3)))
    (declare-const m0 (Array (_ BitVec 4) (Array (_ BitVec 4) (_ BitVec 3))))
    (declare-const x (_ BitVec 4))
    (assert (bvult x #x3))
    (assert (= (select u #x5) #b100))
"#;

#[test]
fn test_single_nested_read_keeps_its_model_through_completion() {
    let input = format!(
        "{ONE_NESTED_READ} (assert (= (select (select m0 x) #x5) (select u #x5)))
         (check-sat)
         (get-value ((select (select m0 x) #x5)))"
    );
    let out = run(&input);
    assert_eq!(out[0], "sat", "{out:?}");
    assert_eq!(out[1], "(((select (select m0 x) #x5) #b100))", "{out:?}");
}

#[test]
fn test_single_nested_read_contradiction_is_unsat() {
    let input = format!(
        "{ONE_NESTED_READ} (assert (= (select (select m0 x) #x5) (select u #x5)))
         (assert (not (= (select (select m0 x) #x5) #b100)))
         (check-sat)"
    );
    assert_eq!(run(&input), vec!["unsat"]);
}

/// The fuzz shape whose nested definitions the SAT assignment refused while
/// the reads make both sides of `(= m (store n x ...))` one array.
const REFUSED_NESTED_DEFINITION: &str = r#"
    (set-logic QF_AUFBV)
    (set-option :produce-models true)
    (declare-const a (Array (_ BitVec 4) Bool))
    (declare-const b (Array (_ BitVec 4) Bool))
    (declare-const u (Array (_ BitVec 4) (_ BitVec 3)))
    (declare-const w (Array (_ BitVec 4) (_ BitVec 3)))
    (declare-const z (Array (_ BitVec 4) (_ BitVec 3)))
    (declare-const m0 (Array (_ BitVec 4) (Array (_ BitVec 4) (_ BitVec 3))))
    (declare-const m (Array (_ BitVec 4) (Array (_ BitVec 4) (_ BitVec 3))))
    (declare-const n (Array (_ BitVec 4) (Array (_ BitVec 4) (_ BitVec 3))))
    (declare-const x (_ BitVec 4))
    (declare-const y (_ BitVec 4))
    (declare-fun f ((_ BitVec 4)) Bool)
    (declare-fun g ((_ BitVec 4)) (_ BitVec 3))
    (declare-fun k ((_ BitVec 3)) (_ BitVec 4))
    (assert (ite (= m (store n x (store (select n #xc) y (select w x)))) (= u w) (= b a)))
    (assert (or (ite (= w (store u (k #b010) (g (k #b111)))) true (f x))
                (and (not (bvult x #xb)) (= n (store m0 x z)))))
    (assert (bvult x #x3))
    (assert (= (select (select m0 x) #x5) (select u #x5)))
"#;

/// The top-level s-expressions of `text`.
fn top_level_forms(text: &str) -> Vec<&str> {
    let mut forms = Vec::new();
    let mut depth = 0usize;
    let mut start = 0usize;
    for (at, ch) in text.char_indices() {
        match ch {
            '(' => {
                if depth == 0 {
                    start = at;
                }
                depth += 1;
            }
            ')' if depth > 0 => {
                depth -= 1;
                if depth == 0 {
                    forms.push(&text[start..=at]);
                }
            }
            _ => {}
        }
    }
    forms
}

/// A `sat` must come with a model that satisfies every assertion: the
/// printed definitions together with the assertions must not be `unsat`.
#[test]
fn test_refused_nested_definition_answers_sat_only_with_its_model() {
    let out = run(&format!(
        "{REFUSED_NESTED_DEFINITION} (check-sat) (get-model)"
    ));
    if out[0] == "sat" {
        assert_printed_model_holds(REFUSED_NESTED_DEFINITION, &out);
    }
}

/// The model-checker-consumer memory write of one byte, forced by `(select a #x..42)`.
const ROW_WRITE: &str = r#"
    (set-logic QF_AUFBV)
    (set-option :produce-models true)
    (declare-const a (Array (_ BitVec 64) Bool))
    (declare-const m (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 8))))
    (declare-const m0 (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 8))))
    (declare-const k (_ BitVec 64))
    (assert (select a #x0000000000000042))
    (assert (or (not (select a #x0000000000000042))
                (= m (store m0 k (store (select m0 k) #x0000000000000000 #x2a)))))
"#;

#[test]
fn test_forced_row_write_of_a_free_memory_is_sat_with_its_model() {
    let source = format!("{ROW_WRITE} (assert (= (select (select m k) #x0000000000000000) #x2a))");
    let out = run(&format!("{source} (check-sat) (get-model)"));
    assert_eq!(out[0], "sat", "{out:?}");
    assert_printed_model_holds(&source, &out);
}

#[test]
fn test_forced_row_write_contradiction_is_not_sat() {
    let input = format!(
        "{ROW_WRITE} (assert (= (select (select m k) #x0000000000000000) #x2b)) (check-sat)"
    );
    let out = run(&input);
    assert_ne!(out[0], "sat", "the written byte pins the cell: {out:?}");
}

/// Re-check a `sat` answer to `source` against the model it printed (`out[1]`):
/// the re-check must not be `unsat`.
fn assert_printed_model_holds(source: &str, out: &[String]) {
    assert_ne!(
        printed_model_recheck(source, out),
        "unsat",
        "the printed model falsifies an assertion: {}",
        out[1]
    );
}

/// The decisive form: every assertion holds under the printed model, so the
/// closed re-check is `sat`.
pub(super) fn assert_printed_model_satisfies(source: &str, out: &[String]) {
    assert_eq!(
        printed_model_recheck(source, out),
        "sat",
        "the printed model must satisfy every assertion: {}",
        out[1]
    );
}

/// AY's answer to the assertions of `source` with the definitions a `sat`
/// answer printed (`out[1]`) in place of its declarations.
fn printed_model_recheck(source: &str, out: &[String]) -> String {
    let model = top_level_forms(&out[1])
        .first()
        .and_then(|form| form.strip_prefix('(')?.strip_suffix(')'))
        .unwrap_or_else(|| panic!("unexpected get-model shape: {out:?}"));
    let definitions: Vec<&str> = top_level_forms(model)
        .into_iter()
        .filter(|form| form.starts_with("(define-fun"))
        .collect();
    assert!(!definitions.is_empty(), "no definitions printed: {out:?}");
    let name = |form: &str| form.split_whitespace().nth(1).map(str::to_owned);
    let defined: Vec<String> = definitions.iter().filter_map(|form| name(form)).collect();
    let source = top_level_forms(source);
    // Symbols the model leaves out stay declared, so the re-check parses.
    let undefined = source.iter().filter(|form| {
        form.starts_with("(declare-") && name(form).is_some_and(|n| !defined.contains(&n))
    });
    let assertions = source.iter().filter(|form| form.starts_with("(assert"));
    let recheck: Vec<&str> = undefined
        .chain(definitions.iter())
        .chain(assertions)
        .copied()
        .collect();
    let recheck = format!("(set-logic QF_AUFBV)\n{}\n(check-sat)", recheck.join("\n"));
    run(&recheck).swap_remove(0)
}

/// nA n7001_086: `m`'s only definition sits in an `and` beside `p`, and the
/// model takes `(= x y)`; withheld, `m` left every round's
/// `(= (select m (ite p x y)) (select m0 #b00))` unevaluable.
const NESTED_ONLY_DEFINITION: &str = r#"
    (set-option :produce-models true)
    (set-logic QF_AUFBV)
    (declare-const u (Array (_ BitVec 2) (_ BitVec 1)))
    (declare-const w (Array (_ BitVec 2) (_ BitVec 1)))
    (declare-const z (Array (_ BitVec 2) (_ BitVec 1)))
    (declare-const m0 (Array (_ BitVec 2) (Array (_ BitVec 2) (_ BitVec 1))))
    (declare-const m (Array (_ BitVec 2) (Array (_ BitVec 2) (_ BitVec 1))))
    (declare-const n (Array (_ BitVec 2) (Array (_ BitVec 2) (_ BitVec 1))))
    (declare-const p Bool)
    (declare-const q Bool)
    (declare-const x (_ BitVec 2))
    (declare-const y (_ BitVec 2))
    (declare-const v (_ BitVec 1))
    (declare-fun ff ((_ BitVec 2)) Bool)
    (declare-fun gg ((_ BitVec 2)) (_ BitVec 1))
    (declare-fun kk ((_ BitVec 1)) (_ BitVec 2))
    (assert (or (= x y) (and p (not (= m m0)) (= m (store n (ite p x y) (store (select m0 (kk (_ bv1 1))) (bvadd x (_ bv1 2)) (gg (_ bv2 2))))))))
    (assert (= (select m (ite p x y)) (select m0 (_ bv0 2))))
    (assert (not (= (select n (ite p x y)) (select n (_ bv1 2)))))
    (assert (= v (_ bv1 1)))
"#;

#[test]
fn test_nested_only_definition_does_not_withhold_its_array() {
    let out = run(&format!("{NESTED_ONLY_DEFINITION} (check-sat) (get-model)"));
    assert_eq!(out[0], "sat", "{out:?}");
    assert_printed_model_satisfies(NESTED_ONLY_DEFINITION, &out);
}

/// tN t9101_004: `z`'s only definition is under `(=> (= v #b011) ..)` with
/// `v = 0`. The first round was confirmed with `z` withheld, so `(get-model)`
/// could not print it. What this pins is `sat` with a printable model: AY's
/// own re-check of the printed model is not decisive here (the large `or`
/// stops on its resource budget, `unknown`), so it only refuses `unsat`; z3
/// 5.1.0 accepts the printed model.
const IMPLIED_DEFINITION: &str = r#"
    (set-option :produce-models true)
    (set-logic QF_AUFBV)
    (declare-const a (Array (_ BitVec 4) Bool))
    (declare-const b (Array (_ BitVec 4) Bool))
    (declare-const c (Array (_ BitVec 4) Bool))
    (declare-const d (Array (_ BitVec 4) Bool))
    (declare-const e (Array (_ BitVec 4) Bool))
    (declare-const u (Array (_ BitVec 4) (_ BitVec 3)))
    (declare-const w (Array (_ BitVec 4) (_ BitVec 3)))
    (declare-const z (Array (_ BitVec 4) (_ BitVec 3)))
    (declare-const m0 (Array (_ BitVec 4) (Array (_ BitVec 4) (_ BitVec 3))))
    (declare-const m (Array (_ BitVec 4) (Array (_ BitVec 4) (_ BitVec 3))))
    (declare-const n (Array (_ BitVec 4) (Array (_ BitVec 4) (_ BitVec 3))))
    (declare-const p Bool)
    (declare-const q Bool)
    (declare-const x (_ BitVec 4))
    (declare-const y (_ BitVec 4))
    (declare-const v (_ BitVec 3))
    (declare-fun f ((_ BitVec 4)) Bool)
    (declare-fun g ((_ BitVec 4)) (_ BitVec 3))
    (declare-fun h (Bool) Bool)
    (declare-fun k ((_ BitVec 3)) (_ BitVec 4))
    (assert (=> (= v (_ bv3 3)) (= z ((as const (Array (_ BitVec 4) (_ BitVec 3))) (_ bv3 3)))))
    (assert (or (bvult x (_ bv13 4)) (and (= (g x) (g y)) (= w (store ((as const (Array (_ BitVec 4) (_ BitVec 3))) (select u (_ bv0 4))) (_ bv1 4) (select u (_ bv12 4))))) (and (= (select u (k (_ bv0 3))) (ite (select b (_ bv3 4)) (_ bv3 3) (g (_ bv9 4)))) (= (select u (k (_ bv7 3))) (select (select m (_ bv13 4)) (_ bv5 4))))))
    (assert (not (= b e)))
    (assert (= v (_ bv0 3)))
    (assert (= (select u x) (select (select m (_ bv1 4)) (bvadd x (_ bv1 4)))))
    (assert (select c (_ bv6 4)))
    (assert (not (= (select w (k (g y))) (g (_ bv10 4)))))
    (assert (select a (_ bv10 4)))
    (assert (= x y))
    (assert (not (select e x)))
    (assert (= (select n (bvadd x (_ bv1 4))) w))
    (assert (not (bvult x (_ bv15 4))))
"#;

#[test]
fn test_definition_under_a_false_antecedent_keeps_the_model_printable() {
    let out = run(&format!("{IMPLIED_DEFINITION} (check-sat) (get-model)"));
    assert_eq!(out[0], "sat", "{out:?}");
    assert!(!out[1].contains("(error"), "{out:?}");
    assert_printed_model_holds(IMPLIED_DEFINITION, &out);
}

/// qB q8002_035: `m[#b10][x + 1]` and `m[#b10][#b10]` with `x = #b01`.
const NESTED_READ_PATHS: &str = r#"
    (set-option :produce-models true)
    (set-logic QF_AUFBV)
    (declare-const u (Array (_ BitVec 2) Bool))
    (declare-const w (Array (_ BitVec 2) Bool))
    (declare-const z (Array (_ BitVec 2) Bool))
    (declare-const m0 (Array (_ BitVec 2) (Array (_ BitVec 2) Bool)))
    (declare-const m (Array (_ BitVec 2) (Array (_ BitVec 2) Bool)))
    (declare-const n (Array (_ BitVec 2) (Array (_ BitVec 2) Bool)))
    (declare-const p Bool)
    (declare-const q Bool)
    (declare-const x (_ BitVec 2))
    (declare-const y (_ BitVec 2))
    (declare-const v Bool)
    (declare-fun ff ((_ BitVec 2)) Bool)
    (declare-fun gg ((_ BitVec 2)) Bool)
    (assert (= n (store (store m (bvadd x (_ bv1 2)) ((as const (Array (_ BitVec 2) Bool)) (select (select n (bvadd x (_ bv1 2))) (_ bv0 2)))) (_ bv0 2) w)))
    (assert (not (= u w)))
    (assert (or (ite (= (select (select m0 (_ bv2 2)) (_ bv3 2)) true) (= n (store (store m (ite (select (select m0 x) (_ bv2 2)) x y) (store (select m0 x) (_ bv0 2) (gg (ite p x y)))) (_ bv2 2) (store (select m (ite (gg (bvadd x (_ bv1 2))) x y)) (_ bv1 2) true))) (not (= x y))) (and (not q) (= (select (select n (_ bv0 2)) (bvadd x (_ bv1 2))) (gg (_ bv1 2))))))
    (assert (ff x))
    (assert (= (select m (_ bv3 2)) (select m (bvadd x (_ bv1 2)))))
    (assert (= (select (select m (_ bv2 2)) (bvadd x (_ bv1 2))) false))
"#;

#[test]
fn test_one_cell_read_through_two_row_terms_reaches_a_model() {
    let out = run(&format!("{NESTED_READ_PATHS} (check-sat) (get-model)"));
    assert_eq!(out[0], "sat", "{out:?}");
    assert_printed_model_satisfies(NESTED_READ_PATHS, &out);
}

/// A flat array released with its reads: `w`'s two definitions are both
/// live, so neither is adopted and `w` is published (no longer withheld) with
/// the cells its reads give it, which must satisfy the formula. Either
/// definition pins `w[2]` to `u[2]`, so the contradiction is not `sat`; the
/// search refutes it before any model exists, so that half passes with or
/// without the release. The release's fail-closed twin is the model-level
/// `released_array_of_arrays_holding_its_refused_definition_fails_closed`
/// (`model/tests/bv_array_delegation.rs`).
const TWO_LIVE_DEFINITIONS: &str = r#"
    (set-logic QF_AUFBV)
    (set-option :produce-models true)
    (declare-const u (Array (_ BitVec 4) (_ BitVec 3)))
    (declare-const w (Array (_ BitVec 4) (_ BitVec 3)))
    (assert (or (= w (store u #x1 #b101)) (= w (store u #x1 #b110))))
    (assert (= (select u #x2) #b011))
"#;

#[test]
fn test_two_live_definitions_keep_their_read() {
    let sat = format!("{TWO_LIVE_DEFINITIONS} (assert (= (select w #x2) #b011))");
    let out = run(&format!("{sat} (check-sat) (get-model)"));
    assert_eq!(out[0], "sat", "{out:?}");
    assert_printed_model_satisfies(&sat, &out);
    let unsat =
        format!("{TWO_LIVE_DEFINITIONS} (assert (not (= (select w #x2) #b011))) (check-sat)");
    assert_ne!(run(&unsat)[0], "sat", "either definition pins w[2]");
}
