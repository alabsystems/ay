// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Regression tests for array model-VALUE soundness (#model-array-witness).
//!
//! The verdict was already correct, but `(get-model)` / `(get-value (a))`
//! rendered a whole-array value as the BARE const-array default
//! (`((as const ...) <default>)`), dropping every constrained `(select a i)=v`
//! entry. The printed witness then VIOLATED the assertions: e.g. for
//! `(= (select a 1) #x09)` the model read `(select a 1) = #x00 != #x09`.
//!
//! The fix renders a `store`-chain over the default that includes every
//! constrained point, so the printed array satisfies the assertions. Per-index
//! evaluation (`(get-value (select a i))`) was already correct and is reused.

use std::io::Write;
use std::path::PathBuf;

fn results(output: &str) -> Vec<String> {
    output
        .lines()
        .map(|l| l.trim().to_string())
        .filter(|l| !l.is_empty())
        .collect()
}

/// Extract `VALUE` from a single-binding `(get-value ...)` line `((NAME VALUE))`.
fn pair_value(getvalue: &str) -> String {
    let s = getvalue.trim();
    // ((NAME VALUE)) -> (NAME VALUE)
    let s = s.strip_prefix('(').unwrap_or(s);
    let s = s.strip_suffix(')').unwrap_or(s).trim();
    // (NAME VALUE) -> NAME VALUE
    let s = s.strip_prefix('(').unwrap_or(s);
    let s = s.strip_suffix(')').unwrap_or(s).trim();
    s.split_once(char::is_whitespace)
        .map(|(_, v)| v.trim().to_string())
        .unwrap_or_default()
}

/// Write `smt` to a unique temp file and return its path.
fn temp_smt(tag: &str, smt: &str) -> PathBuf {
    let path = std::env::temp_dir().join(format!(
        "ay_array_witness_{tag}_{}.smt2",
        std::process::id()
    ));
    let mut f = std::fs::File::create(&path).expect("create temp smt");
    f.write_all(smt.as_bytes()).expect("write temp smt");
    path
}

/// Extract the balanced s-expression value bound to `name` from a `(get-value)`
/// line like `((a VALUE) (b VALUE))`. Returns the `VALUE` text.
fn binding(line: &str, name: &str) -> Option<String> {
    let needle = format!("({name} ");
    let start = line.find(&needle)? + needle.len();
    let bytes = line.as_bytes();
    if bytes.get(start) == Some(&b'(') {
        let mut depth = 0usize;
        let mut i = start;
        while i < bytes.len() {
            match bytes[i] {
                b'(' => depth += 1,
                b')' => {
                    depth -= 1;
                    if depth == 0 {
                        i += 1;
                        break;
                    }
                }
                _ => {}
            }
            i += 1;
        }
        Some(line[start..i].to_string())
    } else {
        let end = line[start..]
            .find([' ', ')'])
            .map(|e| start + e)
            .unwrap_or(line.len());
        Some(line[start..end].to_string())
    }
}

/// Repro 1: array constrained by selects. The printed model must be a
/// `store`-chain whose entries satisfy `(select a 1)=#x09` and
/// `(select a 2)=#x13`, not the bare const default.
#[test]
fn array_select_constrained_model_is_valid_store_chain() {
    let smt = r#"
        (set-logic ALL)
        (declare-const a (Array Int (_ BitVec 8)))
        (assert (= (select a 1) #x09))
        (assert (= (select a 2) #x13))
        (check-sat)
        (get-model)
        (get-value (a))
    "#;
    let output = crate::common::solve(smt);
    let lines = results(&output);
    assert_eq!(lines[0], "sat", "{output}");

    // The whole-array model literally contains the constrained store points.
    assert!(
        output.contains("(store"),
        "array model must be a store-chain, got:\n{output}"
    );
    assert!(
        output.contains("1 #x09"),
        "store at index 1 -> #x09 missing:\n{output}"
    );
    assert!(
        output.contains("2 #x13"),
        "store at index 2 -> #x13 missing:\n{output}"
    );

    // Re-feed ay's printed array value (pinned) + the originals to z3: the
    // witness must be CONSISTENT (`sat`), proving it does not violate the
    // assertions.
    if crate::common::check_z3_or_skip() {
        let value = pair_value(lines.last().expect("get-value line"));
        let refed = format!(
            "(set-logic ALL)\n\
             (declare-const a (Array Int (_ BitVec 8)))\n\
             (assert (= (select a 1) #x09))\n\
             (assert (= (select a 2) #x13))\n\
             (assert (= a {value}))\n\
             (check-sat)\n"
        );
        let path = temp_smt("repro1", &refed);
        let outcome = crate::common::run_z3_file(&path, 10).expect("run z3");
        let _ = std::fs::remove_file(&path);
        assert_eq!(
            outcome,
            crate::common::SolverOutcome::Sat,
            "ay's printed array model is inconsistent with the assertions (z3):\n{refed}"
        );
    }
}

/// Bug A: array-of-arrays (nested). The OUTER array's default element is itself
/// an array; rendering it as the bare const-0 inner array makes `a[0][0]=0 != 1`
/// (invalid witness). The nested element must reflect the inner constraint, and
/// `(get-model)` / `(get-value)` of `a` must agree and re-feed to `sat`.
#[test]
fn nested_array_of_arrays_model_is_valid_witness() {
    let smt = r#"
        (set-logic ALL)
        (declare-const a (Array Int (Array Int Int)))
        (assert (= (select (select a 0) 0) 1))
        (check-sat)
        (get-model)
        (get-value (a))
    "#;
    let output = crate::common::solve(smt);
    let lines = results(&output);
    assert_eq!(lines[0], "sat", "{output}");

    // The whole-array model must NOT collapse to a const-0 inner default
    // everywhere (that reads a[0][0]=0, violating the constraint).
    assert!(
        !output
            .contains("((as const (Array Int (Array Int Int))) ((as const (Array Int Int)) 0)))"),
        "nested array collapsed to const-0 default (invalid witness):\n{output}"
    );

    let gv = lines.last().expect("get-value line");
    let a_val = binding(gv, "a").expect("a binding");
    // get-model define-fun(a) and get-value(a) agree (same renderer).
    assert!(
        output.contains(&a_val),
        "get-model and get-value disagree on a:\n{output}"
    );

    if crate::common::check_z3_or_skip() {
        let refed = format!(
            "(set-logic ALL)\n\
             (declare-const a (Array Int (Array Int Int)))\n\
             (assert (= (select (select a 0) 0) 1))\n\
             (assert (= a {a_val}))\n\
             (check-sat)\n"
        );
        let path = temp_smt("repro_nested", &refed);
        let outcome = crate::common::run_z3_file(&path, 10).expect("run z3");
        let _ = std::fs::remove_file(&path);
        assert_eq!(
            outcome,
            crate::common::SolverOutcome::Sat,
            "nested array witness inconsistent with the assertion (z3):\n{refed}"
        );
    }
}

/// Bug B: a store-equality-dependent array must stay COHERENT with its base.
/// For `b = (store a 1 10)`, `b[j] = a[j]` for every `j != 1` and `b[1] = 10`;
/// the historical bug desynced b's don't-care cells from a's (b read a stale
/// value its own printed witness contradicted), and/or adopted the stored
/// value `10` as b's default. The exact value of the unconstrained cell
/// `a[2]` is a completion CHOICE and is deliberately not pinned
/// (#partial-interp-no-invented-default keeps don't-care cells out of the
/// interpretation; the printer completes a and b coherently) — what is pinned
/// is `b[2] = a[2]`, `b[1] = 10`, the forced `b[0] = a[0] = 99`,
/// `(get-model)`/`(get-value)` agreement, and a `sat` re-feed.
#[test]
fn store_equality_array_inherits_base_default() {
    let smt = r#"
        (set-logic ALL)
        (declare-const a (Array Int Int))
        (declare-const b (Array Int Int))
        (assert (= b (store a 1 10)))
        (assert (= (select a 0) 99))
        (check-sat)
        (get-model)
        (get-value (a b))
        (get-value ((select b 0) (select b 1) (select b 2) (select a 2)))
    "#;
    let output = crate::common::solve(smt);
    let lines = results(&output);
    assert_eq!(lines[0], "sat", "{output}");

    // get-value cells: b[0]=99 (forced), b[1]=10 (the store), b[2]=a[2].
    assert!(
        output.contains("((select b 0) 99)"),
        "b[0] must be 99 (forced through b = store(a,1,10) and a[0]=99):\n{output}"
    );
    assert!(
        output.contains("((select b 1) 10)"),
        "b[1] must be 10:\n{output}"
    );
    let cells_line = lines
        .iter()
        .find(|l| l.contains("((select b 2) "))
        .expect("get-value cells line");
    let b2 = binding(cells_line, "(select b 2)").expect("b[2] value");
    let a2 = binding(cells_line, "(select a 2)").expect("a[2] value");
    assert_eq!(
        b2, a2,
        "b[2] must inherit a[2] through b = (store a 1 10):\n{output}"
    );
    // b's printed model must NOT adopt the stored value 10 as its default.
    assert!(
        !output.contains("((as const (Array Int Int)) 10)"),
        "b default wrongly taken from the stored value 10:\n{output}"
    );

    let consts_line = lines
        .iter()
        .find(|l| l.contains("(a ") && l.contains("(b "))
        .expect("get-value (a b) line");
    let a_val = binding(consts_line, "a").expect("a binding");
    let b_val = binding(consts_line, "b").expect("b binding");
    // get-model define-fun(b) and get-value(b) agree (same renderer).
    assert!(
        output.contains(&b_val),
        "get-model and get-value disagree on b:\n{output}"
    );

    if crate::common::check_z3_or_skip() {
        let refed = format!(
            "(set-logic ALL)\n\
             (declare-const a (Array Int Int))\n\
             (declare-const b (Array Int Int))\n\
             (assert (= b (store a 1 10)))\n\
             (assert (= (select a 0) 99))\n\
             (assert (= a {a_val}))\n\
             (assert (= b {b_val}))\n\
             (check-sat)\n"
        );
        let path = temp_smt("repro_storeeq", &refed);
        let outcome = crate::common::run_z3_file(&path, 10).expect("run z3");
        let _ = std::fs::remove_file(&path);
        assert_eq!(
            outcome,
            crate::common::SolverOutcome::Sat,
            "store-equality array witness inconsistent with the assertions (z3):\n{refed}"
        );
    }
}

/// True if `s` contains an internal skolem token (`@Sort!n` or `name!n`), which
/// z3 rejects as an unknown constant.
fn has_skolem(s: &str) -> bool {
    let b = s.as_bytes();
    for (i, &c) in b.iter().enumerate() {
        if c == b'!' {
            let mut j = i + 1;
            while j < b.len() && b[j].is_ascii_digit() {
                j += 1;
            }
            if j > i + 1 {
                return true;
            }
        }
    }
    false
}

/// Bug E: a datatype-sorted array KEY (store index) must be concretized to a
/// constructor term, not the internal `@Color!0` skolem (z3 rejects it). The
/// model knows the skolem key equals `red` because `(select a red)` puts them in
/// one equivalence class. get-model and get-value must agree and re-feed `sat`.
#[test]
fn datatype_keyed_array_index_has_no_skolem() {
    let smt = r#"
        (set-logic ALL)
        (declare-datatypes ((Color 0)) (((red) (green) (blue))))
        (declare-const a (Array Color Int))
        (assert (= (select a red) 1))
        (assert (= (select a blue) 3))
        (check-sat)
        (get-model)
        (get-value (a))
    "#;
    let output = crate::common::solve(smt);
    let lines = results(&output);
    assert_eq!(lines[0], "sat", "{output}");

    // No skolem token anywhere (the store INDEX must be a Color constructor).
    assert!(
        !has_skolem(&output),
        "datatype-keyed array model leaks a skolem index:\n{output}"
    );
    // The concrete constructor keys appear as store indices.
    assert!(
        output.contains(" red 1") || output.contains(" red\n") || output.contains("red 1"),
        "store index must be the concrete constructor `red`:\n{output}"
    );

    let a_val = pair_value(lines.last().expect("get-value line"));
    // get-model define-fun(a) and get-value(a) agree.
    assert!(
        output.contains(&a_val),
        "get-model and get-value disagree on a:\n{output}"
    );

    if crate::common::check_z3_or_skip() {
        let refed = format!(
            "(set-logic ALL)\n\
             (declare-datatypes ((Color 0)) (((red) (green) (blue))))\n\
             (declare-const a (Array Color Int))\n\
             (assert (= (select a red) 1))\n\
             (assert (= (select a blue) 3))\n\
             (assert (= a {a_val}))\n\
             (check-sat)\n"
        );
        let path = temp_smt("buge", &refed);
        let outcome = crate::common::run_z3_file(&path, 10).expect("run z3");
        let _ = std::fs::remove_file(&path);
        assert_eq!(
            outcome,
            crate::common::SolverOutcome::Sat,
            "datatype-keyed array witness rejected by z3:\n{refed}"
        );
    }
}
