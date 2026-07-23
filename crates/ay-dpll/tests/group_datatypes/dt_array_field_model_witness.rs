// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Regression test for array-typed datatype FIELD model soundness
//! (#model-array-witness).
//!
//! An array nested as a datatype-constructor field exhibited the same invalid
//! witness as a top-level array: `bx`'s model rendered the `arr` field as the
//! bare const-array default `((as const (Array Int Int)) 0)`, so
//! `(select (arr bx) 3)` read `0 != 7` and violated the assertion.
//!
//! The fix renders the field as a `store`-chain (or a const-array whose default
//! already satisfies the constraint) so the constructor value is a valid
//! witness.

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
    let s = s.strip_prefix('(').unwrap_or(s);
    let s = s.strip_suffix(')').unwrap_or(s).trim();
    let s = s.strip_prefix('(').unwrap_or(s);
    let s = s.strip_suffix(')').unwrap_or(s).trim();
    s.split_once(char::is_whitespace)
        .map(|(_, v)| v.trim().to_string())
        .unwrap_or_default()
}

fn temp_smt(tag: &str, smt: &str) -> PathBuf {
    let path = std::env::temp_dir().join(format!(
        "ay_dt_array_witness_{tag}_{}.smt2",
        std::process::id()
    ));
    let mut f = std::fs::File::create(&path).expect("create temp smt");
    f.write_all(smt.as_bytes()).expect("write temp smt");
    path
}

/// Repro 2: array nested as a datatype field. `bx`'s model must satisfy
/// `(select (arr bx) 3) = 7` and `(n bx) = 5`; the array field must not
/// collapse to the const-`0` default (which reads `0 != 7`).
#[test]
fn datatype_array_field_model_is_valid_witness() {
    let smt = r#"
        (set-logic ALL)
        (declare-datatypes ((Box 0)) (((mkbox (arr (Array Int Int)) (n Int)))))
        (declare-const bx Box)
        (assert (= (select (arr bx) 3) 7))
        (assert (= (n bx) 5))
        (check-sat)
        (get-model)
        (get-value (bx))
    "#;
    let output = crate::common::solve(smt);
    let lines = results(&output);
    assert_eq!(lines[0], "sat", "{output}");

    // bx renders as the mkbox constructor.
    assert!(
        output.contains("(mkbox"),
        "bx must render as an mkbox constructor:\n{output}"
    );
    // The array field must NOT collapse to the const-0 default (invalid: it
    // would read (select (arr bx) 3) = 0 != 7).
    assert!(
        !output.contains("((as const (Array Int Int)) 0)"),
        "array field collapsed to const-0 default (invalid witness):\n{output}"
    );
    // A valid field is either a store at index 3 -> 7, or a const array whose
    // default is 7 (both satisfy (select (arr bx) 3) = 7).
    assert!(
        output.contains("3 7") || output.contains("((as const (Array Int Int)) 7)"),
        "array field does not satisfy (select (arr bx) 3) = 7:\n{output}"
    );

    // Re-feed ay's printed `bx` value (pinned) + the originals to z3: must be
    // CONSISTENT (`sat`).
    if crate::common::check_z3_or_skip() {
        let value = pair_value(lines.last().expect("get-value line"));
        let refed = format!(
            "(set-logic ALL)\n\
             (declare-datatypes ((Box 0)) (((mkbox (arr (Array Int Int)) (n Int)))))\n\
             (declare-const bx Box)\n\
             (assert (= (select (arr bx) 3) 7))\n\
             (assert (= (n bx) 5))\n\
             (assert (= bx {value}))\n\
             (check-sat)\n"
        );
        let path = temp_smt("repro2", &refed);
        let outcome = crate::common::run_z3_file(&path, 10).expect("run z3");
        let _ = std::fs::remove_file(&path);
        assert_eq!(
            outcome,
            crate::common::SolverOutcome::Sat,
            "ay's printed datatype/array model is inconsistent with the assertions (z3):\n{refed}"
        );
    }
}

/// True if `s` contains an internal skolem token (`@Sort!n` or `name!n`), which
/// z3 rejects as an unknown constant — an invalid model value.
fn has_skolem(s: &str) -> bool {
    let bytes = s.as_bytes();
    for (i, &b) in bytes.iter().enumerate() {
        if b == b'!' {
            // a run of ASCII digits must follow `!` for this to be a skolem
            let mut j = i + 1;
            while j < bytes.len() && bytes[j].is_ascii_digit() {
                j += 1;
            }
            if j > i + 1 {
                return true;
            }
        }
    }
    false
}

/// Bug C: a fully unconstrained datatype const must render a CONCRETE canonical
/// constructor value, not an internal `@Sort!n` skolem (z3 rejects it). Applies
/// to both `(get-value)` and `(get-model)`; constrained values are unchanged.
#[test]
fn unconstrained_datatype_const_has_no_skolem() {
    let smt = r#"
        (set-logic ALL)
        (declare-datatypes ((O 0)) (((non) (som (g Int)))))
        (declare-const o O)
        (check-sat)
        (get-model)
        (get-value (o))
    "#;
    let output = crate::common::solve(smt);
    let lines = results(&output);
    assert_eq!(lines[0], "sat", "{output}");

    // No skolem token anywhere in the printed model.
    assert!(
        !has_skolem(&output),
        "unconstrained datatype model leaks an internal skolem:\n{output}"
    );
    let value = pair_value(lines.last().expect("get-value line"));
    // Concrete canonical value: a constructor of O (here the nullary `non`).
    assert_eq!(
        value, "non",
        "expected canonical default `non`, got: {output}"
    );

    if crate::common::check_z3_or_skip() {
        let refed = format!(
            "(set-logic ALL)\n\
             (declare-datatypes ((O 0)) (((non) (som (g Int)))))\n\
             (declare-const o O)\n\
             (assert (= o {value}))\n\
             (check-sat)\n"
        );
        let path = temp_smt("bugc", &refed);
        let outcome = crate::common::run_z3_file(&path, 10).expect("run z3");
        let _ = std::fs::remove_file(&path);
        assert_eq!(
            outcome,
            crate::common::SolverOutcome::Sat,
            "unconstrained datatype witness rejected by z3:\n{refed}"
        );
    }
}

/// A constrained / tester-determined datatype value still renders exactly (the
/// Bug-C fix must not disturb determined values).
#[test]
fn constrained_datatype_const_unchanged() {
    let constrained = crate::common::solve(
        "(set-logic ALL)\n\
         (declare-datatypes ((O 0)) (((non) (som (g Int)))))\n\
         (declare-const o O)\n(assert (= o (som 7)))\n(check-sat)\n(get-value (o))\n",
    );
    assert!(
        constrained.contains("(o (som 7))"),
        "constrained datatype value changed: {constrained}"
    );
    let tester = crate::common::solve(
        "(set-logic ALL)\n\
         (declare-datatypes ((O 0)) (((non) (som (g Int)))))\n\
         (declare-const o O)\n(assert ((_ is som) o))\n(check-sat)\n(get-value (o))\n",
    );
    assert!(
        tester.contains("(o (som ") && !has_skolem(&tester),
        "tester-determined datatype value wrong: {tester}"
    );
}

/// Bug D: an array of datatype elements must use a CONCRETE default element and
/// capture the datatype-valued select constraint, so the witness reads back the
/// constrained cell and contains no skolem.
#[test]
fn array_of_datatype_model_is_valid_witness() {
    let smt = r#"
        (set-logic ALL)
        (declare-datatypes ((O 0)) (((non) (som (g Int)))))
        (declare-const a (Array Int O))
        (assert (= (select a 0) (som 7)))
        (check-sat)
        (get-model)
        (get-value (a))
    "#;
    let output = crate::common::solve(smt);
    let lines = results(&output);
    assert_eq!(lines[0], "sat", "{output}");

    // No skolem default; constrained cell present; concrete default element.
    assert!(
        !has_skolem(&output),
        "array-of-datatype model leaks an internal skolem:\n{output}"
    );
    assert!(
        output.contains("(som 7)"),
        "array model dropped the (select a 0)=(som 7) constraint:\n{output}"
    );
    assert!(
        output.contains("((as const (Array Int O)) non)"),
        "array default element must be the concrete `non`, got:\n{output}"
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
             (declare-datatypes ((O 0)) (((non) (som (g Int)))))\n\
             (declare-const a (Array Int O))\n\
             (assert (= (select a 0) (som 7)))\n\
             (assert (= a {a_val}))\n\
             (check-sat)\n"
        );
        let path = temp_smt("bugd", &refed);
        let outcome = crate::common::run_z3_file(&path, 10).expect("run z3");
        let _ = std::fs::remove_file(&path);
        assert_eq!(
            outcome,
            crate::common::SolverOutcome::Sat,
            "array-of-datatype witness rejected by z3:\n{refed}"
        );
    }
}

/// #dt-array-model-census — Phase 1 model census must CERTIFY select-congruence
/// over a datatype whose field is itself an array (the `Slice{ptr,len,data}`
/// shape). Two reads of one array at a DERIVED-equal index (`i = j + 0`) denote
/// the same `Slice` cell; their scalar fields are pinned equal and their `data`
/// array fields are observed at DISJOINT indices, so the two field arrays are
/// syntactically distinct terms that are nonetheless model-COMPATIBLE. The
/// census must reconstruct them cell-by-cell and certify SAT — the earlier
/// identity-by-term keying spuriously conflicted on the `data` field and
/// degraded this to `unknown`. Regression for the compatibility rewrite.
#[test]
fn datatype_array_field_select_congruence_certifies() {
    let smt = r#"
        (set-logic ALL)
        (declare-datatype Slice ((mk (ptr (_ BitVec 8)) (len (_ BitVec 8)) (dat (Array (_ BitVec 8) (_ BitVec 8))))))
        (declare-const A (Array (_ BitVec 8) Slice))
        (declare-const i (_ BitVec 8))
        (declare-const j (_ BitVec 8))
        (declare-const z Slice)
        (assert (= i (bvadd j #x00)))
        (assert (= z (select A i)))
        (assert (= (ptr (select A i)) #xFF))
        (assert (= (ptr (select A j)) #xFF))
        (assert (= (len (select A i)) #xFF))
        (assert (= (len (select A j)) #xFF))
        (assert (= (select (dat (select A i)) #x00) #x11))
        (assert (= (select (dat (select A j)) #x05) #x22))
        (check-sat)
    "#;
    let lines = results(&crate::common::solve(smt));
    assert_eq!(
        lines[0], "sat",
        "census must certify select-congruence over the datatype array field:\n{lines:?}"
    );
}

/// #dt-array-model-census — SOUNDNESS twin of the above. When the two `data`
/// field arrays are read at a COMMON index with CONFLICTING values while the
/// reads denote the same cell (`i = j + 0`), the instance is UNSAT. The census
/// must detect the definite congruence conflict (a common observed cell whose
/// values are incompatible) — ay must NOT answer `sat`.
#[test]
fn datatype_array_field_congruence_conflict_is_sound() {
    let smt = r#"
        (set-logic ALL)
        (declare-datatype Slice ((mk (ptr (_ BitVec 8)) (len (_ BitVec 8)) (dat (Array (_ BitVec 8) (_ BitVec 8))))))
        (declare-const A (Array (_ BitVec 8) Slice))
        (declare-const i (_ BitVec 8))
        (declare-const j (_ BitVec 8))
        (declare-const k (_ BitVec 8))
        (declare-const z Slice)
        (assert (= i (bvadd j #x00)))
        (assert (= z (select A i)))
        (assert (= (select (dat (select A i)) k) #x01))
        (assert (= (select (dat (select A j)) k) #x02))
        (check-sat)
    "#;
    let lines = results(&crate::common::solve(smt));
    assert_ne!(
        lines[0], "sat",
        "congruence conflict at a common data cell must NOT be reported sat:\n{lines:?}"
    );
    if crate::common::check_z3_or_skip() {
        let path = temp_smt("dt_cong_conflict", smt);
        let outcome = crate::common::run_z3_file(&path, 10).expect("run z3");
        let _ = std::fs::remove_file(&path);
        assert_eq!(
            outcome,
            crate::common::SolverOutcome::Unsat,
            "sanity: the congruence-conflict instance is unsat by z3"
        );
    }
}

/// #dt-array-nested-const-idx — NESTED array-of-array datatype select-congruence
/// across a CONSTANT vs SYMBOLIC inner index. `R : Array -> Array -> T`. The two
/// reads `(select (select R #x3) i)` and `(select (select R k) i)` with `k = #x3`
/// denote the SAME `T` cell, so their `p`-fields must agree. The scalar-projection
/// pass finds the contradiction, but nested-array UNSAT is intentionally
/// quarantined at the public boundary until the theory-combination refutation has
/// a trust-free certificate. Preserve the sound `unknown`; in particular, this
/// congruence conflict must never be reported `sat`.
#[test]
fn nested_array_of_array_const_symbolic_index_congruence_is_quarantined() {
    let smt = r#"
        (set-logic ALL)
        (declare-datatype T ((mk (p (_ BitVec 4)) (q (_ BitVec 4)))))
        (declare-const R (Array (_ BitVec 4) (Array (_ BitVec 4) T)))
        (declare-const k (_ BitVec 4))
        (declare-const i (_ BitVec 4))
        (declare-const z T)
        (assert (= z (select (select R k) i)))
        (assert (= k #x3))
        (assert (not (= (p (select (select R #x3) i)) (p (select (select R k) i)))))
        (check-sat)
    "#;
    let lines = results(&crate::common::solve(smt));
    assert_eq!(
        lines[0], "unknown",
        "uncertified nested array-of-array UNSAT must be quarantined:\n{lines:?}"
    );
}
