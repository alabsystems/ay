// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! AUFLIA preprocessing under arrays+UF used to skip variable
//! substitution wholesale (the array fixpoint can reintroduce
//! pre-substitution applications whose arguments need defining
//! equalities in EUF). It now eliminates variables that occur only
//! in builtin contexts, keeps application/select/store arguments
//! named, and retains defining assertions for what it substitutes.

use super::*;

fn load(input: &str) -> Executor {
    let commands = parse(input).expect("SMT-LIB script should parse");
    let mut exec = Executor::new();
    exec.execute_all(&commands)
        .expect("SMT-LIB script should execute");
    exec
}

fn var_id(exec: &mut Executor, name: &str, sort: Sort) -> TermId {
    exec.ctx.terms.mk_var(name, sort)
}

fn roots_mentioning(terms: &TermStore, roots: &[TermId], needle: TermId) -> usize {
    roots
        .iter()
        .filter(|&&root| {
            let mut pending = vec![root];
            let mut seen = vec![false; terms.len()];
            while let Some(id) = pending.pop() {
                if id == needle {
                    return true;
                }
                if seen[id.index()] {
                    continue;
                }
                seen[id.index()] = true;
                match terms.get(id) {
                    TermData::App(_, args) => pending.extend_from_slice(args),
                    TermData::Not(a) => pending.push(*a),
                    TermData::Ite(a, b, c) => pending.extend([*a, *b, *c]),
                    _ => {}
                }
            }
            false
        })
        .count()
}

const MIXED: &str = "(set-logic QF_AUFLIA)
    (declare-fun f (Int) Int)
    (declare-const a0 (Array Int Int))
    (declare-const a1 (Array Int Int))
    (declare-const base Int)
    (declare-const o0 Int)
    (declare-const o1 Int)
    (declare-const idx Int)
    (declare-const v Int)
    (assert (= o0 (+ base 1)))
    (assert (= o1 (+ o0 4)))
    (assert (= idx (+ base 2)))
    (assert (= v (+ o0 3)))
    (assert (= a1 (store a0 idx v)))
    (assert (= (select a0 o1) 7))
    (assert (= (f idx) 3))
    (assert (> o0 0))";

#[test]
fn auflia_preprocessing_eliminates_only_builtin_context_vars() {
    let mut exec = load(MIXED);
    let o0 = var_id(&mut exec, "o0", Sort::Int);
    let o1 = var_id(&mut exec, "o1", Sort::Int);
    let idx = var_id(&mut exec, "idx", Sort::Int);
    let v = var_id(&mut exec, "v", Sort::Int);
    let a1 = var_id(&mut exec, "a1", Sort::array(Sort::Int, Sort::Int));
    let (preprocessed, _provenance, _var_subst) =
        exec.preprocess_auflia_assertions_with_proof_provenance();
    // o0 occurs only in builtin arithmetic contexts: substituted
    // everywhere, with only its retained defining root mentioning it.
    assert!(exec.recorded_var_substitutions.contains_key(&o0));
    assert_eq!(
        roots_mentioning(&exec.ctx.terms, &preprocessed, o0),
        1,
        "o0 should survive only in its retained defining assertion"
    );
    // o1 (select index), idx (UF argument + store index) and v (store
    // value) keep their names and defining equalities.
    for protected in [o1, idx, v] {
        assert!(!exec.recorded_var_substitutions.contains_key(&protected));
        assert!(roots_mentioning(&exec.ctx.terms, &preprocessed, protected) >= 2);
    }
    // The array definition is retained.
    assert!(!exec.recorded_var_substitutions.contains_key(&a1));
    assert!(roots_mentioning(&exec.ctx.terms, &preprocessed, a1) >= 1);
}

#[test]
fn auflia_eliminated_values_are_recovered_in_the_model() {
    let output = run_script(&format!(
        "{MIXED}\n(assert (= base 10))\n(check-sat)\n(get-value (o0 o1 v))\n"
    ));
    let joined = output.join(" ");
    assert!(joined.contains("sat"), "expected sat, got: {joined}");
    assert!(
        joined.contains("(o0 11)") && joined.contains("(o1 15)") && joined.contains("(v 14)"),
        "values must be consistent (o0=11, o1=15, v=14), got: {joined}"
    );
}

#[test]
fn auflia_array_congruence_stays_unsat_after_substitution() {
    let output = run_script(
        "(set-logic QF_AUFLIA)
         (declare-fun f (Int) Int)
         (declare-const a0 (Array Int Int))
         (declare-const a1 (Array Int Int))
         (declare-const k Int)
         (declare-const w Int)
         (declare-const base Int)
         (assert (= w (+ base 1)))
         (assert (= a1 (store a0 k w)))
         (assert (= (f base) 0))
         (assert (distinct (select a1 k) w))
         (check-sat)",
    );
    let joined = output.join(" ");
    assert!(
        joined.contains("unsat"),
        "read-over-write must stay unsat, got: {joined}"
    );
}
