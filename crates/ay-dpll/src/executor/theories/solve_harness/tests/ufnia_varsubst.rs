// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! UFNIA preprocessing must eliminate scalar SSA definitions the way
//! z3's solve-eqs collapse does on blast encodings (the s3 family),
//! while keeping array definitions for the deferred model validator
//! and recording every substitution for model completion.

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

fn mentions(terms: &TermStore, roots: &[TermId], needle: TermId) -> bool {
    let mut pending: Vec<TermId> = roots.to_vec();
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
}

/// No declared UF: full scalar substitution is enrolled. (With a
/// declared UF the lane folds only VAR := CONSTANT — see
/// `ufnia_preprocessing_with_uf_folds_only_constants`.)
const SSA: &str = "(set-logic QF_AUFNIA)
    (declare-const a0 (Array Int Int))
    (declare-const a1 (Array Int Int))
    (declare-const x Int)
    (declare-const y0 Int)
    (declare-const y1 Int)
    (declare-const b Bool)
    (assert (= y0 (+ x 1)))
    (assert (= y1 (* y0 2)))
    (assert (= b (> y1 3)))
    (assert (= a1 (store a0 0 7)))
    (assert (= (select a0 y1) 9))
    (assert b)";

#[test]
fn ufnia_preprocessing_eliminates_scalar_ssa_definitions() {
    let mut exec = load(SSA);
    let y0 = var_id(&mut exec, "y0", Sort::Int);
    let y1 = var_id(&mut exec, "y1", Sort::Int);
    let b = var_id(&mut exec, "b", Sort::Bool);
    let (preprocessed, _provenance) = exec.preprocess_ufnia_assertions_with_proof_provenance();
    // Scalar SSA variables are eliminated from every remaining root.
    assert!(
        !mentions(&exec.ctx.terms, &preprocessed, y0),
        "y0 must be eliminated by UFNIA preprocessing"
    );
    assert!(
        !mentions(&exec.ctx.terms, &preprocessed, y1),
        "y1 must be eliminated by UFNIA preprocessing"
    );
    assert!(
        !mentions(&exec.ctx.terms, &preprocessed, b),
        "b must be eliminated by UFNIA preprocessing"
    );
    // The array definition is retained for the model validator.
    let a1 = var_id(&mut exec, "a1", Sort::array(Sort::Int, Sort::Int));
    assert!(
        mentions(&exec.ctx.terms, &preprocessed, a1),
        "array definition must be retained (skip-array-sort)"
    );
    // Substitutions are recorded for model completion at finalize time.
    assert!(exec.recorded_var_substitutions.contains_key(&y0));
    assert!(exec.recorded_var_substitutions.contains_key(&y1));
    assert!(exec.recorded_var_substitutions.contains_key(&b));
    assert!(!exec.recorded_var_substitutions.contains_key(&a1));
}

#[test]
fn ufnia_preprocessing_eliminates_long_ssa_chains() {
    // Blast SSA chains run hundreds of links; a composed-DAG node cap
    // (the ABV budgeted variant) would stop accepting substitutions
    // after ~16 links and leave the tail named.
    let mut script = String::from(
        "(set-logic QF_AUFNIA)\n(declare-const a0 (Array Int Int))\n(declare-const x Int)\n(declare-const z0 Int)\n(assert (= z0 (+ x (select a0 0))))\n",
    );
    for i in 1..40 {
        script.push_str(&format!("(declare-const z{i} Int)\n"));
        script.push_str(&format!("(assert (= z{i} (+ z{} 1)))\n", i - 1));
    }
    script.push_str("(assert (= (select a0 z39) 3))\n");
    let mut exec = load(&script);
    let z39 = var_id(&mut exec, "z39", Sort::Int);
    let (preprocessed, _provenance) = exec.preprocess_ufnia_assertions_with_proof_provenance();
    assert!(
        !mentions(&exec.ctx.terms, &preprocessed, z39),
        "chain tail z39 must be eliminated (no composed-DAG cap)"
    );
    assert!(exec.recorded_var_substitutions.contains_key(&z39));
}

#[test]
fn ufnia_preprocessing_with_uf_folds_only_constants() {
    // Declared UF present: full substitution degrades instant SATs to
    // Unknown through model recovery on this lane (measured on
    // QF_UFNIA CLEARSY/Zohar shapes), so only VAR := CONSTANT folds.
    let mut exec = load(
        "(set-logic QF_UFNIA)
         (declare-fun f (Int) Int)
         (declare-const x Int)
         (declare-const c0 Int)
         (declare-const y0 Int)
         (assert (= c0 5))
         (assert (= y0 (+ x c0)))
         (assert (= (f y0) 9))",
    );
    let c0 = var_id(&mut exec, "c0", Sort::Int);
    let y0 = var_id(&mut exec, "y0", Sort::Int);
    let (preprocessed, _provenance) = exec.preprocess_ufnia_assertions_with_proof_provenance();
    assert!(
        !mentions(&exec.ctx.terms, &preprocessed, c0),
        "VAR := CONSTANT must fold under UF"
    );
    assert!(
        mentions(&exec.ctx.terms, &preprocessed, y0),
        "compound-RHS definitions stay named under UF"
    );
    assert!(exec.recorded_var_substitutions.contains_key(&c0));
    assert!(!exec.recorded_var_substitutions.contains_key(&y0));
}

#[test]
fn ufnia_eliminated_values_are_recovered_in_the_model() {
    let output = run_script(&format!(
        "{SSA}\n(assert (= x 4))\n(check-sat)\n(get-value (x y0 y1 b))\n"
    ));
    let joined = output.join(" ");
    assert!(joined.contains("sat"), "expected sat, got: {joined}");
    assert!(
        joined.contains("(y0 5)") && joined.contains("(y1 10)"),
        "eliminated SSA values must be reconstructed (y0=5, y1=10), got: {joined}"
    );
}

#[test]
fn ufnia_elimination_keeps_unsat_through_substituted_terms() {
    let output = run_script(
        "(set-logic QF_AUFNIA)
         (declare-fun f (Int) Int)
         (declare-const a0 (Array Int Int))
         (declare-const x Int)
         (declare-const y0 Int)
         (declare-const y1 Int)
         (assert (= y0 (+ x (select a0 0))))
         (assert (= y1 (+ y0 (f x))))
         (assert (= (* y1 y1) 2))
         (check-sat)",
    );
    let joined = output.join(" ");
    assert!(
        joined.contains("unsat"),
        "no integer squares to 2; expected unsat, got: {joined}"
    );
}
