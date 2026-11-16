// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! LIA preprocessing must NOT solve linear equalities for a variable
//! (DR-AY-DPLL-LIA-LINEAR-SOLVE-REJECTED-20261116): LIA artifacts feed
//! the #4751 proof replay, which licenses a substitution only from a
//! source spelled exactly `(= var value)`. A solved row's source is
//! the unsolved row, which withholds the whole replay run and leaves
//! premiseless `trust` steps — measured as three failing
//! `eq_diffvar` proof tests when the mode was enabled here, even
//! gated on `!is_producing_proofs()` (artifact consumers derive
//! proofs after preprocessing). The AUFLIA/UFNIA lanes, whose changed
//! roots drop provenance instead, keep the mode.

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

const SUM_ROW: &str = "(set-logic QF_LIA)
    {OPT}
    (declare-const x Int)
    (declare-const y Int)
    (declare-const z Int)
    (assert (= (+ x y) 10))
    (assert (= z (+ x 1)))
    (assert (> z 0))";

#[test]
fn lia_preprocessing_does_not_solve_sum_rows() {
    for opt in ["", "(set-option :produce-proofs true)"] {
        let mut exec = load(&SUM_ROW.replace("{OPT}", opt));
        let x = var_id(&mut exec, "x", Sort::Int);
        let artifacts = exec.preprocess_lia_artifacts();
        assert!(
            !artifacts.var_subst.substitutions().contains_key(&x),
            "x must not be solved from the (= (+ x y) 10) row on the LIA lane"
        );
        assert!(
            mentions(&exec.ctx.terms, &artifacts.assertions, x),
            "x stays named in preprocessed LIA assertions"
        );
    }
}
