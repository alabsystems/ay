// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates

use super::super::*;

#[test]
fn build_pair_explanation_for_lemma_uses_source_equality() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let y = terms.mk_var("y", Sort::String);
    let z = terms.mk_var("z", Sort::String);
    let eq = terms.mk_eq(x, y);
    let xz = terms.mk_eq(x, z);
    let zy = terms.mk_eq(z, y);

    let mut state = SolverState::new();
    state.assert_literal(&terms, xz, true);
    state.assert_literal(&terms, zy, true);
    let rep = state.find(x);

    let nf1 = NormalForm {
        base: vec![rep],
        rep: Some(rep),
        source: Some(x),
        deps: Vec::new(),
    };
    let nf2 = NormalForm {
        base: vec![rep],
        rep: Some(rep),
        source: Some(y),
        deps: Vec::new(),
    };

    let explanation = CoreSolver::build_pair_explanation_for_lemma(&terms, &nf1, &nf2, &state)
        .expect("source equality should justify dependency-free NF pair");
    assert!(
        !explanation.is_empty(),
        "source-equality fallback should contribute a guard literal"
    );
    assert!(
        !explanation.contains(&TheoryLit::new(xz, true))
            && !explanation.contains(&TheoryLit::new(zy, true)),
        "source-equality fallback should not replay the proof-forest chain"
    );
    assert!(
        explanation.contains(&TheoryLit {
            term: eq,
            value: true,
        }),
        "source-equality fallback should use the direct x = y term"
    );
}

#[test]
fn build_explanation_does_not_replay_eqc_representative_merges() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let y = terms.mk_var("y", Sort::String);
    let z = terms.mk_var("z", Sort::String);
    let xz = terms.mk_eq(x, z);
    let zy = terms.mk_eq(z, y);

    let mut state = SolverState::new();
    state.assert_literal(&terms, xz, true);
    state.assert_literal(&terms, zy, true);

    let component = [x, y, z]
        .into_iter()
        .find(|term| state.find(*term) != *term)
        .expect("merged EQC should contain a non-representative member");
    let nf = NormalForm {
        base: vec![component],
        rep: Some(state.find(component)),
        source: Some(component),
        deps: Vec::new(),
    };

    let explanation = CoreSolver::build_explanation(&nf, &state);
    assert!(
        explanation.is_empty(),
        "non-lemma explanation should stay empty for dependency-free EQC membership"
    );
}

#[test]
fn build_explanation_strict_does_not_replay_eqc_representative_merges() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let y = terms.mk_var("y", Sort::String);
    let z = terms.mk_var("z", Sort::String);
    let xz = terms.mk_eq(x, z);
    let zy = terms.mk_eq(z, y);

    let mut state = SolverState::new();
    state.assert_literal(&terms, xz, true);
    state.assert_literal(&terms, zy, true);

    let component = [x, y, z]
        .into_iter()
        .find(|term| state.find(*term) != *term)
        .expect("merged EQC should contain a non-representative member");
    let nf = NormalForm {
        base: vec![component],
        rep: Some(state.find(component)),
        source: Some(component),
        deps: Vec::new(),
    };

    let explanation =
        CoreSolver::build_explanation_strict(&terms, &nf, &state).expect("no deps to reject");
    assert!(
        explanation.is_empty(),
        "strict non-lemma explanation should not import representative proof chains"
    );
}

#[test]
fn build_nf_vs_constant_explanation_rejects_eqc_only_membership() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let y = terms.mk_var("y", Sort::String);
    let z = terms.mk_var("z", Sort::String);
    let xz = terms.mk_eq(x, z);
    let zy = terms.mk_eq(z, y);

    let mut state = SolverState::new();
    state.assert_literal(&terms, xz, true);
    state.assert_literal(&terms, zy, true);

    let component = [x, y, z]
        .into_iter()
        .find(|term| state.find(*term) != *term)
        .expect("merged EQC should contain a non-representative member");
    let nf = NormalForm {
        base: vec![component],
        rep: Some(state.find(component)),
        source: Some(component),
        deps: Vec::new(),
    };

    let explanation = CoreSolver::build_nf_vs_constant_explanation(&terms, &nf, &state);
    assert!(
        explanation.is_none(),
        "NF-vs-constant conflicts should not become guarded by EQC-only membership"
    );
}
