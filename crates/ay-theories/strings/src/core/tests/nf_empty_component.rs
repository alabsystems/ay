// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! process_simple_neq against the empty-string EQC's own normal form.

use super::*;
use crate::normal_form::ExplainEntry;
use ay_core::term::Symbol;
use ay_core::Sort;

/// The empty-string EQC's singleton NF consumes nothing.
///
/// Case A in `nf_equality` compares each concat NF of a constant EQC against
/// that EQC's own NF, and for the EQC of `""` that NF is the singleton
/// `[rep]`. With `x ++ w = ""` and `x != ""`, NF1 = `[x, w]` against it used
/// to take the variable-vs-constant branch and request a ConstSplit of `x`
/// against the empty constant, which has no first character (the
/// `ConstSplit char_offset 0 >= constant y length 0` debug assertion). The
/// empty component must be skipped instead: NF2 is then exhausted, and
/// N_ENDPOINT_EQ infers every remaining component of NF1 empty.
#[test]
fn process_simple_neq_skips_the_empty_string_singleton() {
    let mut terms = TermStore::new();
    let empty = terms.mk_string(String::new());
    let x = terms.mk_var("x", Sort::String);
    let w = terms.mk_var("w", Sort::String);
    let cat = terms.mk_app(Symbol::named("str.++"), vec![x, w], Sort::String);
    let cat_is_empty = terms.mk_eq(cat, empty);
    let x_is_empty = terms.mk_eq(x, empty);

    let mut state = SolverState::new();
    state.set_empty_string_id(&terms, empty);
    state.register_term(&terms, cat);
    state.assert_literal(&terms, cat_is_empty, true);
    state.assert_literal(&terms, x_is_empty, false);
    assert!(
        state.is_known_nonempty(&terms, x),
        "fixture: x != \"\" must make x known non-empty"
    );

    let rep = state.find(empty);
    let nf1 = NormalForm {
        base: vec![x, w],
        rep: Some(rep),
        source: Some(cat),
        deps: vec![ExplainEntry {
            lhs: cat,
            rhs: empty,
        }],
    };
    let nf2 = NormalForm::singleton(rep);

    let mut infer = InferenceManager::new();
    let result = CoreSolver::process_simple_neq(
        &terms,
        &state,
        &nf1,
        &nf2,
        &mut infer,
        &mut SkolemCache::new(),
    );

    assert!(
        !matches!(result, NfCheckResult::NeedLemma(_)),
        "[x, w] vs the empty EQC's [rep] must not request a split lemma"
    );
    let inferred: Vec<(TermId, TermId)> = infer
        .drain_internal_equalities()
        .iter()
        .map(|eq| (state.find(eq.lhs), state.find(eq.rhs)))
        .collect();
    for component in [x, w] {
        assert!(
            inferred.contains(&(state.find(component), rep)),
            "{component:?} must be inferred empty (N_ENDPOINT_EQ); got {inferred:?}"
        );
    }
}
