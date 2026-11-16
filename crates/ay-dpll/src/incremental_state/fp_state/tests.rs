// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_core::{Sort, Symbol, TermStore};

#[path = "tests/admission.rs"]
mod admission;
#[path = "tests/namespace.rs"]
mod namespace;
#[path = "tests/ownership.rs"]
mod ownership;

fn empty_encoding(state: &IncrementalFpState) {
    assert!(state.persistent_sat.is_none());
    assert_eq!(state.tseitin_state.next_var, 1);
    assert!(state.tseitin_state.term_to_var.is_empty());
    assert!(state.fp_cache.term_to_fp.is_empty());
    assert!(state.fp_cache.bool_input_lits.is_empty());
    assert_eq!(state.fp_cache.next_var, 1);
    assert_eq!(state.next_fp_var, 1);
    assert!(state.fp_var_offset.is_none());
    assert!(state.encoded_assertions.is_empty());
    assert!(state.assertion_activation_scope.is_empty());
    assert!(state.linked_predicate_vars.is_empty());
    assert!(state.linked_bool_inputs.is_empty());
    assert!(state.reuse_probe.is_none());
    assert_eq!(state.fp_relevance_cache, [] as [Option<bool>; 0]);
    assert_eq!(state.solves, 0);
}

fn fp_root(terms: &mut TermStore, name: &str) -> TermId {
    let fp = terms.mk_var(name, Sort::FloatingPoint(5, 11));
    terms.mk_app(Symbol::named("fp.isZero"), [fp], Sort::Bool)
}

fn observe(
    state: &mut IncrementalFpState,
    terms: &TermStore,
    roots: &[TermId],
) -> FpIncrementalAdmission {
    state
        .observe_live_assertion_reuse_with_control(terms, roots, &mut || Ok(()))
        .unwrap()
}
