// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! #model-eq-encoded-atom: a re-request of an encoded model equality is not
//! new work for the round budget. Each test also states the counterfactual:
//! 4e96ceb50's test, which reads `find_eq(lhs, rhs)`, calls the re-request new.

use super::{model_equality_atom, model_equality_request_is_new};
use crate::incremental_proof_cache::IncrementalNegationCache;
use crate::pipeline_fns::encode_model_equality;
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::Symbol;
use ay_core::{Sort, TermId, TermStore};
use num_bigint::BigInt;

/// Encode the model equality `lhs = rhs` the way the split loops do and
/// return the resulting term -> SAT var map. `arith_triangle` is the
/// encoder's triangle switch (off on the pure-ArrayEUF path).
fn encode(
    terms: &mut TermStore,
    lhs: TermId,
    rhs: TermId,
    arith_triangle: bool,
) -> HashMap<TermId, u32> {
    let mut solver = ay_sat::Solver::new(0);
    let mut term_to_var = HashMap::default();
    let mut var_to_term = HashMap::default();
    let mut next_var = 0u32;
    let mut negations = IncrementalNegationCache::seed(terms, [], false);
    let mut triangle_atoms = HashSet::default();
    encode_model_equality(
        terms,
        &mut solver,
        &mut term_to_var,
        &mut var_to_term,
        &mut next_var,
        &mut negations,
        lhs,
        rhs,
        false,
        &[],
        Some(&mut triangle_atoms),
        None,
        arith_triangle,
    );
    term_to_var
}

/// [`model_equality_request_is_new`] against the term -> SAT var map `mapped`.
fn is_new(terms: &mut TermStore, lhs: TermId, rhs: TermId, mapped: &HashMap<TermId, u32>) -> bool {
    model_equality_request_is_new(terms, lhs, rhs, |atom| mapped.contains_key(&atom))
}

/// The 4e96ceb50 freshness test: new unless `find_eq` names a mapped term.
fn find_eq_reads_new(
    terms: &TermStore,
    term_to_var: &HashMap<TermId, u32>,
    lhs: TermId,
    rhs: TermId,
) -> bool {
    !terms
        .find_eq(lhs, rhs)
        .is_some_and(|atom| term_to_var.contains_key(&atom))
}

/// `v07_real_elements_never_unsat`'s re-request: two distinct constants,
/// whose equality the encoder folds to `false`. As there, the store also
/// holds the raw `(= 3 0)`, which `find_eq` returns and nothing maps.
#[test]
fn a_re_request_of_a_folded_equality_is_not_new() {
    let mut terms = TermStore::new();
    let three = terms.mk_int(BigInt::from(3));
    let zero = terms.mk_int(BigInt::from(0));
    let raw = terms.mk_app(Symbol::named("="), vec![three, zero], Sort::Bool);
    assert_eq!(terms.find_eq(three, zero), Some(raw));
    assert!(is_new(&mut terms, three, zero, &HashMap::default()));

    let term_to_var = encode(&mut terms, three, zero, true);
    let false_atom = terms.mk_bool(false);
    assert_eq!(model_equality_atom(&mut terms, three, zero), false_atom);
    assert!(!is_new(&mut terms, three, zero, &term_to_var));
    assert!(
        find_eq_reads_new(&terms, &term_to_var, three, zero),
        "counterfactual: the find_eq test reads the re-request as new"
    );
}

/// An Int side against a Real side is encoded through `to_real`, which a
/// raw `find_eq` lookup of the pair does not name. (Encoded without the
/// arithmetic triangle, whose comparisons take same-sort sides.)
#[test]
fn a_re_request_of_a_coerced_equality_is_not_new() {
    let mut terms = TermStore::new();
    let i = terms.mk_var("i", Sort::Int);
    let r = terms.mk_var("r", Sort::Real);
    let term_to_var = encode(&mut terms, i, r, false);
    assert!(!is_new(&mut terms, i, r, &term_to_var));
    assert!(
        find_eq_reads_new(&terms, &term_to_var, i, r),
        "counterfactual: the find_eq test reads the re-request as new"
    );
}

/// Same-sort, non-constant sides: new until encoded, then not; the
/// `find_eq` test agrees here (the common case is unchanged), and a
/// withheld atom is new again.
#[test]
fn a_plain_request_is_new_until_encoded() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    assert!(is_new(&mut terms, x, y, &HashMap::default()));
    let term_to_var = encode(&mut terms, x, y, true);
    assert!(!is_new(&mut terms, x, y, &term_to_var));
    assert!(!find_eq_reads_new(&terms, &term_to_var, x, y));
    let withheld = |_: TermId| false;
    assert!(model_equality_request_is_new(&mut terms, x, y, withheld));
}
