// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use ay_core::Sort;

/// The authored `forall` of `(assert QUANTIFIER)`.
fn authored_forall(quantifier: &str) -> FrontendTerm {
    let commands = ay_frontend::parse(&format!("(assert {quantifier})")).expect("fixture parses");
    let [ay_frontend::Command::Assert(term)] = commands.as_slice() else {
        panic!("fixture must be one assertion")
    };
    term.clone()
}

/// A composite authored body whose instance the store folded to the SHARED
/// `false` must not key its spelling on `false`: every `false` in the document
/// would print as `(and false false)` (the expansion certificate's
/// `(forall ((q Bool)) (and q q))`), and the `false` axiom with it.
#[test]
fn a_composite_body_never_spells_a_constant_instance() {
    let terms = TermStore::new();
    let false_term = terms.false_term();
    for quantifier in [
        "(forall ((q Bool)) (and q q))",
        "(forall ((q Bool)) (= q true))",
        "(forall ((q Bool)) (not (not q)))",
        "(forall ((q Bool)) (! (and q q) :named a))",
    ] {
        let parsed = authored_forall(quantifier);
        assert!(
            forall_instance_would_hijack_atom(&terms, false_term, &parsed),
            "{quantifier}: its instance at `false` would re-spell the shared constant"
        );
    }
}

/// The same for a VARIABLE fold result: `(and p x)` at `x := true` is `p`.
#[test]
fn a_composite_body_never_spells_a_variable_instance() {
    let mut terms = TermStore::new();
    let p = terms.mk_var("p", Sort::Bool);
    let parsed = authored_forall("(forall ((x Bool)) (and p x))");
    assert!(forall_instance_would_hijack_atom(&terms, p, &parsed));
}

/// What the guard leaves alone: a bare binder body (its instance at `false`
/// IS `false`, an identity spelling), a composite instance (a genuine
/// re-spelling the pass exists for), and anything that is not a `forall`.
#[test]
fn identity_and_composite_instances_stay_spellable() {
    let mut terms = TermStore::new();
    let false_term = terms.false_term();
    let bare = authored_forall("(forall ((q Bool)) q)");
    assert!(!forall_instance_would_hijack_atom(
        &terms, false_term, &bare
    ));

    let p = terms.mk_var("p", Sort::Bool);
    let r = terms.mk_var("r", Sort::Bool);
    let composite = terms.mk_and(vec![p, r]);
    let body = authored_forall("(forall ((x Bool)) (and p x))");
    assert!(!forall_instance_would_hijack_atom(&terms, composite, &body));

    let exists = authored_forall("(exists ((q Bool)) (and q q))");
    assert!(!forall_instance_would_hijack_atom(
        &terms, false_term, &exists
    ));
}
