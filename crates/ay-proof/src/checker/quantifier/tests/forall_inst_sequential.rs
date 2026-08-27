// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#[test]
fn forall_inst_rejects_a_sequential_reading_of_a_binder_named_argument() {
    // `forall ((a S) (b S)) (p a b)` with args `[b, c]`. The ONLY valid
    // conclusion is the simultaneous `(p b c)`; the sequential misreading
    // `(p c c)` — substitute `a := b`, then `b := c` inside the result — is not
    // a consequence and must stay rejected now that `b` is an admissible
    // argument spelling.
    let mut terms = TermStore::new();
    let sort = Sort::Uninterpreted("fi_simul_S".to_string());
    let a = terms.mk_var("fi_simul_a", sort.clone());
    let b = terms.mk_var("fi_simul_b", sort.clone());
    let c = terms.mk_var("fi_simul_c", sort.clone());
    let body = terms.mk_app(Symbol::named("fi_simul_p"), [a, b], Sort::Bool);
    let quantified = terms.mk_forall(
        vec![
            ("fi_simul_a".to_string(), sort.clone()),
            ("fi_simul_b".to_string(), sort),
        ],
        body,
    );
    let not_quantified = terms.mk_not_raw(quantified);

    let simultaneous = terms.mk_app(Symbol::named("fi_simul_p"), [b, c], Sort::Bool);
    let valid = terms.mk_app(
        Symbol::named("or"),
        [not_quantified, simultaneous],
        Sort::Bool,
    );
    validate_forall_inst(&terms, ProofId(0), &[valid], 0, &[b, c])
        .expect("the simultaneous instance is a valid consequence");

    let sequential = terms.mk_app(Symbol::named("fi_simul_p"), [c, c], Sort::Bool);
    let forged = terms.mk_app(
        Symbol::named("or"),
        [not_quantified, sequential],
        Sort::Bool,
    );
    assert!(
        validate_forall_inst(&terms, ProofId(0), &[forged], 0, &[b, c]).is_err(),
        "a sequential re-substitution is not the exact simultaneous instance"
    );
}
