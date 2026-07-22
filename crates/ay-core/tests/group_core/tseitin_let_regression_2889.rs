// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ay_core::{Sort, TermStore, Tseitin};

#[test]
fn encode_and_assert_let_term_uses_opaque_literal_instead_of_panicking() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Bool);
    let body = terms.mk_not(x);
    let let_term = terms.mk_let(vec![("y".to_string(), x)], body);

    let mut tseitin = Tseitin::new(&terms);
    let root_lit = tseitin.encode_and_assert(let_term);
    let clauses = tseitin.take_new_clauses();

    assert_ne!(root_lit, 0, "encoding should produce a valid CNF literal");
    assert_eq!(
        clauses.len(),
        1,
        "let term should be asserted as a unit literal"
    );
    let expected = [root_lit];
    assert_eq!(clauses[0].literals(), expected.as_slice());
    assert!(
        tseitin.get_var_for_term(let_term).is_some(),
        "let term should be mapped to an opaque Tseitin variable"
    );
}
