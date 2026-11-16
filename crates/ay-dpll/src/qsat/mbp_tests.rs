// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::{parse, Lit};
use ay_core::term::Symbol;
use ay_core::{Sort, TermStore};
use num_bigint::BigInt;

fn parsed_mod_equality(divisor: i64, residue: i64) -> Option<Lit> {
    let mut terms = TermStore::new();
    let variable = terms.mk_var("x", Sort::Int);
    let divisor = terms.mk_int(BigInt::from(divisor));
    let modulo = terms.mk_app(Symbol::named("mod"), vec![variable, divisor], Sort::Int);
    let residue = terms.mk_int(BigInt::from(residue));
    let equality = terms.mk_app(Symbol::named("="), vec![modulo, residue], Sort::Bool);
    parse(&terms, equality, true)
}

#[test]
fn mod_parser_requires_a_nonzero_divisor_and_canonical_residue() {
    for residue in [0, 4] {
        match parsed_mod_equality(5, residue) {
            Some(Lit::Div(divisor, _, true)) => assert_eq!(divisor, BigInt::from(5)),
            parsed => panic!("expected positive divisibility literal, got {parsed:?}"),
        }
    }

    for (divisor, residue) in [(0, 0), (5, -1), (5, 5)] {
        assert!(parsed_mod_equality(divisor, residue).is_none());
    }
}
