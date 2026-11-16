// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn registered_range_functions_do_not_supply_arithmetic_facts() {
    let mut terms = TermStore::new();
    let word = Sort::bitvec(8);
    let point = terms.mk_var("point", word.clone());
    let base = terms.mk_var("base", word.clone());
    let bound = terms.mk_bitvec(BigInt::from(4), 8);
    let delta = terms.mk_app(Symbol::named("bvsub"), [point, base], word);
    let predicate = terms.mk_app(Symbol::named("bvult"), [delta, bound], Sort::Bool);
    let literal = terms.mk_not_raw(predicate);
    assert!(negative_range(&terms, literal, 0).is_some());
    for identity in ["bvult", "bvsub"] {
        let mut declared = terms.clone();
        declared.register_declared_function(identity);
        assert!(
            negative_range(&declared, literal, 0).is_none(),
            "{identity}"
        );
        assert!(negative_range(&declared.clone(), literal, 0).is_none());
    }
}
