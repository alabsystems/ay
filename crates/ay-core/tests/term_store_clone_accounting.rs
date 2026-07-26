// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Process-isolated checks for the global `TermStore` allocation ledger.
//!
//! This is a dedicated integration-test binary because every `TermStore` in a
//! process contributes to the same atomic counter. Exact equality assertions
//! would race unrelated unit tests inside the library test process.

use ay_core::{Sort, TermStore};

#[test]
fn cloned_stores_balance_global_term_memory_in_any_drop_order() {
    TermStore::reset_global_term_bytes();

    let mut source = TermStore::new();
    let _ = source.mk_var("source-x", Sort::bitvec(257));
    let _ = source.mk_string("clone-accounting-payload".repeat(32));
    let source_bytes = source.instance_term_bytes();
    assert_eq!(TermStore::global_term_bytes(), source_bytes);

    let mut first = source.clone();
    assert_eq!(first.instance_term_bytes(), source_bytes);
    assert_eq!(
        TermStore::global_term_bytes(),
        source_bytes * 2,
        "cloning must credit the second store's tracked allocation"
    );

    let before_first_growth = first.instance_term_bytes();
    let _ = first.mk_var("clone-only", Sort::Int);
    let first_growth = first.instance_term_bytes() - before_first_growth;
    assert!(first_growth > 0);
    assert_eq!(
        TermStore::global_term_bytes(),
        source_bytes * 2 + first_growth
    );

    let second = first.clone();
    let second_bytes = second.instance_term_bytes();
    assert_eq!(
        TermStore::global_term_bytes(),
        source_bytes * 2 + first_growth + second_bytes
    );

    drop(first);
    assert_eq!(
        TermStore::global_term_bytes(),
        source_bytes + second_bytes,
        "dropping the middle clone must preserve both live stores"
    );
    drop(source);
    assert_eq!(
        TermStore::global_term_bytes(),
        second_bytes,
        "dropping the source first must leave the nested clone fully charged"
    );
    drop(second);
    assert_eq!(TermStore::global_term_bytes(), 0);
}
