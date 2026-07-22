// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for the set_terms() / unset_terms() bracket contract (#6612).
//!
//! The raw-pointer architecture (#6590) requires:
//! 1. set_terms() installs a live TermStore pointer for one operation batch
//! 2. solver operations may call terms() only while that bracket is active
//! 3. unset_terms() clears the pointer; future terms() calls must panic

use super::*;
use ay_core::term::TermStore;

/// After unset_terms(), calling terms() must panic with the null-pointer message.
#[test]
#[should_panic(expected = "BUG: LraSolver::terms() called without set_terms()")]
fn test_terms_panics_after_unset_6612() {
    let terms = TermStore::new();
    let mut solver = LraSolver::new(&terms);

    // Bracket is active after construction — terms() should work
    let _ = solver.terms();

    // Close the bracket
    solver.unset_terms();

    // This must panic: no active bracket
    let _ = solver.terms();
}

/// set_terms() rebinds the internal pointer to the new TermStore.
#[test]
fn test_set_terms_rebinds_pointer_6612() {
    let terms_a = TermStore::new();
    let terms_b = TermStore::new();

    let mut solver = LraSolver::new(&terms_a);

    // Initially points at terms_a
    assert_eq!(
        solver.terms_ptr,
        std::ptr::from_ref(&terms_a),
        "initial pointer must point to terms_a"
    );

    // Close and rebind to terms_b
    solver.unset_terms();
    assert!(
        solver.terms_ptr.is_null(),
        "pointer must be null after unset"
    );

    solver.set_terms(&terms_b);
    assert_eq!(
        solver.terms_ptr,
        std::ptr::from_ref(&terms_b),
        "pointer must point to terms_b after set_terms"
    );

    // terms() should now read from terms_b without panic
    let _ = solver.terms();
}
