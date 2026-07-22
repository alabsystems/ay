// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

// ========================================================================
// Unsafe Bracket Contract (#6612)
// ========================================================================

/// The set_terms() / unset_terms() / terms() pointer state machine:
/// - After new(): pointer is non-null (points to constructor arg)
/// - After unset_terms(): pointer is null
/// - After set_terms(): pointer equals the new TermStore address
///
/// This proof verifies the internal state machine that the unsafe
/// dereference in terms() relies on.
///
/// Uses `TermStore::new_kani_minimal()` and `LraSolver::new_kani_minimal()`
/// to avoid the `mk_bool()` → `hash_cons.insert()` and `lra_debug_flags()`
/// paths that trigger deep BTree/OnceLock symbolic exploration in CBMC (#6612).
#[kani::proof]
#[kani::unwind(2)]
fn proof_set_terms_unset_terms_toggle_pointer_6612() {
    let terms_a = TermStore::new_kani_minimal();
    let terms_b = TermStore::new_kani_minimal();

    let mut solver = LraSolver::new_kani_minimal(std::ptr::from_ref(&terms_a));

    // After construction, pointer must be non-null and equal to terms_a
    assert!(!solver.terms_ptr.is_null());
    assert!(solver.terms_ptr == std::ptr::from_ref(&terms_a));

    // After unset, pointer must be null
    solver.unset_terms();
    assert!(solver.terms_ptr.is_null());

    // After set_terms with terms_b, pointer must equal terms_b
    solver.set_terms(&terms_b);
    assert!(!solver.terms_ptr.is_null());
    assert!(solver.terms_ptr == std::ptr::from_ref(&terms_b));
}
