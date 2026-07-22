// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

/// REQUIRES: lit is a valid CnfLit (non-zero by DIMACS convention)
/// ENSURES: negate(negate(lit)) == lit (double negation identity)
#[kani::proof]
fn proof_literal_double_negation() {
    let lit: CnfLit = kani::any();
    kani::assume(lit != 0); // DIMACS literals are non-zero
    kani::assume(lit != i32::MIN); // Avoid overflow on negation

    let negated = -lit;
    let double_negated = -negated;

    assert_eq!(
        double_negated, lit,
        "Double negation must return original literal"
    );
}

/// REQUIRES: lit > 0 (positive literal)
/// ENSURES: -lit < 0 (negation produces negative literal)
#[kani::proof]
fn proof_positive_literal_negation_is_negative() {
    let lit: CnfLit = kani::any();
    kani::assume(lit > 0);

    let negated = -lit;

    assert!(
        negated < 0,
        "Negating positive literal must produce negative"
    );
}

/// REQUIRES: literals is a non-empty vec
/// ENSURES: CnfClause::new(literals).is_empty() == false
#[kani::proof]
fn proof_non_empty_clause_not_empty() {
    let lit: CnfLit = kani::any();
    kani::assume(lit != 0);

    let clause = CnfClause::unit(lit);

    assert!(!clause.is_empty(), "Unit clause must not be empty");
    assert_eq!(
        clause.literals().len(),
        1,
        "Unit clause must have exactly one literal"
    );
}
