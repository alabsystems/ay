// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use ay_core::Sort;
use num_bigint::BigInt;

impl Preprocessor {
    fn new_with_subst() -> (Self, Arc<Mutex<VariableSubstitution>>) {
        let (preprocessor, var_subst, _) = Self::new_with_subst_and_propagation();
        (preprocessor, var_subst)
    }
}

#[test]
fn test_preprocessor_with_no_assertions() {
    let mut terms = TermStore::new();
    let mut assertions = Vec::new();
    let mut preprocessor = Preprocessor::new();

    let iterations = preprocessor.preprocess(&mut terms, &mut assertions);
    assert_eq!(iterations, 1);
}

#[test]
fn test_preprocessor_normalize_concat_eq_produces_extract_equalities() {
    let mut terms = TermStore::new();

    // (= x (concat a b)) where |a|=4, |b|=4, |x|=8
    let a = terms.mk_var("a", Sort::bitvec(4));
    let b = terms.mk_var("b", Sort::bitvec(4));
    let x = terms.mk_var("x", Sort::bitvec(8));
    let concat_ab = terms.mk_bvconcat(vec![a, b]);
    let eq = terms.mk_eq(x, concat_ab);

    let mut assertions = vec![eq];
    let (mut preprocessor, var_subst) = Preprocessor::new_with_subst();
    preprocessor.preprocess(&mut terms, &mut assertions);

    // After #2830 cycle detection, variable substitution is stronger:
    // concat normalization produces a = extract(7,4,x) and b = extract(3,0,x),
    // then variable substitution eliminates a and b, recording them in the
    // substitution map. The assertions become tautologies and are removed.
    let expected_a_extract = terms.mk_bvextract(7, 4, x);
    let expected_b_extract = terms.mk_bvextract(3, 0, x);

    let substitutions = var_subst.lock().unwrap();
    assert_eq!(
        substitutions.substitutions().get(&a).copied(),
        Some(expected_a_extract),
        "a should be substituted with extract(7,4,x)"
    );
    assert_eq!(
        substitutions.substitutions().get(&b).copied(),
        Some(expected_b_extract),
        "b should be substituted with extract(3,0,x)"
    );
}

#[test]
fn test_preprocessor_concat_constant_enables_variable_substitution() {
    let mut terms = TermStore::new();

    // (= (concat a b) #xABCD) where |a|=8, |b|=8
    let a = terms.mk_var("a", Sort::bitvec(8));
    let b = terms.mk_var("b", Sort::bitvec(8));
    let const_abcd = terms.mk_bitvec(BigInt::from(0xABCD_u32), 16);
    let concat_ab = terms.mk_bvconcat(vec![a, b]);
    let eq = terms.mk_eq(concat_ab, const_abcd);

    let mut assertions = vec![eq];
    let (mut preprocessor, var_subst) = Preprocessor::new_with_subst();
    preprocessor.preprocess(&mut terms, &mut assertions);

    let substitutions = var_subst.lock().unwrap();
    let const_ab = terms.mk_bitvec(BigInt::from(0xAB_u32), 8);
    let const_cd = terms.mk_bitvec(BigInt::from(0xCD_u32), 8);

    assert_eq!(
        substitutions.substitutions().get(&a).copied(),
        Some(const_ab)
    );
    assert_eq!(
        substitutions.substitutions().get(&b).copied(),
        Some(const_cd)
    );
}
