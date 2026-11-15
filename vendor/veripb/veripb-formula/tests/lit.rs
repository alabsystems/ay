use veripb_formula::prelude::*;

#[test]
fn create_lit() {
    let var = 0;
    let lit = Lit::from_var(var, false);

    assert_eq!(lit.get_var(), 0);
    assert!(!lit.is_negated());
}

#[test]
fn create_lit_negated() {
    let var = 0;
    let lit_not = Lit::from_var(var, true);

    assert_eq!(lit_not.get_var(), 0);
    assert!(lit_not.is_negated());
}

#[test]
fn hundred_thousand_lits() {
    for var in 0..100_000 {
        let lit = Lit::from_var(var, false);

        assert_eq!(lit.get_var(), var);
        assert!(!lit.is_negated());
    }
}

#[test]
fn negation() {
    let var = 0;
    let mut lit = Lit::from_var(var, false);

    assert_eq!(lit.get_var(), 0);
    assert!(!lit.is_negated());

    lit.negate();
    assert_eq!(lit.get_var(), 0);
    assert!(lit.is_negated());

    lit.negate();
    assert_eq!(lit.get_var(), 0);
    assert!(!lit.is_negated());
}

#[test]
fn one_var_multiple_lit() {
    let var = 0;
    let lit = Lit::from_var(var, false);
    let lit_not = Lit::from_var(var, true);

    assert_eq!(lit.get_var(), 0);
    assert!(!lit.is_negated());
    assert_eq!(lit_not.get_var(), 0);
    assert!(lit_not.is_negated());
}

#[test]
fn create_lit_from_var_set() {
    let mut var_name_manager = VarNameManager::default();
    let lit = Lit::from_var(var_name_manager.add_by_name("x1"), false);

    assert_eq!(lit.get_var(), 0);
    assert!(!lit.is_negated());
}

// This test assumes properties about the internal structure of the literal data type.
#[test]
fn check_internal_data_var_idx() {
    let lit = Lit::from_var(42, false);

    assert_eq!(lit.get_lit_data() / 2, 42);
}

// This test assumes properties about the internal structure of the literal data type.
#[test]
fn check_internal_data_negated() {
    let lit = Lit::from_var(42, true);

    assert_eq!(lit.get_lit_data() % 2, 1);
}

// This test assumes properties about the internal structure of the literal data type.
#[test]
fn check_internal_data_negate_function() {
    let mut lit = Lit::from_var(42, false);

    assert_eq!(lit.get_lit_data() % 2, 0);

    lit.negate();

    assert_eq!(lit.get_lit_data() % 2, 1);
}

// --------------------------------------------------------------------------
// Sentinel collision: `Lit::new_undef()` is a legal packing of a variable
// index, so the representable range has to be stated and checked.
// --------------------------------------------------------------------------

#[test]
fn max_var_idx_is_the_last_index_that_does_not_collide_with_a_sentinel() {
    // `MAX_VAR_IDX` itself packs cleanly in both polarities...
    let positive = Lit::from_var(Lit::MAX_VAR_IDX, false);
    let negative = Lit::from_var(Lit::MAX_VAR_IDX, true);
    assert_eq!(positive.get_var(), Lit::MAX_VAR_IDX);
    assert_eq!(negative.get_var(), Lit::MAX_VAR_IDX);
    assert!(!positive.is_undef());
    assert!(!negative.is_undef());

    // ...and the next index up is exactly the reserved `new_undef()` value
    // (negated) and the `SubstitutionValue::FALSE` bit pattern (positive).
    assert_eq!(Lit::MAX_VAR_IDX + 1, usize::MAX >> 1);
    assert_eq!(
        Lit::from_raw_data(usize::MAX).get_var(),
        Lit::MAX_VAR_IDX + 1
    );
    assert!(Lit::from_raw_data(usize::MAX).is_undef());
}

#[test]
fn try_from_var_rejects_indices_outside_the_representable_range() {
    assert!(Lit::try_from_var(Lit::MAX_VAR_IDX, true).is_some());
    assert!(Lit::try_from_var(Lit::MAX_VAR_IDX, false).is_some());
    assert!(Lit::try_from_var(Lit::MAX_VAR_IDX + 1, true).is_none());
    assert!(Lit::try_from_var(usize::MAX, false).is_none());
}
