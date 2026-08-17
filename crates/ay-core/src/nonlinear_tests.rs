use super::*;
use crate::Sort;

#[test]
fn test_product_sign_basic() {
    assert_eq!(product_sign(&[1, 1]), 1);
    assert_eq!(product_sign(&[1, -1]), -1);
    assert_eq!(product_sign(&[-1, -1]), 1);
    assert_eq!(product_sign(&[1, 0]), 0);
    assert_eq!(product_sign(&[0, -1]), 0);
}

#[test]
fn test_sign_contradicts() {
    assert!(sign_contradicts(SignConstraint::Positive, 0));
    assert!(sign_contradicts(SignConstraint::Positive, -1));
    assert!(!sign_contradicts(SignConstraint::Positive, 1));
    assert!(sign_contradicts(SignConstraint::Negative, 0));
    assert!(sign_contradicts(SignConstraint::Negative, 1));
    assert!(!sign_contradicts(SignConstraint::Negative, -1));
    assert!(sign_contradicts(SignConstraint::Zero, 1));
    assert!(sign_contradicts(SignConstraint::Zero, -1));
    assert!(!sign_contradicts(SignConstraint::Zero, 0));
    assert!(sign_contradicts(SignConstraint::NonNegative, -1));
    assert!(!sign_contradicts(SignConstraint::NonNegative, 0));
    assert!(sign_contradicts(SignConstraint::NonPositive, 1));
    assert!(!sign_contradicts(SignConstraint::NonPositive, 0));
}

#[test]
fn test_monomial_accessors_and_scaling() {
    let tid = |n: u32| TermId(n);
    let monomial = Monomial::new(vec![tid(1), tid(2)], tid(10));
    assert!(monomial.is_binary());
    assert!(!monomial.is_square());
    assert_eq!(monomial.x(), Some(tid(1)));
    assert_eq!(monomial.y(), Some(tid(2)));

    let square = Monomial::new_scaled(
        vec![tid(3), tid(3)],
        tid(11),
        BigRational::from_integer((-2).into()),
    );
    assert!(square.is_square());
    assert!(square.is_scaled());
    assert_eq!(square.coeff_sign(), -1);
    assert_eq!(
        square.aux_from_product(&BigRational::from_integer(4.into())),
        BigRational::from_integer((-8).into())
    );
}

#[test]
fn record_sign_constraint_reports_only_an_inserted_monomial_row() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let negative_two = terms.mk_rational(BigRational::from_integer((-2).into()));
    let scaled = terms.mk_mul(vec![x, y, negative_two]);
    let zero = terms.mk_rational(BigRational::zero());
    let assertion = terms.mk_le(scaled, zero);
    let mut aux_to_monomial = HashMap::default();
    let mut sign_constraints = HashMap::default();
    let mut var_sign_constraints = HashMap::default();

    assert!(record_sign_constraint(
        &terms,
        &aux_to_monomial,
        &mut sign_constraints,
        &mut var_sign_constraints,
        scaled,
        SignConstraint::NonPositive,
        assertion,
    )
    .is_none());
    assert!(sign_constraints.is_empty());

    let mut key = vec![x, y];
    key.sort_by_key(|term| term.0);
    aux_to_monomial.insert(scaled, key.clone());
    assert_eq!(
        record_sign_constraint(
            &terms,
            &aux_to_monomial,
            &mut sign_constraints,
            &mut var_sign_constraints,
            scaled,
            SignConstraint::NonPositive,
            assertion,
        ),
        Some(key.clone())
    );
    assert_eq!(
        sign_constraints.get(&key),
        Some(&vec![(SignConstraint::NonNegative, assertion)])
    );
}
