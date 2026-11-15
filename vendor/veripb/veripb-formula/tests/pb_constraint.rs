use std::str::FromStr;

use malachite_bigint::BigInt;
use veripb_formula::prelude::*;

#[test]
fn create_general_constraint_i64() {
    let ineq = GeneralPBConstraint::<i64>::default();

    assert_eq!(ineq.get_terms().len(), 0);
    assert_eq!(*ineq.get_degree(), 0);
}

#[test]
fn create_general_constraint_arbitrary() {
    let ineq = GeneralPBConstraint::<i64>::default();

    assert_eq!(ineq.get_terms().len(), 0);
    assert_eq!(*ineq.get_degree(), 0);
}

#[test]
fn from_terms_i64() {
    let ineq = GeneralPBConstraint::<i64>::from_terms(
        vec![
            GeneralPBTerm::new(732, Lit::from_var(0, false)),
            GeneralPBTerm::new(5233, Lit::from_var(1, true)),
        ],
        5965,
        42,
    );

    assert_eq!(ineq.get_terms().len(), 2);
    assert_eq!(*ineq.get_degree(), 42);
}

#[test]
fn from_terms_arbitrary() {
    let ineq = GeneralPBConstraint::from_terms(
        vec![
            GeneralPBTerm::new(BigInt::from_str("334823947983274982374237498238749237").unwrap(), Lit::from_var(0, false)),
            GeneralPBTerm::new(BigInt::from_str("483723984349457623987481239748923749823498234987234923748234982374983249823").unwrap(), Lit::from_var(1, true)),
        ],
        BigInt::from_str("483723984349457623987481239748923749823498234987234923748234982374983249823").unwrap(),
        BigInt::from_str("7846238747872347123984982347238947923749823749723894732987492387498237498237498230479823749823749823798423984798237498237498324932748973294872398432794873298472398473298473298479823").unwrap(),
    );

    assert_eq!(ineq.get_terms().len(), 2);
    assert_eq!(*ineq.get_degree(), BigInt::from_str("7846238747872347123984982347238947923749823749723894732987492387498237498237498230479823749823749823798423984798237498237498324932748973294872398432794873298472398473298473298479823").unwrap());
}

#[test]
fn from_terms_cancelling() {
    let ineq = GeneralPBConstraint::<i64>::from_terms(
        vec![
            GeneralPBTerm::new(100, Lit::from_var(0, false)),
            GeneralPBTerm::new(17, Lit::from_var(0, true)),
        ],
        117,
        42,
    );

    assert_eq!(ineq.get_terms().len(), 1);
    assert_eq!(*ineq.get_degree(), 25);
    assert_eq!(ineq.get_coeff_sum(), 83);
}

#[test]
fn from_terms_negative_coeff() {
    let ineq = GeneralPBConstraint::<i64>::from_terms(
        vec![
            GeneralPBTerm::new(100, Lit::from_var(0, false)),
            GeneralPBTerm::new(-17, Lit::from_var(0, false)),
        ],
        117,
        42,
    );

    assert_eq!(ineq.get_terms().len(), 1);
    assert!(!ineq.get_terms()[0].get_lit().is_negated());
    assert_eq!(*ineq.get_terms()[0].get_coeff(), 83);
    assert_eq!(*ineq.get_degree(), 42);
}

#[test]
fn from_terms_negative_coeff_negated_lit() {
    let ineq = GeneralPBConstraint::<i64>::from_terms(
        vec![
            GeneralPBTerm::new(100, Lit::from_var(0, false)),
            GeneralPBTerm::new(-17, Lit::from_var(0, true)),
        ],
        117,
        42,
    );

    assert_eq!(ineq.get_terms().len(), 1);
    assert!(!ineq.get_terms()[0].get_lit().is_negated());
    assert_eq!(*ineq.get_terms()[0].get_coeff(), 117);
    assert_eq!(*ineq.get_degree(), 59);
}

#[test]
fn from_terms_first_negative_coeff() {
    let ineq = GeneralPBConstraint::<i64>::from_terms(
        vec![
            GeneralPBTerm::new(-17, Lit::from_var(0, false)),
            GeneralPBTerm::new(100, Lit::from_var(0, false)),
        ],
        117,
        42,
    );

    assert_eq!(ineq.get_terms().len(), 1);
    assert!(!ineq.get_terms()[0].get_lit().is_negated());
    assert_eq!(*ineq.get_terms()[0].get_coeff(), 83);
    assert_eq!(*ineq.get_degree(), 42);
}

#[test]
fn from_terms_first_negative_coeff_negated_lit() {
    let ineq = GeneralPBConstraint::<i64>::from_terms(
        vec![
            GeneralPBTerm::new(-17, Lit::from_var(0, true)),
            GeneralPBTerm::new(100, Lit::from_var(0, false)),
        ],
        117,
        42,
    );

    assert_eq!(ineq.get_terms().len(), 1);
    assert!(!ineq.get_terms()[0].get_lit().is_negated());
    assert_eq!(*ineq.get_terms()[0].get_coeff(), 117);
    assert_eq!(*ineq.get_degree(), 59);
}

#[test]
fn from_terms_10_terms() {
    let ineq = GeneralPBConstraint::<i64>::from_terms(
        vec![
            GeneralPBTerm::new(-17, Lit::from_var(0, true)),
            GeneralPBTerm::new(100, Lit::from_var(0, true)),
            GeneralPBTerm::new(42132, Lit::from_var(1, false)),
            GeneralPBTerm::new(24, Lit::from_var(4, true)),
            GeneralPBTerm::new(231, Lit::from_var(2, true)),
            GeneralPBTerm::new(-12, Lit::from_var(4, true)),
            GeneralPBTerm::new(-15, Lit::from_var(3, false)),
            GeneralPBTerm::new(12, Lit::from_var(4, false)),
            GeneralPBTerm::new(8, Lit::from_var(5, false)),
            GeneralPBTerm::new(4, Lit::from_var(5, true)),
        ],
        45132,
        100,
    );

    assert_eq!(ineq.get_terms().len(), 5);
    assert_eq!(*ineq.get_degree(), 100 - 24 + 12 + 15 - 4);
}

#[test]
fn set_degree_i64() {
    let mut ineq: GeneralPBConstraint<i64> = GeneralPBConstraint::default();
    ineq.set_degree(42);

    assert_eq!(ineq.get_terms().len(), 0);
    assert_eq!(*ineq.get_degree(), 42);
}

#[test]
fn set_degree_arbitrary() {
    let mut ineq: GeneralPBConstraint<BigInt> = GeneralPBConstraint::default();
    ineq.set_degree(BigInt::from_str("7846238747872347123984982347238947923749823749723894732987492387498237498237498230479823749823749823798423984798237498237498324932748973294872398432794873298472398473298473298479823").unwrap());

    assert_eq!(ineq.get_terms().len(), 0);
    assert_eq!(*ineq.get_degree(), BigInt::from_str("7846238747872347123984982347238947923749823749723894732987492387498237498237498230479823749823749823798423984798237498237498324932748973294872398432794873298472398473298473298479823").unwrap());
}

#[test]
fn create_new_cardinality() {
    let card: Cardinality = Cardinality::default();

    assert_eq!(card.len(), 0);
    assert_eq!(*card.get_degree(), 0);
}

#[test]
fn create_cardinality_from_lits() {
    let card = Cardinality::from_lits(
        vec![
            Lit::from_var(0, true),
            Lit::from_var(1, false),
            Lit::from_var(42, true),
            Lit::from_var(23, true),
        ],
        42,
    );

    assert_eq!(card.len(), 4);
    assert_eq!(*card.get_degree(), 42);
}

#[test]
fn cardinality_get_terms() {
    let card = Cardinality::from_lits(vec![Lit::from_var(42, true)], 42);

    assert_eq!(card.get_terms()[0].get_lit(), Lit::from_var(42, true));
}

#[test]
fn general_to_card() {
    let ineq = GeneralPBConstraint::from_terms(
        vec![
            GeneralPBTerm::new(2, Lit::from_var(0, false)),
            GeneralPBTerm::new(1, Lit::from_var(0, true)),
            GeneralPBTerm::new(1, Lit::from_var(1, true)),
            GeneralPBTerm::new(1, Lit::from_var(2, false)),
            GeneralPBTerm::new(1, Lit::from_var(3, true)),
        ],
        6,
        42,
    );

    assert!(ineq.all_coeff_one());

    let card = Cardinality::from_lits(ineq.get_lits().copied().collect(), *ineq.get_degree());

    assert_eq!(card.len(), 4);
    assert_eq!(*card.get_degree(), 41);
}

#[test]
fn general_to_card_auto() {
    let ineq = constraint_from_terms(
        vec![
            GeneralPBTerm::new(2_i64, Lit::from_var(0, false)),
            GeneralPBTerm::new(1, Lit::from_var(0, true)),
            GeneralPBTerm::new(1, Lit::from_var(1, true)),
            GeneralPBTerm::new(1, Lit::from_var(2, false)),
            GeneralPBTerm::new(1, Lit::from_var(3, true)),
        ],
        4,
    );

    assert!(matches!(
        ineq,
        PBConstraintEnum::Cardinality(Cardinality { .. })
    ));
    assert_eq!(ineq.len(), 4);
}

#[test]
fn create_new_clause() {
    let card: Clause = Clause::default();

    assert_eq!(card.len(), 0);
    assert_eq!(*card.get_degree(), 1);
}

#[test]
fn create_clause_from_lits() {
    let card = Clause::from_lits(vec![
        Lit::from_var(0, true),
        Lit::from_var(1, false),
        Lit::from_var(42, true),
        Lit::from_var(23, true),
    ]);

    assert_eq!(card.len(), 4);
    assert_eq!(*card.get_degree(), 1);
}

#[test]
fn general_to_clause() {
    let ineq = GeneralPBConstraint::<i64>::from_terms(
        vec![
            GeneralPBTerm::new(2, Lit::from_var(0, false)),
            GeneralPBTerm::new(1, Lit::from_var(0, true)),
            GeneralPBTerm::new(1, Lit::from_var(1, true)),
            GeneralPBTerm::new(1, Lit::from_var(2, false)),
            GeneralPBTerm::new(1, Lit::from_var(3, true)),
        ],
        6,
        2,
    );

    assert!(ineq.all_coeff_one());
    assert_eq!(*ineq.get_degree(), 1);

    let clause = Clause::from_lits(ineq.get_lits().copied().collect());

    assert_eq!(clause.len(), 4);
    assert_eq!(*clause.get_degree(), 1);
}

#[test]
fn general_to_clause_auto() {
    let ineq = constraint_from_terms(
        vec![
            GeneralPBTerm::new(2_i64, Lit::from_var(0, false)),
            GeneralPBTerm::new(1, Lit::from_var(0, true)),
            GeneralPBTerm::new(1, Lit::from_var(1, true)),
            GeneralPBTerm::new(1, Lit::from_var(2, false)),
            GeneralPBTerm::new(1, Lit::from_var(3, true)),
        ],
        2,
    );

    assert!(matches!(ineq, PBConstraintEnum::Clause(Clause { .. })));
    assert_eq!(ineq.len(), 4);
}

// --------------------------------------------------------------------------
// `pol <id> 0 *` forged a constraint: `multiply` scaled the coefficients in
// situ and left the zero-coefficient terms behind, and `all_coeff_one` then
// inferred "all ones" from a normalization invariant it cannot see.
// --------------------------------------------------------------------------

/// `2 x1 1 x2 >= 2` at width `N`.
fn scalable_constraint<N: Int>() -> GeneralPBConstraint<N>
where
    PBConstraintEnum: From<GeneralPBConstraint<N>>,
{
    GeneralPBConstraint::<N>::from_terms(
        vec![
            GeneralPBTerm::new(N::from(2), Lit::from_var(0, false)),
            GeneralPBTerm::new(N::from(1), Lit::from_var(1, false)),
        ],
        N::from(3),
        N::from(2),
    )
}

/// Scaling by zero must leave the empty `0 >= 0`, not a constraint whose terms
/// all have coefficient zero: the stored form has to satisfy the "no zero
/// coefficient" invariant that `all_coeff_one()` reads.
fn assert_multiply_by_zero_empties<N: Int>(mut constraint: GeneralPBConstraint<N>)
where
    PBConstraintEnum: From<GeneralPBConstraint<N>>,
{
    assert!(
        constraint.multiply(&BigInt::from(0)).is_none(),
        "scaling by zero stays in situ"
    );
    assert!(constraint.is_empty(), "no term survives a scaling by zero");
    assert_eq!(constraint.get_coeff_sum(), N::from(0));
    assert_eq!(*constraint.get_degree(), N::from(0));
    assert!(constraint.all_coeff_one());
}

#[test]
fn multiply_by_zero_drops_every_term_i64() {
    assert_multiply_by_zero_empties(scalable_constraint::<i64>());
}

#[test]
fn multiply_by_zero_drops_every_term_i128() {
    assert_multiply_by_zero_empties(scalable_constraint::<i128>());
}

#[test]
fn multiply_by_zero_drops_every_term_bigint() {
    assert_multiply_by_zero_empties(scalable_constraint::<BigInt>());
}

#[test]
fn multiply_by_zero_with_a_negative_degree_drops_every_term() {
    // `2 x1 >= -5` times 0 is `0 >= 0`, not `0 x1 >= 0`.
    let mut constraint = GeneralPBConstraint::<i64>::from_terms(
        vec![GeneralPBTerm::new(2, Lit::from_var(0, false))],
        2,
        -5,
    );
    assert!(constraint.multiply(&BigInt::from(0)).is_none());
    assert!(constraint.is_empty());
    assert_eq!(constraint.get_coeff_sum(), 0);
    assert_eq!(*constraint.get_degree(), 0);
}

#[test]
fn multiply_by_zero_then_add_does_not_forge_a_cardinality() {
    // The end-to-end shape of the defect: `2 x1 1 x2 >= 1` scaled by 0 and then
    // added to `2 x2 >= 2` must be `2 x2 >= 2`. With the zero terms left in
    // place the coefficient sum (2) equalled the term count (2) and
    // `into_smallest_type` rebuilt `1 x1 1 x2 >= 2` from the literals alone.
    let mut scaled = GeneralPBConstraint::<i64>::from_terms(
        vec![
            GeneralPBTerm::new(2, Lit::from_var(0, false)),
            GeneralPBTerm::new(1, Lit::from_var(1, false)),
        ],
        3,
        1,
    );
    assert!(scaled.multiply(&BigInt::from(0)).is_none());

    let summand = GeneralPBConstraint::<i64>::from_terms(
        vec![GeneralPBTerm::new(2, Lit::from_var(1, false))],
        2,
        2,
    );
    assert!(scaled.add(&summand).is_none());

    assert_eq!(scaled.len(), 1);
    assert_eq!(*scaled.get_degree(), 2);
    assert_eq!(scaled.get_term(0).unwrap().get_coeff(), &BigInt::from(2));
    assert_eq!(
        scaled.get_term(0).unwrap().get_lit(),
        Lit::from_var(1, false)
    );
}

#[test]
fn all_coeff_one_rejects_a_zero_coefficient_term() {
    // `coeff_sum == terms.len()` is only *sufficient* for a normalized
    // constraint. `add_term` is a public mutator that does not normalize, so a
    // zero-coefficient term can reach `all_coeff_one` without ever passing
    // through `normalize()` -- which is what made the O(1) inference forge a
    // coefficient. The scan has to confirm the terms.
    let mut constraint = GeneralPBConstraint::<i64>::from_terms(
        vec![GeneralPBTerm::new(2, Lit::from_var(1, false))],
        2,
        2,
    );
    constraint.add_term(GeneralPBTerm::new(0, Lit::from_var(0, false)));

    assert_eq!(constraint.len(), 2);
    assert_eq!(constraint.get_coeff_sum(), constraint.len() as i64);
    assert!(
        !constraint.all_coeff_one(),
        "a zero coefficient is not a coefficient of one"
    );

    // ... and the consumer that discards coefficients must not forge one.
    assert!(matches!(
        constraint.into_smallest_type(),
        PBConstraintEnum::GeneralPBI64(_)
    ));
}

// --------------------------------------------------------------------------
// `Clause::from_unnormalized_lits` used `Lit::new_undef()` as its "no previous
// literal" sentinel, which is a legal literal.
// --------------------------------------------------------------------------

#[test]
fn from_unnormalized_lits_keeps_the_literal_that_packs_as_the_undef_sentinel() {
    // `Lit::new_undef()` is the packed value `usize::MAX`, which is also the
    // negated form of variable `Lit::MAX_VAR_IDX + 1`. The DIMACS CNF parser
    // used to hand exactly this literal to `from_unnormalized_lits` (for
    // `-9223372036854775807`), where the dedup loop read it as a duplicate of
    // "nothing" and dropped it -- turning a unit clause into the empty clause,
    // i.e. a contradiction. The parser rejects that index now, but the loop
    // must not depend on the caller's range either.
    let lit = Lit::from_raw_data(usize::MAX);
    assert!(lit.is_undef(), "this is the sentinel bit pattern");

    let constraint = Clause::from_unnormalized_lits(vec![lit]);

    assert_eq!(constraint.len(), 1, "the unit clause must survive");
    assert!(
        !constraint.is_contradicting(),
        "a unit clause is not the empty clause"
    );
    assert_eq!(constraint.get_lit(0), Some(&lit));
}

#[test]
fn from_unnormalized_lits_keeps_the_sibling_of_the_undef_sentinel() {
    // The positive sibling packs to `usize::MAX - 1`; it equalled `-last_lit`
    // on the first iteration and drove `new_idx -= 1` through an unsigned
    // underflow (release builds have no overflow checks), after which
    // `truncate(usize::MAX)` was a no-op.
    let lit = Lit::from_raw_data(usize::MAX - 1);
    let constraint = Clause::from_unnormalized_lits(vec![lit]);

    assert_eq!(constraint.len(), 1);
    assert!(!constraint.is_trivial());
    assert!(!constraint.is_contradicting());
    assert_eq!(constraint.get_lit(0), Some(&lit));
}

#[test]
fn from_unnormalized_lits_cancels_opposing_literals_at_the_range_boundary() {
    // `x v ~x` is trivially true and normalizes to the degree-0 cardinality,
    // for the boundary variable exactly as for any other.
    for var in [Lit::MAX_VAR_IDX, Lit::MAX_VAR_IDX + 1] {
        let constraint = Clause::from_unnormalized_lits(vec![
            Lit::from_raw_data(var << 1),
            Lit::from_raw_data((var << 1) ^ 1),
        ]);

        assert_eq!(constraint.len(), 0);
        assert!(constraint.is_trivial());
    }

    // Duplicates on either side of the cancellation are dropped, not counted.
    let constraint = Clause::from_unnormalized_lits(vec![
        Lit::from_var(Lit::MAX_VAR_IDX - 1, false),
        Lit::from_raw_data(usize::MAX - 1),
        Lit::from_raw_data(usize::MAX - 1),
        Lit::from_raw_data(usize::MAX),
    ]);

    assert_eq!(constraint.len(), 1);
    assert_eq!(
        constraint.get_lit(0),
        Some(&Lit::from_var(Lit::MAX_VAR_IDX - 1, false))
    );
    assert!(constraint.is_trivial());
}
