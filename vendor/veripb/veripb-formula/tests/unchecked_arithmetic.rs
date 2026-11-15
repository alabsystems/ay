//! Regression tests for unchecked integer arithmetic on the degree of a constraint.
//!
//! The release profile built without overflow checks until 2026-08-23, so every
//! one of these operations used to wrap *silently*
//! instead of panicking. `debug_assert!` and plain arithmetic are therefore not
//! enough: the operations have to be checked and either escalate the integer
//! width or fail closed.
//!
//! * degree decrement in `weaken` / `weaken_all` / variable-form `c` and `m`
//!   (a legal degree of `i64::MIN` wrapped to a huge *positive* number, turning
//!   a trivially true constraint into the empty contradiction),
//! * the oversized-divisor fallback of the MIR cut, which hard-coded the
//!   quotient `ceil(A/d)` to `1` although it is `0` for `A <= 0`,
//! * `get_reification`, which computed `coeff_sum - degree + 1` in the
//!   constraint's own integer width.

use malachite_bigint::BigInt;
use num_traits::One;
use veripb_formula::prelude::*;

/// Read the degree of a [`PBConstraintEnum`] as a [`BigInt`], whatever
/// representation the constraint ended up in.
fn degree_of(constraint: &PBConstraintEnum) -> BigInt {
    match constraint {
        PBConstraintEnum::Clause(c) => (*c.get_degree()).into(),
        PBConstraintEnum::Cardinality(c) => (*c.get_degree()).into(),
        PBConstraintEnum::GeneralPBI64(c) => (*c.get_degree()).into(),
        PBConstraintEnum::GeneralPBI128(c) => (*c.get_degree()).into(),
        PBConstraintEnum::GeneralPBBigInt(c) => c.get_degree().clone(),
    }
}

/// The coefficient of `lit`, or zero if the constraint does not contain it.
fn coeff_of(constraint: &PBConstraintEnum, lit: Lit) -> BigInt {
    for index in 0..constraint.len() {
        let term = constraint.get_term(index).unwrap();
        if term.get_lit() == lit {
            return term.get_coeff().clone();
        }
    }
    BigInt::from(0)
}

/// `2^63`, the smallest divisor that does not fit into an `i64` constraint.
fn oversized_divisor() -> BigInt {
    BigInt::from(i64::MAX as u64 + 1)
}

/// `2^62`, the largest power of two that still fits into an `i64` constraint.
/// Used as the control: for these inputs it exercises the (correct) in-situ MIR
/// branch and must produce exactly the same constraint as the fallback.
fn largest_fitting_divisor() -> BigInt {
    BigInt::from(1_i64 << 62)
}

#[test]
fn weaken_with_minimal_degree_does_not_wrap() {
    // `2 x1 >= i64::MIN` is trivially true and is accepted by both parsers.
    let mut constraint = GeneralPBConstraint::<i64>::from_terms(
        vec![GeneralPBTerm::new(2, Lit::from_var(0, false))],
        2,
        i64::MIN,
    );

    // Weakening away `x1` lowers the degree by 2. Before the fix this wrapped to
    // 9223372036854775806 and produced the empty contradiction.
    let replacement = constraint.weaken(0);
    let degree = match replacement {
        Some(ref replacement) => degree_of(replacement),
        None => BigInt::from(*constraint.get_degree()),
    };

    assert_eq!(degree, BigInt::from(i64::MIN) - BigInt::from(2));
    assert!(
        replacement.is_some_and(|c| !c.is_contradicting()),
        "weakening a trivially true constraint must not yield a contradiction"
    );
}

#[test]
fn weaken_all_with_minimal_degree_does_not_wrap() {
    let mut constraint = GeneralPBConstraint::<i64>::from_terms(
        vec![
            GeneralPBTerm::new(2, Lit::from_var(0, false)),
            GeneralPBTerm::new(3, Lit::from_var(1, false)),
        ],
        5,
        i64::MIN,
    );

    let replacement = constraint
        .weaken_all(vec![0, 1])
        .expect("weakening below i64::MIN must escalate the integer width");

    assert_eq!(
        degree_of(&replacement),
        BigInt::from(i64::MIN) - BigInt::from(5)
    );
    assert!(!replacement.is_contradicting());
}

#[test]
fn cardinality_weaken_with_minimal_degree_does_not_wrap() {
    // The `Cardinality` representation stores its degree in an `i64` too.
    let mut constraint = Cardinality::from_lits(
        vec![Lit::from_var(0, false), Lit::from_var(1, false)],
        i64::MIN,
    );

    let replacement = constraint
        .weaken_all(vec![0, 1])
        .expect("weakening below i64::MIN must escalate the integer width");

    assert_eq!(
        degree_of(&replacement),
        BigInt::from(i64::MIN) - BigInt::from(2)
    );
    assert!(!replacement.is_contradicting());
}

/// `2 ~x1 >= i64::MIN`, in the narrow and in the arbitrary-precision representation.
///
/// The [`BigInt`] instantiation runs the exact same code but cannot wrap, so it is
/// used as the oracle for the `i64` instantiation.
fn negated_term_with_minimal_degree() -> (GeneralPBConstraint<i64>, GeneralPBConstraint<BigInt>) {
    (
        GeneralPBConstraint::<i64>::from_terms(
            vec![GeneralPBTerm::new(2, Lit::from_var(0, true))],
            2,
            i64::MIN,
        ),
        GeneralPBConstraint::<BigInt>::from_terms(
            vec![GeneralPBTerm::new(BigInt::from(2), Lit::from_var(0, true))],
            BigInt::from(2),
            BigInt::from(i64::MIN),
        ),
    )
}

#[test]
fn variable_form_div_with_minimal_degree_does_not_wrap() {
    // Moving `~x1` to the right-hand side subtracts its coefficient from the degree,
    // which underflows below `i64::MIN`.
    let (mut narrow, mut oracle) = negated_term_with_minimal_degree();

    let replacement = narrow
        .variable_form_div(&BigInt::from(2))
        .expect("a variable-form degree below i64::MIN must escalate the integer width");
    assert!(oracle.variable_form_div(&BigInt::from(2)).is_none());

    assert_eq!(degree_of(&replacement), *oracle.get_degree());
    assert_eq!(
        coeff_of(&replacement, Lit::from_var(0, true)),
        *oracle.get_coeff(Lit::from_var(0, true)).unwrap()
    );
    assert!(!replacement.is_contradicting());
}

#[test]
fn variable_form_mir_with_minimal_degree_does_not_wrap() {
    let (mut narrow, mut oracle) = negated_term_with_minimal_degree();

    // `d = 3` keeps the remainder non-zero, so the cut is not the trivial special case.
    let replacement = narrow
        .variable_form_mir(&BigInt::from(3))
        .expect("a variable-form degree below i64::MIN must escalate the integer width");
    assert!(oracle.variable_form_mir(&BigInt::from(3)).is_none());

    assert_eq!(degree_of(&replacement), *oracle.get_degree());
    assert_eq!(
        coeff_of(&replacement, Lit::from_var(0, true)),
        *oracle.get_coeff(Lit::from_var(0, true)).unwrap()
    );
    assert!(!replacement.is_contradicting());
}

#[test]
fn normalized_form_mir_oversized_divisor_of_trivial_constraint_is_trivial() {
    // `2 x1 >= -1` is trivially true. With `d = 2^63` the remainder is
    // `A mod d = 2^63 - 1`, but the quotient `ceil(A / d)` is 0, so the MIR degree is 0.
    // The fallback used to hard-code the quotient to 1 and returned
    // `2 x1 >= 9223372036854775807`, a constraint that is not even satisfiable.
    let mut constraint = GeneralPBConstraint::<i64>::from_terms(
        vec![GeneralPBTerm::new(2, Lit::from_var(0, false))],
        2,
        -1,
    );

    let replacement = constraint.normalized_form_mir(&oversized_divisor());
    let (degree, coeff) = match replacement {
        Some(ref replacement) => (
            degree_of(replacement),
            coeff_of(replacement, Lit::from_var(0, false)),
        ),
        None => (
            BigInt::from(*constraint.get_degree()),
            BigInt::from(*constraint.get_coeff(Lit::from_var(0, false)).unwrap()),
        ),
    };

    assert_eq!(degree, BigInt::from(0));
    assert_eq!(coeff, BigInt::from(2));

    // Control: the same cut with the largest divisor that still fits into the
    // constraint's integer type takes the (correct) in-situ branch and must agree.
    let mut control = GeneralPBConstraint::<i64>::from_terms(
        vec![GeneralPBTerm::new(2, Lit::from_var(0, false))],
        2,
        -1,
    );
    assert!(
        control
            .normalized_form_mir(&largest_fitting_divisor())
            .is_none()
    );
    assert_eq!(*control.get_degree(), 0);
    assert_eq!(*control.get_coeff(Lit::from_var(0, false)).unwrap(), 2);
}

#[test]
fn normalized_form_mir_oversized_divisor_of_positive_degree_saturates() {
    // For `0 < A < d` the quotient really is 1 and `r == A`, so the cut degenerates
    // into saturation. This is the case the old fallback happened to get right; it
    // must keep working.
    let mut constraint = GeneralPBConstraint::<i64>::from_terms(
        vec![
            GeneralPBTerm::new(7, Lit::from_var(0, false)),
            GeneralPBTerm::new(2, Lit::from_var(1, false)),
        ],
        9,
        3,
    );

    let replacement = constraint.normalized_form_mir(&oversized_divisor());
    assert!(replacement.is_none());
    assert_eq!(*constraint.get_degree(), 3);
    assert_eq!(*constraint.get_coeff(Lit::from_var(0, false)).unwrap(), 3);
    assert_eq!(*constraint.get_coeff(Lit::from_var(1, false)).unwrap(), 2);
}

#[test]
fn variable_form_mir_oversized_divisor_of_trivial_constraint_is_trivial() {
    // `2 ~x1 >= 1` has variable-form degree `1 - 2 = -1`, so the quotient is 0 again.
    // The old fallback computed `r + 1` with `r = 2^63 - 1`, which wrapped to i64::MIN.
    let mut constraint = GeneralPBConstraint::<i64>::from_terms(
        vec![GeneralPBTerm::new(2, Lit::from_var(0, true))],
        2,
        1,
    );

    let replacement = constraint.variable_form_mir(&oversized_divisor());
    let (degree, coeff) = match replacement {
        Some(ref replacement) => (
            degree_of(replacement),
            coeff_of(replacement, Lit::from_var(0, true)),
        ),
        None => (
            BigInt::from(*constraint.get_degree()),
            BigInt::from(*constraint.get_coeff(Lit::from_var(0, true)).unwrap()),
        ),
    };

    assert_eq!(degree, BigInt::from(1));
    assert_eq!(coeff, BigInt::from(1));

    // Control: the in-situ branch with the largest fitting divisor agrees.
    let mut control = GeneralPBConstraint::<i64>::from_terms(
        vec![GeneralPBTerm::new(2, Lit::from_var(0, true))],
        2,
        1,
    );
    assert!(
        control
            .variable_form_mir(&largest_fitting_divisor())
            .is_none()
    );
    assert_eq!(*control.get_degree(), 1);
    assert_eq!(*control.get_coeff(Lit::from_var(0, true)).unwrap(), 1);
}

#[test]
fn reification_degree_is_not_computed_in_the_narrow_width() {
    // `2^62 x1 >= -2^62`. The reified degree is `coeff_sum - degree + 1 = 2^63 + 1`,
    // which does not fit into an i64: it used to wrap negative, which flipped the
    // reification literal and left the proof goal at degree 0 — auto-discharged as
    // trivial, so the real proof obligation was skipped.
    let half = 1_i64 << 62;
    let constraint = GeneralPBConstraint::<i64>::from_terms(
        vec![GeneralPBTerm::new(half, Lit::from_var(0, false))],
        half,
        -half,
    );

    let reified = constraint.get_reification(1, ReificationDir::IneqImplVar);

    let expected = BigInt::from(half) + BigInt::from(half) + BigInt::from(1);
    assert_eq!(degree_of(&reified), expected);
    // The reification literal must be the positive `x2`, not its complement.
    assert_eq!(coeff_of(&reified, Lit::from_var(1, false)), expected);
    assert!(
        !reified.is_trivial(),
        "the reification is a real proof obligation and must not look trivial"
    );
}

#[test]
fn normalizing_cancelling_terms_with_minimal_degree_does_not_wrap() {
    // `1 x1 + 1 ~x1 >= i64::MIN` is trivially true. Normalizing cancels the two terms
    // and moves the constant 1 to the right-hand side, i.e. the degree becomes
    // `i64::MIN - 1`. Before the fix that wrapped to `i64::MAX` and the constraint was
    // stored as the empty contradiction, so `conclusion UNSAT` accepted it.
    let constraint = constraint_from_terms_and_coeff_sum(
        vec![
            GeneralPBTerm::new(1_i64, Lit::from_var(0, false)),
            GeneralPBTerm::new(1_i64, Lit::from_var(0, true)),
        ],
        i64::MIN,
        2,
    );

    assert_eq!(constraint.len(), 0);
    assert_eq!(
        degree_of(&constraint),
        BigInt::from(i64::MIN) - BigInt::from(1)
    );
    assert!(constraint.is_trivial());
    assert!(
        !constraint.is_contradicting(),
        "a trivially true constraint must not normalize into the empty contradiction"
    );
}

#[test]
fn normalizing_negative_coefficient_with_maximal_degree_does_not_wrap() {
    // `-1 x1 >= i64::MAX` is infeasible: the left-hand side is at most 0. Normalizing
    // flips the term to `1 ~x1` and *raises* the degree by one, to `i64::MAX + 1`, which
    // used to wrap to `i64::MIN` and turned the infeasible constraint into a trivially
    // true one.
    let constraint = constraint_from_terms(
        vec![GeneralPBTerm::new(-1_i64, Lit::from_var(0, false))],
        i64::MAX,
    );

    assert_eq!(
        degree_of(&constraint),
        BigInt::from(i64::MAX) + BigInt::from(1)
    );
    assert!(
        constraint.is_contradicting(),
        "an infeasible constraint must not normalize into a trivially true one"
    );
    assert!(!constraint.is_trivial());
}

/// The sum of two constraints, as a [`BigInt`] oracle, computed from the exact operands.
///
/// Every `add` implementation is supposed to agree with this, whatever integer width it took.
fn add_oracle(
    first: &[(BigInt, Lit)],
    first_degree: BigInt,
    second: &[(BigInt, Lit)],
    second_degree: BigInt,
) -> PBConstraintEnum {
    let mut terms: Vec<GeneralPBTerm<BigInt>> = first
        .iter()
        .chain(second.iter())
        .map(|(coeff, lit)| GeneralPBTerm::new(coeff.clone(), *lit))
        .collect();
    terms.sort_unstable_by_key(|term| term.get_lit());
    constraint_from_terms(terms, first_degree + second_degree)
}

#[test]
fn add_degree_underflow_in_general_pb_does_not_wrap() {
    // `5 x1 1 x2 >= i64::MIN + 2` is trivially true. Adding the literal axiom `5 ~x1 >= 0`
    // cancels 5, so the true degree of the sum is `i64::MIN - 3`. The addition used to check
    // that the *unadjusted* degree sum (`i64::MIN + 2`) fits into an i64 and then subtract the
    // cancellation from it in i64, which wrapped to 9223372036854775805 and turned the
    // trivially true sum into a contradiction.
    let mut constraint = GeneralPBConstraint::<i64>::from_terms(
        vec![
            GeneralPBTerm::new(5, Lit::from_var(0, false)),
            GeneralPBTerm::new(1, Lit::from_var(1, false)),
        ],
        6,
        i64::MIN + 2,
    );
    let summand = GeneralPBConstraint::<i64>::from_terms(
        vec![GeneralPBTerm::new(5, Lit::from_var(0, true))],
        5,
        0,
    );

    let replacement = constraint
        .add(&summand)
        .expect("a degree below i64::MIN must escalate the integer width");

    assert_eq!(
        degree_of(&replacement),
        BigInt::from(i64::MIN) + BigInt::from(2) - BigInt::from(5)
    );
    assert_eq!(
        coeff_of(&replacement, Lit::from_var(1, false)),
        BigInt::from(1)
    );
    assert_eq!(replacement.len(), 1);
    assert!(!replacement.is_contradicting());
    assert!(replacement.is_trivial());
}

#[test]
fn add_degree_underflow_in_general_pb_i128_does_not_wrap() {
    // The same shape one width up: degree `i128::MIN + 3`, cancellation 5, true degree
    // `i128::MIN - 2`.
    let mut constraint = GeneralPBConstraint::<i128>::from_terms(
        vec![
            GeneralPBTerm::new(5, Lit::from_var(0, false)),
            GeneralPBTerm::new(1, Lit::from_var(1, false)),
        ],
        6,
        i128::MIN + 3,
    );
    let summand = GeneralPBConstraint::<i128>::from_terms(
        vec![GeneralPBTerm::new(5, Lit::from_var(0, true))],
        5,
        0,
    );

    let replacement = constraint
        .add(&summand)
        .expect("a degree below i128::MIN must escalate the integer width");

    assert_eq!(
        degree_of(&replacement),
        BigInt::from(i128::MIN) + BigInt::from(3) - BigInt::from(5)
    );
    assert_eq!(replacement.len(), 1);
    assert!(!replacement.is_contradicting());
}

#[test]
fn add_degree_underflow_when_promoting_i64_to_i128_does_not_wrap() {
    // The accumulator is an i64 constraint and the summand an i128 one, so the sum is built in
    // i128 — and that branch subtracted the cancellation in i128 after checking only the
    // unadjusted sums. Degree sum `i128::MIN + 1`, cancellation 2, true degree `i128::MIN - 1`.
    let mut constraint = GeneralPBConstraint::<i64>::from_terms(
        vec![
            GeneralPBTerm::new(2, Lit::from_var(0, false)),
            GeneralPBTerm::new(1, Lit::from_var(1, false)),
        ],
        3,
        1,
    );
    let summand = GeneralPBConstraint::<i128>::from_terms(
        vec![GeneralPBTerm::new(2, Lit::from_var(0, true))],
        2,
        i128::MIN,
    );

    let replacement = constraint
        .add(&summand)
        .expect("a degree below i128::MIN must escalate the integer width");

    assert_eq!(
        degree_of(&replacement),
        BigInt::from(i128::MIN) + BigInt::from(1) - BigInt::from(2)
    );
    assert_eq!(
        coeff_of(&replacement, Lit::from_var(1, false)),
        BigInt::from(1)
    );
    assert!(!replacement.is_contradicting());
}

#[test]
fn add_degree_underflow_in_clause_does_not_wrap() {
    // `Clause::add` falls back to a general PB constraint. Degree sum `i64::MIN + 1`, both
    // variables cancel, so the true degree is `i64::MIN - 1`; it used to wrap to `i64::MAX` and
    // produced the empty contradiction.
    let mut clause = Clause::from_lits(vec![Lit::from_var(0, false), Lit::from_var(1, false)]);
    let summand = GeneralPBConstraint::<i64>::from_terms(
        vec![
            GeneralPBTerm::new(1, Lit::from_var(0, true)),
            GeneralPBTerm::new(1, Lit::from_var(1, true)),
        ],
        2,
        i64::MIN,
    );

    let replacement = clause
        .add(&summand)
        .expect("a degree below i64::MIN must escalate the integer width");

    assert_eq!(
        degree_of(&replacement),
        BigInt::from(i64::MIN) + BigInt::from(1) - BigInt::from(2)
    );
    assert_eq!(replacement.len(), 0);
    assert!(!replacement.is_contradicting());
}

#[test]
fn add_degree_underflow_in_cardinality_does_not_wrap() {
    // `Cardinality::add` uses the same fallback. Degree sum `i64::MIN + 2`, three merges cancel
    // 3, so the true degree is `i64::MIN - 1`.
    let mut card = Cardinality::from_lits(
        vec![
            Lit::from_var(0, false),
            Lit::from_var(1, false),
            Lit::from_var(2, false),
        ],
        2,
    );
    let summand = GeneralPBConstraint::<i64>::from_terms(
        vec![
            GeneralPBTerm::new(3, Lit::from_var(0, true)),
            GeneralPBTerm::new(3, Lit::from_var(1, true)),
            GeneralPBTerm::new(3, Lit::from_var(2, true)),
        ],
        9,
        i64::MIN,
    );

    let replacement = card
        .add(&summand)
        .expect("a degree below i64::MIN must escalate the integer width");

    assert_eq!(
        degree_of(&replacement),
        BigInt::from(i64::MIN) + BigInt::from(2) - BigInt::from(3)
    );
    // Each `1 xi` merged with `3 ~xi` leaves `2 ~xi`.
    assert_eq!(replacement.len(), 3);
    assert_eq!(
        coeff_of(&replacement, Lit::from_var(0, true)),
        BigInt::from(2)
    );
    assert!(!replacement.is_contradicting());

    // Control: the arbitrary-precision oracle agrees, terms and degree.
    let oracle = add_oracle(
        &[
            (BigInt::from(1), Lit::from_var(0, false)),
            (BigInt::from(1), Lit::from_var(1, false)),
            (BigInt::from(1), Lit::from_var(2, false)),
        ],
        BigInt::from(2),
        &[
            (BigInt::from(3), Lit::from_var(0, true)),
            (BigInt::from(3), Lit::from_var(1, true)),
            (BigInt::from(3), Lit::from_var(2, true)),
        ],
        BigInt::from(i64::MIN),
    );
    assert_eq!(degree_of(&replacement), degree_of(&oracle));
    assert_eq!(replacement.len(), oracle.len());
}

#[test]
fn add_without_underflow_stays_in_the_narrow_type() {
    // Control: the guard must not escalate additions that do fit. `5 x1 1 x2 >= 3` plus
    // `5 ~x1 >= 0` has degree `3 - 5 = -2` and stays an in-situ i64 addition.
    let mut constraint = GeneralPBConstraint::<i64>::from_terms(
        vec![
            GeneralPBTerm::new(5, Lit::from_var(0, false)),
            GeneralPBTerm::new(1, Lit::from_var(1, false)),
        ],
        6,
        3,
    );
    let summand = GeneralPBConstraint::<i64>::from_terms(
        vec![GeneralPBTerm::new(5, Lit::from_var(0, true))],
        5,
        0,
    );

    assert!(constraint.add(&summand).is_none());
    assert_eq!(*constraint.get_degree(), -2);
    assert_eq!(constraint.get_coeff_sum(), 1);
    assert_eq!(constraint.len(), 1);
}

#[test]
fn multiply_by_a_factor_that_does_not_fit_the_type_does_not_abort() {
    // The `s`/`n`/`m` rules can reduce a constraint to `0 >= 0`. Multiplying it decided to stay
    // in situ because both products are zero for *any* factor, and then unwrapped the factor
    // itself into the constraint's integer type — an abort (SIGABRT, exit 134) on a well-formed
    // `pol` line.
    for exponent in [64_u32, 200_u32] {
        let factor = BigInt::from(1u64) << exponent;

        let mut constraint = GeneralPBConstraint::<i64>::from_terms(vec![], 0, 0);
        let replacement = constraint.multiply(&factor);
        let (degree, len) = match replacement {
            Some(ref replacement) => (degree_of(replacement), replacement.len()),
            None => (BigInt::from(*constraint.get_degree()), constraint.len()),
        };

        assert_eq!(degree, BigInt::from(0), "2^{exponent}");
        assert_eq!(len, 0, "2^{exponent}");
    }
}

#[test]
fn multiply_a_non_empty_constraint_by_an_oversized_factor_escalates() {
    // Control: with a term to scale, the factor really does have to leave the narrow type, and
    // the result must be the exact product rather than an abort.
    let factor = BigInt::from(1u64) << 64;
    let mut constraint = GeneralPBConstraint::<i64>::from_terms(
        vec![GeneralPBTerm::new(3, Lit::from_var(0, false))],
        3,
        2,
    );

    let replacement = constraint
        .multiply(&factor)
        .expect("a factor above i64::MAX must escalate the integer width");

    assert_eq!(degree_of(&replacement), BigInt::from(2) * &factor);
    assert_eq!(
        coeff_of(&replacement, Lit::from_var(0, false)),
        BigInt::from(3) * &factor
    );
}

#[test]
fn substitute_degree_underflow_does_not_wrap() {
    // `5 x1 1 x2 >= i64::MIN + 2` is trivially true. Substituting x1 to true subtracts 5 from the
    // degree, i.e. `i64::MIN - 3`, which used to wrap to a huge positive degree — a *contradicting*
    // constraint. A contradicting source syntactically implies every target, so every `red`/`dom`
    // proof goal was auto-discharged with no proof at all.
    let constraint = GeneralPBConstraint::<i64>::from_terms(
        vec![
            GeneralPBTerm::new(5, Lit::from_var(0, false)),
            GeneralPBTerm::new(1, Lit::from_var(1, false)),
        ],
        6,
        i64::MIN + 2,
    );
    let mut substitution = Substitution::default();
    substitution.set(0, SubstitutionValue::TRUE);

    let substituted = constraint.substitute(&substitution);

    assert_eq!(
        degree_of(&substituted),
        BigInt::from(i64::MIN) + BigInt::from(2) - BigInt::from(5)
    );
    assert!(
        !substituted.is_contradicting(),
        "substituting into a trivially true constraint must not yield a contradiction"
    );
    assert!(substituted.is_trivial());
}

#[test]
fn cardinality_substitute_degree_underflow_does_not_wrap() {
    // The same for the `Cardinality` representation, whose degree is an i64 as well: two literals
    // substituted to true lower `i64::MIN + 1` to `i64::MIN - 1`.
    let card = Cardinality::from_lits(
        vec![
            Lit::from_var(0, false),
            Lit::from_var(1, false),
            Lit::from_var(2, false),
        ],
        i64::MIN + 1,
    );
    let mut substitution = Substitution::default();
    substitution.set(0, SubstitutionValue::TRUE);
    substitution.set(1, SubstitutionValue::TRUE);

    let substituted = card.substitute(&substitution);

    assert_eq!(
        degree_of(&substituted),
        BigInt::from(i64::MIN) + BigInt::from(1) - BigInt::from(2)
    );
    assert!(!substituted.is_contradicting());
}

#[test]
fn negating_a_trivially_true_constraint_yields_a_contradiction() {
    // The negation of `sum a_i l_i >= d` has degree `coeff_sum - d + 1`. For the trivially true
    // `2 ~x1 >= i64::MIN` that is `2^63 + 3`, which used to be computed in the constraint's own
    // width: it wrapped, so the negation — which has to be *the* contradiction — came out as a
    // strictly weaker constraint (and aborted a debug build outright).
    let constraint = GeneralPBConstraint::<i64>::from_terms(
        vec![GeneralPBTerm::new(2, Lit::from_var(0, true))],
        2,
        i64::MIN,
    );

    let negated = constraint.negate();

    assert_eq!(
        degree_of(&negated),
        BigInt::from(2) - BigInt::from(i64::MIN) + BigInt::from(1)
    );
    assert!(
        negated.is_contradicting(),
        "the negation of a trivially true constraint is unsatisfiable"
    );
}

#[test]
fn negating_a_trivially_true_cardinality_yields_a_contradiction() {
    let card = Cardinality::from_lits(
        vec![Lit::from_var(0, false), Lit::from_var(1, false)],
        i64::MIN,
    );

    let negated = card.negate();

    assert_eq!(
        degree_of(&negated),
        BigInt::from(2) - BigInt::from(i64::MIN) + BigInt::from(1)
    );
    assert!(negated.is_contradicting());
}

#[test]
fn negating_an_ordinary_constraint_is_unchanged() {
    // Control: `2 ~x1 1 x2 >= 2` negates to `2 x1 1 ~x2 >= 3 - 2 + 1 = 2`.
    let constraint = GeneralPBConstraint::<i64>::from_terms(
        vec![
            GeneralPBTerm::new(2, Lit::from_var(0, true)),
            GeneralPBTerm::new(1, Lit::from_var(1, false)),
        ],
        3,
        2,
    );

    let negated = constraint.negate();

    assert_eq!(degree_of(&negated), BigInt::from(2));
    assert_eq!(coeff_of(&negated, Lit::from_var(0, false)), BigInt::from(2));
    assert_eq!(coeff_of(&negated, Lit::from_var(1, true)), BigInt::from(1));
    assert!(!negated.is_contradicting());
}

// --------------------------------------------------------------------------
// `lower_rhs` escalation: `None` means "the receiver was lowered in place", so
// escalating by calling `lower_rhs` on a `GeneralPBConstraint::<BigInt>`
// *temporary* silently discarded the whole step. A `BigInt` `checked_sub`
// never fails, so that implementation always takes its in situ branch.
// --------------------------------------------------------------------------

/// The two literals every constraint in this section is built over.
fn lits() -> Vec<Lit> {
    vec![Lit::from_var(0, false), Lit::from_var(1, false)]
}

/// Lower `constraint`'s right-hand side by `amount` and return the resulting
/// degree, whichever representation the operation ended up in.
fn lowered_degree(mut constraint: PBConstraintEnum, amount: &BigInt) -> BigInt {
    match constraint.lower_rhs(amount) {
        Some(replacement) => degree_of(&replacement),
        None => degree_of(&constraint),
    }
}

#[test]
fn clause_lower_rhs_escalation_hands_back_the_lowered_constraint() {
    let start = BigInt::one();
    for amount in [
        BigInt::from(i64::MAX),
        BigInt::from(i64::MAX as u128 + 1),
        BigInt::from(u64::MAX) + BigInt::one(),
        BigInt::from(u128::MAX),
    ] {
        let clause = PBConstraintEnum::from(Clause::from_lits(lits()));
        assert_eq!(
            lowered_degree(clause, &amount),
            start.clone() - &amount,
            "lowering a clause by {amount} must reach the exact degree"
        );
    }
}

#[test]
fn cardinality_lower_rhs_escalation_hands_back_the_lowered_constraint() {
    // The `i64` underflow route is the one the guard was added for: the guard
    // correctly refuses to wrap, and the escalation it hands off to has to do
    // the work rather than mutate a value that is thrown away.
    for start in [i64::MIN, i64::MIN + 1, 1 - i64::MAX, 0, 1] {
        for amount in [
            BigInt::one(),
            BigInt::from(i64::MAX),
            BigInt::from(i64::MAX as u128 + 1),
            BigInt::from(u64::MAX) + BigInt::one(),
            BigInt::from(u128::MAX),
        ] {
            let card = PBConstraintEnum::from(Cardinality::from_lits(lits(), start));
            assert_eq!(
                lowered_degree(card, &amount),
                BigInt::from(start) - &amount,
                "lowering a cardinality of degree {start} by {amount}"
            );
        }
    }
}

#[test]
fn general_lower_rhs_escalation_hands_back_the_lowered_constraint() {
    for start in [i64::MIN, -1, 0, i64::MAX] {
        for amount in [BigInt::from(i64::MAX), BigInt::from(u128::MAX)] {
            let general = PBConstraintEnum::from(GeneralPBConstraint::<i64>::from_terms(
                vec![
                    GeneralPBTerm::new(2, Lit::from_var(0, false)),
                    GeneralPBTerm::new(1, Lit::from_var(1, false)),
                ],
                3,
                start,
            ));
            assert_eq!(
                lowered_degree(general, &amount),
                BigInt::from(start) - &amount,
                "lowering a general constraint of degree {start} by {amount}"
            );
        }
    }
}

/// The degree is not the whole result: `lower_rhs` also chooses the
/// representation, and `PBConstraintEnum` compares by variant.
///
/// Every other assertion in this file reads only the degree, so reverting the
/// `into_smallest_type()` at the end of `GeneralPBConstraint::lower_rhs` leaves
/// the whole workspace suite green — and no `.pbp` can tell the difference
/// either, because `PolRule::compute` re-narrows its final stack top anyway.
/// So the variant is pinned here, which is the only place that can see it.
#[test]
fn general_lower_rhs_escalation_hands_back_the_smallest_representation() {
    let mut general = PBConstraintEnum::from(GeneralPBConstraint::<i64>::from_terms(
        vec![
            GeneralPBTerm::new(2, Lit::from_var(0, false)),
            GeneralPBTerm::new(1, Lit::from_var(1, false)),
        ],
        3,
        1,
    ));
    // A degree of `1 - 2^64` overflows `i64` but fits `i128` comfortably.
    let lowered = general
        .lower_rhs(&(BigInt::from(u64::MAX) + BigInt::one()))
        .expect("the escalation must hand the lowered constraint back");
    assert_eq!(
        degree_of(&lowered),
        BigInt::one() - (BigInt::from(u64::MAX) + BigInt::one())
    );
    assert!(
        matches!(lowered, PBConstraintEnum::GeneralPBI128(_)),
        "a lowered degree that fits i128 must not stay pinned at BigInt, got {lowered:?}"
    );

    // The demotion arm: all-one coefficients come back as a cardinality rather
    // than a general constraint at all.
    let mut ones = PBConstraintEnum::from(GeneralPBConstraint::<i64>::from_terms(
        vec![
            GeneralPBTerm::new(1, Lit::from_var(0, false)),
            GeneralPBTerm::new(1, Lit::from_var(1, false)),
        ],
        2,
        1,
    ));
    let lowered_ones = ones
        .lower_rhs(&(BigInt::from(i64::MAX) + BigInt::one()))
        .expect("the escalation must hand the lowered constraint back");
    assert!(
        matches!(lowered_ones, PBConstraintEnum::Cardinality(_)),
        "an all-ones constraint must come back as a cardinality, got {lowered_ones:?}"
    );
}

#[test]
fn lower_rhs_repeated_underflow_keeps_accumulating() {
    // Two lowerings by `i64::MAX` from degree 1: the second one is the step
    // that used to be a no-op, leaving constraint 3 byte-identical to 2.
    let mut constraint = PBConstraintEnum::from(Clause::from_lits(lits()));
    let amount = BigInt::from(i64::MAX);
    if let Some(replacement) = constraint.lower_rhs(&amount) {
        constraint = replacement;
    }
    assert_eq!(degree_of(&constraint), BigInt::one() - &amount);
    if let Some(replacement) = constraint.lower_rhs(&amount) {
        constraint = replacement;
    }
    assert_eq!(
        degree_of(&constraint),
        BigInt::one() - &amount - &amount,
        "the second lowering must not be dropped"
    );
}

// ---------------------------------------------------------------------------
// Division and MIR: wide intermediates and oversized divisors.
// ---------------------------------------------------------------------------

/// `2^127`, the smallest divisor that does not fit into an `i128` constraint.
fn oversized_divisor_i128() -> BigInt {
    BigInt::from(i128::MAX as u128 + 1)
}

/// The four `pol` operators that divide a degree: `d`, `c`, `n`, `m`.
#[derive(Clone, Copy, Debug)]
enum DivideRule {
    NormalizedDiv,
    VariableDiv,
    NormalizedMir,
    VariableMir,
}

const DIVIDE_RULES: [DivideRule; 4] = [
    DivideRule::NormalizedDiv,
    DivideRule::VariableDiv,
    DivideRule::NormalizedMir,
    DivideRule::VariableMir,
];

/// Apply `rule` to a [`Cardinality`], returning whatever representation it ended up in.
fn divide_cardinality(
    rule: DivideRule,
    lits: Vec<Lit>,
    degree: i64,
    divisor: &BigInt,
) -> PBConstraintEnum {
    let mut constraint = Cardinality::from_lits(lits, degree);
    let replacement = match rule {
        DivideRule::NormalizedDiv => {
            constraint.normalized_form_div(divisor);
            None
        }
        DivideRule::VariableDiv => constraint.variable_form_div(divisor),
        DivideRule::NormalizedMir => constraint.normalized_form_mir(divisor),
        DivideRule::VariableMir => constraint.variable_form_mir(divisor),
    };
    replacement.unwrap_or_else(|| constraint.into_smallest_type())
}

/// Apply `rule` to a [`GeneralPBConstraint`], returning whatever representation it ended up in.
fn divide_general<N>(
    rule: DivideRule,
    mut constraint: GeneralPBConstraint<N>,
    divisor: &BigInt,
) -> PBConstraintEnum
where
    N: Int,
    PBConstraintEnum: From<GeneralPBConstraint<N>>,
{
    let replacement = match rule {
        DivideRule::NormalizedDiv => {
            constraint.normalized_form_div(divisor);
            None
        }
        DivideRule::VariableDiv => constraint.variable_form_div(divisor),
        DivideRule::NormalizedMir => constraint.normalized_form_mir(divisor),
        DivideRule::VariableMir => constraint.variable_form_mir(divisor),
    };
    replacement.unwrap_or_else(|| constraint.into_smallest_type())
}

/// The same cardinality constraint as an arbitrary-precision oracle: same rule, same code, but
/// in a width that cannot wrap and whose divisor never has to be approximated.
fn cardinality_oracle(lits: &[Lit], degree: i64) -> GeneralPBConstraint<BigInt> {
    GeneralPBConstraint::<BigInt>::from_terms(
        lits.iter()
            .map(|lit| GeneralPBTerm::new(BigInt::one(), *lit))
            .collect(),
        BigInt::from(lits.len() as i64),
        BigInt::from(degree),
    )
}

#[test]
fn cardinality_oversized_divisor_agrees_with_the_exact_quotient() {
    // Every one of `d`, `c`, `n` and `m` used to divide by `i64::MAX` instead of by the real
    // divisor once the divisor stopped fitting into an `i64`. That is faithful only while
    // `|A| < i64::MAX`: at `A == -i64::MAX` it yields `ceil(A / i64::MAX) == -1` where the rule's
    // quotient is `0`, so the checker stored `>= -1` and then rejected the proof for writing down
    // the `>= 0` the rule actually derives.
    let positive = vec![Lit::from_var(0, false), Lit::from_var(1, false)];
    let mixed = vec![
        Lit::from_var(0, false),
        Lit::from_var(1, true),
        Lit::from_var(2, false),
    ];

    for lits in [positive, mixed] {
        for degree in [i64::MIN, -i64::MAX, -1, 0, 1, i64::MAX] {
            for divisor in [
                oversized_divisor(),
                BigInt::from(u64::MAX) + BigInt::one(),
                oversized_divisor_i128(),
                // Control: the largest divisor that still fits, i.e. the branch that was always
                // exact. The two branches must not disagree about the same rule.
                largest_fitting_divisor(),
            ] {
                for rule in DIVIDE_RULES {
                    let live = divide_cardinality(rule, lits.clone(), degree, &divisor);
                    let oracle = divide_general(rule, cardinality_oracle(&lits, degree), &divisor);
                    assert_eq!(
                        degree_of(&live),
                        degree_of(&oracle),
                        "{rule:?} of a cardinality of degree {degree} by {divisor}"
                    );
                    for lit in &lits {
                        assert_eq!(
                            coeff_of(&live, *lit),
                            coeff_of(&oracle, *lit),
                            "{rule:?} coefficient of {lit:?} at degree {degree} by {divisor}"
                        );
                    }
                }
            }
        }
    }
}

#[test]
fn cardinality_oversized_divisor_of_minimal_degree_is_not_weakened() {
    // The exact values behind the differential test above, so a broken oracle cannot make it
    // pass vacuously. `A == -i64::MAX` is strictly inside `(-d, 0]` for every oversized `d`, so
    // the quotient is 0; `A == i64::MIN == -d` for `d == 2^63` is the one place it is `-1`.
    let lits = vec![Lit::from_var(0, false), Lit::from_var(1, false)];
    for rule in DIVIDE_RULES {
        assert_eq!(
            degree_of(&divide_cardinality(
                rule,
                lits.clone(),
                -i64::MAX,
                &oversized_divisor()
            )),
            BigInt::from(0),
            "{rule:?} at A = -i64::MAX must have quotient 0, not -1"
        );
    }
    // `c`/`d` at `A == -d`: the quotient really is `-1` here, and the MIR rules return the
    // trivial constraint because the remainder is zero.
    for rule in [DivideRule::NormalizedDiv, DivideRule::VariableDiv] {
        assert_eq!(
            degree_of(&divide_cardinality(
                rule,
                lits.clone(),
                i64::MIN,
                &oversized_divisor()
            )),
            BigInt::from(-1),
            "{rule:?} at A = -d must have quotient -1"
        );
    }
}

#[test]
fn general_div_oversized_divisor_of_minimal_degree_is_not_strengthened() {
    // The mirror image in `GeneralPBConstraint`: the fallback clamped the quotient to
    // `A.is_positive()`, which is `0` at `A == i64::MIN` where the real quotient is `-1`. That
    // errs on the *stronger* side — it stays sound only because the surviving coefficients are
    // all `1`, so `>= 0` is still trivially true — but it is not the constraint `d`/`c` define,
    // and `--kernel-verify` rejects the valid proof over it.
    //
    // `2 x1 + 1 x2 >= i64::MIN` divided by `2^63`: normalized form.
    let normalized = GeneralPBConstraint::<i64>::from_terms(
        vec![
            GeneralPBTerm::new(2, Lit::from_var(0, false)),
            GeneralPBTerm::new(1, Lit::from_var(1, false)),
        ],
        3,
        i64::MIN,
    );
    assert_eq!(
        degree_of(&divide_general(
            DivideRule::NormalizedDiv,
            normalized,
            &oversized_divisor()
        )),
        BigInt::from(-1)
    );

    // `(i64::MAX - 1) ~x1 + 1 x2 >= -2` has variable-form degree `-2 - (i64::MAX - 1)`, which is
    // exactly `i64::MIN`, and the coefficient sum still fits: variable form.
    let variable = GeneralPBConstraint::<i64>::from_terms(
        vec![
            GeneralPBTerm::new(i64::MAX - 1, Lit::from_var(0, true)),
            GeneralPBTerm::new(1, Lit::from_var(1, false)),
        ],
        i64::MAX,
        -2,
    );
    assert_eq!(
        degree_of(&divide_general(
            DivideRule::VariableDiv,
            variable,
            &oversized_divisor()
        )),
        BigInt::from(-1)
    );

    // The same two at the `i128` tier, where the boundary is `A == i128::MIN, d == 2^127`.
    let normalized_i128 = GeneralPBConstraint::<i128>::from_terms(
        vec![
            GeneralPBTerm::new(2, Lit::from_var(0, false)),
            GeneralPBTerm::new(1, Lit::from_var(1, false)),
        ],
        3,
        i128::MIN,
    );
    assert_eq!(
        degree_of(&divide_general(
            DivideRule::NormalizedDiv,
            normalized_i128,
            &oversized_divisor_i128()
        )),
        BigInt::from(-1)
    );
    let variable_i128 = GeneralPBConstraint::<i128>::from_terms(
        vec![
            GeneralPBTerm::new(i128::MAX - 1, Lit::from_var(0, true)),
            GeneralPBTerm::new(1, Lit::from_var(1, false)),
        ],
        i128::MAX,
        -2,
    );
    assert_eq!(
        degree_of(&divide_general(
            DivideRule::VariableDiv,
            variable_i128,
            &oversized_divisor_i128()
        )),
        BigInt::from(-1)
    );
}

#[test]
fn variable_form_mir_wide_quotient_does_not_overflow() {
    // `i64::MAX ~x1 >= 0` cut by `d = i64::MAX - 1`. The negated term's new coefficient is
    // `ceil(a / d) * r - min((-a) mod d, r) = 2r - r = r`, which fits — but the leading product
    // `2r` is `i64::MAX + r - 1`, which does not. Both wraps used to cancel; with overflow
    // checks on, the release binary aborted on this valid one-line proof.
    let divisor = BigInt::from(i64::MAX - 1);
    let mut narrow = GeneralPBConstraint::<i64>::from_terms(
        vec![GeneralPBTerm::new(i64::MAX, Lit::from_var(0, true))],
        i64::MAX,
        0,
    );
    let mut oracle = GeneralPBConstraint::<BigInt>::from_terms(
        vec![GeneralPBTerm::new(
            BigInt::from(i64::MAX),
            Lit::from_var(0, true),
        )],
        BigInt::from(i64::MAX),
        BigInt::from(0),
    );

    assert!(narrow.variable_form_mir(&divisor).is_none());
    assert!(oracle.variable_form_mir(&divisor).is_none());

    assert_eq!(*narrow.get_degree(), 0);
    assert_eq!(
        *narrow.get_coeff(Lit::from_var(0, true)).unwrap(),
        i64::MAX - 2
    );
    assert_eq!(BigInt::from(*narrow.get_degree()), *oracle.get_degree());
    assert_eq!(
        BigInt::from(*narrow.get_coeff(Lit::from_var(0, true)).unwrap()),
        *oracle.get_coeff(Lit::from_var(0, true)).unwrap()
    );
}

#[test]
fn variable_form_mir_wide_quotient_does_not_overflow_i128() {
    // The same shape one tier up: the routine is generic, so `i128` had the identical abort.
    let divisor = BigInt::from(i128::MAX - 1);
    let mut narrow = GeneralPBConstraint::<i128>::from_terms(
        vec![GeneralPBTerm::new(i128::MAX, Lit::from_var(0, true))],
        i128::MAX,
        0,
    );
    let mut oracle = GeneralPBConstraint::<BigInt>::from_terms(
        vec![GeneralPBTerm::new(
            BigInt::from(i128::MAX),
            Lit::from_var(0, true),
        )],
        BigInt::from(i128::MAX),
        BigInt::from(0),
    );

    assert!(narrow.variable_form_mir(&divisor).is_none());
    assert!(oracle.variable_form_mir(&divisor).is_none());

    assert_eq!(*narrow.get_degree(), 0);
    assert_eq!(
        *narrow.get_coeff(Lit::from_var(0, true)).unwrap(),
        i128::MAX - 2
    );
    assert_eq!(BigInt::from(*narrow.get_degree()), *oracle.get_degree());
    assert_eq!(
        BigInt::from(*narrow.get_coeff(Lit::from_var(0, true)).unwrap()),
        *oracle.get_coeff(Lit::from_var(0, true)).unwrap()
    );
}

#[test]
fn division_rules_agree_with_the_exact_oracle_at_the_top_of_the_range() {
    // The corpus could not have caught the MIR overflow: every shipped instance produces
    // byte-identical verdicts with and without overflow checks. Only the region where the
    // per-term intermediate `ceil(a / d) * r` can exceed `N::MAX` fires it, so draw the
    // coefficient and the divisor from the top of the range deliberately. Deterministic seed:
    // this is a pin, not a fuzzer.
    use rand::{RngExt, SeedableRng};
    let mut rng = rand::rngs::StdRng::seed_from_u64(0x5eed_0d19);

    for _ in 0..20_000 {
        // One dominant coefficient near `i64::MAX` plus a small spectator, so the coefficient
        // sum still fits the narrow type while `a + r` does not.
        let dominant = rng.random_range((i64::MAX / 2)..=(i64::MAX - 1024));
        let spectator = rng.random_range(1_i64..=1024);
        let terms = vec![
            GeneralPBTerm::new(dominant, Lit::from_var(0, rng.random_bool(0.5))),
            GeneralPBTerm::new(spectator, Lit::from_var(1, rng.random_bool(0.5))),
        ];
        let coeff_sum = dominant + spectator;
        let degree = rng.random_range(i64::MIN..=coeff_sum);
        let divisor = BigInt::from(rng.random_range(2_i64..=i64::MAX));

        let oracle_terms: Vec<GeneralPBTerm<BigInt>> = terms
            .iter()
            .map(|term| GeneralPBTerm::new(BigInt::from(*term.get_coeff()), term.get_lit()))
            .collect();

        for rule in DIVIDE_RULES {
            let narrow = GeneralPBConstraint::<i64>::from_terms(terms.clone(), coeff_sum, degree);
            let oracle = GeneralPBConstraint::<BigInt>::from_terms(
                oracle_terms.clone(),
                BigInt::from(coeff_sum),
                BigInt::from(degree),
            );
            let live = divide_general(rule, narrow, &divisor);
            let exact = divide_general(rule, oracle, &divisor);
            assert_eq!(
                degree_of(&live),
                degree_of(&exact),
                "{rule:?} degree, coeffs {terms:?} degree {degree} divisor {divisor}"
            );
            for term in &terms {
                assert_eq!(
                    coeff_of(&live, term.get_lit()),
                    coeff_of(&exact, term.get_lit()),
                    "{rule:?} coefficient of {:?}, coeffs {terms:?} degree {degree} divisor {divisor}",
                    term.get_lit()
                );
            }
        }
    }
}
