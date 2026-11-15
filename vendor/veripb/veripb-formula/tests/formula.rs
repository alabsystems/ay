use veripb_formula::prelude::*;

#[test]
fn create_empty_formula() {
    assert_eq!(Formula::default().len(), 0);
}

#[test]
fn creat_empty_formula_with_capacity() {
    let formula = Formula::with_capacity(100_000);

    assert_eq!(formula.len(), 0);
    assert_eq!(formula.capacity(), 100_000);
}

#[test]
fn add_constraints_to_formula() {
    let mut formula = Formula::default();

    formula
        .constraints
        .push(Clause::from_lits(vec![Lit::from_var(0, false), Lit::from_var(1, true)]).into());
    formula.constraints.push(
        GeneralPBConstraint::<i64>::from_terms(
            vec![
                GeneralPBTerm::new(1342, Lit::from_var(1, false)),
                GeneralPBTerm::new(312, Lit::from_var(2, true)),
            ],
            1654,
            432,
        )
        .into(),
    );

    assert_eq!(formula.len(), 2);

    assert!(matches!(
        formula.constraints[0],
        PBConstraintEnum::Clause(..)
    ));
    assert!(matches!(
        formula.constraints[1],
        PBConstraintEnum::GeneralPBI64(..)
    ));
}
