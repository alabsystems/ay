use std::rc::Rc;

use veripb_formula::prelude::*;
use veripb_propagator::{
    propagation_set::PropagationSet,
    propagator::PropagationResult,
    trail::{Propagation, Reason, Trail},
};

const NUM_VARS: usize = 6;

#[test]
fn mix_constraints_propagate_to_conflict() {
    let mut prop_set = PropagationSet::with_size(NUM_VARS);
    let clause = Rc::new(DBConstraint::from(Clause::from_lits(vec![
        Lit::from_var(0, false),
        Lit::from_var(1, true),
    ])));
    prop_set
        .add(&clause)
        .expect("Adding a clause to the propagation set should be fine");
    let card = Rc::new(DBConstraint::from(Cardinality::from_lits(
        vec![
            Lit::from_var(1, false),
            Lit::from_var(2, true),
            Lit::from_var(3, true),
        ],
        2,
    )));
    prop_set
        .add(&card)
        .expect("Adding a cardinality to the propagation set should be fine");
    let constraint = Rc::new(DBConstraint::from(GeneralPBConstraint::<i64>::from_terms(
        vec![
            GeneralPBTerm::new(1, Lit::from_var(2, false)),
            GeneralPBTerm::new(2, Lit::from_var(4, true)),
            GeneralPBTerm::new(3, Lit::from_var(3, false)),
        ],
        6,
        3,
    )));
    prop_set
        .add(&constraint)
        .expect("Adding a general PB constraint to the propagation set should be fine");

    // Propagating the set without any assumptions on the trail should not result on any further propagation.
    let mut trail = Trail::with_size(NUM_VARS);
    assert_eq!(
        prop_set.propagate(&mut trail, false),
        PropagationResult::Unknown
    );
    assert_eq!(trail.len(), 0);

    // Assuming the variable with index 0 to false should propagate to a conflict.
    assert!(
        trail
            .push(
                Propagation::new(Lit::from_var(0, true), Reason::Assumption),
                false
            )
            .is_ok()
    );
    assert_eq!(
        prop_set.propagate(&mut trail, false),
        PropagationResult::Conflict
    );
}

#[test]
fn mix_constraints_propagate_to_conflict_reverse_order() {
    let mut prop_set = PropagationSet::with_size(NUM_VARS);
    let clause = Rc::new(DBConstraint::from(Clause::from_lits(vec![
        Lit::from_var(3, false),
        Lit::from_var(4, false),
    ])));
    prop_set
        .add(&clause)
        .expect("Adding a clause to the propagation set should be fine");
    let card = Rc::new(DBConstraint::from(Cardinality::from_lits(
        vec![
            Lit::from_var(2, false),
            Lit::from_var(3, true),
            Lit::from_var(4, true),
        ],
        2,
    )));
    prop_set
        .add(&card)
        .expect("Adding a cardinality to the propagation set should be fine");
    let constraint = Rc::new(DBConstraint::from(GeneralPBConstraint::<i64>::from_terms(
        vec![
            GeneralPBTerm::new(1, Lit::from_var(0, false)),
            GeneralPBTerm::new(2, Lit::from_var(1, true)),
            GeneralPBTerm::new(3, Lit::from_var(2, true)),
        ],
        6,
        3,
    )));
    prop_set
        .add(&constraint)
        .expect("Adding a general PB constraint to the propagation set should be fine");

    // Propagating the set without any assumptions on the trail should not result on any further propagation.
    let mut trail = Trail::with_size(NUM_VARS);
    assert_eq!(
        prop_set.propagate(&mut trail, false),
        PropagationResult::Unknown
    );
    assert_eq!(trail.len(), 0);

    // Assuming the variable with index 0 to false should propagate to a conflict.
    assert!(
        trail
            .push(
                Propagation::new(Lit::from_var(0, true), Reason::Assumption),
                false
            )
            .is_ok()
    );
    assert_eq!(
        prop_set.propagate(&mut trail, false),
        PropagationResult::Conflict
    );
}

#[test]
fn mix_constraints_propagate_to_unknown() {
    let mut prop_set = PropagationSet::with_size(NUM_VARS);
    let clause = Rc::new(DBConstraint::from(Clause::from_lits(vec![
        Lit::from_var(4, false),
        Lit::from_var(5, false),
    ])));
    prop_set
        .add(&clause)
        .expect("Adding a clause to the propagation set should be fine");
    let card = Rc::new(DBConstraint::from(Cardinality::from_lits(
        vec![
            Lit::from_var(2, false),
            Lit::from_var(3, true),
            Lit::from_var(4, true),
        ],
        2,
    )));
    prop_set
        .add(&card)
        .expect("Adding a cardinality to the propagation set should be fine");
    let constraint = Rc::new(DBConstraint::from(GeneralPBConstraint::<i64>::from_terms(
        vec![
            GeneralPBTerm::new(1, Lit::from_var(0, false)),
            GeneralPBTerm::new(2, Lit::from_var(1, true)),
            GeneralPBTerm::new(3, Lit::from_var(2, true)),
        ],
        6,
        3,
    )));
    prop_set
        .add(&constraint)
        .expect("Adding a general PB constraint to the propagation set should be fine");

    // Propagating the set without any assumptions on the trail should not result on any further propagation.
    let mut trail = Trail::with_size(NUM_VARS);
    assert_eq!(
        prop_set.propagate(&mut trail, false),
        PropagationResult::Unknown
    );
    assert_eq!(trail.len(), 0);

    // Assuming the variable with index 0 to false should propagate to a conflict.
    assert!(
        trail
            .push(
                Propagation::new(Lit::from_var(0, true), Reason::Assumption),
                false
            )
            .is_ok()
    );
    assert_eq!(
        prop_set.propagate(&mut trail, false),
        PropagationResult::Unknown
    );

    // Check that trail contains the expected assignments.
    assert_eq!(trail.assignment.get_value(1), BoolValue::Unassigned);
    assert_eq!(trail.assignment.get_value(2), BoolValue::Assigned(false));
    assert_eq!(trail.assignment.get_value(3), BoolValue::Assigned(false));
    assert_eq!(trail.assignment.get_value(4), BoolValue::Assigned(false));
    assert_eq!(trail.assignment.get_value(5), BoolValue::Assigned(true));
}
