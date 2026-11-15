use std::rc::Rc;

use veripb_formula::prelude::*;
use veripb_propagator::{
    cardinality_watcher::CardinalityWatcher,
    clause_watcher::ClauseWatcher,
    general_pb_watcher::GeneralPBWatcher,
    propagator::{PropagationResult, Propagator},
    trail::{Propagation, Reason, Trail},
};

const NUM_VARS: usize = 5;

#[test]
fn clause_propagator_to_conflict() {
    // Initialize propagator
    let mut propagator: Propagator<ClauseWatcher> = Propagator::with_size(NUM_VARS);
    let clause1 = Rc::new(DBConstraint::from(Clause::from_lits(vec![
        Lit::from_var(0, false),
        Lit::from_var(1, true),
    ])));
    propagator
        .add(&clause1)
        .expect("Adding clause1 should be fine");
    let clause2 = Rc::new(DBConstraint::from(Clause::from_lits(vec![
        Lit::from_var(1, false),
        Lit::from_var(2, true),
    ])));
    propagator
        .add(&clause2)
        .expect("Adding clause2 should be fine");
    let clause3 = Rc::new(DBConstraint::from(Clause::from_lits(vec![
        Lit::from_var(2, false),
        Lit::from_var(3, true),
    ])));
    propagator
        .add(&clause3)
        .expect("Adding clause3 should be fine");
    let clause4 = Rc::new(DBConstraint::from(Clause::from_lits(vec![
        Lit::from_var(3, false),
        Lit::from_var(4, true),
    ])));
    propagator
        .add(&clause4)
        .expect("Adding clause4 should be fine");
    let clause5 = Rc::new(DBConstraint::from(Clause::from_lits(vec![
        Lit::from_var(4, false),
        Lit::from_var(0, false),
    ])));
    propagator
        .add(&clause5)
        .expect("Adding clause5 should be fine");

    // Nothing should propagate, when the trail is empty.
    let mut trail = Trail::with_size(NUM_VARS);
    assert_eq!(
        propagator.propagate(&mut trail, false, false),
        PropagationResult::Unknown
    );
    assert_eq!(trail.len(), 0);

    // Assuming the variable with index 0 to false should propagate to conflict.
    assert!(
        trail
            .push(
                Propagation::new(Lit::from_var(0, true), Reason::Assumption),
                false
            )
            .is_ok()
    );
    let result = propagator.propagate(&mut trail, false, false);

    // Check that we have reached a conflict.
    assert_eq!(result, PropagationResult::Conflict);
}

#[test]
fn clause_propagator_to_unknown() {
    // Initialize propagator
    let mut propagator: Propagator<ClauseWatcher> = Propagator::with_size(NUM_VARS);
    let clause1 = Rc::new(DBConstraint::from(Clause::from_lits(vec![
        Lit::from_var(0, false),
        Lit::from_var(1, true),
    ])));
    propagator
        .add(&clause1)
        .expect("Adding clause1 should be fine");
    let clause2 = Rc::new(DBConstraint::from(Clause::from_lits(vec![
        Lit::from_var(1, false),
        Lit::from_var(2, true),
    ])));
    propagator
        .add(&clause2)
        .expect("Adding clause2 should be fine");
    let clause3 = Rc::new(DBConstraint::from(Clause::from_lits(vec![
        Lit::from_var(2, false),
        Lit::from_var(3, true),
    ])));
    propagator
        .add(&clause3)
        .expect("Adding clause3 should be fine");

    // Propagate clauses due to trail.
    let mut trail = Trail::with_size(NUM_VARS);
    assert!(
        trail
            .push(
                Propagation::new(Lit::from_var(0, true), Reason::Assumption),
                false
            )
            .is_ok()
    );
    let result = propagator.propagate(&mut trail, false, false);

    // Check that the trail has been correctly populated.
    assert_eq!(result, PropagationResult::Unknown);
    assert_eq!(trail.pop().unwrap().lit, Lit::from_var(3, true));
    assert_eq!(trail.pop().unwrap().lit, Lit::from_var(2, true));
    assert_eq!(trail.pop().unwrap().lit, Lit::from_var(1, true));
}

#[test]
fn clause_propagator_continue_propagation() {
    // Initialize propagator
    let mut propagator: Propagator<ClauseWatcher> = Propagator::with_size(NUM_VARS);
    let clause1 = Rc::new(DBConstraint::from(Clause::from_lits(vec![
        Lit::from_var(0, false),
        Lit::from_var(1, true),
    ])));
    propagator
        .add(&clause1)
        .expect("Adding clause1 should be fine");
    let clause2 = Rc::new(DBConstraint::from(Clause::from_lits(vec![
        Lit::from_var(1, false),
        Lit::from_var(2, true),
        Lit::from_var(4, false),
    ])));
    propagator
        .add(&clause2)
        .expect("Adding clause2 should be fine");
    let clause3 = Rc::new(DBConstraint::from(Clause::from_lits(vec![
        Lit::from_var(1, false),
        Lit::from_var(2, false),
        Lit::from_var(4, false),
    ])));
    propagator
        .add(&clause3)
        .expect("Adding clause3 should be fine");

    // Propagate clauses due to trail.
    let mut trail = Trail::with_size(NUM_VARS);
    assert!(
        trail
            .push(
                Propagation::new(Lit::from_var(0, true), Reason::Assumption),
                false
            )
            .is_ok()
    );
    let result = propagator.propagate(&mut trail, false, false);

    // Check that the trail has been correctly populated.
    assert_eq!(result, PropagationResult::Unknown);

    // Add another literal to trail.
    assert!(
        trail
            .push(
                Propagation::new(Lit::from_var(4, true), Reason::Assumption),
                false
            )
            .is_ok()
    );
    let result = propagator.propagate(&mut trail, false, false);

    // Result should be conflicting.
    assert_eq!(result, PropagationResult::Conflict);
}

#[test]
fn card_propagator_to_conflict() {
    // Initialize propagator
    let mut propagator: Propagator<CardinalityWatcher> = Propagator::with_size(NUM_VARS);
    let card1 = Rc::new(DBConstraint::from(Cardinality::from_lits(
        vec![
            Lit::from_var(0, false),
            Lit::from_var(1, true),
            Lit::from_var(2, true),
        ],
        2,
    )));
    propagator.add(&card1).expect("Adding card1 should be fine");
    let card2 = Rc::new(DBConstraint::from(Cardinality::from_lits(
        vec![
            Lit::from_var(2, false),
            Lit::from_var(3, true),
            Lit::from_var(4, true),
        ],
        2,
    )));
    propagator.add(&card2).expect("Adding card2 should be fine");
    let card3 = Rc::new(DBConstraint::from(Cardinality::from_lits(
        vec![
            Lit::from_var(3, false),
            Lit::from_var(4, true),
            Lit::from_var(0, false),
        ],
        2,
    )));
    propagator.add(&card3).expect("Adding card3 should be fine");

    // Propagate clauses due to trail.
    let mut trail = Trail::with_size(NUM_VARS);
    assert!(
        trail
            .push(
                Propagation::new(Lit::from_var(0, true), Reason::Assumption),
                false
            )
            .is_ok()
    );
    let result = propagator.propagate(&mut trail, false, false);

    // Check that we have reached a conflict.
    assert_eq!(result, PropagationResult::Conflict);
}

#[test]
fn card_propagator_to_unknown() {
    // Initialize propagator
    let mut propagator: Propagator<CardinalityWatcher> = Propagator::with_size(NUM_VARS);
    let card1 = Rc::new(DBConstraint::from(Cardinality::from_lits(
        vec![
            Lit::from_var(0, false),
            Lit::from_var(1, true),
            Lit::from_var(2, true),
        ],
        2,
    )));
    propagator.add(&card1).expect("Adding card1 should be fine");
    let card2 = Rc::new(DBConstraint::from(Cardinality::from_lits(
        vec![
            Lit::from_var(2, false),
            Lit::from_var(3, true),
            Lit::from_var(4, true),
        ],
        2,
    )));
    propagator.add(&card2).expect("Adding card2 should be fine");

    // Propagate clauses due to trail.
    let mut trail = Trail::with_size(NUM_VARS);
    assert!(
        trail
            .push(
                Propagation::new(Lit::from_var(0, true), Reason::Assumption),
                false
            )
            .is_ok()
    );
    let result = propagator.propagate(&mut trail, false, false);

    // Check that we have reached a no conflict and the trail is as expected.
    assert_eq!(result, PropagationResult::Unknown);
    let trail_end = &[
        trail.pop().unwrap().lit,
        trail.pop().unwrap().lit,
        trail.pop().unwrap().lit,
        trail.pop().unwrap().lit,
    ];
    assert!(trail_end.contains(&Lit::from_var(1, true)));
    assert!(trail_end.contains(&Lit::from_var(2, true)));
    assert!(trail_end.contains(&Lit::from_var(3, true)));
    assert!(trail_end.contains(&Lit::from_var(4, true)));
}

#[test]
fn card_propagator_to_unknown_only_update() {
    // Initialize propagator
    let mut propagator: Propagator<CardinalityWatcher> = Propagator::with_size(NUM_VARS);
    let card1 = Rc::new(DBConstraint::from(Cardinality::from_lits(
        vec![
            Lit::from_var(0, false),
            Lit::from_var(1, true),
            Lit::from_var(2, true),
        ],
        2,
    )));
    propagator.add(&card1).expect("Adding card1 should be fine");
    let card2 = Rc::new(DBConstraint::from(Cardinality::from_lits(
        vec![
            Lit::from_var(1, true),
            Lit::from_var(2, false),
            Lit::from_var(3, true),
            Lit::from_var(4, true),
        ],
        2,
    )));
    propagator.add(&card2).expect("Adding card2 should be fine");

    // Propagate clauses due to trail.
    let mut trail = Trail::with_size(NUM_VARS);
    assert!(
        trail
            .push(
                Propagation::new(Lit::from_var(0, true), Reason::Assumption),
                false
            )
            .is_ok()
    );
    let result = propagator.propagate(&mut trail, false, false);

    // Check that we have reached a no conflict and the trail is as expected.
    assert_eq!(result, PropagationResult::Unknown);
    let trail_end = &[trail.pop().unwrap().lit, trail.pop().unwrap().lit];
    assert!(trail_end.contains(&Lit::from_var(1, true)));
    assert!(trail_end.contains(&Lit::from_var(2, true)));
}

#[test]
fn card_propagator_continue_propagation() {
    // Initialize propagator
    let mut propagator: Propagator<CardinalityWatcher> = Propagator::with_size(NUM_VARS);
    let card1 = Rc::new(DBConstraint::from(Cardinality::from_lits(
        vec![
            Lit::from_var(0, false),
            Lit::from_var(1, true),
            Lit::from_var(2, true),
        ],
        2,
    )));
    propagator.add(&card1).expect("Adding card1 should be fine");
    let card2 = Rc::new(DBConstraint::from(Cardinality::from_lits(
        vec![
            Lit::from_var(1, true),
            Lit::from_var(2, false),
            Lit::from_var(3, true),
            Lit::from_var(4, false),
        ],
        2,
    )));
    propagator.add(&card2).expect("Adding card2 should be fine");
    let card3 = Rc::new(DBConstraint::from(Cardinality::from_lits(
        vec![
            Lit::from_var(2, true),
            Lit::from_var(3, false),
            Lit::from_var(4, false),
        ],
        2,
    )));
    propagator.add(&card3).expect("Adding card3 should be fine");

    // Propagate clauses due to trail.
    let mut trail = Trail::with_size(NUM_VARS);
    assert!(
        trail
            .push(
                Propagation::new(Lit::from_var(0, true), Reason::Assumption),
                false
            )
            .is_ok()
    );
    let result = propagator.propagate(&mut trail, false, false);

    // Check that we have no conflict yet.
    assert_eq!(result, PropagationResult::Unknown);

    // Add more assignments to trail and propagate.
    assert!(
        trail
            .push(
                Propagation::new(Lit::from_var(4, true), Reason::Assumption),
                false
            )
            .is_ok()
    );
    let result = propagator.propagate(&mut trail, false, false);

    // We should now be conflicting.
    assert_eq!(result, PropagationResult::Conflict);
}

#[test]
fn general_constraint_propagator_to_conflict() {
    // Initialize propagator
    let mut propagator: Propagator<GeneralPBWatcher<i64>> = Propagator::with_size(NUM_VARS);
    let constraint1 = Rc::new(DBConstraint::from(GeneralPBConstraint::<i64>::from_terms(
        vec![
            GeneralPBTerm::new(1, Lit::from_var(0, false)),
            GeneralPBTerm::new(2, Lit::from_var(1, false)),
            GeneralPBTerm::new(3, Lit::from_var(2, false)),
        ],
        6,
        3,
    )));
    propagator
        .add(&constraint1)
        .expect("Adding constraint1 should be fine");
    let constraint2 = Rc::new(DBConstraint::from(GeneralPBConstraint::<i64>::from_terms(
        vec![
            GeneralPBTerm::new(1, Lit::from_var(2, true)),
            GeneralPBTerm::new(2, Lit::from_var(3, false)),
            GeneralPBTerm::new(3, Lit::from_var(4, false)),
        ],
        6,
        3,
    )));
    propagator
        .add(&constraint2)
        .expect("Adding constraint2 should be fine");
    let constraint3 = Rc::new(DBConstraint::from(GeneralPBConstraint::<i64>::from_terms(
        vec![
            GeneralPBTerm::new(1, Lit::from_var(2, true)),
            GeneralPBTerm::new(2, Lit::from_var(3, false)),
            GeneralPBTerm::new(3, Lit::from_var(4, true)),
        ],
        6,
        3,
    )));
    propagator
        .add(&constraint3)
        .expect("Adding constraint3 should be fine");

    // Propagate clauses due to trail.
    let mut trail = Trail::with_size(NUM_VARS);
    assert!(
        trail
            .push(
                Propagation::new(Lit::from_var(0, true), Reason::Assumption),
                false
            )
            .is_ok()
    );
    let result = propagator.propagate(&mut trail, false, false);

    // Check that we have reached a conflict.
    assert_eq!(result, PropagationResult::Conflict);
}

#[test]
fn general_constraint_propagator_to_unknown1() {
    // Initialize propagator
    let mut propagator: Propagator<GeneralPBWatcher<i64>> = Propagator::with_size(NUM_VARS);
    let constraint1 = Rc::new(DBConstraint::from(GeneralPBConstraint::<i64>::from_terms(
        vec![
            GeneralPBTerm::new(1, Lit::from_var(0, false)),
            GeneralPBTerm::new(2, Lit::from_var(1, false)),
            GeneralPBTerm::new(3, Lit::from_var(2, false)),
        ],
        6,
        3,
    )));
    propagator
        .add(&constraint1)
        .expect("Adding constraint1 should be fine");
    let constraint2 = Rc::new(DBConstraint::from(GeneralPBConstraint::<i64>::from_terms(
        vec![
            GeneralPBTerm::new(1, Lit::from_var(2, true)),
            GeneralPBTerm::new(2, Lit::from_var(3, false)),
            GeneralPBTerm::new(3, Lit::from_var(4, false)),
        ],
        6,
        3,
    )));
    propagator
        .add(&constraint2)
        .expect("Adding constraint2 should be fine");

    // Propagate clauses due to trail.
    let mut trail = Trail::with_size(NUM_VARS);
    assert!(
        trail
            .push(
                Propagation::new(Lit::from_var(0, true), Reason::Assumption),
                false
            )
            .is_ok()
    );
    let result = propagator.propagate(&mut trail, false, false);

    // Check that we have reached a no conflict and the trail is as expected.
    assert_eq!(result, PropagationResult::Unknown);
    assert_eq!(trail.pop().unwrap().lit, Lit::from_var(4, false));
    assert_eq!(trail.pop().unwrap().lit, Lit::from_var(2, false));
    assert_eq!(trail.pop().unwrap().lit, Lit::from_var(0, true));
}

#[test]
fn general_constraint_propagator_to_unknown2() {
    // Initialize propagator
    let mut propagator: Propagator<GeneralPBWatcher<i64>> = Propagator::with_size(NUM_VARS);
    let constraint1 = Rc::new(DBConstraint::from(GeneralPBConstraint::<i64>::from_terms(
        vec![
            GeneralPBTerm::new(1, Lit::from_var(0, false)),
            GeneralPBTerm::new(2, Lit::from_var(1, false)),
            GeneralPBTerm::new(3, Lit::from_var(2, false)),
        ],
        6,
        3,
    )));
    propagator
        .add(&constraint1)
        .expect("Adding constraint1 should be fine");
    let constraint2 = Rc::new(DBConstraint::from(GeneralPBConstraint::<i64>::from_terms(
        vec![
            GeneralPBTerm::new(1, Lit::from_var(2, true)),
            GeneralPBTerm::new(2, Lit::from_var(3, false)),
            GeneralPBTerm::new(3, Lit::from_var(4, false)),
        ],
        6,
        4,
    )));
    propagator
        .add(&constraint2)
        .expect("Adding constraint2 should be fine");

    // Propagate clauses due to trail.
    let mut trail = Trail::with_size(NUM_VARS);
    assert!(
        trail
            .push(
                Propagation::new(Lit::from_var(0, true), Reason::Assumption),
                false
            )
            .is_ok()
    );
    let result = propagator.propagate(&mut trail, false, false);

    // Check that we have reached a no conflict and the assignment is as expected.
    assert_eq!(result, PropagationResult::Unknown);
    assert_eq!(trail.assignment.get_value(4), BoolValue::Assigned(true));
    assert_eq!(trail.assignment.get_value(3), BoolValue::Assigned(true));
    assert_eq!(trail.assignment.get_value(2), BoolValue::Assigned(true));
    assert_eq!(trail.assignment.get_value(0), BoolValue::Assigned(false));
}

#[test]
fn general_constraint_propagator_continue_after_partial_propagation() {
    // Initialize propagator
    let mut propagator: Propagator<GeneralPBWatcher<i64>> = Propagator::with_size(NUM_VARS);
    let constraint1 = Rc::new(DBConstraint::from(GeneralPBConstraint::<i64>::from_terms(
        vec![
            GeneralPBTerm::new(1, Lit::from_var(0, false)),
            GeneralPBTerm::new(2, Lit::from_var(1, false)),
            GeneralPBTerm::new(3, Lit::from_var(2, false)),
        ],
        6,
        3,
    )));
    propagator
        .add(&constraint1)
        .expect("Adding constraint1 should be fine");
    let constraint2 = Rc::new(DBConstraint::from(GeneralPBConstraint::<i64>::from_terms(
        vec![
            GeneralPBTerm::new(1, Lit::from_var(2, true)),
            GeneralPBTerm::new(2, Lit::from_var(3, false)),
            GeneralPBTerm::new(3, Lit::from_var(4, false)),
        ],
        6,
        4,
    )));
    propagator
        .add(&constraint2)
        .expect("Adding constraint2 should be fine");
    let constraint3 = Rc::new(DBConstraint::from(GeneralPBConstraint::<i64>::from_terms(
        vec![
            GeneralPBTerm::new(1, Lit::from_var(2, true)),
            GeneralPBTerm::new(2, Lit::from_var(4, false)),
            GeneralPBTerm::new(3, Lit::from_var(3, true)),
        ],
        6,
        3,
    )));
    propagator
        .add(&constraint3)
        .expect("Adding constraint3 should be fine");

    // Propagate clauses due to trail.
    let mut trail = Trail::with_size(NUM_VARS);
    let result = propagator.propagate(&mut trail, false, false);

    // Check that we have reached a no conflict and the trail is as expected.
    assert_eq!(result, PropagationResult::Unknown);
    assert_eq!(trail.assignment.get_value(4), BoolValue::Assigned(true));

    // Add literal to trail and propagate again.
    assert!(
        trail
            .push(
                Propagation::new(Lit::from_var(0, true), Reason::Assumption),
                false
            )
            .is_ok()
    );
    let result = propagator.propagate(&mut trail, false, false);

    // The result of the propagation should be contradicting.
    assert_eq!(result, PropagationResult::Conflict);
}
