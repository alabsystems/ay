use veripb_formula::prelude::*;
use veripb_propagator::{
    general_pb_watcher::GeneralPBWatcher,
    watcher::{WatchInit, WatchUpdate, Watchable},
};

fn get_test_constraint() -> GeneralPBConstraint<i64> {
    // Constraint: neg(x0) + 2 x1 + 3 neg(x2) + 5 x3 + 4 neg(x4) >= 5
    GeneralPBConstraint::from_terms(
        vec![
            GeneralPBTerm::new(1, Lit::from_var(0, true)),
            GeneralPBTerm::new(2, Lit::from_var(1, false)),
            GeneralPBTerm::new(3, Lit::from_var(2, true)),
            GeneralPBTerm::new(5, Lit::from_var(3, false)),
            GeneralPBTerm::new(4, Lit::from_var(4, true)),
        ],
        15,
        5,
    )
}

#[test]
fn init_watcher() {
    let constraint = get_test_constraint();

    let watcher = GeneralPBWatcher::from_constraint(constraint);

    assert_eq!(watcher.max_coeff, 5);
    assert_eq!(watcher.watches_slack, -5)
}

#[test]
fn general_pb_init() {
    let constraint = get_test_constraint();
    let mut watcher = GeneralPBWatcher::from_constraint(constraint);
    let assign = Assignment::with_size(5);

    if let WatchInit::Watching {
        propagated,
        watches,
    } = watcher.init_watches(&assign)
    {
        assert!(watches.contains(&Lit::from_var(2, true)));
        assert!(watches.contains(&Lit::from_var(3, false)));
        assert!(watches.contains(&Lit::from_var(4, true)));
        assert_eq!(watches.len(), 3);
        assert_eq!(propagated.len(), 0);
    } else {
        panic!("Wrong type returned by init_watches")
    }

    assert_eq!(watcher.next_pos, 3);
    assert_eq!(watcher.watches_slack, 7); // 3 + 5 + 4 - 5
}

#[test]
fn general_pb_init_some_assignment() {
    let constraint = get_test_constraint();
    let mut watcher = GeneralPBWatcher::from_constraint(constraint);
    let mut assign = Assignment::with_size(5);
    assign.set_value(3, BoolValue::Assigned(true));
    assign.set_value(4, BoolValue::Assigned(true));

    if let WatchInit::Watching {
        propagated,
        watches,
    } = watcher.init_watches(&assign)
    {
        assert!(watches.contains(&Lit::from_var(1, false)));
        assert!(watches.contains(&Lit::from_var(2, true)));
        assert!(watches.contains(&Lit::from_var(3, false)));
        assert_eq!(watches.len(), 3);
        assert_eq!(propagated.len(), 0);
    } else {
        panic!("Wrong type returned by init_watches")
    }

    assert_eq!(watcher.next_pos, 4);
    assert_eq!(watcher.watches_slack, 5); // 2 + 3 + 5 - 5
}

#[test]
fn general_pb_init_propagation() {
    let constraint = get_test_constraint();
    let mut watcher = GeneralPBWatcher::from_constraint(constraint);
    let mut assign = Assignment::with_size(5);
    assign.set_value(3, BoolValue::Assigned(false));
    assign.set_value(4, BoolValue::Assigned(true));

    if let WatchInit::Watching {
        propagated,
        watches,
    } = watcher.init_watches(&assign)
    {
        assert!(watches.contains(&Lit::from_var(0, true)));
        assert!(watches.contains(&Lit::from_var(1, false)));
        assert!(watches.contains(&Lit::from_var(2, true)));
        assert!(watches.contains(&Lit::from_var(3, false)));
        assert!(propagated.contains(&Lit::from_var(1, false)));
        assert!(propagated.contains(&Lit::from_var(2, true)));
        assert_eq!(watches.len(), 4);
        assert_eq!(propagated.len(), 2);
    } else {
        panic!("Wrong type returned by init_watches")
    }

    assert_eq!(watcher.next_pos, 0);
    assert_eq!(watcher.watches_slack, 1); // 1 + 2 + 3 - 5
}

#[test]
fn general_pb_init_conflict_all() {
    let constraint = get_test_constraint();
    let mut watcher = GeneralPBWatcher::from_constraint(constraint);
    let mut assign = Assignment::with_size(5);
    assign.set_value(0, BoolValue::Assigned(true));
    assign.set_value(2, BoolValue::Assigned(true));
    assign.set_value(3, BoolValue::Assigned(false));
    assign.set_value(4, BoolValue::Assigned(true));

    assert_eq!(watcher.init_watches(&assign), WatchInit::Conflict);

    assert_eq!(watcher.next_pos, 0);
    assert_eq!(watcher.watches_slack, -5);
}

#[test]
fn general_pb_update_enough_watching() {
    // when assigning watches in coefficient order (large to small), WatchUpdate::None can only happen after a reset
    let constraint = get_test_constraint();
    let mut watcher = GeneralPBWatcher::from_constraint(constraint);
    let mut assign = Assignment::with_size(5);
    assign.set_value(4, BoolValue::Assigned(true));

    if let WatchInit::Watching {
        propagated,
        watches,
    } = watcher.init_watches(&assign)
    {
        assert!(watches.contains(&Lit::from_var(1, false)));
        assert!(watches.contains(&Lit::from_var(2, true)));
        assert!(watches.contains(&Lit::from_var(3, false)));
        assert_eq!(watches.len(), 3);
        assert_eq!(propagated.len(), 0);
    } else {
        panic!("Wrong type returned by init_watches")
    }

    assert_eq!(watcher.watches_slack, 5);

    assign.set_value(2, BoolValue::Assigned(true));

    assert_eq!(
        watcher.update_watch(Lit::from_var(2, true), &assign),
        WatchUpdate::Unknown {
            propagated: vec![Lit::from_var(3, false)],
            new_watches: vec![Lit::from_var(0, true), Lit::from_var(2, true)]
        }
    );

    assert_eq!(watcher.watches_slack, 3);

    assign.set_value(2, BoolValue::Unassigned);
    watcher.reset_watch();

    // non-contributing watch is only updated on next watch update
    assert_eq!(watcher.watches_slack, 3);

    assert_eq!(
        watcher.update_watch(Lit::from_var(0, true), &assign),
        WatchUpdate::None
    );

    assert_eq!(watcher.next_pos, 0);
    // no watch update, but accounted for watched but not contributing watches that are now contributing
    // hence, slack increased by 3 (due to x2 becoming unassigned) then decreased by 1 (due to x0 being falsified)
    assert_eq!(watcher.watches_slack, 5);
}

#[test]
fn general_pb_update_new_watches() {
    let constraint = get_test_constraint();
    let mut watcher = GeneralPBWatcher::from_constraint(constraint);
    let mut assign = Assignment::with_size(5);
    watcher.init_watches(&assign);

    assign.set_value(2, BoolValue::Assigned(true));

    assert_eq!(
        watcher.update_watch(Lit::from_var(2, true), &assign),
        WatchUpdate::Unknown {
            propagated: vec![],
            new_watches: vec![Lit::from_var(1, false)]
        }
    );

    assert_eq!(watcher.next_pos, 4);
    assert_eq!(watcher.watches_slack, 6); // 5 + 4 + 2 - 5
}

#[test]
fn general_pb_update_propagate() {
    let constraint = get_test_constraint();
    let mut watcher = GeneralPBWatcher::from_constraint(constraint);
    let mut assign = Assignment::with_size(5);
    watcher.init_watches(&assign);

    assign.set_value(2, BoolValue::Assigned(true));
    assign.set_value(4, BoolValue::Assigned(true));

    assert_eq!(
        watcher.update_watch(Lit::from_var(2, true), &assign),
        WatchUpdate::Unknown {
            propagated: vec![],
            new_watches: vec![Lit::from_var(1, false)]
        }
    );

    assert_eq!(watcher.watches_slack, 6); // 5 + 4 + 2 - 5

    assert_eq!(
        watcher.update_watch(Lit::from_var(4, true), &assign),
        WatchUpdate::Unknown {
            propagated: vec![Lit::from_var(3, false)],
            new_watches: vec![Lit::from_var(0, true), Lit::from_var(4, true)]
        }
    );

    assert_eq!(watcher.next_pos, 5);
    assert_eq!(watcher.watches_slack, 3);
}

#[test]
fn general_pb_update_conflict() {
    let constraint = get_test_constraint();
    let mut watcher = GeneralPBWatcher::from_constraint(constraint);
    let mut assign = Assignment::with_size(5);
    watcher.init_watches(&assign);

    assign.set_value(2, BoolValue::Assigned(true));
    assign.set_value(3, BoolValue::Assigned(false));
    assign.set_value(4, BoolValue::Assigned(true));

    watcher.update_watch(Lit::from_var(2, true), &assign);
    watcher.update_watch(Lit::from_var(3, false), &assign);

    assert_eq!(
        watcher.update_watch(Lit::from_var(4, true), &assign),
        WatchUpdate::Conflict
    );

    let watches = watcher.watches;
    assert!(watches.contains_key(&Lit::from_var(0, true)));
    assert!(watches.contains_key(&Lit::from_var(1, false)));
    assert!(watches.contains_key(&Lit::from_var(4, true)));
    // Lit(3, false) is falsified, so it is watched but not contributing to slack.
    assert!(
        watcher
            .watched_but_not_contributing
            .iter()
            .any(|(l, _)| *l == Lit::from_var(3, false))
    );

    assert_eq!(watcher.next_pos, 5);
    assert_eq!(watcher.watches_slack, 2); // 1 + 2 + 4 - 5
}

#[test]
fn assignment_independent_complete_propagating_constraint() {
    let constraint = GeneralPBConstraint::<i64>::from_terms(
        vec![
            GeneralPBTerm::new(2, Lit::from_var(0, true)),
            GeneralPBTerm::new(3, Lit::from_var(1, false)),
            GeneralPBTerm::new(4, Lit::from_var(2, true)),
        ],
        9,
        8,
    );
    let watcher = GeneralPBWatcher::from_constraint(constraint);

    let result = watcher.get_assignment_independent_propagations();

    assert!(result.is_some());
    assert_eq!(result.as_ref().unwrap()[0].lit, Lit::from_var(2, true));
    assert_eq!(result.as_ref().unwrap()[1].lit, Lit::from_var(1, false));
    assert_eq!(result.as_ref().unwrap()[2].lit, Lit::from_var(0, true));
}

#[test]
fn assignment_independent_partial_propagating_constraint() {
    let constraint = GeneralPBConstraint::<i64>::from_terms(
        vec![
            GeneralPBTerm::new(1, Lit::from_var(0, true)),
            GeneralPBTerm::new(2, Lit::from_var(1, false)),
            GeneralPBTerm::new(3, Lit::from_var(2, true)),
        ],
        6,
        5,
    );
    let watcher = GeneralPBWatcher::from_constraint(constraint);

    let result = watcher.get_assignment_independent_propagations();

    assert!(result.is_some());
    assert_eq!(result.as_ref().unwrap()[0].lit, Lit::from_var(2, true));
    assert_eq!(result.as_ref().unwrap()[1].lit, Lit::from_var(1, false));
}

#[test]
fn assignment_independent_not_propagating_constraint() {
    let constraint = get_test_constraint();
    let watcher = GeneralPBWatcher::from_constraint(constraint);

    let result = watcher.get_assignment_independent_propagations();

    assert!(result.is_none());
}

/// A trivially true constraint propagates nothing, at every width.
///
/// The watcher derives its slack as `coeff_sum - degree`, but the integer type of a constraint is
/// only chosen so that the coefficient sum and the degree each fit into it — not their difference.
/// Because coefficients are non-negative, the difference can only leave the type when the degree is
/// non-positive, i.e. for a trivially true constraint. Before the fix the subtraction wrapped
/// silently (the release profile had no overflow checks then) to a large *negative* number, so every
/// coefficient compared greater than it and the watcher reported *all* literals as
/// assignment-independent propagations. Two such constraints on complementary literals then made
/// the level-zero trail conflict and every subsequent `rup` — including the empty contradiction —
/// was accepted.
#[test]
fn assignment_independent_trivial_constraint_propagates_nothing_i64() {
    // `2 ~x1 >= i64::MIN`: the true slack is `2 + 2^63`, which is not representable in an i64.
    let constraint = GeneralPBConstraint::<i64>::from_terms(
        vec![GeneralPBTerm::new(2, Lit::from_var(0, true))],
        2,
        i64::MIN,
    );
    let watcher = GeneralPBWatcher::from_constraint(constraint);

    assert!(watcher.get_assignment_independent_propagations().is_none());
    assert!(!watcher.is_propagating_independent_of_assignment());
}

#[test]
fn assignment_independent_trivial_constraint_propagates_nothing_i128() {
    // `i128::MAX ~x1 >= -1`: the true slack is `i128::MAX + 1`.
    let constraint = GeneralPBConstraint::<i128>::from_terms(
        vec![GeneralPBTerm::new(i128::MAX, Lit::from_var(0, true))],
        i128::MAX,
        -1,
    );
    let watcher = GeneralPBWatcher::from_constraint(constraint);

    assert!(watcher.get_assignment_independent_propagations().is_none());
    assert!(!watcher.is_propagating_independent_of_assignment());
}

/// A trivially true constraint needs no watches and must not be reported as propagating, but it
/// must still be usable: building the watcher for a degree of `i64::MIN` also negates the degree
/// for the initial watch slack, which is not representable and used to wrap (or panic in debug).
#[test]
fn trivial_constraint_watcher_is_inert_but_well_formed() {
    let constraint = GeneralPBConstraint::<i64>::from_terms(
        vec![
            GeneralPBTerm::new(2, Lit::from_var(0, true)),
            GeneralPBTerm::new(3, Lit::from_var(1, false)),
        ],
        5,
        i64::MIN,
    );
    let mut watcher = GeneralPBWatcher::from_constraint(constraint);

    assert!(watcher.no_watches_required());
    assert!(!watcher.get_constraint().is_contradicting());
    assert!(watcher.get_constraint().is_trivial());
    assert!(watcher.get_assignment_independent_propagations().is_none());
}

/// Control: a constraint that really does propagate all of its literals independently of the
/// assignment must keep doing so. This is the behaviour the trivial-constraint early return must
/// not disturb.
#[test]
fn assignment_independent_propagation_of_non_trivial_constraint_is_unchanged() {
    let constraint = GeneralPBConstraint::<i64>::from_terms(
        vec![
            GeneralPBTerm::new(2, Lit::from_var(0, true)),
            GeneralPBTerm::new(3, Lit::from_var(1, false)),
        ],
        5,
        4,
    );
    let watcher = GeneralPBWatcher::from_constraint(constraint);

    let result = watcher
        .get_assignment_independent_propagations()
        .expect("slack 1 is smaller than both coefficients, so both literals propagate");
    assert_eq!(result.len(), 2);
    assert!(watcher.is_propagating_independent_of_assignment());
}
