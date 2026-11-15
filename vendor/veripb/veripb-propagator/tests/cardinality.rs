use veripb_formula::{
    lit::Lit,
    prelude::{Assignment, BoolValue, Cardinality},
};
use veripb_propagator::{
    cardinality_watcher::CardinalityWatcher,
    watcher::{WatchInit, WatchUpdate, Watchable},
};

#[test]
fn card_init() {
    let card = Cardinality::from_lits(
        vec![
            Lit::from_var(0, true),
            Lit::from_var(1, false),
            Lit::from_var(2, true),
            Lit::from_var(3, false),
            Lit::from_var(4, true),
        ],
        3,
    );
    let assign = Assignment::with_size(5);

    let mut watcher = CardinalityWatcher::from_card(card);

    if let WatchInit::Watching {
        propagated,
        watches,
    } = watcher.init_watches(&assign)
    {
        assert!(watches.contains(&Lit::from_var(0, true)));
        assert!(watches.contains(&Lit::from_var(1, false)));
        assert!(watches.contains(&Lit::from_var(2, true)));
        assert!(watches.contains(&Lit::from_var(3, false)));
        assert_eq!(watches.len(), 4);
        assert_eq!(propagated.len(), 0);
    } else {
        panic!("Wrong type returned by init_watches")
    }

    assert_eq!(watcher.next_pos, 4);
}

#[test]
fn card_init_satisfied() {
    let card = Cardinality::from_lits(
        vec![
            Lit::from_var(0, true),
            Lit::from_var(1, false),
            Lit::from_var(2, true),
            Lit::from_var(3, false),
            Lit::from_var(4, true),
        ],
        3,
    );
    let mut assign = Assignment::with_size(5);
    assign.set_value(0, BoolValue::Assigned(false));
    assign.set_value(1, BoolValue::Assigned(false));
    assign.set_value(2, BoolValue::Assigned(false));
    assign.set_value(3, BoolValue::Assigned(true));

    let mut watcher = CardinalityWatcher::from_card(card);
    if let WatchInit::Watching {
        propagated,
        watches,
    } = watcher.init_watches(&assign)
    {
        assert!(watches.contains(&Lit::from_var(0, true)));
        assert!(watches.contains(&Lit::from_var(2, true)));
        assert!(watches.contains(&Lit::from_var(3, false)));
        assert!(watches.contains(&Lit::from_var(4, true)));
        assert_eq!(watches.len(), 4);
        assert_eq!(propagated.len(), 0);
    } else {
        panic!("Wrong type returned by init_watches")
    }

    assert_eq!(watcher.next_pos, 5);
}

#[test]
fn card_init_propagation() {
    let card = Cardinality::from_lits(
        vec![
            Lit::from_var(0, true),
            Lit::from_var(1, false),
            Lit::from_var(2, true),
            Lit::from_var(3, false),
            Lit::from_var(4, true),
        ],
        3,
    );
    let mut assign = Assignment::with_size(5);
    assign.set_value(0, BoolValue::Assigned(true));
    assign.set_value(2, BoolValue::Assigned(true));

    let mut watcher = CardinalityWatcher::from_card(card);
    if let WatchInit::Watching {
        propagated,
        watches,
    } = watcher.init_watches(&assign)
    {
        assert!(watches.contains(&Lit::from_var(0, true)));
        assert!(watches.contains(&Lit::from_var(1, false)));
        assert!(watches.contains(&Lit::from_var(3, false)));
        assert!(watches.contains(&Lit::from_var(4, true)));
        assert!(propagated.contains(&Lit::from_var(1, false)));
        assert!(propagated.contains(&Lit::from_var(3, false)));
        assert!(propagated.contains(&Lit::from_var(4, true)));
        assert_eq!(watches.len(), 4);
        assert_eq!(propagated.len(), 3);
    } else {
        panic!("Wrong type returned by init_watches")
    }
    assert_eq!(watcher.next_pos, 0);
}

#[test]
fn card_init_conflict() {
    let card = Cardinality::from_lits(
        vec![
            Lit::from_var(0, true),
            Lit::from_var(1, false),
            Lit::from_var(2, true),
            Lit::from_var(3, false),
            Lit::from_var(4, true),
        ],
        3,
    );
    let mut assign = Assignment::with_size(5);
    assign.set_value(0, BoolValue::Assigned(true));
    assign.set_value(2, BoolValue::Assigned(true));
    assign.set_value(4, BoolValue::Assigned(true));

    let mut watcher = CardinalityWatcher::from_card(card);
    assert_eq!(watcher.init_watches(&assign), WatchInit::Conflict);

    assert_eq!(watcher.next_pos, 0);
}

#[test]
fn card_update_unknown() {
    let card = Cardinality::from_lits(
        vec![
            Lit::from_var(0, true),
            Lit::from_var(1, false),
            Lit::from_var(2, true),
            Lit::from_var(3, false),
            Lit::from_var(4, true),
        ],
        3,
    );
    let mut assign = Assignment::with_size(5);
    let mut watcher = CardinalityWatcher::from_card(card);
    watcher.init_watches(&assign);

    assign.set_value(1, BoolValue::Assigned(false));

    assert_eq!(
        watcher.update_watch(Lit::from_var(1, false), &assign),
        WatchUpdate::UnknownSingle {
            propagated: None,
            new_watches: Lit::from_var(4, true)
        }
    );

    assert_eq!(watcher.next_pos, 5);
}

#[test]
fn card_update_satisfied() {
    let card = Cardinality::from_lits(
        vec![
            Lit::from_var(0, true),
            Lit::from_var(1, false),
            Lit::from_var(2, true),
            Lit::from_var(3, false),
            Lit::from_var(4, true),
        ],
        3,
    );
    let mut assign = Assignment::with_size(5);
    let mut watcher = CardinalityWatcher::from_card(card);
    watcher.init_watches(&assign);

    assign.set_value(1, BoolValue::Assigned(false));
    assign.set_value(2, BoolValue::Assigned(false));
    assign.set_value(4, BoolValue::Assigned(false));

    assert_eq!(
        watcher.update_watch(Lit::from_var(1, false), &assign),
        WatchUpdate::UnknownSingle {
            propagated: None,
            new_watches: Lit::from_var(4, true)
        }
    );

    assert_eq!(watcher.next_pos, 5);
}

#[test]
fn card_update_propagated() {
    let card = Cardinality::from_lits(
        vec![
            Lit::from_var(0, true),
            Lit::from_var(1, false),
            Lit::from_var(2, true),
            Lit::from_var(3, false),
            Lit::from_var(4, true),
        ],
        3,
    );
    let mut assign = Assignment::with_size(5);
    let mut watcher = CardinalityWatcher::from_card(card);
    watcher.init_watches(&assign);

    assign.set_value(1, BoolValue::Assigned(false));
    assign.set_value(2, BoolValue::Assigned(false));
    assign.set_value(4, BoolValue::Assigned(true));

    if let WatchUpdate::Unknown {
        propagated,
        new_watches,
    } = watcher.update_watch(Lit::from_var(1, false), &assign)
    {
        assert!(new_watches.contains(&Lit::from_var(1, false)));
        assert!(propagated.contains(&Lit::from_var(0, true)));
        assert!(propagated.contains(&Lit::from_var(3, false)));
        assert!(propagated.contains(&Lit::from_var(2, true)));
        assert_eq!(new_watches.len(), 1);
        assert_eq!(propagated.len(), 3);
    } else {
        panic!("Wrong type returned by update_watch")
    }

    assert_eq!(watcher.next_pos, 4);
}

#[test]
fn card_update_conflict() {
    let card = Cardinality::from_lits(
        vec![
            Lit::from_var(0, true),
            Lit::from_var(1, false),
            Lit::from_var(2, true),
            Lit::from_var(3, false),
            Lit::from_var(4, true),
        ],
        3,
    );
    let mut assign = Assignment::with_size(5);
    let mut watcher = CardinalityWatcher::from_card(card);
    watcher.init_watches(&assign);

    assign.set_value(1, BoolValue::Assigned(false));
    assign.set_value(2, BoolValue::Assigned(true));
    assign.set_value(4, BoolValue::Assigned(true));

    assert_eq!(
        watcher.update_watch(Lit::from_var(1, false), &assign),
        WatchUpdate::Conflict
    );

    assert_eq!(watcher.next_pos, 4);
    let watches = watcher.watches;
    assert!(watches.contains(&Lit::from_var(0, true)));
    assert!(watches.contains(&Lit::from_var(3, false)));
    assert!(watches.contains(&Lit::from_var(2, true)));
    assert!(watches.contains(&Lit::from_var(1, false)));
    assert_eq!(watches.len(), 4);
}

#[test]
fn assignment_independent_propagating_cardinality() {
    let card = Cardinality::from_lits(
        vec![
            Lit::from_var(0, true),
            Lit::from_var(1, false),
            Lit::from_var(2, true),
        ],
        3,
    );
    let watcher = CardinalityWatcher::from_card(card);
    let result = watcher.get_assignment_independent_propagations();

    assert!(result.is_some());
    assert_eq!(result.as_ref().unwrap()[0].lit, Lit::from_var(0, true));
    assert_eq!(result.as_ref().unwrap()[1].lit, Lit::from_var(1, false));
    assert_eq!(result.as_ref().unwrap()[2].lit, Lit::from_var(2, true));
}

#[test]
fn assignment_independent_not_propagating_cardinality() {
    let card = Cardinality::from_lits(
        vec![
            Lit::from_var(0, true),
            Lit::from_var(1, false),
            Lit::from_var(2, true),
            Lit::from_var(3, false),
            Lit::from_var(4, true),
        ],
        3,
    );
    let watcher = CardinalityWatcher::from_card(card);

    assert_eq!(watcher.get_assignment_independent_propagations(), None)
}
