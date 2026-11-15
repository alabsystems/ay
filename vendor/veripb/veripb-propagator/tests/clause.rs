use veripb_formula::{
    clause::Clause,
    lit::Lit,
    prelude::{Assignment, BoolValue},
};
use veripb_propagator::{
    clause_watcher::ClauseWatcher,
    watcher::{WatchInit, WatchUpdate, Watchable},
};

#[test]
fn clause_init() {
    let clause = Clause::from_lits(vec![
        Lit::from_var(0, true),
        Lit::from_var(1, false),
        Lit::from_var(2, true),
    ]);
    let assign = Assignment::with_size(3);

    let mut watcher = ClauseWatcher::from_clause(clause);
    assert_eq!(
        watcher.init_watches(&assign),
        WatchInit::Watching {
            propagated: vec![],
            watches: vec![Lit::from_var(0, true), Lit::from_var(1, false)]
        }
    );

    assert_eq!(watcher.next_pos, 2);
}

#[test]
fn clause_init_with_assignment_satisfied() {
    let clause = Clause::from_lits(vec![
        Lit::from_var(0, true),
        Lit::from_var(1, false),
        Lit::from_var(2, true),
        Lit::from_var(3, false),
        Lit::from_var(4, true),
    ]);
    let mut assign = Assignment::with_size(5);
    assign.set_value(0, BoolValue::Assigned(true));
    assign.set_value(1, BoolValue::Assigned(false));
    assign.set_value(2, BoolValue::Assigned(false));

    let mut watcher = ClauseWatcher::from_clause(clause);
    assert_eq!(
        watcher.init_watches(&assign),
        WatchInit::Watching {
            propagated: vec![],
            watches: vec![Lit::from_var(2, true), Lit::from_var(0, true)]
        }
    );

    assert_eq!(watcher.next_pos, 3);
}

#[test]
fn clause_init_with_assignment_conflict() {
    let clause = Clause::from_lits(vec![
        Lit::from_var(0, true),
        Lit::from_var(1, false),
        Lit::from_var(2, true),
        Lit::from_var(3, false),
        Lit::from_var(4, true),
    ]);
    let mut assign = Assignment::with_size(5);
    assign.set_value(0, BoolValue::Assigned(true));
    assign.set_value(1, BoolValue::Assigned(false));
    assign.set_value(2, BoolValue::Assigned(true));
    assign.set_value(3, BoolValue::Assigned(false));
    assign.set_value(4, BoolValue::Assigned(true));

    let mut watcher = ClauseWatcher::from_clause(clause);
    assert_eq!(watcher.init_watches(&assign), WatchInit::Conflict);

    assert_eq!(watcher.next_pos, 0);
}

#[test]
fn clause_init_with_assignment_propagate() {
    let clause = Clause::from_lits(vec![
        Lit::from_var(0, true),
        Lit::from_var(1, false),
        Lit::from_var(2, true),
        Lit::from_var(3, false),
        Lit::from_var(4, true),
    ]);
    let mut assign = Assignment::with_size(5);
    assign.set_value(0, BoolValue::Assigned(true));
    assign.set_value(1, BoolValue::Assigned(false));
    assign.set_value(3, BoolValue::Assigned(false));
    assign.set_value(4, BoolValue::Assigned(true));

    let mut watcher = ClauseWatcher::from_clause(clause);
    assert_eq!(
        watcher.init_watches(&assign),
        WatchInit::Watching {
            propagated: vec![Lit::from_var(2, true)],
            watches: vec![Lit::from_var(2, true), Lit::from_var(0, true)]
        }
    );

    assert_eq!(watcher.next_pos, 3);
}

#[test]
fn clause_update_unknown() {
    let clause = Clause::from_lits(vec![
        Lit::from_var(0, true),
        Lit::from_var(1, false),
        Lit::from_var(2, true),
        Lit::from_var(3, false),
        Lit::from_var(4, true),
    ]);
    let mut assign = Assignment::with_size(5);
    let mut watcher = ClauseWatcher::from_clause(clause);
    watcher.init_watches(&assign);

    assign.set_value(1, BoolValue::Assigned(false));
    assert_eq!(
        watcher.update_watch(Lit::from_var(1, false), &assign),
        WatchUpdate::UnknownSingle {
            propagated: None,
            new_watches: Lit::from_var(2, true)
        }
    );

    assert_eq!(watcher.next_pos, 3);
}

#[test]
fn clause_update_unknown_both_set() {
    let clause = Clause::from_lits(vec![
        Lit::from_var(0, true),
        Lit::from_var(1, false),
        Lit::from_var(2, true),
        Lit::from_var(3, false),
        Lit::from_var(4, true),
    ]);
    let mut assign = Assignment::with_size(5);
    let mut watcher = ClauseWatcher::from_clause(clause);
    watcher.init_watches(&assign);

    assign.set_value(0, BoolValue::Assigned(true));
    assign.set_value(1, BoolValue::Assigned(false));
    assign.set_value(2, BoolValue::Assigned(true));
    assert_eq!(
        watcher.update_watch(Lit::from_var(1, false), &assign),
        WatchUpdate::UnknownSingle {
            propagated: None,
            new_watches: Lit::from_var(3, false)
        }
    );
    assert_eq!(
        watcher.update_watch(Lit::from_var(0, true), &assign),
        WatchUpdate::UnknownSingle {
            propagated: None,
            new_watches: Lit::from_var(4, true)
        }
    );

    assert_eq!(watcher.next_pos, 5);
}

#[test]
fn clause_update_propagate_other_watch() {
    let clause = Clause::from_lits(vec![
        Lit::from_var(0, true),
        Lit::from_var(1, false),
        Lit::from_var(2, true),
        Lit::from_var(3, false),
        Lit::from_var(4, true),
    ]);
    let mut assign = Assignment::with_size(5);
    let mut watcher = ClauseWatcher::from_clause(clause);
    watcher.init_watches(&assign);

    assign.set_value(1, BoolValue::Assigned(false));
    assign.set_value(2, BoolValue::Assigned(true));
    assign.set_value(3, BoolValue::Assigned(false));
    assign.set_value(4, BoolValue::Assigned(true));
    assert_eq!(
        watcher.update_watch(Lit::from_var(1, false), &assign),
        WatchUpdate::UnknownSingle {
            propagated: Some(Lit::from_var(0, true)),
            new_watches: Lit::from_var(1, false)
        }
    );

    assert_eq!(watcher.next_pos, 2);
}

#[test]
fn clause_update_conflict() {
    let clause = Clause::from_lits(vec![
        Lit::from_var(0, true),
        Lit::from_var(1, false),
        Lit::from_var(2, true),
        Lit::from_var(3, false),
        Lit::from_var(4, true),
    ]);
    let mut assign = Assignment::with_size(5);
    let mut watcher = ClauseWatcher::from_clause(clause);
    watcher.init_watches(&assign);

    assign.set_value(0, BoolValue::Assigned(true));
    assign.set_value(1, BoolValue::Assigned(false));
    assign.set_value(2, BoolValue::Assigned(true));
    assign.set_value(3, BoolValue::Assigned(false));
    assign.set_value(4, BoolValue::Assigned(true));
    assert_eq!(
        watcher.update_watch(Lit::from_var(1, false), &assign),
        WatchUpdate::Conflict
    );

    let watches = watcher.watches;
    assert_eq!(Lit::from_var(0, true), watches[0]);
    assert_eq!(Lit::from_var(1, false), watches[1]);
    assert_eq!(watcher.next_pos, 2);
}

#[test]
fn assignment_independent_unit_clause() {
    let clause = Clause::from_lits(vec![Lit::from_var(0, true)]);
    let watcher = ClauseWatcher::from_clause(clause);

    let result = watcher.get_assignment_independent_propagations();
    assert!(result.is_some());
    assert_eq!(result.unwrap()[0].lit, Lit::from_var(0, true));
}

#[test]
fn assignment_independent_general_clause() {
    let clause = Clause::from_lits(vec![
        Lit::from_var(0, true),
        Lit::from_var(1, false),
        Lit::from_var(2, true),
        Lit::from_var(3, false),
        Lit::from_var(4, true),
    ]);
    let watcher = ClauseWatcher::from_clause(clause);

    assert_eq!(watcher.get_assignment_independent_propagations(), None);
}
