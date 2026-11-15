//! Tests for the [`PropagationEngine`] state machine: enabling and disabling propagation
//! sets, saving and loading trail levels, poisoning, and watcher resets.
//!
//! These drive the engine through the same call shapes `veripb-checker` uses:
//! `attach_checker` / `detach_checker` stand in for `Database::update_propagation_index` and
//! `Database::delete_constraint`, `get_propagated_assignment` for
//! `utils::check_substituted_implication`, and `reverse_unit_propagation_check` for
//! `RUPRule::compute` / `Proofgoal::autoprove`.

use std::rc::Rc;

use veripb_formula::prelude::*;
use veripb_propagator::propagation_engine::{
    CORE_CLAUSES_CARD, CORE_GENERAL, DERIVED_CLAUSES_CARD, DERIVED_GENERAL, PropagationEngine,
};

/// A general PB constraint over `(coefficient, variable index, negated)` triples.
#[derive(Clone, Debug)]
struct Constraint {
    terms: Vec<(i64, usize, bool)>,
    degree: i64,
}

impl Constraint {
    fn new(terms: &[(i64, usize, bool)], degree: i64) -> Self {
        Constraint {
            terms: terms.to_vec(),
            degree,
        }
    }

    /// Whether the constraint holds under the assignment encoded by the bits of `bits`.
    fn holds(&self, bits: u32) -> bool {
        let mut sum = 0i64;
        for &(coeff, var, negated) in self.terms.iter() {
            let mut value = (bits >> var) & 1 == 1;
            if negated {
                value = !value;
            }
            if value {
                sum += coeff;
            }
        }
        sum >= self.degree
    }

    fn to_db_constraint(&self) -> Rc<DBConstraint> {
        let terms: Vec<GeneralPBTerm<i64>> = self
            .terms
            .iter()
            .map(|&(coeff, var, negated)| GeneralPBTerm::new(coeff, Lit::from_var(var, negated)))
            .collect();
        let coeff_sum: i64 = self.terms.iter().map(|term| term.0).sum();
        Rc::new(DBConstraint::from(PBConstraintEnum::from(
            GeneralPBConstraint::<i64>::from_terms(terms, coeff_sum, self.degree),
        )))
    }
}

fn engine_with_checker_sets() -> PropagationEngine {
    let mut engine = PropagationEngine::default();
    for _ in 0..5 {
        engine.add_set();
    }
    engine.enable_back(CORE_CLAUSES_CARD);
    engine.enable_back(CORE_GENERAL);
    engine.enable_back(DERIVED_CLAUSES_CARD);
    engine.enable_back(DERIVED_GENERAL);
    engine
}

fn var_names(num_vars: usize) -> VarNameManager {
    let mut names = VarNameManager::with_capacity(num_vars);
    for i in 0..num_vars {
        names.add_by_name(&format!("x{}", i + 1));
    }
    names
}

/// `reset_watch()` used to iterate only the *enabled* propagation sets. Every trail unwind goes
/// through it, and the derived sets are disabled exactly while an `only_core` phase runs -- the
/// same `init_trail` that disables them also truncates the trail in `unpoison()`. The derived
/// [`GeneralPBWatcher`]s therefore kept the `next_pos` / `next_pos_prop` /
/// `is_reset_not_contributing` state of the longer trail, violating invariants 1. and 2. of the
/// watcher: literals before `next_pos` were no longer "watched or falsified" but unassigned, and
/// `watched_but_not_contributing` held literals that were contributing again. Both leave
/// `watches_slack` *below* the true slack, so the watcher invents conflicts, and an invented
/// conflict makes an arbitrary RUP goal succeed.
#[test]
fn core_only_phase_does_not_leave_derived_watchers_stale() {
    const NUM_VARS: usize = 7;
    let names = var_names(NUM_VARS);

    // 3 x1 1 ~x4 2 x5 >= 6 -- core, deleted below; propagates x1, ~x4 and x5 at level zero.
    let core_deleted = Constraint::new(&[(3, 0, false), (1, 3, true), (2, 4, false)], 6);
    // 2 ~x2 3 x3 2 ~x5 3 x6 2 x7 >= 9 -- derived; the watcher whose state goes stale.
    let derived = Constraint::new(
        &[
            (2, 1, true),
            (3, 2, false),
            (2, 4, true),
            (3, 5, false),
            (2, 6, false),
        ],
        9,
    );
    // 3 x1 7 ~x2 3 x3 >= 11 -- core, stays live.
    let core_kept = Constraint::new(&[(3, 0, false), (7, 1, true), (3, 2, false)], 11);
    // The goal the engine must not accept once `core_deleted` is gone.
    let goal = Constraint::new(&[(3, 1, true), (1, 6, false)], 4);

    let mut engine = engine_with_checker_sets();

    let core_deleted_rc = core_deleted.to_db_constraint();
    core_deleted_rc.add_id(1, true);
    engine.attach_checker(true, &core_deleted_rc).unwrap();
    let derived_rc = derived.to_db_constraint();
    derived_rc.add_id(2, false);
    engine.attach_checker(false, &derived_rc).unwrap();
    let core_kept_rc = core_kept.to_db_constraint();
    core_kept_rc.add_id(3, true);
    engine.attach_checker(true, &core_kept_rc).unwrap();

    // The one checker entry point that runs `init_trail` and then leaves the trail in place, so
    // the derived watchers stay resumed against it.
    engine.get_propagated_assignment(NUM_VARS, false);

    // `del id 1` detaches a saved reason, poisoning the trail.
    engine.detach_checker(true, &core_deleted_rc, true).unwrap();
    core_deleted_rc.remove_id(1);

    // The checked deletion that follows runs a core-only phase: it disables the derived sets and
    // then truncates the trail.
    let probe = Constraint::new(&[], 1).to_db_constraint();
    engine
        .reverse_unit_propagation_check(&names, &[], Some(&probe), true, false, false)
        .unwrap();

    // Back to a normal core+derived RUP check.
    let goal_rc = goal.to_db_constraint();
    let accepted = engine
        .reverse_unit_propagation_check(&names, &[], Some(&goal_rc), false, false, false)
        .unwrap()
        .is_conflict();

    // Ground truth over every assignment: with the core constraint deleted, the live set does not
    // entail the goal.
    let live = [derived, core_kept];
    let counter_model = (0..(1u32 << NUM_VARS))
        .find(|&bits| live.iter().all(|c| c.holds(bits)) && !goal.holds(bits));
    assert!(
        counter_model.is_some(),
        "the test constraints should leave the goal unentailed"
    );

    assert!(
        !accepted,
        "the RUP check accepted a goal the live constraint set does not entail: the derived \
         watchers were still resumed against the pre-truncation trail"
    );
}

/// The same shape, but the derived set is never disabled: the engine must reject here too, which
/// pins that the test above fails for the stale-watcher reason and not because the goal is
/// somehow unreachable.
#[test]
fn unentailed_goal_is_rejected_without_a_core_only_phase() {
    const NUM_VARS: usize = 7;
    let names = var_names(NUM_VARS);

    let derived = Constraint::new(
        &[
            (2, 1, true),
            (3, 2, false),
            (2, 4, true),
            (3, 5, false),
            (2, 6, false),
        ],
        9,
    );
    let core_kept = Constraint::new(&[(3, 0, false), (7, 1, true), (3, 2, false)], 11);
    let goal = Constraint::new(&[(3, 1, true), (1, 6, false)], 4);

    let mut engine = engine_with_checker_sets();

    let derived_rc = derived.to_db_constraint();
    derived_rc.add_id(2, false);
    engine.attach_checker(false, &derived_rc).unwrap();
    let core_kept_rc = core_kept.to_db_constraint();
    core_kept_rc.add_id(3, true);
    engine.attach_checker(true, &core_kept_rc).unwrap();

    let goal_rc = goal.to_db_constraint();
    let accepted = engine
        .reverse_unit_propagation_check(&names, &[], Some(&goal_rc), false, false, false)
        .unwrap()
        .is_conflict();

    assert!(!accepted, "the goal is not entailed and must be rejected");
}
