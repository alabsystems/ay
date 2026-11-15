// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn domain_priority_fallback_and_bucket_consumption_match() {
    assert_parity(|| {
        let mut s = domain_fixture();
        s.cold.random_var_freq = 1.0;
        s.indep_support = vec![3];
        s.set_relevancy_branching(true);
        s.set_relevancy_hard(true);
        s
    });
    assert_parity(|| {
        let mut s = domain_fixture();
        s.active_domain = s.decision_domain.take();
        s
    });
    assert_parity(|| {
        let mut s = domain_fixture();
        s.set_ic3_mode();
        s.vsids
            .rebuild_bucket_queue_with_domain(&[Variable::new(0), Variable::new(6)]);
        s.bucket_queue_active = true;
        s
    });
}

#[test]
fn independent_support_selection_and_exhausted_fallback_match() {
    for heuristic in [
        BranchHeuristic::Evsids,
        BranchHeuristic::Chb,
        BranchHeuristic::Vmtf,
    ] {
        for support in [vec![0, 1, 7, 8, 100], vec![0, 1, 8, 100]] {
            assert_parity(|| {
                let mut s = fixture(heuristic);
                s.indep_support = support.clone();
                s
            });
        }
    }
}

#[test]
fn random_frequency_and_burst_gates_keep_exact_schedule_and_result() {
    for kissat in [false, true] {
        let mut switches = ay_core::sat_ab_switches();
        switches.randec_kissat = Some(kissat);
        let _guard = ay_core::sat_ab_test_override::set(switches);
        check_random_schedules();
    }
}

fn check_random_schedules() {
    for frequency in [0.0, 0.5, 1.0] {
        for (stable, conflicts, remaining, level) in [
            (true, 1000, 0, 0),
            (false, 100, 0, 0),
            (false, 1000, 0, 0),
            (false, 1000, 0, 1),
            (false, 1000, 10, 1),
        ] {
            assert_parity(|| {
                let mut s = Solver::new(12);
                s.stable_mode = stable;
                s.cold.random_var_freq = frequency;
                s.num_conflicts = conflicts;
                s.cold.next_random_decision = 500;
                s.cold.randomized_deciding = remaining;
                if level > 0 {
                    s.decide(lit(0));
                }
                s
            });
        }
    }
}

#[test]
fn forced_target_focused_cycle_saved_and_default_phases_match() {
    // Domain fixture selects v6. Exercise every phase-priority edge, not just
    // agreement between two wrappers around an untested forced-phase branch.
    for (stable, forced, target, saved, switch, positive) in [
        (true, -1, 1, 1, 0, false),
        (true, 1, -1, -1, 0, true),
        (true, 0, -1, 1, 0, false),
        (true, 0, 0, -1, 0, false),
        (true, 0, 0, 0, 0, true),
        (false, 0, -1, -1, 2, true),
        (false, 0, 1, 1, 6, false),
        (false, 0, 1, -1, 0, false),
        (false, 1, -1, -1, 6, true),
    ] {
        let make = || {
            let mut s = domain_fixture();
            s.stable_mode = stable;
            s.cold.forced_phase[6] = forced;
            s.target_phase[6] = target;
            s.phase[6] = saved;
            s.cold.mode_switch_count = switch;
            s
        };
        assert_parity(make);
        let mut s = make();
        attach(&mut s, &test_owner(10_000_000, 10_000_000));
        assert_eq!(
            s.pick_next_decision_literal_counted(),
            Ok(Some(if positive { lit(6) } else { lit(6).negated() }))
        );
    }
}

fn synced_frontier_fixture() -> Solver {
    let mut s = frontier_fixture();
    assert!(ordinary(&mut s).is_some());
    s
}

#[test]
fn frontier_pending_bcp_append_and_formula_epoch_rebuild_match() {
    assert_parity(|| {
        let mut s = synced_frontier_fixture();
        s.decide(lit(3));
        assert!(s.search_propagate().is_none());
        s.arena.add(&[lit(9), lit(10), lit(11)], true);
        s
    });
    assert_parity(|| {
        let mut s = synced_frontier_fixture();
        let offset = s.arena.indices().next().unwrap();
        s.arena.delete(offset);
        s
    });
}

#[test]
fn completed_selection_can_feed_real_decision_and_counted_search_bcp() {
    let mut expected = fixture(BranchHeuristic::Evsids);
    let selected = ordinary(&mut expected).unwrap();
    expected.decide(selected);
    let conflict = expected.search_propagate();
    let mut actual = fixture(BranchHeuristic::Evsids);
    attach(&mut actual, &test_owner(10_000_000, 10_000_000));
    let selected = actual
        .pick_next_decision_literal_counted()
        .unwrap()
        .unwrap();
    // Assignment is intentionally ordinary: this test does not certify that
    // separate trace/log/replay-aware transaction as counted.
    actual.decide(selected);
    assert_eq!(actual.search_propagate_counted().unwrap(), conflict);
    assert_eq!(state(&actual), state(&expected));
}
