// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn sort_shrink_entries_preserves_level_and_trail_descending_order() {
    let mut entries = vec![(2, 4, 0), (5, 1, 1), (2, 9, 2), (5, 7, 3), (1, 10, 4)];

    sort_shrink_entries(&mut entries);

    assert_eq!(
        entries,
        vec![(5, 7, 3), (5, 1, 1), (2, 9, 2), (2, 4, 0), (1, 10, 4)],
        "shrink entries must sort by decision level desc, then trail position desc"
    );
}

#[test]
fn is_redundant_cached_keep_overrides_poison() {
    let mut solver = Solver::new(2);
    let pos_lit = Literal::positive(Variable(0));
    let neg_lit = Literal::negative(Variable(0));

    solver.decision_level = 1;
    solver.enqueue(pos_lit, None);
    solver.min.minimize_flags[0] |= MIN_KEEP;
    solver.min.minimize_flags[0] |= MIN_POISON;

    assert!(
        solver.is_redundant_cached(neg_lit, 1),
        "minimize_keep must take precedence over minimize_poison"
    );
}

#[test]
fn is_literal_removable_for_shrink_keep_overrides_poison() {
    let mut solver = Solver::new(2);
    let pos_lit = Literal::positive(Variable(0));
    let neg_lit = Literal::negative(Variable(0));

    solver.decision_level = 1;
    solver.enqueue(pos_lit, None);
    solver.min.minimize_flags[0] |= MIN_KEEP;
    solver.min.minimize_flags[0] |= MIN_POISON;

    assert!(
        solver.is_literal_removable_for_shrink(neg_lit),
        "shrink removability must treat keep as a successful base case"
    );
}

/// A block whose literals are implied through binary literal reasons (#8034)
/// shrinks to its block UIP. Before, `find_block_uip` read a binary reason as
/// a decision and gave the block up.
#[test]
fn find_block_uip_resolves_through_binary_literal_reasons() {
    let mut solver = Solver::new(4);
    let d = Literal::positive(Variable(0));
    let a = Literal::positive(Variable(1));
    let b = Literal::positive(Variable(2));
    let c = Literal::positive(Variable(3));
    solver.decide(d);
    // (a | -d), (b | -a), (c | -a): all implied at level 1 by the decision d.
    solver.enqueue_binary_reason(a, d.negated());
    solver.enqueue_binary_reason(b, a.negated());
    solver.enqueue_binary_reason(c, a.negated());
    assert!(matches!(
        solver.var_reason_kind(3),
        ReasonKind::BinaryLiteral(_)
    ));

    let uip = solver.find_block_uip(&[b.negated(), c.negated()], 1);

    // The block {-b, -c} is replaced by the negation of a literal implying
    // both: `a`, or the decision `d` when BCP jumped the binary reasons.
    assert!(
        uip == Some(a.negated()) || uip == Some(d.negated()),
        "expected a block UIP, got {uip:?}"
    );
    assert_eq!(solver.stats.shrink_fail_decision, 0);
}

/// A block containing the decision finds the decision as its UIP once it is
/// the last open literal.
#[test]
fn find_block_uip_reaches_the_decision_only_as_the_last_open_literal() {
    let mut solver = Solver::new(3);
    let d = Literal::positive(Variable(0));
    let a = Literal::positive(Variable(1));
    solver.decide(d);
    solver.enqueue_binary_reason(a, d.negated());

    let uip = solver.find_block_uip(&[d.negated(), a.negated()], 1);

    assert_eq!(uip, Some(d.negated()));
}

/// Trail for the `--sat-shrink-removable-kissat` tests, variables numbered
/// by trail position. Level 1: decision d0, then s1 <- d0, t2 <- s1,
/// y3 <- s1, a4 <- t2, b5 <- s1. Level 2: decision e6, then p7 <- e6, t2 and
/// q8 <- e6, y3. Level 3: decision x9.
fn removable_kissat_trail(on: bool) -> Solver {
    let _switches = ay_core::sat_ab_test_override::set(ay_core::SatAbSwitches {
        shrink_removable_kissat: Some(on),
        ..Default::default()
    });
    let mut solver = Solver::new(10);
    assert_eq!(solver.cold.shrink_removable_kissat, on);
    let lit = |v: u32| Literal::positive(Variable(v));
    let mut reason = [NO_REASON; 10];
    let reasons: [(u32, &[u32]); 7] = [
        (1, &[0]),
        (2, &[1]),
        (3, &[1]),
        (4, &[2]),
        (5, &[1]),
        (7, &[6, 2]),
        (8, &[6, 3]),
    ];
    for (v, antecedents) in reasons {
        let mut clause = vec![lit(v)];
        clause.extend(antecedents.iter().map(|&a| lit(a).negated()));
        reason[v as usize] = solver.add_clause_db(&clause, false) as u32;
    }
    for (v, level) in [1, 1, 1, 1, 1, 1, 2, 2, 2, 3].into_iter().enumerate() {
        let positive = lit(v as u32);
        solver.vals[positive.index()] = 1;
        solver.vals[positive.negated().index()] = -1;
        solver.var_data[v].level = level;
        solver.var_data[v].trail_pos = v as u32;
        solver.var_data[v].reason = reason[v];
        solver.trail.push(positive);
    }
    solver.decision_level = 3;
    solver
}

/// Shrink the first-UIP clause (-x9 | -a4 | -b5 | -p7 | -q8) with its levels
/// tracked as conflict analysis tracks them. Returns the final non-UIP
/// literals, the removed ones, and the solver.
fn shrink_removable_kissat_clause(on: bool) -> (Vec<Literal>, Vec<Literal>, Solver) {
    let mut solver = removable_kissat_trail(on);
    solver.conflict.clear(&mut solver.var_data);
    solver
        .conflict
        .set_asserting_literal(Literal::negative(Variable(9)));
    for v in [4, 5, 7, 8, 9] {
        solver.track_level_seen(solver.var_data[v].level, v);
        if v != 9 {
            solver
                .conflict
                .add_to_learned(Literal::negative(Variable(v as u32)));
        }
    }
    let mut removed = Vec::new();
    solver.shrink_and_minimize_repeated_level_learned_clause_collect_removed(4, Some(&mut removed));
    let learned = (0..solver.conflict.learned_count())
        .map(|i| solver.conflict.learned_at(i))
        .collect();
    (learned, removed, solver)
}

/// Rank 22 of PLAN-kissat-404-parity.md. The level-1 block {-a4, -b5}
/// shrinks to -s1, walking t2 but not y3. The level-2 block {-p7, -q8} then
/// reaches t2 and y3, both before a4, level 1's first clause literal. By
/// default the trail abort refuses y3, the block fails, and fallback
/// minimization keeps both literals. Under the switch t2 is removable and y3
/// is proved through s1, as Kissat accepts them (shrink.c:63-73), and the
/// block shrinks to -e6. The clause stays implied: s1 gives t2, y3, a4 and
/// b5; e6 with t2 gives p7 and with y3 gives q8.
#[test]
fn shrink_removable_kissat_shrinks_a_block_reaching_below_the_first_clause_literal() {
    let neg = |v: u32| Literal::negative(Variable(v));

    // Default: level 2 keeps -q8 and -p7; level 1's bound stays at a4.
    let (learned, removed, solver) = shrink_removable_kissat_clause(false);
    assert_eq!(learned, [neg(1), neg(8), neg(7)]);
    assert_eq!(removed, [neg(5), neg(4)]);
    assert_eq!(solver.stats.shrink_fail_lower, 1);
    assert_eq!(solver.stats.shrink_block_successes, 1);
    assert_eq!(solver.min.level_seen[1].trail, 4);

    // Switch on: level 2 shrinks to -e6; each bound drops to its block UIP.
    let (learned, removed, solver) = shrink_removable_kissat_clause(true);
    assert_eq!(learned, [neg(1), neg(6)]);
    assert_eq!(removed, [neg(5), neg(4), neg(8), neg(7)]);
    assert_eq!(solver.stats.shrink_fail_lower, 0);
    assert_eq!(solver.stats.shrink_block_successes, 2);
    assert_eq!(solver.min.level_seen[1].trail, 1);
    assert_eq!(solver.min.level_seen[2].trail, 6);
}

/// The walk records Kissat's shrinkable set only under the switch: the block
/// literals, the intermediate t2 and the UIP s1, never y3. Marking makes all
/// but the UIP removable and lowers the level's trail bound to the UIP.
#[test]
fn shrink_removable_kissat_marks_the_walked_literals_removable() {
    let neg = |v: u32| Literal::negative(Variable(v));
    let block = [neg(5), neg(4)];

    let mut solver = removable_kissat_trail(false);
    assert_eq!(solver.find_block_uip(&block, 1), Some(neg(1)));
    assert!(solver.min.shrink_walked.is_empty());

    let mut solver = removable_kissat_trail(true);
    solver.min.minimize_level_seen[1].count = 2;
    solver.min.minimize_level_seen[1].trail = 4;
    assert_eq!(solver.find_block_uip(&block, 1), Some(neg(1)));
    // Popped by descending trail position: b5, a4, t2, then the UIP s1.
    assert_eq!(solver.min.shrink_walked, [5, 4, 2, 1]);
    solver.mark_shrink_walked_removable(1, 1);
    // Neither the UIP s1 nor the unwalked y3 is marked.
    let removable: Vec<usize> = (0..10)
        .filter(|&v| solver.min.minimize_flags[v] & MIN_REMOVABLE != 0)
        .collect();
    assert_eq!(removable, [2, 4, 5]);
    assert_eq!(solver.min.minimize_to_clear, [5, 4, 2]);
    assert_eq!(solver.min.minimize_level_seen[1].trail, 1);
}
