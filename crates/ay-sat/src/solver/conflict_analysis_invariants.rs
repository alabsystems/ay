// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl Solver {
    pub(super) fn debug_assert_learned_clause_invariants(
        &self,
        uip: Literal,
        backtrack_level: u32,
        learned_clause: &[Literal],
    ) {
        debug_assert!(!learned_clause.is_empty(), "BUG: learned clause is empty");
        debug_assert_eq!(
            learned_clause[0], uip,
            "BUG: learned clause[0] {:?} != UIP {:?}",
            learned_clause[0], uip
        );
        debug_assert!(
            learned_clause.iter().all(|&lit| self.lit_val(lit) < 0),
            "BUG: learned clause contains a non-falsified literal",
        );
        debug_assert!(
            {
                let mut ok = true;
                'dup_check: for (i, lit_i) in learned_clause.iter().enumerate() {
                    for lit_j in learned_clause.iter().skip(i + 1) {
                        if lit_i.variable() == lit_j.variable() {
                            ok = false;
                            break 'dup_check;
                        }
                    }
                }
                ok
            },
            "BUG: learned clause has duplicate variables after minimize",
        );
        debug_assert_eq!(
            self.var_data[uip.variable().index()].level,
            self.decision_level,
            "BUG: 1UIP literal not at current decision level (var={}, level={}, decision_level={})",
            uip.variable().index(),
            self.var_data[uip.variable().index()].level,
            self.decision_level,
        );
        debug_assert_eq!(
            learned_clause
                .iter()
                .filter(|lit| self.var_data[lit.variable().index()].level == self.decision_level)
                .count(),
            1,
            "BUG: learned clause has non-UIP literals at the asserting decision level",
        );
        debug_assert!(
            {
                let mut ok = true;
                'outer: for (i, lit_i) in learned_clause.iter().enumerate() {
                    for lit_j in learned_clause.iter().skip(i + 1) {
                        if *lit_j == lit_i.negated() {
                            ok = false;
                            break 'outer;
                        }
                    }
                }
                ok
            },
            "BUG: learned clause is tautological (contains both a literal and its negation)",
        );
        debug_assert!(
            backtrack_level < self.decision_level,
            "BUG: backtrack level ({backtrack_level}) >= decision level ({})",
            self.decision_level,
        );
        debug_assert!(
            learned_clause.len() < 2
                || learned_clause[2..].iter().all(|lit| {
                    self.var_data[lit.variable().index()].level
                        <= self.var_data[learned_clause[1].variable().index()].level
                }),
            "BUG: clause[1] is not at the highest non-UIP level after reorder"
        );
    }
}
