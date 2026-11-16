// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use std::cell::Cell;

use ay_core::{Symbol, Tseitin};
use ay_fp::{FpBuildError, FpBuildProgress, FpConstruction};

use super::*;

fn fixture(argument: Sort, count: usize) -> (TermStore, Vec<TermId>) {
    let mut terms = TermStore::new();
    let mut roots = Vec::new();
    for i in 0..count {
        let arg = terms.mk_var(format!("x{i}"), argument.clone());
        roots.push(terms.mk_app(Symbol::named("foreign"), [arg], Sort::Bool));
    }
    (terms, roots)
}

fn tseitin(terms: &TermStore, roots: &[TermId]) -> ay_core::TseitinResult {
    let mut encoder = Tseitin::new(terms);
    for &root in roots {
        encoder.assert_term(root);
    }
    encoder.into_assertion_result()
}

fn rows(plan: &CongruencePlan) -> Vec<Vec<(u8, i32)>> {
    plan.clauses
        .iter()
        .map(|clause| {
            clause
                .iter()
                .map(|lit| match lit {
                    PlanLit::Fp(lit) => (0, *lit),
                    PlanLit::Tseitin(lit) => (1, *lit),
                })
                .collect()
        })
        .collect()
}

#[test]
fn controlled_foreign_fp_and_bv_pairs_match_the_complete_legacy_plan() {
    for sort in [Sort::FloatingPoint(5, 11), Sort::bitvec(8)] {
        let (terms, roots) = fixture(sort, 3);
        let old_scan = scan_foreign(&terms, &roots);
        let scan = scan_foreign_controlled(&terms, &roots, &mut || Ok(())).unwrap();
        assert_eq!(scan.groups, old_scan.groups);
        assert_eq!(scan.unencodable, old_scan.unencodable);
        let tseitin = tseitin(&terms, &roots);
        let mut legacy = FpSolver::new(&terms);
        let expected = plan_congruence(&terms, &mut legacy, &tseitin, &old_scan);
        assert_eq!(expected.clauses.len(), 6);
        assert!(!expected.incomplete);
        let mut allow = |_| false;
        let mut owner = FpConstruction::new(FpSolver::new(&terms), &mut allow).unwrap();
        let actual =
            plan_congruence_controlled(&terms, &mut owner, &tseitin, &scan, &mut || Ok(()))
                .unwrap();
        let built = owner.finish().unwrap();
        assert_eq!(rows(&actual), rows(&expected));
        assert_eq!(actual.incomplete, expected.incomplete);
        assert_eq!(built.clauses.as_slice(), legacy.clauses());
        assert_eq!(built.cache.next_var - 1, legacy.num_vars());
        assert_eq!(built.has_encoding_gap, legacy.has_encoding_gap());
        assert_eq!(built.pending_condition_links, Vec::new());
    }
}

#[test]
fn foreign_fp_results_and_unsupported_bv_results_keep_legacy_gap_semantics() {
    for result_sort in [Sort::FloatingPoint(5, 11), Sort::bitvec(8)] {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::FloatingPoint(5, 11));
        let y = terms.mk_var("y", Sort::FloatingPoint(5, 11));
        let first = terms.mk_app(Symbol::named("foreign"), [x], result_sort.clone());
        let second = terms.mk_app(Symbol::named("foreign"), [y], result_sort.clone());
        let root = terms.mk_app(Symbol::named("="), [first, second], Sort::Bool);
        let roots = [root];
        let scan = scan_foreign(&terms, &roots);
        assert_eq!(scan.groups.len(), 1);
        let tseitin = tseitin(&terms, &roots);
        let mut legacy = FpSolver::new(&terms);
        let expected = plan_congruence(&terms, &mut legacy, &tseitin, &scan);
        let unsupported = matches!(result_sort, Sort::BitVec(_));
        assert_eq!(expected.incomplete, unsupported);
        assert_eq!(expected.clauses.len(), usize::from(!unsupported));
        // An unsupported composite BV equality returns None; the planner's
        // incomplete flag, not the separate base-encoding gap, owns refusal.
        assert!(!legacy.has_encoding_gap());

        let mut allow = |_| false;
        let mut owner = FpConstruction::new(FpSolver::new(&terms), &mut allow).unwrap();
        let actual =
            plan_congruence_controlled(&terms, &mut owner, &tseitin, &scan, &mut || Ok(()))
                .unwrap();
        let built = owner.finish().unwrap();
        assert_eq!(rows(&actual), rows(&expected));
        assert_eq!(actual.incomplete, expected.incomplete);
        assert_eq!(built.clauses.as_slice(), legacy.clauses());
        assert_eq!(built.cache.next_var - 1, legacy.num_vars());
        assert_eq!(built.has_encoding_gap, legacy.has_encoding_gap());
    }
}

#[test]
fn pair_cancellation_after_real_fp_or_bv_encoding_never_returns_a_partial_plan() {
    for sort in [Sort::FloatingPoint(5, 11), Sort::bitvec(8)] {
        let (terms, roots) = fixture(sort, 3);
        let scan = scan_foreign(&terms, &roots);
        let tseitin = tseitin(&terms, &roots);
        let cancelled = Cell::new(false);
        let clauses = Cell::new(0);
        let calls = Cell::new(0);
        let mut stop = |p: FpBuildProgress| {
            clauses.set(p.clauses);
            cancelled.get()
        };
        let mut owner = FpConstruction::new(FpSolver::new(&terms), &mut stop).unwrap();
        let mut check = || {
            calls.set(calls.get() + 1);
            if clauses.get() > 0 {
                cancelled.set(true);
                Err(FpBuildError::Interrupted)
            } else {
                Ok(())
            }
        };
        assert!(matches!(
            plan_congruence_controlled(&terms, &mut owner, &tseitin, &scan, &mut check),
            Err(FpBuildError::Interrupted)
        ));
        assert!(clauses.get() > 0 && calls.get() > 3);
        assert!(matches!(
            owner.try_has_encoding_gap(),
            Err(FpBuildError::Interrupted)
        ));
        cancelled.set(false);
        assert!(matches!(owner.finish(), Err(FpBuildError::Interrupted)));
    }
}

#[test]
fn every_scan_checkpoint_refuses_without_returning_partial_groups() {
    let (terms, roots) = fixture(Sort::FloatingPoint(5, 11), 3);
    let calls = Cell::new(0);
    scan_foreign_controlled(&terms, &roots, &mut || {
        calls.set(calls.get() + 1);
        Ok(())
    })
    .unwrap();
    let total = calls.get();
    assert!(total > roots.len() * 2);
    for cutoff in 1..=total {
        let visited = Cell::new(0);
        let result = scan_foreign_controlled(&terms, &roots, &mut || {
            visited.set(visited.get() + 1);
            if visited.get() == cutoff {
                Err(FpBuildError::Interrupted)
            } else {
                Ok(())
            }
        });
        assert!(matches!(result, Err(FpBuildError::Interrupted)));
        assert_eq!(visited.get(), cutoff);
    }
}

#[test]
fn the_exact_group_cap_and_unencodable_argument_refusals_are_preserved() {
    for count in [64, 65] {
        let (terms, roots) = fixture(Sort::Int, count);
        let scan = scan_foreign(&terms, &roots);
        assert!(scan.unencodable);
        assert_eq!(scan.groups[0].len(), count);
        let tseitin = tseitin(&terms, &roots);
        let checks = Cell::new(0);
        let mut allow = |_| false;
        let mut owner = FpConstruction::new(FpSolver::new(&terms), &mut allow).unwrap();
        let plan = plan_congruence_controlled(&terms, &mut owner, &tseitin, &scan, &mut || {
            checks.set(checks.get() + 1);
            Ok(())
        })
        .unwrap();
        assert!(plan.incomplete && plan.clauses.is_empty());
        assert_eq!(
            owner.finish().unwrap().clauses,
            [] as [ay_core::CnfClause; 0]
        );
        if count == 65 {
            assert_eq!(checks.get(), 3); // Entry, skipped group, final.
        } else {
            assert!(checks.get() > count * (count - 1) / 2);
        }
        // Even an oversized group or an unsupported pair must poll, although
        // neither invokes an encoder or emits a clause.
        let mut owner = FpConstruction::new(FpSolver::new(&terms), &mut allow).unwrap();
        let seen = Cell::new(0);
        assert!(matches!(
            plan_congruence_controlled(&terms, &mut owner, &tseitin, &scan, &mut || {
                seen.set(seen.get() + 1);
                if seen.get() == 2 {
                    Err(FpBuildError::Interrupted)
                } else {
                    Ok(())
                }
            }),
            Err(FpBuildError::Interrupted)
        ));
        assert_eq!(seen.get(), 2);
        drop(owner); // A failed external check requires discarding its owner.
    }
}
