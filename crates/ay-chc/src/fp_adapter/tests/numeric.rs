// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_core::term::Constant;
use std::time::{Duration, Instant};

mod malformed;

fn owner<T>(run: impl FnOnce(&mut WorkBudget<'_>) -> T) -> T {
    let end = Instant::now() + Duration::from_secs(20);
    owner_until(end, run)
}

fn owner_until<T>(end: Instant, run: impl FnOnce(&mut WorkBudget<'_>) -> T) -> T {
    let mut work = 200_000_000_000u64;
    let mut bytes = 800_000_000_000u64;
    let mut admission = |w: usize, b: usize| {
        if Instant::now() >= end {
            return Err(QueryError::Interrupted(StopReason::Deadline));
        }
        work = work.checked_sub(w as u64).ok_or(QueryError::Exhausted)?;
        bytes = bytes.checked_sub(b as u64).ok_or(QueryError::Exhausted)?;
        Ok(())
    };
    let mut budget = WorkBudget::with_admission(200_000_000_000, &mut admission);
    let result = run(&mut budget);
    budget.charge(0).unwrap();
    result
}

fn fixture(
    mode: (TermData, Sort),
    word: (TermData, Sort),
    symbol: Symbol,
    args: Vec<TermId>,
) -> TermStore {
    TermStore::from_entries(
        vec![
            mode,
            word,
            (TermData::App(symbol, args), Sort::FloatingPoint(8, 24)),
            (
                TermData::App(Symbol::named("fp.isNormal"), vec![TermId(2)]),
                Sort::Bool,
            ),
        ],
        None,
        None,
        0,
    )
}

fn literal_mode(name: &str) -> (TermData, Sort) {
    (
        TermData::App(Symbol::named(name), vec![]),
        Sort::Uninterpreted("RoundingMode".into()),
    )
}

fn word(value: i64, n: u32) -> (TermData, Sort) {
    (
        TermData::Const(Constant::BitVec {
            value: value.into(),
            width: n,
        }),
        Sort::bitvec(n),
    )
}

fn refuses(terms: &TermStore, budget: &mut WorkBudget<'_>) {
    assert!(matches!(
        source::plan(terms, &[TermId(3)], &[], budget),
        Err(FpAdapterError::Invalid(_)) | Err(FpAdapterError::Unsupported(_))
    ));
}

#[test]
fn signed_and_unsigned_numeric_counts_are_disjoint_and_repeated_occurrences_not_discounted() {
    owner(|budget| {
        for name in ["to_fp", "to_fp_unsigned"] {
            for n in [8, 32, 64] {
                for (e, s) in [(8, 24), (11, 53)] {
                    let mut terms = TermStore::new();
                    let raw = terms.mk_var("numeric_original", Sort::bitvec(n));
                    let rm = terms.mk_app(
                        Symbol::named("RNE"),
                        [],
                        Sort::Uninterpreted("RoundingMode".into()),
                    );
                    let result = terms.mk_app(
                        Symbol::indexed(name, vec![e, s]),
                        [rm, raw],
                        Sort::FloatingPoint(e, s),
                    );
                    let root = predicate(&mut terms, "fp.isNormal", &[result]);
                    let target = ChcVar::new("numeric_original", crate::ChcSort::BitVec(n));
                    let input = bindings(raw, &target);
                    let one = source::plan(&terms, &[root], &input, budget).unwrap();
                    assert_eq!(one.occurrences, 4);
                    assert_eq!(one.gates, 18_432 + 3 * 4096 + 64);
                    let repeated = source::plan(&terms, &[root, root], &input, budget).unwrap();
                    assert_eq!(repeated.occurrences, 8);
                    assert_eq!(repeated.gates, 2 * (one.gates - 64) + 64);
                    assert!(matches!(
                        typed::children(&terms, result, &input, budget).unwrap().1,
                        typed::CostClass::NumericConversion
                    ));
                }
            }
        }
    });
}

#[test]
fn numeric_plan_exact_and_one_short_work_and_storage_precede_native_build() {
    let end = Instant::now() + Duration::from_secs(20);
    let terms = fixture(
        literal_mode("RNE"),
        word(127, 8),
        Symbol::indexed("to_fp", vec![8, 24]),
        vec![TermId(0), TermId(1)],
    );
    let plan = owner_until(end, |budget| {
        source::plan(&terms, &[TermId(3)], &[], budget).unwrap()
    });
    let work = plan.gates.checked_mul(1024).unwrap();
    let bytes = plan.gates.checked_mul(4096).unwrap();
    for (w, b, pass) in [
        (work, bytes, true),
        (work - 1, bytes, false),
        (work, bytes - 1, false),
    ] {
        let mut left = b;
        let mut admit = |_: usize, storage: usize| {
            if Instant::now() >= end {
                return Err(QueryError::Interrupted(StopReason::Deadline));
            }
            left = left.checked_sub(storage).ok_or(QueryError::Exhausted)?;
            Ok(())
        };
        let mut budget = WorkBudget::with_admission(u64::try_from(w).unwrap(), &mut admit);
        if pass {
            plan.prepay(&mut budget).unwrap();
        } else {
            assert_eq!(
                plan.prepay(&mut budget).err(),
                Some(FpAdapterError::Owner(QueryError::Exhausted))
            );
            assert_eq!(budget.charge(0), Err(QueryError::Exhausted));
        }
    }
}

#[test]
fn complete_numeric_occurrence_cap_is_not_bypassed_by_native_cache_reuse() {
    owner(|budget| {
        let terms = TermStore::from_entries(
            vec![
                literal_mode("RNE"),
                word(127, 8),
                (
                    TermData::App(
                        Symbol::indexed("to_fp", vec![8, 24]),
                        vec![TermId(0), TermId(1)],
                    ),
                    Sort::FloatingPoint(8, 24),
                ),
                (
                    TermData::App(Symbol::named("="), vec![TermId(2), TermId(2)]),
                    Sort::Bool,
                ),
            ],
            None,
            None,
            0,
        );
        budget.admit(4096, 4096).unwrap();
        let roots = vec![TermId(3); 512];
        assert!(matches!(
            source::plan(&terms, &roots, &[], budget),
            Err(FpAdapterError::Unsupported("complete circuit envelope"))
        ));
    });
}
