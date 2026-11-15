// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Fixed-format rounded DATA, never a source/proof/Rust payload credential.

use super::remainder::support::{roots, with_owner};
use super::*;
use ay_fp::RoundingMode;
use std::time::{Duration, Instant};

mod ownership;
mod semantics;
mod support;
mod validation;

fn format(width: u32) -> (u32, u32) {
    match width {
        32 => (8, 24),
        64 => (11, 53),
        _ => panic!("fixed test format"),
    }
}

fn mode(terms: &mut TermStore, rm: RoundingMode) -> TermId {
    terms.mk_app(
        Symbol::named(rm.name()),
        [],
        Sort::Uninterpreted("RoundingMode".into()),
    )
}

fn operation(
    terms: &mut TermStore,
    name: &str,
    width: u32,
    rm: RoundingMode,
    operands: &[TermId],
) -> TermId {
    let (e, s) = format(width);
    let rm = mode(terms, rm);
    let args = std::iter::once(rm)
        .chain(operands.iter().copied())
        .collect::<Vec<_>>();
    terms.mk_app(Symbol::named(name), args, Sort::FloatingPoint(e, s))
}

fn error(terms: &TermStore, root: TermId, budget: &mut WorkBudget<'_>) -> FpAdapterError {
    match source::plan(terms, &[root], &[], budget) {
        Ok(_) => panic!("invalid rounded source must refuse before native entry"),
        Err(error) => error,
    }
}

#[test]
fn distinct_sqrt_and_fma_classes_keep_all_literal_modes_formats_and_other_fees() {
    with_owner(20, |budget| {
        for width in [32, 64] {
            for rm in ay_fp::RM_ORDER {
                for (name, arity, class) in [("fp.sqrt", 1, 0), ("fp.fma", 3, 1)] {
                    budget.admit(8192, 65_536).unwrap();
                    let mut terms = TermStore::new();
                    let bits = if width == 32 {
                        0x3f800000
                    } else {
                        0x3ff0000000000000
                    };
                    let x = fp_constant(&mut terms, bits, width);
                    let actual = operation(&mut terms, name, width, rm, &vec![x; arity]);
                    let root = predicate(&mut terms, "fp.isNormal", &[actual]);
                    let (_, cost) = typed::children(&terms, actual, &[], budget).unwrap();
                    assert!(if class == 0 {
                        matches!(cost, typed::CostClass::SquareRoot)
                    } else {
                        matches!(cost, typed::CostClass::Fused)
                    });
                    let plan = source::plan(&terms, &[root], &[], budget).unwrap();
                    assert_eq!(plan.occurrences, 3 + 2 * arity);
                    assert_eq!(plan.gates, 262_144 + (plan.occurrences - 1) * 4096 + 64);
                    assert_eq!(plan.clauses, 4 * plan.gates + 1);
                    let before = budget.remaining();
                    plan.prepay(budget).unwrap();
                    assert_eq!(before - budget.remaining(), (plan.gates * 1024) as u64);
                    drop(terms);
                    budget.charge(0).unwrap();
                }
            }
        }
    });
}

#[test]
fn nested_mixed_shared_and_repeated_occurrences_never_borrow_memo_refunds() {
    with_owner(1, |budget| {
        budget.admit(8192, 65_536).unwrap();
        let mut terms = TermStore::new();
        let x = fp_constant(&mut terms, 0x3f800000, 32);
        let sqrt = operation(&mut terms, "fp.sqrt", 32, RoundingMode::RNE, &[x]);
        let fma = operation(
            &mut terms,
            "fp.fma",
            32,
            RoundingMode::RNE,
            &[sqrt, sqrt, x],
        );
        let root = predicate(&mut terms, "=", &[fma, x]);
        let plan = source::plan(&terms, &[root], &[], budget).unwrap();
        // One FMA and BOTH raw sqrt children; the RM and full original leaf
        // descriptors are OTHER occurrences even when native caches share them.
        assert_eq!(plan.occurrences, 15);
        assert_eq!(plan.gates, 3 * 262_144 + 12 * 4096 + 64);
        let twice = source::plan(&terms, &[root, root], &[], budget).unwrap();
        assert_eq!(twice.occurrences, 2 * plan.occurrences);
        assert_eq!(twice.gates - 64, 2 * (plan.gates - 64));
        assert!(matches!(
            source::plan(&terms, &[root; 22], &[], budget),
            Err(FpAdapterError::Unsupported("complete circuit envelope"))
        ));
        drop(terms);
        budget.charge(0).unwrap();
    });
}
