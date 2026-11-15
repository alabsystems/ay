// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Manual exact-word division oracles; no host FP or proof credential.

use super::*;
use ay_fp::{FpBuildError, FpBuildStage, FpConstruction, FpSolver, RoundingMode};

mod support;
use support::{constant_roots, div, with_owner, word};

#[test]
fn division_has_a_separate_full_prepaid_class_for_both_formats_and_all_modes() {
    with_owner(10, |budget| {
        for (eb, sb) in [(8, 24), (11, 53)] {
            for rm in ay_fp::RM_ORDER {
                budget.admit(8192, 65_536).unwrap();
                let mut terms = TermStore::new();
                let x = terms.mk_var("x", Sort::FloatingPoint(eb, sb));
                let y = terms.mk_var("y", Sort::FloatingPoint(eb, sb));
                let actual = div(&mut terms, x, y, eb + sb, rm);
                let root = predicate(&mut terms, "fp.isNormal", &[actual]);
                let targets = [
                    ChcVar::new("x", crate::ChcSort::BitVec(eb + sb)),
                    ChcVar::new("y", crate::ChcSort::BitVec(eb + sb)),
                ];
                let inputs = [
                    FpInputBinding {
                        source: x,
                        target: &targets[0],
                    },
                    FpInputBinding {
                        source: y,
                        target: &targets[1],
                    },
                ];
                let plan = source::plan(&terms, &[root], &inputs, budget).unwrap();
                assert_eq!(plan.gates, 524_288 + (plan.occurrences - 1) * 4096 + 64);
                let before = budget.remaining();
                plan.prepay(budget).unwrap();
                assert_eq!(before - budget.remaining(), (plan.gates * 1024) as u64);
            }
        }
    });
}

#[test]
fn binary32_one_third_and_its_negative_match_manual_words_in_all_modes() {
    with_owner(10, |budget| {
        // 2^25/3 = 11184810 + 2/3: nearest rounds upward, and this is not a tie.
        let positive = [
            0x3eaaaaabu64,
            0x3eaaaaab,
            0x3eaaaaab,
            0x3eaaaaaa,
            0x3eaaaaaa,
        ];
        let negative = [
            0xbeaaaaabu64,
            0xbeaaaaab,
            0xbeaaaaaa,
            0xbeaaaaab,
            0xbeaaaaaa,
        ];
        for (index, rm) in ay_fp::RM_ORDER.into_iter().enumerate() {
            word(32, 0x3f800000, 0x40400000, rm, positive[index], budget);
            word(32, 0xbf800000, 0x40400000, rm, negative[index], budget);
        }
    });
}

#[test]
fn binary64_one_third_and_its_negative_match_manual_words_in_all_modes() {
    with_owner(10, |budget| {
        // 2^54/3 = 6004799503160661 + 1/3: nearest rounds downward, not a tie.
        let low = 0x3fd5555555555555u64;
        let sign = 1u64 << 63;
        let positive = [low, low, low + 1, low, low];
        let negative = [
            sign | low,
            sign | low,
            sign | low,
            sign | (low + 1),
            sign | low,
        ];
        for (index, rm) in ay_fp::RM_ORDER.into_iter().enumerate() {
            word(
                64,
                0x3ff0000000000000,
                0x4008000000000000,
                rm,
                positive[index],
                budget,
            );
            word(
                64,
                0xbff0000000000000,
                0x4008000000000000,
                rm,
                negative[index],
                budget,
            );
        }
    });
}

#[test]
fn half_minsubnormal_ties_and_exact_halves_match_all_five_modes() {
    with_owner(30, |budget| {
        for (width, sign, one, two, half) in [
            (32, 1u64 << 31, 0x3f800000u64, 0x40000000u64, 0x3f000000u64),
            (
                64,
                1u64 << 63,
                0x3ff0000000000000u64,
                0x4000000000000000u64,
                0x3fe0000000000000u64,
            ),
        ] {
            let positive = [0, 1, 1, 0, 0];
            let negative = [sign, sign | 1, sign, sign | 1, sign];
            for (index, rm) in ay_fp::RM_ORDER.into_iter().enumerate() {
                word(width, 1, two, rm, positive[index], budget);
                word(width, sign | 1, two, rm, negative[index], budget);
                word(width, one, two, rm, half, budget);
            }
        }
    });
}

#[test]
fn division_zero_infinity_and_nan_are_smt_values_not_payload_promises() {
    with_owner(90, |budget| {
        for (width, sign, one, two, infinity, nan) in [
            (
                32,
                1u64 << 31,
                0x3f800000u64,
                0x40000000u64,
                0x7f800000u64,
                0x7fc00001u64,
            ),
            (
                64,
                1u64 << 63,
                0x3ff0000000000000u64,
                0x4000000000000000u64,
                0x7ff0000000000000u64,
                0x7ff8000000000001u64,
            ),
        ] {
            for rm in ay_fp::RM_ORDER {
                for (x, y, expected) in [
                    (0, sign | two, sign),
                    (sign, sign | two, 0),
                    (one, sign, sign | infinity),
                    (sign | infinity, two, sign | infinity),
                    (one, infinity, 0),
                ] {
                    word(width, x, y, rm, expected, budget);
                }
                for (x, y) in [
                    (0, 0),
                    (infinity, sign | infinity),
                    (nan, one),
                    (one, sign | nan),
                ] {
                    budget.admit(8192, 65_536).unwrap();
                    let mut terms = TermStore::new();
                    let x = fp_constant(&mut terms, x, width);
                    let y = fp_constant(&mut terms, y, width);
                    let actual = div(&mut terms, x, y, width, rm);
                    let roots = [
                        predicate(&mut terms, "fp.isNaN", &[actual]),
                        predicate(&mut terms, "fp.eq", &[actual, actual]),
                    ];
                    assert_eq!(constant_roots(&terms, &roots, budget), [true, false]);
                }
            }
        }
    });
}

#[test]
fn normal_power_of_two_and_declined_reciprocal_use_the_full_division_fee() {
    with_owner(20, |budget| {
        for (width, one, two, half, huge, reciprocal) in [
            (
                32,
                0x3f800000u64,
                0x40000000u64,
                0x3f000000u64,
                0x7f000000u64,
                0x00400000u64,
            ),
            (
                64,
                0x3ff0000000000000u64,
                0x4000000000000000u64,
                0x3fe0000000000000u64,
                0x7fe0000000000000u64,
                0x0008000000000000u64,
            ),
        ] {
            for rm in ay_fp::RM_ORDER {
                word(width, one, two, rm, half, budget);
                word(width, one, huge, rm, reciprocal, budget);
            }
        }
    });
}

#[test]
fn whole_division_relation_keeps_all_original_roots_and_both_input_words() {
    with_owner(1, |budget| {
        budget.admit(8192, 65_536).unwrap();
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::FloatingPoint(11, 53));
        let y = terms.mk_var("y", Sort::FloatingPoint(11, 53));
        let actual = div(&mut terms, x, y, 64, RoundingMode::RNE);
        let normal = predicate(&mut terms, "fp.isNormal", &[actual]);
        let equal = predicate(&mut terms, "=", &[actual, x]);
        let roots = [normal, equal, normal];
        let targets = [
            ChcVar::new("x", crate::ChcSort::BitVec(64)),
            ChcVar::new("y", crate::ChcSort::BitVec(64)),
        ];
        let inputs = [
            FpInputBinding {
                source: x,
                target: &targets[0],
            },
            FpInputBinding {
                source: y,
                target: &targets[1],
            },
        ];
        let namespace = ChcProblem::new();
        let output = lower_fp_clause(&terms, &roots, &inputs, &namespace, budget).unwrap();
        assert_eq!(output.source_roots(), &roots);
        assert!(std::ptr::eq(output.source_terms(), &terms));
        assert!(std::ptr::eq(output.source_namespace(), &namespace));
        assert!(output
            .auxiliary_variables()
            .iter()
            .all(|v| v.sort == crate::ChcSort::Bool));
        let ChcExpr::Op(crate::ChcOp::And, entries) = output.constraint() else {
            panic!()
        };
        let start = entries.len() - 128 - roots.len();
        assert_eq!(entries[start], entries[start + 2]);
        for (index, entry) in entries.iter().skip(entries.len() - 128).enumerate() {
            let ChcExpr::Op(crate::ChcOp::Eq, pair) = entry.as_ref() else {
                panic!()
            };
            let ChcExpr::Op(crate::ChcOp::Eq, value) = pair[1].as_ref() else {
                panic!()
            };
            let ChcExpr::Op(crate::ChcOp::BvExtract(hi, lo), child) = value[0].as_ref() else {
                panic!()
            };
            assert_eq!((*hi, *lo), ((index % 64) as u32, (index % 64) as u32));
            assert_eq!(
                child[0].as_ref(),
                &ChcExpr::Var(targets[index / 64].clone())
            );
        }
    });
}

#[test]
fn division_rejects_symbolic_rounding_mixed_formats_and_wrong_arity() {
    for case in 0..3 {
        let mut terms = TermStore::new();
        let x = fp_constant(&mut terms, 0x3f800000, 32);
        let y = if case == 1 {
            fp_constant(&mut terms, 0x3ff0000000000000, 64)
        } else {
            x
        };
        let mode = if case == 0 {
            terms.mk_var("RNE", Sort::Uninterpreted("RoundingMode".into()))
        } else {
            terms.mk_app(
                Symbol::named("RNE"),
                [],
                Sort::Uninterpreted("RoundingMode".into()),
            )
        };
        let args = if case == 2 {
            vec![mode, x]
        } else {
            vec![mode, x, y]
        };
        let actual = terms.mk_app(Symbol::named("fp.div"), args, Sort::FloatingPoint(8, 24));
        let root = predicate(&mut terms, "fp.isZero", &[actual]);
        let mut checkpoint = || ControlFlow::Continue(());
        let mut budget = WorkBudget::new(10_000_000_000, &mut checkpoint);
        assert!(matches!(
            source::plan(&terms, &[root], &[], &mut budget),
            Err(FpAdapterError::Unsupported(_))
        ));
    }
}

#[test]
fn a_general_divider_row_stop_poisoning_survives_original_flag_reset() {
    let end = std::time::Instant::now() + std::time::Duration::from_secs(20);
    let mut terms = TermStore::new();
    let x = terms.mk_var("division_x", Sort::FloatingPoint(11, 53));
    let y = terms.mk_var("division_y", Sort::FloatingPoint(11, 53));
    let actual = div(&mut terms, x, y, 64, RoundingMode::RNE);
    let root = predicate(&mut terms, "fp.isNormal", &[actual]);
    let targets = [
        ChcVar::new("division_x", crate::ChcSort::BitVec(64)),
        ChcVar::new("division_y", crate::ChcSort::BitVec(64)),
    ];
    let inputs = [
        FpInputBinding {
            source: x,
            target: &targets[0],
        },
        FpInputBinding {
            source: y,
            target: &targets[1],
        },
    ];
    let cancelled = Cell::new(false);
    let mut checkpoint = || {
        if cancelled.get() {
            ControlFlow::Break(StopReason::Cancelled)
        } else if std::time::Instant::now() >= end {
            ControlFlow::Break(StopReason::Deadline)
        } else {
            ControlFlow::Continue(())
        }
    };
    let mut budget = WorkBudget::new(10_000_000_000, &mut checkpoint);
    let plan = source::plan(&terms, &[root], &inputs, &mut budget).unwrap();
    plan.prepay(&mut budget).unwrap();
    let mut rows = 0;
    let mut first_frontier = 0;
    let mut stop = |progress: ay_fp::FpBuildProgress| {
        if progress.stage == FpBuildStage::DivideRow {
            rows += 1;
            if rows == 1 {
                first_frontier = progress.variables;
            }
            if rows == 3 {
                assert!(progress.variables > first_frontier);
                cancelled.set(true);
            }
        }
        budget.charge(0).is_err()
    };
    let mut attempt = FpConstruction::new(FpSolver::new(&terms), &mut stop).unwrap();
    assert!(matches!(
        attempt.try_encode_bool_condition(root),
        Err(FpBuildError::Interrupted)
    ));
    assert!(matches!(attempt.finish(), Err(FpBuildError::Interrupted)));
    drop(stop);
    cancelled.set(false);
    assert_eq!(
        budget.charge(0),
        Err(QueryError::Interrupted(StopReason::Cancelled))
    );
}

#[test]
fn division_storage_and_original_deadline_refusals_do_not_renew_the_owner() {
    let mut terms = TermStore::new();
    let x = fp_constant(&mut terms, 0x3f800000, 32);
    let y = fp_constant(&mut terms, 0x40400000, 32);
    let actual = div(&mut terms, x, y, 32, RoundingMode::RNE);
    let root = predicate(&mut terms, "fp.isNormal", &[actual]);
    let namespace = ChcProblem::new();
    let permit = Cell::new(false);
    let mut admission = |_, bytes| {
        if bytes >= 524_288usize * 4096 && !permit.get() {
            Err(QueryError::Exhausted)
        } else {
            Ok(())
        }
    };
    let mut budget = WorkBudget::with_admission(10_000_000_000, &mut admission);
    assert!(matches!(
        lower_fp_clause(&terms, &[root], &[], &namespace, &mut budget),
        Err(FpAdapterError::Owner(QueryError::Exhausted))
    ));
    permit.set(true);
    assert_eq!(budget.charge(0), Err(QueryError::Exhausted));
    let expired = Cell::new(true);
    let mut checkpoint = || {
        if expired.get() {
            ControlFlow::Break(StopReason::Deadline)
        } else {
            ControlFlow::Continue(())
        }
    };
    let mut budget = WorkBudget::new(10_000_000_000, &mut checkpoint);
    assert!(matches!(
        lower_fp_clause(&terms, &[root], &[], &namespace, &mut budget),
        Err(FpAdapterError::Owner(QueryError::Interrupted(
            StopReason::Deadline
        )))
    ));
    expired.set(false);
    assert_eq!(
        budget.charge(0),
        Err(QueryError::Interrupted(StopReason::Deadline))
    );
}

#[test]
fn division_multiplicity_never_raises_the_original_complete_gate_ceiling() {
    let mut terms = TermStore::new();
    let x = fp_constant(&mut terms, 0x3f800000, 32);
    let y = fp_constant(&mut terms, 0x40400000, 32);
    let actual = div(&mut terms, x, y, 32, RoundingMode::RNE);
    let root = predicate(&mut terms, "fp.isNormal", &[actual]);
    let mut checkpoint = || ControlFlow::Continue(());
    let mut budget = WorkBudget::new(10_000_000_000, &mut checkpoint);
    assert!(matches!(
        source::plan(&terms, &[root; 32], &[], &mut budget),
        Err(FpAdapterError::Unsupported("complete circuit envelope"))
    ));
    drop(budget);
    let mut zero = WorkBudget::new(0, &mut checkpoint);
    assert!(matches!(
        lower_fp_clause(&terms, &[root], &[], &ChcProblem::new(), &mut zero),
        Err(FpAdapterError::Owner(QueryError::Exhausted))
    ));
    assert_eq!(zero.charge(0), Err(QueryError::Exhausted));
}
