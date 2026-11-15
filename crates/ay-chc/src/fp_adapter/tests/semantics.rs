// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Independent constant oracle versus the complete unchanged FP circuit.

use num_traits::ToPrimitive;

use super::*;

fn constant_truth(terms: &TermStore, root: TermId) -> bool {
    let mut checkpoint = || ControlFlow::Continue(());
    let mut budget = WorkBudget::new(10_000_000_000, &mut checkpoint);
    let plan = source::plan(terms, &[root], &[], &mut budget).unwrap();
    plan.prepay(&mut budget).unwrap();
    let built = encoding::build(terms, &[root], &plan, &mut budget).unwrap();
    // Unit propagation is independent of the FP arithmetic implementation.
    // All original leaves here are constants; definitional gates determine
    // every reachable root, without any SAT/model/proof authority transfer.
    let mut values = vec![None; built.encoding.cache.next_var as usize];
    loop {
        let mut changed = false;
        for clause in &built.encoding.clauses {
            let mut open = Vec::new();
            let mut satisfied = false;
            for &lit in clause.literals() {
                match values[lit.unsigned_abs() as usize] {
                    Some(value) if value == (lit > 0) => satisfied = true,
                    Some(_) => {}
                    None => open.push(lit),
                }
            }
            if !satisfied {
                assert!(!open.is_empty(), "constant circuit clauses are consistent");
                if open.len() == 1 {
                    let lit = open[0];
                    values[lit.unsigned_abs() as usize] = Some(lit > 0);
                    changed = true;
                }
            }
        }
        if !changed {
            break;
        }
    }
    let lit = built.roots[0];
    values[lit.unsigned_abs() as usize].expect("constant root determined") == (lit > 0)
}

#[test]
fn ieee_equality_and_sort_identity_distinguish_signed_zero_and_nan_payloads() {
    for (width, sign, nan) in [
        (32, 1u64 << 31, 0x7fc00000u64),
        (64, 1u64 << 63, 0x7ff8000000000000u64),
    ] {
        for (name, a, b, expected) in [
            ("fp.eq", 0, sign, true),
            ("=", 0, sign, false),
            ("fp.eq", nan, nan | 1, false),
            ("=", nan, sign | nan | 1, true),
        ] {
            let mut terms = TermStore::new();
            let a = fp_constant(&mut terms, a, width);
            let b = fp_constant(&mut terms, b, width);
            let root = predicate(&mut terms, name, &[a, b]);
            assert_eq!(constant_truth(&terms, root), expected);
        }
    }
}

#[test]
fn exact_classification_and_quiet_order_match_independent_rational_oracle() {
    for (width, eb, sb, sign, infinity) in [
        (32, 8, 24, 1u64 << 31, 0x7f800000u64),
        (64, 11, 53, 1u64 << 63, 0x7ff0000000000000u64),
    ] {
        let patterns = [
            0,
            sign,
            1,
            sign | 1,
            infinity,
            sign | infinity,
            infinity | 1,
        ];
        for bits in patterns {
            let value = ay_fp::exact::from_ieee_bits(&bits.into(), eb, sb).unwrap();
            for name in [
                "fp.isNaN",
                "fp.isInfinite",
                "fp.isZero",
                "fp.isNormal",
                "fp.isSubnormal",
                "fp.isNegative",
                "fp.isPositive",
            ] {
                let mut terms = TermStore::new();
                let x = fp_constant(&mut terms, bits, width);
                let root = predicate(&mut terms, name, &[x]);
                assert_eq!(
                    constant_truth(&terms, root),
                    ay_fp::exact::classify(name, &value).unwrap()
                );
            }
            for other in patterns {
                let right = ay_fp::exact::from_ieee_bits(&other.into(), eb, sb).unwrap();
                for (name, expected) in [
                    ("fp.eq", ay_fp::exact::fp_eq(&value, &right)),
                    ("fp.lt", ay_fp::exact::fp_lt(&value, &right)),
                    ("fp.leq", ay_fp::exact::fp_leq(&value, &right)),
                    ("fp.gt", ay_fp::exact::fp_lt(&right, &value)),
                    ("fp.geq", ay_fp::exact::fp_leq(&right, &value)),
                ] {
                    let mut terms = TermStore::new();
                    let x = fp_constant(&mut terms, bits, width);
                    let y = fp_constant(&mut terms, other, width);
                    let root = predicate(&mut terms, name, &[x, y]);
                    assert_eq!(constant_truth(&terms, root), expected.unwrap());
                }
            }
        }
    }
}

#[test]
fn add_sub_mul_all_five_modes_match_exact_oracle_at_ties_and_boundaries() {
    for (width, eb, sb, one, half_ulp, max, infinity, sign) in [
        (
            32,
            8,
            24,
            0x3f800000u64,
            0x33800000u64,
            0x7f7fffffu64,
            0x7f800000u64,
            1u64 << 31,
        ),
        (
            64,
            11,
            53,
            0x3ff0000000000000u64,
            0x3ca0000000000000u64,
            0x7fefffffffffffffu64,
            0x7ff0000000000000u64,
            1u64 << 63,
        ),
    ] {
        for mode in ay_fp::RM_ORDER {
            for (left, right) in [
                (one, half_ulp),
                (one + 1, one + 1),
                (max, max),
                (1, one),
                (sign, 0),
                (infinity, 0),
            ] {
                let x = ay_fp::exact::from_ieee_bits(&left.into(), eb, sb).unwrap();
                let y = ay_fp::exact::from_ieee_bits(&right.into(), eb, sb).unwrap();
                for (name, expected) in [
                    ("fp.add", ay_fp::exact::add(mode, &x, &y)),
                    ("fp.sub", ay_fp::exact::sub(mode, &x, &y)),
                    ("fp.mul", ay_fp::exact::mul(mode, &x, &y)),
                ] {
                    let expected_bits = expected.unwrap().to_ieee_bv().0.to_u64().unwrap();
                    let mut terms = TermStore::new();
                    let a = fp_constant(&mut terms, left, width);
                    let b = fp_constant(&mut terms, right, width);
                    let rm = terms.mk_app(
                        Symbol::named(mode.name()),
                        [],
                        Sort::Uninterpreted("RoundingMode".into()),
                    );
                    let actual =
                        terms.mk_app(Symbol::named(name), [rm, a, b], Sort::FloatingPoint(eb, sb));
                    let expected = fp_constant(&mut terms, expected_bits, width);
                    // SMT element equality accepts every NaN pattern; this is
                    // deliberately not a raw-NaN-output equality claim.
                    let root = predicate(&mut terms, "=", &[actual, expected]);
                    assert!(constant_truth(&terms, root), "{name} {mode:?} width{width}");
                }
            }
        }
    }
}
