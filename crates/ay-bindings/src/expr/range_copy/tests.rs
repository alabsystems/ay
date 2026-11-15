// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

mod extra;

fn range(hi: u64) -> Expr {
    Expr::const_array(Sort::bitvec(64), Expr::bitvec_const(7, 8))
        .try_array_range_copy(
            Expr::const_array(Sort::bitvec(64), Expr::bitvec_const(9, 8)),
            Expr::bitvec_const(1, 64),
            Expr::bitvec_const(hi, 64),
            Expr::bitvec_const(0, 64),
        )
        .unwrap()
}

#[test]
fn range_signature_refuses_mismatched_arrays_keys_and_bounds() {
    let d = Expr::const_array(Sort::bitvec(64), Expr::bitvec_const(7, 8));
    let s = Expr::const_array(Sort::bitvec(64), Expr::bitvec_const(9, 16));
    assert!(d
        .clone()
        .try_array_range_copy(
            s,
            Expr::bitvec_const(1, 64),
            Expr::bitvec_const(3, 64),
            Expr::bitvec_const(0, 64)
        )
        .is_err());
    assert!(d
        .clone()
        .try_array_range_copy(
            d,
            Expr::bitvec_const(1, 32),
            Expr::bitvec_const(3, 64),
            Expr::bitvec_const(0, 64)
        )
        .is_err());
    let bad = Expr::const_array(Sort::bitvec(32), Expr::bitvec_const(7, 8));
    assert!(bad
        .clone()
        .try_array_range_copy(
            bad,
            Expr::bitvec_const(1, 64),
            Expr::bitvec_const(3, 64),
            Expr::bitvec_const(0, 64)
        )
        .is_err());
}

#[test]
fn huge_intervals_have_five_children_and_one_lambda_without_stores() {
    for high in [3, 1 << 40, u64::MAX] {
        let value = range(high);
        assert_eq!(value.children().count(), 5);
        assert_eq!(value.to_string().matches("(lambda ").count(), 1);
        assert_eq!(value.to_string().matches("(store ").count(), 0);
        assert!(value.to_string().len() < 600);
    }
}

#[test]
fn generic_fold_rebuilds_every_operand_without_making_a_binder_child() {
    struct Rename;
    impl super::super::fold::ExprFold for Rename {
        fn fold_var(&mut self, name: &str, sort: &Sort) -> Expr {
            Expr::var(format!("renamed_{name}"), sort.clone())
        }
    }
    let a = Sort::array(Sort::bitvec(64), Sort::bitvec(8));
    let value = Expr::var("dst", a.clone())
        .try_array_range_copy(
            Expr::var("src", a),
            Expr::var("lo", Sort::bitvec(64)),
            Expr::var("hi", Sort::bitvec(64)),
            Expr::var("src_lo", Sort::bitvec(64)),
        )
        .unwrap();
    let value = super::super::fold::fold_expr(&mut Rename, &value);
    assert_eq!(value.children().count(), 5);
    for child in value.children() {
        assert!(matches!(child.value(), ExprValue::Var{name} if name.starts_with("renamed_")));
    }
}

#[cfg(feature = "direct")]
fn direct(end: std::time::Instant, claim: Expr) -> crate::execute_direct::ExecuteResult {
    let remaining = end
        .checked_duration_since(std::time::Instant::now())
        .unwrap();
    assert!(remaining.as_millis() > 0, "original fixture end elapsed");
    let mut program = crate::AYProgram::new();
    program.set_logic("ALL");
    program.set_option("timeout", remaining.as_millis().to_string());
    program.assert(claim);
    program.check_sat();
    let result = crate::execute_direct::execute(&program).unwrap();
    drop(program);
    assert!(
        std::time::Instant::now() < end,
        "original fixture end elapsed"
    );
    result
}

#[test]
#[cfg(feature = "direct")]
fn actual_direct_preserved_and_written_lanes_are_safe_and_reachable_lane_is_sat() {
    use crate::execute_direct::ExecuteResult;
    let end = std::time::Instant::now() + std::time::Duration::from_secs(20);
    let range = range(3);
    for (lane, expected) in [(0, 7), (1, 9), (2, 9), (3, 7)] {
        let equality = range
            .clone()
            .select(Expr::bitvec_const(lane, 64))
            .eq(Expr::bitvec_const(expected, 8));
        assert!(matches!(
            direct(end, equality.clone().not()),
            ExecuteResult::Verified
        ));
        assert!(matches!(
            direct(end, equality),
            ExecuteResult::Counterexample { .. }
        ));
    }
}

#[test]
#[cfg(feature = "direct")]
fn aliased_memmove_uses_the_old_source_and_empty_intervals_preserve_destination() {
    use crate::execute_direct::ExecuteResult;
    let end = std::time::Instant::now() + std::time::Duration::from_secs(20);
    let mut d = Expr::const_array(Sort::bitvec(64), Expr::bitvec_const(4, 8));
    for (i, v) in [(0, 1), (1, 2), (2, 3)] {
        d = d.store(Expr::bitvec_const(i, 64), Expr::bitvec_const(v, 8));
    }
    let copied = d
        .clone()
        .try_array_range_copy(
            d.clone(),
            Expr::bitvec_const(1, 64),
            Expr::bitvec_const(3, 64),
            Expr::bitvec_const(0, 64),
        )
        .unwrap();
    for (lane, expected) in [(0, 1), (1, 1), (2, 2), (3, 4)] {
        assert!(matches!(
            direct(
                end,
                copied
                    .clone()
                    .select(Expr::bitvec_const(lane, 64))
                    .eq(Expr::bitvec_const(expected, 8))
                    .not()
            ),
            ExecuteResult::Verified
        ));
    }
    for (lo, hi) in [(2, 2), (3, 1)] {
        let empty = d
            .clone()
            .try_array_range_copy(
                range(3),
                Expr::bitvec_const(lo, 64),
                Expr::bitvec_const(hi, 64),
                Expr::bitvec_const(0, 64),
            )
            .unwrap();
        assert!(matches!(
            direct(
                end,
                empty
                    .select(Expr::bitvec_const(1, 64))
                    .eq(Expr::bitvec_const(2, 8))
                    .not()
            ),
            ExecuteResult::Verified
        ));
    }
}
