// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

fn bv(value: u64) -> Expr {
    Expr::bitvec_const(value, 64)
}

#[test]
fn every_bound_and_nonarray_destination_is_checked_before_construction() {
    let d = Expr::const_array(Sort::bitvec(64), Expr::true_());
    for wrong in 0..3 {
        let mut bounds = [bv(0), bv(3), bv(0)];
        bounds[wrong] = Expr::bitvec_const(0, 32);
        let [lo, hi, start] = bounds;
        assert!(d
            .clone()
            .try_array_range_copy(d.clone(), lo, hi, start)
            .is_err());
    }
    assert!(bv(0).try_array_range_copy(d, bv(0), bv(3), bv(0)).is_err());
}

#[test]
fn bool_and_full_bv128_cells_preserve_sort_and_borrowed_owned_child_order() {
    for cell in [Expr::true_(), Expr::bitvec_const(u128::MAX, 128)] {
        let d = Expr::const_array(Sort::bitvec(64), cell);
        let operands = [d.clone(), d.clone(), bv(1), bv(4), bv(u64::MAX)];
        let value = operands[0]
            .clone()
            .try_array_range_copy(
                operands[1].clone(),
                operands[2].clone(),
                operands[3].clone(),
                operands[4].clone(),
            )
            .unwrap();
        assert_eq!(value.sort(), d.sort());
        assert!(value.value().is_known_variant());
        assert_eq!(
            value.children().cloned().collect::<Vec<_>>(),
            operands.to_vec()
        );
        assert_eq!(value.value().clone().into_children_vec(), operands.to_vec());
    }
}

#[test]
fn parallel_let_rhs_keeps_adversarial_names_outside_the_private_lambda() {
    let a = Sort::array(Sort::bitvec(64), Sort::bool());
    let value = Expr::var("ay_range_src", a.clone())
        .try_array_range_copy(
            Expr::var("ay_range_dst", a),
            Expr::var("ay_range_i", Sort::bitvec(64)),
            Expr::var("ay_range_lo", Sort::bitvec(64)),
            Expr::var("ay_range_hi", Sort::bitvec(64)),
        )
        .unwrap();
    let text = value.to_string();
    assert!(text.starts_with("(let ((ay_range_dst ay_range_src) (ay_range_src ay_range_dst) "));
    assert!(text.contains(
        "(ay_range_lo ay_range_i) (ay_range_hi ay_range_lo) (ay_range_src_lo ay_range_hi)"
    ));
    assert!(text.contains("(lambda ((ay_range_i (_ BitVec 64)))"));
    assert_eq!(text.matches("(let ").count(), 1);
    assert_eq!(text.matches("(lambda ").count(), 1);
}

#[test]
fn iterative_drop_visits_all_range_children_and_preserves_shared_survivors() {
    let source = Expr::const_array(Sort::bitvec(64), Expr::bitvec_const(u128::MAX, 128));
    let mut value = source.clone();
    for _ in 0..4096 {
        value = value
            .try_array_range_copy(source.clone(), bv(0), bv(2), bv(1))
            .unwrap();
    }
    let survivor = value.clone();
    drop(value);
    assert_eq!(survivor.children().count(), 5);
    drop(survivor);
    assert_eq!(source.children().count(), 1);
    assert!(
        matches!(source.children().next().unwrap().value(), ExprValue::BitVecConst { value, width: 128 } if value == &num_bigint::BigInt::from(u128::MAX))
    );
}

#[test]
#[cfg(feature = "direct")]
fn native_read_beta_preserves_modulo_offsets_bv64_max_and_full_bv128_cells() {
    use crate::execute_direct::ExecuteResult;
    let end = std::time::Instant::now() + std::time::Duration::from_secs(20);
    let cell = Expr::bitvec_const(u128::MAX, 128);
    let src = Expr::const_array(Sort::bitvec(64), Expr::bitvec_const(2, 128))
        .store(bv(u64::MAX), cell.clone())
        .store(bv(0), Expr::bitvec_const(3, 128));
    let dst = Expr::const_array(Sort::bitvec(64), Expr::bitvec_const(7, 128));
    let copied = dst
        .clone()
        .try_array_range_copy(src.clone(), bv(1), bv(3), bv(u64::MAX))
        .unwrap();
    let boundary = dst
        .try_array_range_copy(src, bv(u64::MAX - 1), bv(u64::MAX), bv(u64::MAX))
        .unwrap();
    for (array, at, expected) in [
        (copied.clone(), 1, cell.clone()),
        (copied.clone(), 2, Expr::bitvec_const(3, 128)),
        (copied, 3, Expr::bitvec_const(7, 128)),
        (boundary.clone(), u64::MAX - 1, cell),
        (boundary, u64::MAX, Expr::bitvec_const(7, 128)),
    ] {
        let eq = array.select(bv(at)).eq(expected);
        assert!(matches!(
            direct(end, eq.clone().not()),
            ExecuteResult::Verified
        ));
        assert!(matches!(
            direct(end, eq),
            ExecuteResult::Counterexample { .. }
        ));
    }
}

#[test]
#[cfg(feature = "direct")]
fn empty_interval_still_translates_every_source_and_bound_occurrence() {
    let end = std::time::Instant::now() + std::time::Duration::from_secs(20);
    let a = Expr::const_array(Sort::bitvec(64), Expr::true_());
    for missing in 0..5 {
        let mut operands = [a.clone(), a.clone(), bv(2), bv(1), bv(0)];
        operands[missing] = Expr::var("not_declared", operands[missing].sort().clone());
        let [dst, src, lo, hi, start] = operands;
        let value = dst.try_array_range_copy(src, lo, hi, start).unwrap();
        let mut program = crate::AYProgram::new();
        program.set_logic("ALL");
        let remaining = end
            .checked_duration_since(std::time::Instant::now())
            .unwrap();
        assert!(remaining.as_millis() > 0);
        program.set_option("timeout", remaining.as_millis().to_string());
        program.assert(value.select(bv(0)));
        program.check_sat();
        let error = crate::execute_direct::execute(&program).unwrap_err();
        assert!(
            error
                .to_string()
                .contains("undefined variable: not_declared"),
            "{error}"
        );
        drop(program);
        assert!(std::time::Instant::now() < end);
    }
}

#[test]
#[cfg(feature = "direct")]
fn forged_result_sort_is_refused_before_translating_undefined_operands() {
    let end = std::time::Instant::now() + std::time::Duration::from_secs(20);
    let a = Sort::array(Sort::bitvec(64), Sort::bool());
    let bad = Expr {
        sort: Sort::bool(),
        value: Arc::new(ExprValue::ArrayRangeCopy {
            dst: Expr::var("not_declared", a.clone()),
            src: Expr::var("not_declared", a),
            lo: bv(0),
            hi: bv(1),
            src_start: bv(0),
        }),
    };
    let mut program = crate::AYProgram::new();
    program.set_logic("ALL");
    let remaining = end
        .checked_duration_since(std::time::Instant::now())
        .unwrap();
    assert!(remaining.as_millis() > 0);
    program.set_option("timeout", remaining.as_millis().to_string());
    program.assert(bad);
    program.check_sat();
    let error = crate::execute_direct::execute(&program).unwrap_err();
    assert!(
        error
            .to_string()
            .contains("range-copy array/bound sorts differ"),
        "{error}"
    );
    drop(program);
    assert!(std::time::Instant::now() < end);
}
