// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

mod native;

fn array() -> ChcSort {
    ChcSort::Array(Box::new(ChcSort::BitVec(64)), Box::new(ChcSort::BitVec(8)))
}

fn scalar(value: u128, width: u32) -> Arc<ChcExpr> {
    Arc::new(ChcExpr::BitVec(value, width))
}

fn request(lower: u128, upper: u128) -> ArrayRangeWrite {
    ArrayRangeWrite {
        destination: ChcVar::new("d", array()),
        result: ChcVar::new("w", array()),
        range: ArrayRange::UnsignedHalfOpen {
            lower: scalar(lower, 64),
            upper: scalar(upper, 64),
        },
    }
}

fn binder() -> ChcVar {
    ChcVar::new("i", ChcSort::BitVec(64))
}

fn text(premise: &UniversalPremise) -> String {
    crate::InvariantModel::expr_to_smtlib(premise.matrix())
}

#[test]
fn typed_copy_keeps_exact_unsigned_frame_and_modular_source_offset() {
    let premise = UniversalPremise::array_range_write(
        binder(),
        request(1, 3),
        ArrayRangeValue::Copy {
            source: ChcVar::new("s", array()),
            source_lower: scalar(0, 64),
        },
    )
    .unwrap();
    assert_eq!(text(&premise), "(= (select w i) (ite (and (bvule (_ bv1 64) i) (bvult i (_ bv3 64))) (select s (bvadd (_ bv0 64) (bvsub i (_ bv1 64)))) (select d i)))");
    assert_eq!(premise.binder(), &binder());
}

#[test]
fn typed_fill_preserves_outside_and_accepts_symbolic_endpoints_without_unrolling() {
    let mut write = request(0, 0);
    write.range = ArrayRange::UnsignedHalfOpen {
        lower: Arc::new(ChcExpr::Var(ChcVar::new("lo", ChcSort::BitVec(64)))),
        upper: Arc::new(ChcExpr::Var(ChcVar::new("hi", ChcSort::BitVec(64)))),
    };
    let premise = UniversalPremise::array_range_write(
        binder(),
        write,
        ArrayRangeValue::Fill(Arc::new(ChcExpr::Var(ChcVar::new(
            "byte",
            ChcSort::BitVec(8),
        )))),
    )
    .unwrap();
    assert_eq!(
        text(&premise),
        "(= (select w i) (ite (and (bvule lo i) (bvult i hi)) byte (select d i)))"
    );
}

#[test]
fn empty_reversed_and_huge_ranges_keep_the_original_literal_guards() {
    for (lower, upper) in [(0, 0), (9, 3), (0, 1 << 40), (0, u64::MAX.into())] {
        let premise = UniversalPremise::array_range_write(
            binder(),
            request(lower, upper),
            ArrayRangeValue::Fill(scalar(7, 8)),
        )
        .unwrap();
        let rendered = text(&premise);
        assert!(rendered.contains(&format!("(bvule (_ bv{lower} 64) i)")));
        assert!(rendered.contains(&format!("(bvult i (_ bv{upper} 64))")));
        assert!(rendered.contains("(select d i)"));
        assert!(rendered.len() < 256);
    }
}

#[test]
fn full_bv64_domain_is_explicit_and_does_not_encode_two_to_64_as_zero() {
    let mut write = request(0, 0);
    write.range = ArrayRange::Full;
    let premise =
        UniversalPremise::array_range_write(binder(), write, ArrayRangeValue::Fill(scalar(9, 8)))
            .unwrap();
    assert_eq!(
        text(&premise),
        "(= (select w i) (ite true (_ bv9 8) (select d i)))"
    );
}

#[test]
fn overlapping_copy_uses_the_old_destination_snapshot_not_new_result() {
    let premise = UniversalPremise::array_range_write(
        binder(),
        request(1, 4),
        ArrayRangeValue::Copy {
            source: ChcVar::new("d", array()),
            source_lower: scalar(0, 64),
        },
    )
    .unwrap();
    assert!(text(&premise).contains("(select d (bvadd (_ bv0 64) (bvsub i (_ bv1 64))))"));
    assert_eq!(text(&premise).matches("(select w").count(), 1);
}

#[test]
fn booleans_and_full_width_bv128_cells_keep_exact_sorts_and_literals() {
    for (sort, value) in [
        (ChcSort::Bool, Arc::new(ChcExpr::Bool(true))),
        (ChcSort::BitVec(128), scalar(u128::MAX, 128)),
    ] {
        let sort = ChcSort::Array(Box::new(ChcSort::BitVec(64)), Box::new(sort));
        let mut write = request(1, 3);
        write.destination.sort = sort.clone();
        write.result.sort = sort;
        assert!(
            UniversalPremise::array_range_write(binder(), write, ArrayRangeValue::Fill(value))
                .is_ok()
        );
    }
}

#[test]
fn result_backedges_and_fresh_binder_capture_are_refused_before_authentication() {
    for name in ["w", "i"] {
        let input = op(
            ChcOp::Select,
            vec![
                Arc::new(ChcExpr::Var(ChcVar::new(name, array()))),
                scalar(0, 64),
            ],
        );
        assert!(UniversalPremise::array_range_write(
            binder(),
            request(1, 3),
            ArrayRangeValue::Fill(input)
        )
        .is_err());
        let mut write = request(1, 3);
        write.range = ArrayRange::UnsignedHalfOpen {
            lower: Arc::new(ChcExpr::Var(ChcVar::new(name, ChcSort::BitVec(64)))),
            upper: scalar(3, 64),
        };
        assert!(UniversalPremise::array_range_write(
            binder(),
            write,
            ArrayRangeValue::Fill(scalar(9, 8))
        )
        .is_err());
    }
    assert!(UniversalPremise::array_range_write(
        binder(),
        request(1, 3),
        ArrayRangeValue::Copy {
            source: ChcVar::new("w", array()),
            source_lower: scalar(0, 64)
        }
    )
    .is_err());
}

#[test]
fn malformed_arity_width_cell_endpoint_and_marker_never_receive_typed_output() {
    for value in [
        Arc::new(ChcExpr::BitVec(256, 8)),
        scalar(0, 0),
        scalar(0, 9),
        Arc::new(ChcExpr::Bool(true)),
        op(ChcOp::BvAdd, vec![scalar(1, 8)]),
        Arc::new(ChcExpr::ConstArrayMarker(ChcSort::BitVec(64))),
    ] {
        assert!(UniversalPremise::array_range_write(
            binder(),
            request(1, 3),
            ArrayRangeValue::Fill(value)
        )
        .is_err());
    }
    for width in [0, 8, 65, 128] {
        let mut write = request(1, 3);
        write.range = ArrayRange::UnsignedHalfOpen {
            lower: scalar(1, width),
            upper: scalar(3, width),
        };
        assert!(UniversalPremise::array_range_write(
            binder(),
            write,
            ArrayRangeValue::Fill(scalar(9, 8))
        )
        .is_err());
    }
}

#[test]
fn wrong_array_keys_cells_names_and_same_old_new_variable_are_refused() {
    for sort in [
        ChcSort::Bool,
        ChcSort::BitVec(64),
        ChcSort::Array(Box::new(ChcSort::BitVec(8)), Box::new(ChcSort::BitVec(8))),
        ChcSort::Array(
            Box::new(ChcSort::BitVec(64)),
            Box::new(ChcSort::BitVec(129)),
        ),
    ] {
        let mut write = request(1, 3);
        write.destination.sort = sort.clone();
        write.result.sort = sort;
        assert!(UniversalPremise::array_range_write(
            binder(),
            write,
            ArrayRangeValue::Fill(scalar(9, 8))
        )
        .is_err());
    }
    for name in ["", "i", "d", "select"] {
        let mut write = request(1, 3);
        write.result.name = name.into();
        assert!(UniversalPremise::array_range_write(
            binder(),
            write,
            ArrayRangeValue::Fill(scalar(9, 8))
        )
        .is_err());
    }
}

#[test]
fn original_check_stop_and_expired_deadline_refuse_without_resetting_enclosing_scope() {
    let stop = ay_core::resource::enter_check_stop(Arc::new(|| true));
    assert!(UniversalPremise::array_range_write(
        binder(),
        request(1, 3),
        ArrayRangeValue::Fill(scalar(9, 8))
    )
    .is_err());
    drop(stop);
    let end = ay_core::time::Instant::now();
    let _deadline = crate::smt::ScopedSmtDeadline::install_until(end);
    assert!(UniversalPremise::array_range_write(
        binder(),
        request(1, 3),
        ArrayRangeValue::Fill(scalar(9, 8))
    )
    .is_err());
    assert_eq!(crate::smt::deadline::current_smt_deadline(), Some(end));
}

#[test]
fn excessive_depth_and_exponential_shared_occurrences_are_bounded_without_recursion() {
    let mut deep = scalar(7, 8);
    for _ in 0..57 {
        deep = op(ChcOp::BvNot, vec![deep]);
    }
    assert!(UniversalPremise::array_range_write(
        binder(),
        request(1, 3),
        ArrayRangeValue::Fill(deep)
    )
    .is_err());
    let mut repeated = scalar(7, 8);
    for _ in 0..16 {
        repeated = op(ChcOp::BvXor, vec![Arc::clone(&repeated), repeated]);
    }
    assert!(UniversalPremise::array_range_write(
        binder(),
        request(1, 3),
        ArrayRangeValue::Fill(repeated)
    )
    .is_err());
}

#[test]
fn premise_enters_retained_typed_source_with_all_outer_variables_and_original_quantifier() {
    let premise = UniversalPremise::array_range_write(
        binder(),
        request(1, 3),
        ArrayRangeValue::Copy {
            source: ChcVar::new("s", array()),
            source_lower: scalar(0, 64),
        },
    )
    .unwrap();
    let problem = QuantifiedChcProblem::new(
        ChcProblem::new(),
        vec![QuantifiedHornClause::new(
            HornClause::query(ClauseBody::constraint(ChcExpr::Bool(true))),
            vec![premise],
        )],
    )
    .unwrap();
    let source = problem.source_smtlib();
    assert!(source.contains("(forall ((i (_ BitVec 64)))"));
    for name in ["d", "s", "w"] {
        assert!(source.contains(&format!("({name} (Array (_ BitVec 64) (_ BitVec 8)))")));
    }
    assert!(source.contains("(select s (bvadd (_ bv0 64) (bvsub i (_ bv1 64))))"));
}
