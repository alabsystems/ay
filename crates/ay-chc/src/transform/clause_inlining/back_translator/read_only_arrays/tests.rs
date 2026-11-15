// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::super::{bounded_cases, exact_projection, InliningBackTranslator};
use super::*;
use crate::smt::SmtContext;
use crate::PredicateInterpretation;

fn bv(name: &str, width: u32) -> ChcVar {
    ChcVar::new(name, ChcSort::BitVec(width))
}

fn memory(name: &str, index: u32, element: u32) -> ChcVar {
    ChcVar::new(
        name,
        ChcSort::Array(
            Box::new(ChcSort::BitVec(index)),
            Box::new(ChcSort::BitVec(element)),
        ),
    )
}

fn read(array: &ChcVar, index: ChcExpr) -> ChcExpr {
    ChcExpr::select(ChcExpr::var(array.clone()), index)
}

fn lit(value: u128, width: u32) -> ChcExpr {
    ChcExpr::BitVec(value, width)
}

/// `left` and `right` agree on every assignment (an SMT check of their XOR).
fn equivalent(left: &ChcExpr, right: &ChcExpr) -> bool {
    let differ = ChcExpr::not(ChcExpr::eq(left.clone(), right.clone()));
    SmtContext::new().check_sat(&differ).is_unsat()
}

fn close(keep: &[ChcVar], formula: ChcExpr) -> Option<ChcExpr> {
    InliningBackTranslator::close_synthesized_interpretation(PredicateInterpretation::new(
        keep.to_vec(),
        formula,
    ))
    .map(|interp| interp.formula)
}

/// The shape model-checker-consumer `safe_symbolic_from_elem` inlines into `bb5`: a seeded
/// memory, a pointer that is one of two seeded cells, and a read through it
/// that is known not to be the first cell's value. Its exact image is
/// `out = 3`; before the array elimination no projection closed it.
#[test]
fn a_read_through_a_pointer_into_seeded_memory_closes_exactly() {
    let mem = memory("mem", 64, 32);
    let pointer = bv("p", 64);
    let out = bv("out", 32);
    let flag = ChcVar::new("flag", ChcSort::Bool);
    let (c0, c1, c2) = (0x3_0000_0004, 0x3_0000_0000, 0x3_0000_0008);
    let seeded = |cell: u128| {
        ChcExpr::and_all([
            ChcExpr::eq(read(&mem, lit(c0, 64)), lit(2, 32)),
            ChcExpr::eq(read(&mem, lit(c1, 64)), lit(1, 32)),
            ChcExpr::eq(read(&mem, lit(c2, 64)), lit(3, 32)),
            ChcExpr::eq(ChcExpr::var(pointer.clone()), lit(cell, 64)),
        ])
    };
    let formula = ChcExpr::and_all([
        ChcExpr::not(ChcExpr::eq(ChcExpr::var(pointer.clone()), lit(0, 64))),
        ChcExpr::or(seeded(c0), seeded(c2)),
        ChcExpr::eq(
            ChcExpr::var(out.clone()),
            read(&mem, ChcExpr::var(pointer.clone())),
        ),
        ChcExpr::not(ChcExpr::eq(
            read(&mem, ChcExpr::var(pointer.clone())),
            lit(2, 32),
        )),
    ]);
    let projected = close(&[out.clone(), flag], formula).expect("the image closes");
    assert!(
        equivalent(&projected, &ChcExpr::eq(ChcExpr::var(out), lit(3, 32))),
        "exact image is out = 3, got {projected}"
    );
}

/// Two reads at indices that MAY be equal must agree when they are: the
/// consistency constraint is what makes the elimination exact. Here the reads
/// disagree, so the indices cannot coincide and the image is `out != 5`;
/// dropping the constraint would wrongly give `true`.
#[test]
fn reads_at_possibly_equal_indices_keep_their_consistency() {
    let mem = memory("mem", 8, 8);
    let (i, j, out) = (bv("i", 8), bv("j", 8), bv("out", 8));
    let formula = ChcExpr::and_all([
        ChcExpr::eq(read(&mem, ChcExpr::var(i.clone())), lit(1, 8)),
        ChcExpr::eq(read(&mem, ChcExpr::var(j.clone())), lit(2, 8)),
        ChcExpr::eq(ChcExpr::var(i), ChcExpr::var(out.clone())),
        ChcExpr::eq(ChcExpr::var(j), lit(5, 8)),
    ]);
    let rewritten = ackermannize(&formula, std::slice::from_ref(&out)).expect("mem is read-only");
    assert_eq!(
        rewritten.vars().iter().filter(|v| v.name == "mem").count(),
        0,
        "mem is eliminated: {rewritten}"
    );
    let projected = close(std::slice::from_ref(&out), formula).expect("the image closes");
    assert!(
        equivalent(
            &projected,
            &ChcExpr::not(ChcExpr::eq(ChcExpr::var(out), lit(5, 8)))
        ),
        "exact image is out != 5, got {projected}"
    );
}

#[test]
fn reads_at_distinct_literals_add_no_constraint() {
    let mem = memory("mem", 8, 8);
    let out = bv("out", 8);
    let formula = ChcExpr::and_all([
        ChcExpr::eq(read(&mem, lit(1, 8)), ChcExpr::var(out.clone())),
        ChcExpr::eq(read(&mem, lit(2, 8)), lit(7, 8)),
        ChcExpr::eq(read(&mem, lit(1, 8)), lit(4, 8)),
    ]);
    let rewritten = ackermannize(&formula, std::slice::from_ref(&out)).expect("mem is read-only");
    let names: Vec<String> = rewritten.vars().into_iter().map(|v| v.name).collect();
    assert_eq!(
        names.len(),
        3,
        "out and one point per distinct index: {names:?}"
    );
    assert!(
        !rewritten
            .collect_conjuncts()
            .iter()
            .any(|c| matches!(c, ChcExpr::Op(ChcOp::Or, _))),
        "no consistency disjunction between distinct literals: {rewritten}"
    );
}

#[test]
fn an_array_that_is_stored_to_compared_or_kept_is_left_alone() {
    let mem = memory("mem", 8, 8);
    let other = memory("other", 8, 8);
    let out = bv("out", 8);
    let stored = ChcExpr::and(
        ChcExpr::eq(read(&mem, lit(1, 8)), ChcExpr::var(out.clone())),
        ChcExpr::eq(
            ChcExpr::var(other.clone()),
            ChcExpr::store(ChcExpr::var(mem.clone()), lit(2, 8), lit(3, 8)),
        ),
    );
    // `other` is read nowhere, `mem` is stored to: neither is read-only.
    assert!(ackermannize(&stored, std::slice::from_ref(&out)).is_none());

    let compared = ChcExpr::and(
        ChcExpr::eq(read(&mem, lit(1, 8)), ChcExpr::var(out.clone())),
        ChcExpr::eq(ChcExpr::var(mem.clone()), ChcExpr::var(other.clone())),
    );
    assert!(ackermannize(&compared, std::slice::from_ref(&out)).is_none());

    let kept = ChcExpr::eq(read(&mem, lit(1, 8)), ChcExpr::var(out.clone()));
    assert!(ackermannize(&kept, &[out, mem]).is_none());
}

#[test]
fn a_read_indexed_by_another_local_array_is_left_alone() {
    let outer = memory("outer", 8, 8);
    let inner = memory("inner", 8, 8);
    let out = bv("out", 8);
    let formula = ChcExpr::eq(
        read(&outer, read(&inner, lit(1, 8))),
        ChcExpr::var(out.clone()),
    );
    let rewritten = ackermannize(&formula, std::slice::from_ref(&out)).expect("inner is read-only");
    let names: Vec<String> = rewritten.vars().into_iter().map(|v| v.name).collect();
    assert!(names.contains(&"outer".to_string()), "{rewritten}");
    assert!(!names.contains(&"inner".to_string()), "{rewritten}");
}

#[test]
fn fresh_points_never_capture_a_source_name() {
    let mem = memory("mem", 8, 8);
    let taken = bv("__ack0_mem", 8);
    let formula = ChcExpr::and(
        ChcExpr::eq(read(&mem, lit(1, 8)), lit(4, 8)),
        ChcExpr::eq(ChcExpr::var(taken.clone()), lit(9, 8)),
    );
    let rewritten = ackermannize(&formula, &[taken]).expect("mem is read-only");
    let names: Vec<String> = rewritten.vars().into_iter().map(|v| v.name).collect();
    assert!(names.contains(&"__ack0_mem_".to_string()), "{names:?}");
    assert!(
        equivalent(
            &close(&[bv("__ack0_mem", 8)], formula).expect("closes"),
            &ChcExpr::eq(ChcExpr::var(bv("__ack0_mem", 8)), lit(9, 8))
        ),
        "the kept variable keeps its own constraint"
    );
}

/// The shape of `bb5`'s inlined definition itself: the pointer is the element
/// address `concat(#x00000003, #x00000004 + extract(i * 4))` of an offset
/// `i < 2`, so after the array is eliminated the offset is a local no rule
/// inverts. Its cases make the address a literal: the image is `out = 3`.
#[test]
fn a_read_at_a_bounded_offset_closes_by_cases() {
    let mem = memory("mem", 64, 32);
    let offset = bv("i", 64);
    let out = bv("out", 32);
    let scaled = ChcExpr::Op(
        ChcOp::BvMul,
        vec![
            std::sync::Arc::new(ChcExpr::var(offset.clone())),
            std::sync::Arc::new(lit(4, 64)),
        ],
    );
    let low = ChcExpr::Op(
        ChcOp::BvAdd,
        vec![
            std::sync::Arc::new(lit(4, 32)),
            std::sync::Arc::new(ChcExpr::Op(
                ChcOp::BvExtract(31, 0),
                vec![std::sync::Arc::new(scaled)],
            )),
        ],
    );
    let address = ChcExpr::Op(
        ChcOp::BvConcat,
        vec![std::sync::Arc::new(lit(3, 32)), std::sync::Arc::new(low)],
    );
    let formula = ChcExpr::and_all([
        ChcExpr::eq(read(&mem, lit(0x3_0000_0004, 64)), lit(2, 32)),
        ChcExpr::eq(read(&mem, lit(0x3_0000_0000, 64)), lit(1, 32)),
        ChcExpr::eq(read(&mem, lit(0x3_0000_0008, 64)), lit(3, 32)),
        ChcExpr::Op(
            ChcOp::BvULt,
            vec![
                std::sync::Arc::new(ChcExpr::var(offset)),
                std::sync::Arc::new(lit(2, 64)),
            ],
        ),
        ChcExpr::eq(ChcExpr::var(out.clone()), read(&mem, address.clone())),
        ChcExpr::not(ChcExpr::eq(read(&mem, address), lit(2, 32))),
    ]);
    let reduced = ackermannize(&formula, std::slice::from_ref(&out)).expect("read-only array");
    assert!(matches!(
        exact_projection::project(&reduced, std::slice::from_ref(&out)),
        exact_projection::Projection::Declined
    ));
    let projected = close(std::slice::from_ref(&out), formula).expect("the image closes");
    assert!(
        equivalent(&projected, &ChcExpr::eq(ChcExpr::var(out), lit(3, 32))),
        "exact image is out = 3, got {projected}"
    );
}

#[test]
fn a_stopped_reduced_projection_never_retries_with_fresh_credit() {
    let mem = memory("mem", 2, 2);
    let out = bv("out", 2);
    let local = bv("local", 2);
    let mut deep = ChcExpr::eq(ChcExpr::var(local.clone()), lit(0, 2));
    // The source is valid but exceeds exact projection's 128-frame scope.
    // Raw operators avoid the constructors' double-negation simplification.
    for _ in 0..140 {
        deep = ChcExpr::Op(ChcOp::Not, vec![std::sync::Arc::new(deep)]);
    }
    let formula = ChcExpr::and_all([
        ChcExpr::eq(read(&mem, lit(0, 2)), ChcExpr::var(out.clone())),
        ChcExpr::Op(
            ChcOp::BvULt,
            vec![
                std::sync::Arc::new(ChcExpr::var(local)),
                std::sync::Arc::new(lit(1, 2)),
            ],
        ),
        deep,
    ]);
    let keep = std::slice::from_ref(&out);
    let reduced = ackermannize(&formula, keep).expect("read-only array");
    assert!(matches!(
        exact_projection::project(&reduced, keep),
        exact_projection::Projection::Stopped
    ));
    // This is a genuine regression for the caller, not just another None:
    // the old retry simplified the deep term, granted a new scope, and closed.
    let split = bounded_cases::split(&reduced, keep).expect("bounded local has one case");
    assert!(matches!(
        exact_projection::project(&split, keep),
        exact_projection::Projection::Closed(_)
    ));
    assert!(
        close(keep, formula).is_none(),
        "Stopped must suppress every fallback"
    );
}
