// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Fixed-depth patterns over the already strictly typed source arena.
//! Unsupported signedness, operand order, extensions and slices decline.

use super::{Arena, ChcOp, ChcSort, Id, Kind};

#[derive(Clone, Copy)]
pub(super) enum Arithmetic {
    Difference,
    Product,
}

#[derive(Clone, Copy)]
pub(super) enum Polarity {
    Positive,
    Negative,
}

#[derive(Clone, Copy)]
pub(super) struct Candidate {
    pub(super) left: usize,
    pub(super) right: usize,
    pub(super) result: Id,
    pub(super) width: u32,
    pub(super) arithmetic: Arithmetic,
}

pub(super) fn candidate(lhs: Id, rhs: Id, arena: &Arena<'_>) -> Option<Candidate> {
    let Kind::Var(kept) = arena.nodes[lhs].kind else {
        return None;
    };
    let Kind::Op(op, args) = &arena.nodes[rhs].kind else {
        return None;
    };
    let arithmetic = match op {
        ChcOp::BvSub => Arithmetic::Difference,
        ChcOp::BvMul => Arithmetic::Product,
        _ => return None,
    };
    let (Kind::Var(left), Kind::Var(right)) =
        (&arena.nodes[args[0]].kind, &arena.nodes[args[1]].kind)
    else {
        return None;
    };
    let ChcSort::BitVec(width) = arena.nodes[lhs].sort else {
        return None;
    };
    if kept >= arena.kept || left == right || *left < arena.kept || *right < arena.kept {
        return None;
    }
    Some(Candidate {
        left: *left,
        right: *right,
        result: lhs,
        width,
        arithmetic,
    })
}

pub(super) fn flag_binding(
    lhs: Id,
    rhs: Id,
    candidate: Candidate,
    arena: &Arena<'_>,
) -> Option<Polarity> {
    let Kind::Var(kept) = arena.nodes[lhs].kind else {
        return None;
    };
    if kept >= arena.kept || arena.nodes[lhs].sort != ChcSort::Bool {
        return None;
    }
    if observation(rhs, candidate, arena) {
        return Some(Polarity::Positive);
    }
    let Kind::Op(ChcOp::Not, args) = &arena.nodes[rhs].kind else {
        return None;
    };
    observation(args[0], candidate, arena).then_some(Polarity::Negative)
}

pub(super) fn low(id: Id, candidate: Candidate, arena: &Arena<'_>) -> bool {
    let expected = match candidate.arithmetic {
        Arithmetic::Difference => ChcOp::BvSub,
        Arithmetic::Product => ChcOp::BvMul,
    };
    let Kind::Op(op, args) = &arena.nodes[id].kind else {
        return false;
    };
    *op == expected
        && matches!(arena.nodes[args[0]].kind, Kind::Var(var) if var == candidate.left)
        && matches!(arena.nodes[args[1]].kind, Kind::Var(var) if var == candidate.right)
}

pub(super) fn observation(id: Id, candidate: Candidate, arena: &Arena<'_>) -> bool {
    let Kind::Op(op, args) = &arena.nodes[id].kind else {
        return false;
    };
    match candidate.arithmetic {
        Arithmetic::Difference => {
            *op == ChcOp::BvULt
                && matches!(arena.nodes[args[0]].kind, Kind::Var(var) if var == candidate.left)
                && matches!(arena.nodes[args[1]].kind, Kind::Var(var) if var == candidate.right)
        }
        Arithmetic::Product if *op == ChcOp::Eq => [(args[0], args[1]), (args[1], args[0])]
            .into_iter()
            .any(|(high, zero)| {
                matches!(arena.nodes[zero].kind, Kind::BitVec(0, width) if width == candidate.width)
                    && high_product(high, candidate, arena)
            }),
        Arithmetic::Product => false,
    }
}

fn high_product(id: Id, candidate: Candidate, arena: &Arena<'_>) -> bool {
    let Kind::Op(ChcOp::BvExtract(high, low), args) = &arena.nodes[id].kind else {
        return false;
    };
    // Input widths are at most 128, so doubling cannot overflow u32. Strict
    // source admission also enforces the widened result's existing 128 cap.
    if *high != 2 * candidate.width - 1 || *low != candidate.width {
        return false;
    }
    let Kind::Op(ChcOp::BvMul, args) = &arena.nodes[args[0]].kind else {
        return false;
    };
    extended_operand(args[0], candidate.left, candidate.width, arena)
        && extended_operand(args[1], candidate.right, candidate.width, arena)
}

fn extended_operand(id: Id, local: usize, width: u32, arena: &Arena<'_>) -> bool {
    let Kind::Op(ChcOp::BvZeroExtend(extra), args) = &arena.nodes[id].kind else {
        return false;
    };
    *extra == width && matches!(arena.nodes[args[0]].kind, Kind::Var(var) if var == local)
}
