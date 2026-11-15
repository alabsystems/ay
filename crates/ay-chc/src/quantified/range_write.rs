// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Constant-size, exact definitional array updates for typed clause lowering.
//! The pointwise definition and frame follow SMT-LIB ArraysEx extensionality:
//! https://smt-lib.org/theories-ArraysEx.shtml. Index arithmetic follows
//! https://smt-lib.org/theories-FixedSizeBitVectors.shtml, modulo 2^64.

use std::sync::Arc;

use super::{QuantifiedChcProblem, QuantifiedHornClause, UniversalPremise};
use crate::{
    ChcError, ChcExpr, ChcOp, ChcProblem, ChcResult, ChcSort, ChcVar, ClauseBody, HornClause,
};

#[cfg(test)]
mod tests;

/// An unsigned, nonwrapping index interval, or the entire BV64 domain.
/// Empty and reversed half-open intervals preserve the complete destination.
/// `Full` is explicit: no BV64 upper endpoint can denote the integer 2^64.
#[derive(Debug, Clone)]
pub enum ArrayRange {
    UnsignedHalfOpen {
        lower: Arc<ChcExpr>,
        upper: Arc<ChcExpr>,
    },
    Full,
}

/// Exact pre-state and post-state array variables for one update.
/// Construction grants no source, proof, native model or memory-layout credential.
#[derive(Debug, Clone)]
pub struct ArrayRangeWrite {
    pub destination: ChcVar,
    pub result: ChcVar,
    pub range: ArrayRange,
}

/// Values assigned throughout the range, captured from the pre-state.
#[derive(Debug, Clone)]
pub enum ArrayRangeValue {
    Fill(Arc<ChcExpr>),
    /// Read `source[source_lower + (index - lower)]`, modulo 2^64.
    /// For `Full`, lower is zero. `source` may equal the old destination,
    /// giving snapshot/memmove semantics; it must not be the result variable.
    Copy {
        source: ChcVar,
        source_lower: Arc<ChcExpr>,
    },
}

impl UniversalPremise {
    /// Build a typed definitional premise and frame without enumerating lanes.
    ///
    /// The fresh BV64 binder scopes exactly this premise. Arrays have BV64 keys
    /// and Bool/BV1..128 cells. Scalar endpoints/values are borrowed through Arc;
    /// all input occurrences and exact signatures are checked before return.
    /// Fill covers the selected interval; copy captures the WHOLE old source.
    /// Both retain the destination outside the interval. No byte-layout, bounds,
    /// overlap, initialization or definedness condition is inferred: those must
    /// remain explicit constraints in the caller's original clause.
    ///
    /// The result is source DATA, not a verdict. Attach it to QuantifiedHornClause
    /// and authenticate the complete retained source with QuantifiedChcProblem.
    /// Never drop it when converting to an ordinary unquantified ChcProblem.
    /// Logical/depth/name limits and cooperative checks are not hard RSS or
    /// latency guarantees. No new caller time or memory allowance is granted.
    pub fn array_range_write(
        binder: ChcVar,
        write: ArrayRangeWrite,
        value: ArrayRangeValue,
    ) -> ChcResult<Self> {
        let stop = ay_core::resource::current_check_stop()
            .map_err(|_| invalid("original check-stop observation unavailable"))?;
        poll(&stop)?;
        variable(&binder)?;
        variable(&write.destination)?;
        variable(&write.result)?;
        if binder.sort != ChcSort::BitVec(64)
            || write.destination.sort != write.result.sort
            || !array_sort(&write.destination.sort)
            || binder.name == write.destination.name
            || binder.name == write.result.name
            || write.destination.name == write.result.name
        {
            return Err(invalid(
                "BV64 binder and distinct same-sorted old/new arrays required",
            ));
        }
        let mut scan = Scan {
            nodes: 0,
            bytes: 0,
            binder: &binder.name,
            result: &write.result.name,
            stop: &stop,
        };
        let index = Arc::new(ChcExpr::Var(binder.clone()));
        let (inside, lower) = interval(&write.range, &index, &mut scan)?;
        let replacement = replacement(value, &write.destination.sort, &index, lower, &mut scan)?;
        let old = op(
            ChcOp::Select,
            vec![
                Arc::new(ChcExpr::Var(write.destination)),
                Arc::clone(&index),
            ],
        );
        let new = op(
            ChcOp::Select,
            vec![Arc::new(ChcExpr::Var(write.result)), index],
        );
        let matrix = ChcExpr::Op(
            ChcOp::Eq,
            vec![new, op(ChcOp::Ite, vec![inside, replacement, old])],
        );
        let premise = Self::new(binder, matrix);
        // Reuse the original exact source checker, not ChcExpr::sort's permissive
        // inference. This is authentication ONLY; no SMT solve or model is run.
        let clause = HornClause::query(ClauseBody::constraint(ChcExpr::Bool(true)));
        let authenticated = QuantifiedChcProblem::new(
            ChcProblem::new(),
            vec![QuantifiedHornClause::new(clause, vec![premise.clone()])],
        )?;
        drop(authenticated);
        poll(&stop)?;
        Ok(premise)
    }
}

fn invalid(message: &str) -> ChcError {
    ChcError::Verification(format!("array range write: {message}"))
}

fn replacement(
    value: ArrayRangeValue,
    expected: &ChcSort,
    index: &Arc<ChcExpr>,
    lower: Arc<ChcExpr>,
    scan: &mut Scan<'_>,
) -> ChcResult<Arc<ChcExpr>> {
    match value {
        ArrayRangeValue::Fill(value) => {
            scan.expression(&value)?;
            Ok(value)
        }
        ArrayRangeValue::Copy {
            source,
            source_lower,
        } => {
            variable(&source)?;
            if source.sort != *expected || source.name == scan.binder || source.name == scan.result
            {
                return Err(invalid("copy source must be a same-sorted pre-state array"));
            }
            scan.expression(&source_lower)?;
            let offset = op(
                ChcOp::BvAdd,
                vec![
                    source_lower,
                    op(ChcOp::BvSub, vec![Arc::clone(index), lower]),
                ],
            );
            Ok(op(
                ChcOp::Select,
                vec![Arc::new(ChcExpr::Var(source)), offset],
            ))
        }
    }
}

fn array_sort(sort: &ChcSort) -> bool {
    matches!(sort, ChcSort::Array(key, cell) if **key == ChcSort::BitVec(64)
        && matches!(cell.as_ref(), ChcSort::Bool | ChcSort::BitVec(1..=128)))
}

fn variable(var: &ChcVar) -> ChcResult<()> {
    if var.name.is_empty()
        || var.name.len() > 16_384
        || !matches!(var.sort, ChcSort::Bool | ChcSort::BitVec(1..=128)) && !array_sort(&var.sort)
    {
        return Err(invalid("unsupported sort or oversized name"));
    }
    Ok(())
}

fn poll(stop: &Option<ay_core::resource::CheckStop>) -> ChcResult<()> {
    if ay_core::resource::process_cancelled()
        || stop.as_ref().is_some_and(|stop| stop())
        || ay_core::TermStore::global_memory_exceeded()
        || crate::smt::deadline::current_smt_deadline()
            .is_some_and(|end| ay_core::time::Instant::now() >= end)
    {
        return Err(invalid("original resource owner refused construction"));
    }
    Ok(())
}

fn op(operation: ChcOp, arguments: Vec<Arc<ChcExpr>>) -> Arc<ChcExpr> {
    Arc::new(ChcExpr::Op(operation, arguments))
}

fn interval(
    range: &ArrayRange,
    index: &Arc<ChcExpr>,
    scan: &mut Scan<'_>,
) -> ChcResult<(Arc<ChcExpr>, Arc<ChcExpr>)> {
    match range {
        ArrayRange::Full => Ok((
            Arc::new(ChcExpr::Bool(true)),
            Arc::new(ChcExpr::BitVec(0, 64)),
        )),
        ArrayRange::UnsignedHalfOpen { lower, upper } => {
            scan.expression(lower)?;
            scan.expression(upper)?;
            Ok((
                op(
                    ChcOp::And,
                    vec![
                        op(ChcOp::BvULe, vec![Arc::clone(lower), Arc::clone(index)]),
                        op(ChcOp::BvULt, vec![Arc::clone(index), Arc::clone(upper)]),
                    ],
                ),
                Arc::clone(lower),
            ))
        }
    }
}

struct Scan<'a> {
    nodes: usize,
    bytes: usize,
    binder: &'a str,
    result: &'a str,
    stop: &'a Option<ay_core::resource::CheckStop>,
}

impl Scan<'_> {
    fn expression(&mut self, expression: &ChcExpr) -> ChcResult<()> {
        let mut stack = vec![(expression, 0usize)];
        while let Some((node, depth)) = stack.pop() {
            self.nodes = self
                .nodes
                .checked_add(1)
                .ok_or_else(|| invalid("work limit"))?;
            if self.nodes > 65_000 || depth > 56 {
                return Err(invalid("work/depth limit"));
            }
            if self.nodes % 64 == 1 {
                poll(self.stop)?;
            }
            match node {
                ChcExpr::Var(var) => {
                    variable(var)?;
                    if var.name == self.binder || var.name == self.result {
                        return Err(invalid(
                            "binder capture or result back-edge in an input variable",
                        ));
                    }
                    self.bytes = self
                        .bytes
                        .checked_add(var.name.len())
                        .ok_or_else(|| invalid("name limit"))?;
                    if self.bytes > 8 * 1024 * 1024 {
                        return Err(invalid("aggregate name limit"));
                    }
                }
                ChcExpr::Bool(_) | ChcExpr::BitVec(_, _) => {}
                ChcExpr::Op(_, args) => {
                    if args.len() > 65_000 - self.nodes || stack.len() > 65_000 - args.len() {
                        return Err(invalid("pending work limit"));
                    }
                    stack
                        .try_reserve(args.len())
                        .map_err(|_| invalid("work allocation refused"))?;
                    stack.extend(args.iter().rev().map(|arg| (arg.as_ref(), depth + 1)));
                }
                ChcExpr::ConstArray(key, value) if *key == ChcSort::BitVec(64) => {
                    stack.push((value.as_ref(), depth + 1));
                }
                _ => return Err(invalid("unsupported scalar operand family")),
            }
        }
        poll(self.stop)
    }
}
