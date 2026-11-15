// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Prove a local outside-frame read property under an actual positive guard.
//! The full counterexample need not imply that the observation is outside.

use super::*;

mod source;
mod validation;
pub(super) use source::pricing::matching_work;
pub(crate) use source::Shape;

pub(super) fn lower(
    terms: &TermStore,
    shape: Shape,
    limits: &mut BvExprProofLimits,
    deadline: Instant,
    poll: semantic_control::Poll<'_>,
) -> Result<BvExpr, Failure> {
    lower_with_disjoint(terms, shape, limits, deadline, poll, None)
}

pub(super) fn lower_with_disjoint(
    terms: &TermStore,
    shape: Shape,
    limits: &mut BvExprProofLimits,
    deadline: Instant,
    poll: semantic_control::Poll<'_>,
    disjoint: Option<super::super::disjoint::Shape>,
) -> Result<BvExpr, Failure> {
    lower_with_disjoint_and_prover(
        terms,
        shape,
        limits,
        deadline,
        poll,
        disjoint,
        &mut validate_bv_expr_compact,
    )
}

/// The borrowed free-offset theorem must be checked before either disjoint
/// facts or the outside-frame property enter the payload lowerer. Combined
/// lowering forwards the same continuation after its disjoint prerequisite.
pub(super) fn lower_with_disjoint_and_prover<F>(
    terms: &TermStore,
    shape: Shape,
    limits: &mut BvExprProofLimits,
    deadline: Instant,
    poll: semantic_control::Poll<'_>,
    disjoint: Option<super::super::disjoint::Shape>,
    prove: &mut F,
) -> Result<BvExpr, Failure>
where
    F: FnMut(
        &BvExpr,
        &BvExpr,
        &BvExprProofLimits,
        &BvBlastValidateLimits,
        &mut dyn FnMut() -> bool,
    ) -> Result<(), BvExprExportError>,
{
    let mut keep_going = || poll().is_ok();
    let mut lowerer = ProofProducingLowerer::new(terms, deadline);
    lowerer.keep_going = Some(&mut keep_going);
    let query = (|| {
        // Every top-level request of this lowerer, counted before any is
        // made: the offset theorem's four, the property validation's, and
        // the root, whose `property` is answered from the memo entry
        // installed below and so requests nothing.
        lowerer.census_opaque.insert(shape.property);
        lowerer.census_requests(
            [shape.guard, shape.outside, shape.start, shape.observe]
                .map(Request::Lower)
                .into_iter()
                .chain(validation::requests(terms, &shape).into_iter().flatten())
                .chain([Request::Lower(shape.root)]),
        )?;
        let guard = lowerer.lower_bool(shape.guard)?;
        let outside = lowerer.lower_bool(shape.outside)?;
        let start = lowerer.lower_bv(shape.start)?.0;
        let observe = lowerer.lower_bv(shape.observe)?.0;
        // All source leaves use proof_bv_<TermId> or proof_bool_<TermId>.
        // This fresh word quantifies over EVERY offset, not sampled writes.
        let offset = BvExpr::leaf("outside_frame_offset", shape.width);
        let within = BvExpr::Ult(
            Box::new(offset.clone()),
            Box::new(BvExpr::const_val(shape.length, shape.width)),
        );
        let aliases = BvExpr::eq(observe, BvExpr::add(start, offset));
        Ok::<_, String>(BvExpr::not(BvExpr::and(
            BvExpr::and(guard, outside),
            BvExpr::and(within, aliases),
        )))
    })();
    if lowerer.cancelled {
        return Err(Failure::Cancelled);
    }
    let query = query.map_err(Failure::Rejected)?;
    prove_prerequisite(
        &query,
        limits,
        prove,
        &mut || lowerer.poll_lowering().is_ok(),
        "free-offset outside-frame theorem",
    )?;
    drop(query);
    // The disjoint theorem, when present, was independently checked by the
    // caller under positive premises of this exact root. It is used only for
    // the payload, never while proving the outside-frame offset theorem.
    lowerer.install_disjoint_facts(disjoint);
    let validated = validation::property(&mut lowerer, &shape);
    if lowerer.cancelled {
        return Err(Failure::Cancelled);
    }
    validated.map_err(Failure::Rejected)?;
    // Each validated store index equals start + a concrete in-range offset.
    // The theorem and read-over-write therefore imply equality of the two
    // reads when outside holds. Thus preservation is true and a conjunction
    // containing outside and the unequal reads is false. This replacement is
    // used only in this SAME root, which implies guard.
    lowerer.memo.insert(
        shape.property,
        ProofProducingExpr::Bool(BvExpr::const_val(u128::from(shape.property_value), 1)),
    );
    lowerer.memo_node_counts.insert(shape.property, 1);
    let result = lowerer.lower_bool(shape.root);
    if lowerer.cancelled {
        return Err(Failure::Cancelled);
    }
    #[cfg(test)]
    if result.is_ok() {
        lowerer.audit_census();
    }
    result.map(BvExpr::not).map_err(Failure::Rejected)
}

/// Refute a conditional route's free-offset prerequisite `query` through
/// `prove`, under HALF of `limits`. The prerequisite and the clause's own
/// refutation share the original absolute deadline and deterministic work
/// allowance: neither gets a fresh deadline or extra work, and `limits` keeps
/// the halved envelope for what follows.
pub(super) fn prove_prerequisite<F>(
    query: &BvExpr,
    limits: &mut BvExprProofLimits,
    prove: &mut F,
    keep_going: &mut dyn FnMut() -> bool,
    theorem: &str,
) -> Result<(), Failure>
where
    F: FnMut(
        &BvExpr,
        &BvExpr,
        &BvExprProofLimits,
        &BvBlastValidateLimits,
        &mut dyn FnMut() -> bool,
    ) -> Result<(), BvExprExportError>,
{
    limits.max_estimated_gate_work /= 2;
    limits.max_expansion_work /= 2;
    limits.resolution.validation.max_work /= 2;
    limits.resolution.max_conflicts = limits.resolution.max_conflicts.map(|n| n / 2);
    limits.resolution.max_decisions = limits.resolution.max_decisions.map(|n| n / 2);
    let mut replay = proof_replay_limits(limits);
    replay.max_work /= 2;
    prove(query, &BvExpr::const_val(1, 1), limits, &replay, keep_going).map_err(|error| match error
    {
        BvExprExportError::Cancelled => Failure::Cancelled,
        other => Failure::Rejected(format!("{theorem}: {other}")),
    })
}

#[cfg(test)]
mod tests;
