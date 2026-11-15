// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! A single free-offset theorem justifies every conditional read. No offset is
//! sampled: the two fresh words range over their complete bit-vector domains.

use super::*;

pub(super) fn lower(
    terms: &TermStore,
    shape: super::super::disjoint::Shape,
    limits: &mut BvExprProofLimits,
    deadline: Instant,
    poll: semantic_control::Poll<'_>,
) -> Result<BvExpr, Failure> {
    lower_with_prover(
        terms,
        shape,
        limits,
        deadline,
        poll,
        &mut validate_bv_expr_compact,
    )
}

/// Check the exact source-derived prerequisite before installing any facts.
/// The continuation receives only borrowed expressions and the already-split
/// native limits. It must prove their equality; returning success is trusted
/// internal authority, not a serialized declaration or a new proof route.
pub(super) fn lower_with_prover<F>(
    terms: &TermStore,
    shape: super::super::disjoint::Shape,
    limits: &mut BvExprProofLimits,
    deadline: Instant,
    poll: semantic_control::Poll<'_>,
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
    // An outside-frame payload is lowered by that lane's own lowerer.
    let outside = outside_frame::Shape::recognize_root(terms, shape.root);
    let result = (|| {
        declare_requests(&mut lowerer, &shape, outside.is_none())?;
        let [first, second, third] = shape.guards;
        let first = lowerer.lower_bool(first)?;
        let second = lowerer.lower_bool(second)?;
        let third = lowerer.lower_bool(third)?;
        let guard = BvExpr::and(first, BvExpr::and(second, third));
        let a = lowerer.lower_bv(shape.spans[0].start)?.0;
        let b = lowerer.lower_bv(shape.spans[1].start)?.0;
        // Source variables are named proof_bv_<TermId> / proof_bool_<TermId>.
        // These distinct private names cannot alias any source leaf.
        let i = BvExpr::leaf("disjoint_offset_a", shape.width);
        let j = BvExpr::leaf("disjoint_offset_b", shape.width);
        let in_a = BvExpr::Ult(
            Box::new(i.clone()),
            Box::new(BvExpr::const_val(shape.spans[0].length, shape.width)),
        );
        let in_b = BvExpr::Ult(
            Box::new(j.clone()),
            Box::new(BvExpr::const_val(shape.spans[1].length, shape.width)),
        );
        let equal = BvExpr::eq(BvExpr::add(i, a), BvExpr::add(j, b));
        let query = BvExpr::not(BvExpr::and(
            BvExpr::and(guard.clone(), in_a),
            BvExpr::and(in_b, equal),
        ));
        Ok::<_, String>((guard, query))
    })();
    if lowerer.cancelled {
        return Err(Failure::Cancelled);
    }
    let (_guard, query) = result.map_err(Failure::Rejected)?;
    outside_frame::prove_prerequisite(
        &query,
        limits,
        prove,
        &mut || lowerer.poll_lowering().is_ok(),
        "free-offset disjointness theorem",
    )?;
    drop(query);
    if let Some(outside) = outside {
        // This lowerer's requests end with the guards and span starts: the
        // payload is the outside-frame lowerer's.
        #[cfg(test)]
        lowerer.audit_census();
        return outside_frame::lower_with_disjoint_and_prover(
            terms,
            outside,
            limits,
            deadline,
            poll,
            Some(shape),
            prove,
        );
    }
    // Guard memo entries were lowered without conditional facts. Facts apply
    // only to the payload and remain subordinate to this same positive guard.
    let payload = shape.root;
    lowerer.install_disjoint_facts(Some(shape));
    let result = lowerer.lower_bool(payload);
    if lowerer.cancelled {
        return Err(Failure::Cancelled);
    }
    let payload = result.map_err(Failure::Rejected)?;
    #[cfg(test)]
    lowerer.audit_census();
    Ok(BvExpr::not(payload))
}

/// Count the guards, both span starts and (unless handed on to the
/// outside-frame lane) the payload before any is lowered, so a guard term the
/// payload shares is memoized as the guards lower it, without the facts.
fn declare_requests(
    lowerer: &mut ProofProducingLowerer<'_, '_>,
    shape: &super::super::disjoint::Shape,
    lowers_payload: bool,
) -> Result<(), String> {
    lowerer.census_requests(
        shape
            .guards
            .map(Request::Lower)
            .into_iter()
            .chain([
                Request::Lower(shape.spans[0].start),
                Request::Lower(shape.spans[1].start),
            ])
            .chain(lowers_payload.then_some(Request::Lower(shape.root))),
    )
}

#[cfg(test)]
mod tests;
