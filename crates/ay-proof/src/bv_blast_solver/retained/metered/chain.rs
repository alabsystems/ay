// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use work::WorkError;

mod budget;
mod limits;
mod pair;

/// Closure-scoped, non-Clone owner of one additive work ledger. Child order,
/// roles and source lowering belong to the caller; this is not a theorem token.
/// A failed/panicking child cannot be caught and followed by another child or
/// successful publication. Earlier frames stay charged even if dropped.
pub(crate) struct Chain<'a, 'p> {
    proof: &'a BvExprProofLimits,
    gates: &'a BvBlastValidateLimits,
    ledger: &'a mut Ledger,
    poll: &'a mut (dyn FnMut() -> bool + 'p),
    budget: budget::Budget,
    end: Instant,
    refused: bool,
}

pub(crate) fn run<T>(
    proof: &BvExprProofLimits,
    gates: &BvBlastValidateLimits,
    wire: &wire::WireLimits,
    allowance: WorkAllowance,
    poll: &mut dyn FnMut() -> bool,
    operation: impl FnOnce(&mut Chain<'_, '_>) -> Result<T, MeteredError>,
) -> Result<Metered<T>, MeteredError> {
    let (mut proof, mut gates) = effective_limits(proof, gates)?;
    let end = proof
        .resolution
        .deadline
        .ok_or_else(|| malformed("missing proof deadline"))?;
    let mut ledger = Ledger::new(allowance, end.min(wire.deadline));
    let end = ledger.deadline();
    limits::install(&mut proof, &mut gates, end);
    cancellation::run(poll, |poll| {
        finish_expr_export(Some(&proof), poll)?;
        ledger.check()?;
        let (mut result, end, refused) = {
            let mut chain = Chain {
                proof: &proof,
                gates: &gates,
                ledger: &mut ledger,
                poll,
                budget: budget::Budget::new(*wire, &proof),
                end,
                refused: false,
            };
            let result = operation(&mut chain);
            (result, chain.end, chain.refused)
        };
        if refused && result.is_ok() {
            // Drop closure-owned success candidates before the final stop
            // observation. Catching a child failure cannot mint success.
            drop(result);
            result = Err(WorkError::Refused.into());
        }
        limits::install(&mut proof, &mut gates, end);
        if let Err(error) = finish_expr_export(Some(&proof), poll) {
            drop(result);
            let _ = finish_expr_export(Some(&proof), poll);
            return Err(error.into());
        }
        let result = ledger.finish(result?);
        // Ledger was created once at the root deadline. A later child may
        // have shortened it; retain that minimum through final admission too.
        if Instant::now() >= end {
            drop(result);
            let _ = finish_expr_export(Some(&proof), poll);
            return Err(WorkError::Deadline.into());
        }
        if result.is_err() {
            let _ = finish_expr_export(Some(&proof), poll);
        }
        result
    })
}

impl Chain<'_, '_> {
    pub(crate) fn capture_one(
        &mut self,
        lhs: &BvExpr,
        rhs: &BvExpr,
        proof: &BvExprProofLimits,
        gates: &BvBlastValidateLimits,
    ) -> Result<Vec<u8>, MeteredError> {
        self.child(proof, gates, |chain, proof, gates, wire| {
            let (payload, shape) =
                capture_payload(lhs, rhs, proof, gates, chain.ledger, chain.poll)?;
            // Producer graph/DAG scratch is gone before encoding. The payload
            // and all earlier returned frames still coexist with this output.
            let (bytes, usage) = chain.ledger.phase(
                Phase::Wire,
                wire.max_work.min(proof.resolution.validation.max_work),
                |grant| {
                    let mut wire = *wire;
                    wire.max_work = grant;
                    let outcome = wire::encode(&payload, &wire, proof, gates, chain.poll);
                    Ok(((outcome.result?, outcome.usage), outcome.usage.charged_work))
                },
            )?;
            chain.budget.commit(
                shape,
                bytes.len(),
                usage.returned_owned_bytes,
                usage.charged_work,
            )?;
            Ok(bytes)
        })
    }

    pub(crate) fn replay_one(
        &mut self,
        lhs: &BvExpr,
        rhs: &BvExpr,
        bytes: &[u8],
        proof: &BvExprProofLimits,
        gates: &BvBlastValidateLimits,
    ) -> Result<(), MeteredError> {
        self.child(proof, gates, |chain, proof, gates, wire| {
            let (payload, usage) = chain.ledger.phase(
                Phase::Wire,
                wire.max_work.min(proof.resolution.validation.max_work),
                |grant| {
                    let mut wire = *wire;
                    wire.max_work = grant;
                    let outcome = wire::decode(bytes, &wire, proof, gates, chain.poll);
                    Ok(((outcome.result?, outcome.usage), outcome.usage.charged_work))
                },
            )?;
            let shape = replay_payload(lhs, rhs, &payload, proof, gates, chain.ledger, chain.poll)?;
            // Payload/graph/DAG are operation scratch, not surviving owners.
            // The borrowed input was already included in this wire peak.
            chain
                .budget
                .commit(shape, bytes.len(), bytes.len(), usage.charged_work)?;
            Ok(())
        })
    }

    fn child<T>(
        &mut self,
        proof: &BvExprProofLimits,
        gates: &BvBlastValidateLimits,
        operation: impl FnOnce(
            &mut Self,
            &BvExprProofLimits,
            &BvBlastValidateLimits,
            &wire::WireLimits,
        ) -> Result<T, MeteredError>,
    ) -> Result<T, MeteredError> {
        if self.refused {
            return Err(WorkError::Refused.into());
        }
        // Cover prechecks, binding, accounting and final polls outside phase,
        // including a panic caught by the enclosing caller closure.
        self.refused = true;
        let (mut proof, gates) = limits::child(self.proof, self.gates, proof, gates, self.end);
        self.end = proof
            .resolution
            .deadline
            .ok_or_else(|| malformed("missing child deadline"))?;
        let result = self
            .budget
            .child(&mut proof, self.end)
            .and_then(|wire| operation(self, &proof, &gates, &wire));
        // The operation dropped all temporary payloads/graphs/parser errors.
        if let Err(error) = finish_expr_export(Some(&proof), self.poll) {
            drop(result);
            let _ = finish_expr_export(Some(&proof), self.poll);
            return Err(error.into());
        }
        if result.is_ok() {
            self.refused = false;
        }
        result
    }
}

#[cfg(test)]
mod tests;
