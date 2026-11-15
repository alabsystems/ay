// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Preparation is untrusted data work. Only `Prepared::replay` seals evidence.

use super::*;

pub(super) struct Prepared {
    derivation: derivation::Derivation,
    topology_sha256: [u8; 32],
    obligation: String,
    bindings: Vec<QuantifiedChcTraceBinding>,
    functions: Vec<ScalarFunctionModel>,
    pinned: String,
}

pub(super) fn prepare(
    problem: &QuantifiedChcProblem,
    wire: &wire::Wire,
    control: &SourceControl<'_>,
) -> Option<Prepared> {
    control.poll()?;
    control.bytes(wire.source.len())?;
    if wire.schema != wire::SCHEMA || wire.source != problem.source_smtlib() {
        return None;
    }
    let derivation = wire::topology(wire, control)?;
    let rendered = render::render_with_bindings(
        problem,
        &derivation.clause_indices,
        &derivation.premise_steps,
        control,
    )
    .ok()?;
    if rendered.bindings.len() > MAX_BINDINGS {
        return None;
    }
    let registry = registry(problem, control)?;
    let bindings = bindings::import(&wire.steps, &rendered, &registry, control)?;
    let functions = functions::import(&wire.functions, problem, control)?;
    let pinned = pins::render(
        &rendered, &bindings, &functions, problem, &registry, control,
    )?;
    if transport::digest(pinned.as_bytes(), control)? != wire.pinned_sha256 {
        return None;
    }
    let topology_sha256 = derivation::fingerprint(
        &derivation.clause_indices,
        &derivation.premise_steps,
        control,
    )?;
    drop((rendered.bindings, registry));
    control.poll()?;
    Some(Prepared {
        derivation,
        topology_sha256,
        obligation: rendered.obligation,
        bindings,
        functions,
        pinned,
    })
}

impl Prepared {
    #[cfg(test)]
    pub(super) fn test_pins(&self) -> &str {
        &self.pinned
    }

    pub(super) fn replay(
        self,
        problem: &QuantifiedChcProblem,
        deadline: Instant,
        memory: Option<usize>,
        cancellation: &CancellationToken,
        control: &SourceControl<'_>,
    ) -> Option<QuantifiedChcTrace> {
        if !replay::validate(&self.pinned, deadline, memory, cancellation, control) {
            return None;
        }
        control.bytes(problem.source_smtlib().len().checked_add(64)?)?;
        let base = QuantifiedChcCounterexample {
            source: Arc::from(problem.source_smtlib()),
            clause_indices: self.derivation.clause_indices,
            premise_steps: self.derivation.premise_steps,
            topology_sha256: self.topology_sha256,
            obligation: self.obligation,
            memory_budget: memory,
        };
        let trace = QuantifiedChcTrace {
            base,
            bindings: self.bindings,
            functions: self.functions,
            pinned_obligation: self.pinned,
        };
        control.poll()?;
        Some(trace)
    }
}
