// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Untrusted preparation is DATA. Only full original same-pin SAT seals it.

use super::*;

pub(super) struct Prepared {
    derivation: derivation::Derivation,
    topology: [u8; 32],
    obligation: String,
    bindings: Vec<QuantifiedChcCompleteTraceBinding>,
    functions: Vec<ScalarFunctionModel>,
    pub(super) pinned: String,
}

pub(super) fn prepare(
    problem: &QuantifiedChcProblem,
    wire: &wire::Wire,
    control: &SourceControl<'_>,
) -> Option<Prepared> {
    control.debit(wire.source.len().checked_add(1)?, wire.source.len())?;
    if wire.schema != wire::SCHEMA || wire.source != problem.source_smtlib() {
        return None;
    }
    let derivation = topology(wire, control)?;
    let rendered = render::render_complete(
        problem,
        &derivation.clause_indices,
        &derivation.premise_steps,
        control,
    )
    .ok()?;
    let registry = registry(problem, control)?;
    let graphs = arrays::import(&wire.graphs, control)?;
    let bindings = bindings::import(wire, &rendered, &registry, &graphs, control)?;
    let functions = codec_functions::import(&wire.functions, problem, control)?;
    let pinned = pins::render(
        &rendered, &bindings, &functions, problem, &registry, control,
    )?;
    let digest = codec_transport::digest(pinned.as_bytes(), control)?;
    control.debit(digest.len().checked_add(wire.pinned_sha256.len())?, 0)?;
    if digest != wire.pinned_sha256 {
        return None;
    }
    let topology = derivation::fingerprint(
        &derivation.clause_indices,
        &derivation.premise_steps,
        control,
    )?;
    drop((
        graphs,
        rendered.assertions,
        rendered.original.bindings,
        registry,
        digest,
    ));
    control.poll()?;
    Some(Prepared {
        derivation,
        topology,
        obligation: rendered.original.obligation,
        bindings,
        functions,
        pinned,
    })
}

fn topology(wire: &wire::Wire, control: &SourceControl<'_>) -> Option<derivation::Derivation> {
    let count = wire.steps.len();
    if count == 0 || count > wire::MAX_NODES {
        return None;
    }
    let mut indices = Vec::new();
    let mut premises = Vec::new();
    arrays::reserve(&mut indices, count, control)?;
    arrays::reserve(&mut premises, count, control)?;
    let mut edges_left = count.checked_sub(1)?;
    let mut locals_left = MAX_BINDINGS;
    for step in &wire.steps {
        control.debit(1, 0)?;
        edges_left = edges_left.checked_sub(step.premises.len())?;
        locals_left = locals_left.checked_sub(step.bindings.len())?;
        control.bytes(
            step.premises
                .len()
                .checked_mul(std::mem::size_of::<usize>())?,
        )?;
        indices.push(step.clause_index);
        premises.push(step.premises.clone());
    }
    control.poll()?;
    (edges_left == 0).then_some(derivation::Derivation {
        clause_indices: indices,
        premise_steps: premises,
    })
}

impl Prepared {
    pub(super) fn replay(
        self,
        problem: &QuantifiedChcProblem,
        deadline: Instant,
        memory: Option<usize>,
        cancellation: &CancellationToken,
        control: &SourceControl<'_>,
    ) -> Option<QuantifiedChcCompleteTrace> {
        if !replay::validate(&self.pinned, deadline, memory, cancellation, control) {
            return None;
        }
        control.bytes(problem.source_smtlib().len().checked_add(64)?)?;
        let base = QuantifiedChcCounterexample {
            source: Arc::from(problem.source_smtlib()),
            clause_indices: self.derivation.clause_indices,
            premise_steps: self.derivation.premise_steps,
            topology_sha256: self.topology,
            obligation: self.obligation,
            memory_budget: memory,
        };
        let trace = QuantifiedChcCompleteTrace {
            base,
            bindings: self.bindings,
            functions: self.functions,
            pinned_obligation: self.pinned,
        };
        control.poll()?;
        Some(trace)
    }
}
