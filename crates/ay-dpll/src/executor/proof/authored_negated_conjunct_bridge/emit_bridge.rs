// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Strict emission of one source-to-goal literal bridge.

use ay_core::kani_compat::DetHashMap;
use ay_core::{Proof, ProofId, ProofStep, TermId, TheoryLemmaKind};

use super::eq_plan::emit_eq_plan;
use super::{BridgeAuthority, LiteralBridge};

pub(super) fn emit_literal_bridge(
    proof: &mut Proof,
    bridge: &LiteralBridge,
    assumptions: &mut DetHashMap<TermId, ProofId>,
) -> Option<ProofId> {
    let units = bridge
        .equalities
        .iter()
        .map(|plan| {
            emit_eq_plan(proof, plan, assumptions)
                .map(|unit| (plan.equality(), plan.negated_equality(), unit))
        })
        .collect::<Option<Vec<_>>>()?;
    let (mut residual, mut current) = match &bridge.authority {
        BridgeAuthority::Direct => return None,
        BridgeAuthority::Euf { clause } => (
            clause.clone(),
            proof.add_step(ProofStep::TheoryLemma {
                theory: "EUF".to_string(),
                clause: clause.clone(),
                farkas: None,
                kind: TheoryLemmaKind::EufCongruentPred,
                lia: None,
            }),
        ),
        BridgeAuthority::Farkas {
            clause,
            annotation,
            kind,
        } => (
            clause.clone(),
            proof.add_step(ProofStep::TheoryLemma {
                theory: "LIA".to_string(),
                clause: clause.clone(),
                farkas: Some(annotation.clone()),
                kind: *kind,
                lia: None,
            }),
        ),
    };
    for (equality, negated_equality, unit) in units {
        if !residual.contains(&negated_equality) {
            continue;
        }
        residual.retain(|&literal| literal != negated_equality);
        current = proof.add_resolution(residual.clone(), equality, current, unit);
    }
    (residual.as_slice() == [bridge.goal, bridge.source_atom]).then_some(current)
}
