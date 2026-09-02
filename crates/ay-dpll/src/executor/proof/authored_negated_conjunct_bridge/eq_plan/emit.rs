// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Strict Alethe emission for already-bounded equality plans.

use ay_core::kani_compat::DetHashMap;
use ay_core::{AletheRule, Proof, ProofId, ProofStep, TermId};

use super::{EqPlan, EqPlanKind};

pub(in crate::executor::proof::authored_negated_conjunct_bridge) fn emit_eq_plan(
    proof: &mut Proof,
    plan: &EqPlan,
    assumptions: &mut DetHashMap<TermId, ProofId>,
) -> Option<ProofId> {
    match &plan.kind {
        EqPlanKind::Refl => {
            Some(proof.add_rule_step(AletheRule::Refl, vec![plan.eq], Vec::new(), Vec::new()))
        }
        EqPlanKind::Assumed {
            assumption,
            reversed,
        } => {
            let premise = *assumptions
                .entry(*assumption)
                .or_insert_with(|| proof.add_assume(*assumption, None));
            if *reversed {
                Some(proof.add_rule_step(
                    AletheRule::Symm,
                    vec![plan.eq],
                    vec![premise],
                    Vec::new(),
                ))
            } else {
                Some(premise)
            }
        }
        EqPlanKind::PolySimp => Some(proof.add_step(ProofStep::TheoryLemma {
            theory: "arith".to_string(),
            clause: vec![plan.eq],
            farkas: None,
            kind: ay_core::TheoryLemmaKind::ArithClauseTautology,
            lia: None,
        })),
        EqPlanKind::Symm(inner) => {
            let premise = emit_eq_plan(proof, inner, assumptions)?;
            Some(proof.add_rule_step(AletheRule::Symm, vec![plan.eq], vec![premise], Vec::new()))
        }
        EqPlanKind::Cong { children } => {
            let premises = children
                .iter()
                .map(|child| emit_eq_plan(proof, child, assumptions))
                .collect::<Option<Vec<_>>>()?;
            Some(proof.add_rule_step(AletheRule::Cong, vec![plan.eq], premises, Vec::new()))
        }
        EqPlanKind::Trans(left, right) => {
            let left = emit_eq_plan(proof, left, assumptions)?;
            let right = emit_eq_plan(proof, right, assumptions)?;
            Some(proof.add_rule_step(
                AletheRule::Trans,
                vec![plan.eq],
                vec![left, right],
                Vec::new(),
            ))
        }
    }
}
