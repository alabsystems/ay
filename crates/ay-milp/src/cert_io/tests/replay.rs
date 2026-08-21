// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

struct ReplayFixture {
    model: Model,
    scale: BigRational,
    names: Vec<String>,
}

impl ReplayFixture {
    fn new() -> Self {
        let mut model = Model::new();
        model.set_objective_offset(0.0);
        Self {
            model,
            scale: BigRational::one(),
            names: Vec::new(),
        }
    }

    fn context<'a>(&'a self, claims: &'a [ReplayClaim]) -> EmitCtx<'a> {
        EmitCtx {
            model: &self.model,
            model_text: "pb replay fixture",
            col_names: &self.names,
            obj_scale: &self.scale,
            provenance: "test",
            replay_claims: claims,
            affine_aggregation_certificate: None,
            parity_infeasibility_certificate: None,
            sat_relu_infeasibility_certificate: None,
            network_design_infeasibility_certificate: None,
            network_design_optimality_certificate: None,
            block_angular_optimality_certificate: None,
            single_machine_scheduling_optimality_certificate: None,
            single_row_dp_infeasibility_certificate: None,
            multi_row_bdd_infeasibility_certificate: None,
            open_domain_single_row_dp_infeasibility_certificate: None,
            open_domain_multi_row_bdd_infeasibility_certificate: None,
            open_domain_hybrid_pb_lp_infeasibility_certificate: None,
            open_domain_hybrid_integer_lift_infeasibility_certificate: None,
            hybrid_pb_lp_infeasibility_certificate: None,
            hybrid_integer_lift_infeasibility_certificate: None,
            max_bytes: None,
        }
    }
}

fn replay(claim: &str) -> ReplayClaim {
    ReplayClaim {
        claim: claim.to_owned(),
        device: "milp-to-pb-reduction".to_owned(),
        method: "exact-rational-boolean-projection+native-pb-cdcl".to_owned(),
        arithmetic: "exact-rational+i128-pseudo-boolean".to_owned(),
        nodes_visited: None,
        node_budget: 0,
        outcome: "exhausted".to_owned(),
        nondeterminism: Vec::new(),
        reproduce: "ay-milp solve <model> --require none".to_owned(),
        tcb: "pb route".to_owned(),
    }
}

enum ReplayVerdict {
    Optimal,
    Infeasible,
}

fn emit_replay(fixture: &ReplayFixture, claim: &str, verdict: ReplayVerdict) -> String {
    let claims = vec![replay(claim)];
    let context = fixture.context(&claims);
    match verdict {
        ReplayVerdict::Optimal => emit(
            &context,
            &Outcome::Optimal {
                value: BigRational::zero(),
                model_values: Vec::new(),
                cert: None,
            },
        ),
        ReplayVerdict::Infeasible => emit(
            &context,
            &Outcome::Infeasible {
                cert: None,
                tree_cert: None,
            },
        ),
    }
}

pub(super) fn exact_pb_replay_ids_back_only_the_claim_they_proved() {
    let fixture = ReplayFixture::new();
    let optimal = emit_replay(&fixture, "pb-projection-optimal", ReplayVerdict::Optimal);
    assert!(optimal.contains("evidence dual REPLAY pb-projection-optimal"));
    assert!(!optimal.contains("evidence infeasible REPLAY"));

    let infeasible = emit_replay(
        &fixture,
        "pb-projection-infeasible",
        ReplayVerdict::Infeasible,
    );
    assert!(infeasible.contains("evidence infeasible REPLAY pb-projection-infeasible"));
    assert!(!infeasible.contains("evidence dual REPLAY"));
}

pub(super) fn exact_hybrid_replay_ids_back_only_the_claim_they_proved() {
    let fixture = ReplayFixture::new();
    let optimal = emit_replay(&fixture, "hybrid-pb-lp-optimal", ReplayVerdict::Optimal);
    assert!(optimal.contains("evidence dual REPLAY hybrid-pb-lp-optimal"));
    assert!(!optimal.contains("evidence infeasible REPLAY"));

    let infeasible = emit_replay(
        &fixture,
        "hybrid-pb-lp-infeasible",
        ReplayVerdict::Infeasible,
    );
    assert!(infeasible.contains("evidence infeasible REPLAY hybrid-pb-lp-infeasible"));
    assert!(!infeasible.contains("evidence dual REPLAY"));
}

pub(super) fn exact_projection_aliases_back_only_the_claim_they_proved() {
    let fixture = ReplayFixture::new();
    for claim in [
        "pb-portfolio-projection-optimal",
        "network-design-projection-optimal",
        "open-domain-cap-optimal",
    ] {
        let emitted = emit_replay(&fixture, claim, ReplayVerdict::Optimal);
        assert!(emitted.contains(&format!("evidence dual REPLAY {claim}")));
        assert!(!emitted.contains("evidence infeasible REPLAY"));
    }
    for claim in [
        "pb-portfolio-projection-infeasible",
        "network-design-projection-infeasible",
        "open-domain-projection-infeasible",
    ] {
        let emitted = emit_replay(&fixture, claim, ReplayVerdict::Infeasible);
        assert!(emitted.contains(&format!("evidence infeasible REPLAY {claim}")));
        assert!(!emitted.contains("evidence dual REPLAY"));
    }
}
