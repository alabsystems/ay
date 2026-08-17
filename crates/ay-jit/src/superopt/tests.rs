// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::{
    choose_cheapest_equivalent, enumerate_superopt_candidates, Aarch64Template, EquivalenceResult,
    SuperoptCandidate, SuperoptInst, SuperoptReg, SuperoptSearch, VerifiedSuperoptCandidate,
};

#[test]
fn enumeration_prunes_dead_scratch_writes() {
    let candidates = enumerate_superopt_candidates(&SuperoptSearch {
        live_inputs: vec![SuperoptReg::X0, SuperoptReg::X1],
        live_outputs: vec![SuperoptReg::X2],
        scratch: vec![SuperoptReg::Scratch0],
        templates: vec![Aarch64Template::Mov, Aarch64Template::Add],
        max_len: 1,
        max_candidates: 64,
    });

    assert!(!candidates.is_empty());
    assert!(candidates
        .iter()
        .all(|candidate| candidate.insts()[0].dst == SuperoptReg::X2));
    assert!(candidates.iter().any(|candidate| candidate.insts()
        == [SuperoptInst {
            template: Aarch64Template::Add,
            dst: SuperoptReg::X2,
            src0: SuperoptReg::X0,
            src1: Some(SuperoptReg::X1),
        }]));
}

#[test]
fn commutative_operands_are_canonicalized() {
    let candidates = enumerate_superopt_candidates(&SuperoptSearch {
        live_inputs: vec![SuperoptReg::X0, SuperoptReg::X1],
        live_outputs: vec![SuperoptReg::X2],
        scratch: Vec::new(),
        templates: vec![Aarch64Template::Add],
        max_len: 1,
        max_candidates: 64,
    });

    assert!(candidates.iter().any(|candidate| candidate.insts()
        == [SuperoptInst {
            template: Aarch64Template::Add,
            dst: SuperoptReg::X2,
            src0: SuperoptReg::X0,
            src1: Some(SuperoptReg::X1),
        }]));
    assert!(!candidates.iter().any(|candidate| candidate.insts()
        == [SuperoptInst {
            template: Aarch64Template::Add,
            dst: SuperoptReg::X2,
            src0: SuperoptReg::X1,
            src1: Some(SuperoptReg::X0),
        }]));
}

#[test]
fn cheapest_equivalent_candidate_wins() {
    let one_inst = SuperoptCandidate {
        insts: vec![SuperoptInst {
            template: Aarch64Template::Mov,
            dst: SuperoptReg::X2,
            src0: SuperoptReg::X0,
            src1: None,
        }],
    };
    let two_inst = SuperoptCandidate {
        insts: vec![
            SuperoptInst {
                template: Aarch64Template::Mov,
                dst: SuperoptReg::Scratch0,
                src0: SuperoptReg::X0,
                src1: None,
            },
            SuperoptInst {
                template: Aarch64Template::Mov,
                dst: SuperoptReg::X2,
                src0: SuperoptReg::Scratch0,
                src1: None,
            },
        ],
    };
    let three_inst = SuperoptCandidate {
        insts: vec![
            SuperoptInst {
                template: Aarch64Template::Mov,
                dst: SuperoptReg::Scratch0,
                src0: SuperoptReg::X0,
                src1: None,
            },
            SuperoptInst {
                template: Aarch64Template::Mov,
                dst: SuperoptReg::Scratch1,
                src0: SuperoptReg::Scratch0,
                src1: None,
            },
            SuperoptInst {
                template: Aarch64Template::Mov,
                dst: SuperoptReg::X2,
                src0: SuperoptReg::Scratch1,
                src1: None,
            },
        ],
    };

    let selected = choose_cheapest_equivalent([
        VerifiedSuperoptCandidate {
            candidate: one_inst,
            result: EquivalenceResult::Counterexample,
        },
        VerifiedSuperoptCandidate {
            candidate: two_inst.clone(),
            result: EquivalenceResult::Equivalent {
                certificate_id: String::from("cert-two"),
            },
        },
        VerifiedSuperoptCandidate {
            candidate: three_inst,
            result: EquivalenceResult::Equivalent {
                certificate_id: String::from("cert-three"),
            },
        },
    ])
    .expect("expected an equivalent candidate");

    assert_eq!(selected.candidate.insts(), two_inst.insts());
}
