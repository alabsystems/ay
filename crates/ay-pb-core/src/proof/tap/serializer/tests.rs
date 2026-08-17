// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::types::PbLit;

fn lit(var: u32, negated: bool) -> PbLit {
    PbLit { var, negated }
}

fn header(n: u64) -> String {
    format!("pseudo-Boolean proof version 3.0\nf {n} ;\n")
}

#[test]
fn frame_replay_builds_one_pol_line() {
    // BEGIN(3) + PROVEN(reason 1, weaken ~? on x2 rem 2, c=3, w=2)
    // + HEURISTIC(reason 2, lf 2, rf 3, div 5) + FINAL(gcd1 4, weaken x7,
    // gcd2 3, lemma id 1): exactly one pol line, id 1 == first free id.
    let writer = VeriPbWriter::new(Vec::new(), 0).expect("header");
    let mut s = TapSerializer::new(writer);
    assert_eq!(
        s.process(TapRecord::BeginFrame { conflict_pid: 3 })
            .unwrap(),
        SerializerFlow::Continue
    );
    s.process(TapRecord::ProvenResolve {
        reason_pid: 1,
        c: 3,
        w: 2,
        weakened: vec![(lit(2, false), 2)],
    })
    .unwrap();
    s.process(TapRecord::HeuristicResolve {
        reason_pid: 2,
        conflict_factor: 2,
        reason_factor: 3,
        div: Some(5),
    })
    .unwrap();
    s.process(TapRecord::FinalFrame {
        gcd1: 4,
        weaken_ran: true,
        weakened: vec![lit(7, true)],
        gcd2: 3,
        lemma_pid: 1,
    })
    .unwrap();
    let text = String::from_utf8(s.into_writer().into_inner()).unwrap();
    assert_eq!(
        text,
        format!(
            "{}pol 3 s 1 ~x2 2 * + 3 d 2 * + s 2 * 2 3 * + s 5 d s s 4 d x7 w s 3 d ;\n",
            header(0)
        )
    );
}

#[test]
fn unit_factors_and_gcds_are_elided() {
    let writer = VeriPbWriter::new(Vec::new(), 0).expect("header");
    let mut s = TapSerializer::new(writer);
    s.process(TapRecord::BeginFrame { conflict_pid: 2 })
        .unwrap();
    s.process(TapRecord::ProvenResolve {
        reason_pid: 1,
        c: 1,
        w: 1,
        weakened: Vec::new(),
    })
    .unwrap();
    s.process(TapRecord::FinalFrame {
        gcd1: 1,
        weaken_ran: false,
        weakened: Vec::new(),
        gcd2: 0,
        lemma_pid: 1,
    })
    .unwrap();
    let text = String::from_utf8(s.into_writer().into_inner()).unwrap();
    assert_eq!(text, format!("{}pol 2 s 1 + s s ;\n", header(0)));
}

#[test]
fn aborted_frame_emits_nothing_and_allocates_no_id() {
    let writer = VeriPbWriter::new(Vec::new(), 5).expect("header");
    let mut s = TapSerializer::new(writer);
    s.process(TapRecord::BeginFrame { conflict_pid: 4 })
        .unwrap();
    s.process(TapRecord::ProvenResolve {
        reason_pid: 2,
        c: 2,
        w: 3,
        weakened: Vec::new(),
    })
    .unwrap();
    s.process(TapRecord::AbortFrame).unwrap();
    // The next allocation must still be the first free id (6).
    s.process(TapRecord::RupText {
        pid: 6,
        text: String::from(">= 1 ;"),
    })
    .unwrap();
    let text = String::from_utf8(s.into_writer().into_inner()).unwrap();
    assert_eq!(text, format!("{}rup >= 1 ;\n", header(5)));
}

#[test]
fn structured_rup_sorts_terms_and_reconciles_id() {
    let writer = VeriPbWriter::new(Vec::new(), 2).expect("header");
    let mut s = TapSerializer::new(writer);
    s.process(TapRecord::Rup {
        pid: 3,
        terms: vec![(lit(2, true), 2), (lit(1, false), 1)],
        degree: 1,
    })
    .unwrap();
    let text = String::from_utf8(s.into_writer().into_inner()).unwrap();
    assert_eq!(text, format!("{}rup +1 x1 +2 ~x2 >= 1 ;\n", header(2)));
}

#[test]
fn id_desync_is_a_hard_error() {
    let writer = VeriPbWriter::new(Vec::new(), 2).expect("header");
    let mut s = TapSerializer::new(writer);
    let err = s
        .process(TapRecord::RupText {
            pid: 9,
            text: String::from(">= 1 ;"),
        })
        .expect_err("wrong id must fail");
    assert!(matches!(
        err,
        ProofError::TapIdDesync {
            expected: 9,
            actual: 3
        }
    ));
}

#[test]
fn checkpoint_splits_the_pol_line_and_final_deletes_the_intermediate() {
    // BEGIN(3) + resolve + CHECKPOINT(id 4) + resolve + FINAL(id 5):
    // two pol lines welded through the intermediate id, and the
    // serializer-injected `del id 4` right after the lemma line.
    let writer = VeriPbWriter::new(Vec::new(), 3).expect("header");
    let mut s = TapSerializer::new(writer);
    s.process(TapRecord::BeginFrame { conflict_pid: 3 })
        .unwrap();
    s.process(TapRecord::ProvenResolve {
        reason_pid: 1,
        c: 2,
        w: 3,
        weakened: Vec::new(),
    })
    .unwrap();
    s.process(TapRecord::Checkpoint {
        intermediate_pid: 4,
    })
    .unwrap();
    s.process(TapRecord::HeuristicResolve {
        reason_pid: 2,
        conflict_factor: 1,
        reason_factor: 1,
        div: None,
    })
    .unwrap();
    s.process(TapRecord::FinalFrame {
        gcd1: 1,
        weaken_ran: false,
        weakened: Vec::new(),
        gcd2: 0,
        lemma_pid: 5,
    })
    .unwrap();
    let text = String::from_utf8(s.into_writer().into_inner()).unwrap();
    assert_eq!(
        text,
        format!(
            "{}pol 3 s 1 2 d 3 * + s ;\npol 4 2 + s s ;\ndel id 4 ;\n",
            header(3)
        )
    );
}

#[test]
fn consecutive_checkpoints_all_deleted_after_final() {
    let writer = VeriPbWriter::new(Vec::new(), 2).expect("header");
    let mut s = TapSerializer::new(writer);
    s.process(TapRecord::BeginFrame { conflict_pid: 1 })
        .unwrap();
    for intermediate in [3u64, 4] {
        s.process(TapRecord::HeuristicResolve {
            reason_pid: 2,
            conflict_factor: 1,
            reason_factor: 1,
            div: None,
        })
        .unwrap();
        s.process(TapRecord::Checkpoint {
            intermediate_pid: intermediate,
        })
        .unwrap();
    }
    s.process(TapRecord::FinalFrame {
        gcd1: 0,
        weaken_ran: false,
        weakened: Vec::new(),
        gcd2: 0,
        lemma_pid: 5,
    })
    .unwrap();
    let text = String::from_utf8(s.into_writer().into_inner()).unwrap();
    assert_eq!(
        text,
        format!(
            "{}pol 1 s 2 + s ;\npol 3 2 + s ;\npol 4 s ;\ndel id 3 ;\ndel id 4 ;\n",
            header(2)
        )
    );
}

#[test]
fn abort_after_checkpoint_deletes_intermediates_and_keeps_ids_reconciled() {
    let writer = VeriPbWriter::new(Vec::new(), 2).expect("header");
    let mut s = TapSerializer::new(writer);
    s.process(TapRecord::BeginFrame { conflict_pid: 1 })
        .unwrap();
    s.process(TapRecord::HeuristicResolve {
        reason_pid: 2,
        conflict_factor: 1,
        reason_factor: 1,
        div: None,
    })
    .unwrap();
    s.process(TapRecord::Checkpoint {
        intermediate_pid: 3,
    })
    .unwrap();
    s.process(TapRecord::AbortFrame).unwrap();
    // The intermediate consumed id 3 on BOTH sides, so the next
    // allocating record must carry id 4.
    s.process(TapRecord::RupText {
        pid: 4,
        text: String::from(">= 1 ;"),
    })
    .unwrap();
    let text = String::from_utf8(s.into_writer().into_inner()).unwrap();
    assert_eq!(
        text,
        format!("{}pol 1 s 2 + s ;\ndel id 3 ;\nrup >= 1 ;\n", header(2))
    );
}

#[test]
fn weaken_cont_chunks_prepend_to_the_next_proven_resolve() {
    let writer = VeriPbWriter::new(Vec::new(), 2).expect("header");
    let mut s = TapSerializer::new(writer);
    s.process(TapRecord::BeginFrame { conflict_pid: 1 })
        .unwrap();
    s.process(TapRecord::WeakenCont {
        pairs: vec![(lit(5, false), 2)],
    })
    .unwrap();
    s.process(TapRecord::WeakenCont {
        pairs: vec![(lit(6, true), 1)],
    })
    .unwrap();
    s.process(TapRecord::ProvenResolve {
        reason_pid: 2,
        c: 3,
        w: 2,
        weakened: vec![(lit(7, false), 4)],
    })
    .unwrap();
    s.process(TapRecord::FinalFrame {
        gcd1: 0,
        weaken_ran: false,
        weakened: Vec::new(),
        gcd2: 0,
        lemma_pid: 3,
    })
    .unwrap();
    let text = String::from_utf8(s.into_writer().into_inner()).unwrap();
    assert_eq!(
        text,
        format!(
            "{}pol 1 s 2 ~x5 2 * + x6 1 * + ~x7 4 * + 3 d 2 * + s s ;\n",
            header(2)
        )
    );
}

#[test]
fn dangling_weaken_cont_fails_closed() {
    // A non-ProvenResolve record while pairs are buffered is a protocol
    // violation (the chunked op never completed).
    let writer = VeriPbWriter::new(Vec::new(), 2).expect("header");
    let mut s = TapSerializer::new(writer);
    s.process(TapRecord::BeginFrame { conflict_pid: 1 })
        .unwrap();
    s.process(TapRecord::WeakenCont {
        pairs: vec![(lit(5, false), 2)],
    })
    .unwrap();
    assert!(matches!(
        s.process(TapRecord::FinalFrame {
            gcd1: 0,
            weaken_ran: false,
            weakened: Vec::new(),
            gcd2: 0,
            lemma_pid: 3,
        }),
        Err(ProofError::TapProtocol(_))
    ));

    // Outside a frame, WeakenCont itself fails closed.
    let writer = VeriPbWriter::new(Vec::new(), 2).expect("header");
    let mut s = TapSerializer::new(writer);
    assert!(matches!(
        s.process(TapRecord::WeakenCont {
            pairs: vec![(lit(5, false), 2)],
        }),
        Err(ProofError::TapProtocol(_))
    ));
}

#[test]
fn checkpoint_outside_a_frame_fails_closed() {
    let writer = VeriPbWriter::new(Vec::new(), 2).expect("header");
    let mut s = TapSerializer::new(writer);
    assert!(matches!(
        s.process(TapRecord::Checkpoint {
            intermediate_pid: 3,
        }),
        Err(ProofError::TapProtocol(_))
    ));
}

#[test]
fn frame_protocol_violations_fail_closed() {
    let writer = VeriPbWriter::new(Vec::new(), 0).expect("header");
    let mut s = TapSerializer::new(writer);
    assert!(matches!(
        s.process(TapRecord::ProvenResolve {
            reason_pid: 1,
            c: 1,
            w: 1,
            weakened: Vec::new(),
        }),
        Err(ProofError::TapProtocol(_))
    ));
    s.process(TapRecord::BeginFrame { conflict_pid: 1 })
        .unwrap();
    assert!(matches!(
        s.process(TapRecord::BeginFrame { conflict_pid: 1 }),
        Err(ProofError::TapProtocol(_))
    ));
}

#[test]
fn conclusions_emit_footer_and_report_concluded() {
    let writer = VeriPbWriter::new(Vec::new(), 1).expect("header");
    let mut s = TapSerializer::new(writer);
    s.process(TapRecord::RupText {
        pid: 2,
        text: String::from(">= 1 ;"),
    })
    .unwrap();
    assert_eq!(
        s.process(TapRecord::ConcludeUnsat {
            contradiction_pid: 2
        })
        .unwrap(),
        SerializerFlow::Concluded
    );
    let text = String::from_utf8(s.into_writer().into_inner()).unwrap();
    assert_eq!(
        text,
        format!(
            "{}rup >= 1 ;\noutput NONE;\nconclusion UNSAT : 2;\nend pseudo-Boolean proof;\n",
            header(1)
        )
    );
}

#[test]
fn empty_lemma_frame_concludes_on_the_chain_id_without_a_redundant_rup() {
    // BEGIN(1) + resolve + FINAL(lemma id 3) then ConcludeUnsat on that
    // same chain id: the conclusion points straight at the frame's pol
    // lemma and NO fresh `rup >= 1 ;` line is emitted (empty-lemma path).
    let writer = VeriPbWriter::new(Vec::new(), 2).expect("header");
    let mut s = TapSerializer::new(writer);
    s.process(TapRecord::BeginFrame { conflict_pid: 1 })
        .unwrap();
    s.process(TapRecord::ProvenResolve {
        reason_pid: 2,
        c: 1,
        w: 1,
        weakened: Vec::new(),
    })
    .unwrap();
    s.process(TapRecord::FinalFrame {
        gcd1: 0,
        weaken_ran: false,
        weakened: Vec::new(),
        gcd2: 0,
        lemma_pid: 3,
    })
    .unwrap();
    assert_eq!(
        s.process(TapRecord::ConcludeUnsat {
            contradiction_pid: 3
        })
        .unwrap(),
        SerializerFlow::Concluded
    );
    let text = String::from_utf8(s.into_writer().into_inner()).unwrap();
    assert!(
        !text.contains("rup"),
        "no redundant contradiction RUP: {text}"
    );
    assert!(text.contains("pol 1 s 2 + s s ;"), "{text}");
    assert!(text.contains("conclusion UNSAT : 3;"), "{text}");
}

#[test]
fn sat_conclusion_writes_assignment() {
    let writer = VeriPbWriter::new(Vec::new(), 1).expect("header");
    let mut s = TapSerializer::new(writer);
    assert_eq!(
        s.process(TapRecord::ConcludeSat {
            assignment: vec![true, false]
        })
        .unwrap(),
        SerializerFlow::Concluded
    );
    let text = String::from_utf8(s.into_writer().into_inner()).unwrap();
    assert!(text.contains("conclusion SAT : x1 ~x2;"), "{text}");
}
