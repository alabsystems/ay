// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

fn lit(var: u32, negated: bool) -> PbLit {
    PbLit { var, negated }
}

fn round_trip(record: &TapRecord) {
    let mut buf = Vec::new();
    record.encode(&mut buf);
    let decoded = TapRecord::decode(&buf).expect("well-formed record decodes");
    assert_eq!(&decoded, record);
}

#[test]
fn all_record_kinds_round_trip() {
    round_trip(&TapRecord::BeginFrame { conflict_pid: 7 });
    round_trip(&TapRecord::ProvenResolve {
        reason_pid: u64::MAX,
        c: 12345678901234567890123456789i128,
        w: 3,
        weakened: vec![(lit(1, false), 2), (lit(400000, true), 1 << 90)],
    });
    round_trip(&TapRecord::ProvenResolve {
        reason_pid: 1,
        c: 1,
        w: 1,
        weakened: Vec::new(),
    });
    round_trip(&TapRecord::HeuristicResolve {
        reason_pid: 9,
        conflict_factor: 1,
        reason_factor: i128::MAX,
        div: None,
    });
    round_trip(&TapRecord::HeuristicResolve {
        reason_pid: 9,
        conflict_factor: 4,
        reason_factor: 6,
        div: Some(5),
    });
    round_trip(&TapRecord::FinalFrame {
        gcd1: 6,
        weaken_ran: true,
        weakened: vec![lit(3, true), lit(17, false)],
        gcd2: 1,
        lemma_pid: 42,
    });
    round_trip(&TapRecord::FinalFrame {
        gcd1: 0,
        weaken_ran: false,
        weakened: Vec::new(),
        gcd2: 0,
        lemma_pid: 1,
    });
    round_trip(&TapRecord::AbortFrame);
    round_trip(&TapRecord::Checkpoint {
        intermediate_pid: 123456789,
    });
    round_trip(&TapRecord::WeakenCont { pairs: Vec::new() });
    round_trip(&TapRecord::WeakenCont {
        pairs: vec![(lit(9, true), 1), (lit(70000, false), 1 << 80)],
    });
    round_trip(&TapRecord::Rup {
        pid: 11,
        terms: vec![(lit(1, false), -3), (lit(2, true), 5)],
        degree: -7,
    });
    round_trip(&TapRecord::RupText {
        pid: 12,
        text: String::from(">= 1 ;"),
    });
    round_trip(&TapRecord::Delete { pid: 5 });
    round_trip(&TapRecord::ConcludeUnsat {
        contradiction_pid: 99,
    });
    round_trip(&TapRecord::ConcludeSat {
        assignment: vec![true, false, true, true, false, false, true, false, true],
    });
    round_trip(&TapRecord::ConcludeSat {
        assignment: Vec::new(),
    });
    round_trip(&TapRecord::Shutdown);
}

#[test]
fn typical_proven_resolve_is_compact() {
    // Spec size budget: typical PROVEN_RESOLVE is 10-150 bytes.
    let mut buf = Vec::new();
    TapRecord::ProvenResolve {
        reason_pid: 100_000,
        c: 12,
        w: 40,
        weakened: vec![(lit(17, true), 3), (lit(90, false), 5)],
    }
    .encode(&mut buf);
    assert!(buf.len() <= 24, "encoded {} bytes", buf.len());
}

#[test]
fn malformed_records_fail_closed() {
    assert!(TapRecord::decode(&[]).is_err());
    assert!(TapRecord::decode(&[0xff]).is_err());
    // Truncated payload.
    let mut buf = Vec::new();
    TapRecord::Rup {
        pid: 11,
        terms: vec![(lit(1, false), 3)],
        degree: 1,
    }
    .encode(&mut buf);
    buf.pop();
    assert!(TapRecord::decode(&buf).is_err());
    // Trailing garbage.
    let mut buf2 = Vec::new();
    TapRecord::Delete { pid: 5 }.encode(&mut buf2);
    buf2.push(0);
    assert!(TapRecord::decode(&buf2).is_err());
    // Literal with var 0.
    let mut buf3 = vec![TAG_BEGIN_FRAME];
    encode_u64(&mut buf3, 1);
    assert!(TapRecord::decode(&buf3).is_ok());
}
