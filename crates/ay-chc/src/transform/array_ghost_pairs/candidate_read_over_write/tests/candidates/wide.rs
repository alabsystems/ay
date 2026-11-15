// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

fn wide_source() -> String {
    assert_eq!(TWO_ARRAYS.matches("(_ BitVec 2)").count(), 20);
    let source = TWO_ARRAYS.replace("(_ BitVec 2)", "(_ BitVec 64)");
    assert_eq!(source.matches("(_ BitVec 64)").count(), 20);
    assert!(!source.contains("(_ BitVec 2)"));
    source
}

fn positions(problem: &ChcProblem, candidate: &QueryAnchoredGhostCandidate) -> [usize; 6] {
    match problem
        .get_predicate(candidate.predicate)
        .unwrap()
        .name
        .as_str()
    {
        "P" => [2, 3, 4, 5, 6, 7],
        "Q" => [2, 0, 6, 7, 4, 5],
        other => panic!("unexpected candidate {other}"),
    }
}

#[test]
#[timeout(120000)]
fn bv64_symbolic_arrays_preserve_high_key_reads_and_seal_every_original_clause() {
    let problem = ChcParser::parse(&wide_source()).expect("production-width source");
    let original = format!("{:?}", problem.clauses());
    let raw = Box::new(ArrayGhostPairTransformer::new(1))
        .transform(problem.clone())
        .problem;
    let original_query = problem.clauses().last().unwrap();
    let raw_query = raw.clauses().last().unwrap();
    let original_args = &original_query.body.predicates[0].1;
    let raw_args = &raw_query.body.predicates[0].1;
    assert_eq!(
        raw_args[4], original_args[2],
        "B probes read i, not write j"
    );
    assert_eq!(
        raw_args[6], original_args[0],
        "A probes read j, not write i"
    );
    for position in [4, 6] {
        assert_eq!(raw_args[position].sort(), ChcSort::BitVec(64));
    }
    assert_eq!(raw_query.body.constraint, original_query.body.constraint);
    let candidates = batch(&problem);
    assert_eq!(candidates.len(), 2);
    let high = 1u128 << 63;
    let max = u64::MAX as u128;
    for candidate in &candidates {
        let [ip, jp, agp, avp, bgp, bvp] = positions(&problem, candidate);
        for (i, j) in [(0, max), (high, max), (max, max), (high, high)] {
            for av in [0, 7] {
                for bv in [0, 9] {
                    for ag in [j, j ^ high] {
                        for bg in [i, i ^ high] {
                            let expected = ag != j
                                || bg != i
                                || ((if i == j { 7 } else { av }) == 7
                                    && (if i == j { 9 } else { bv }) == 9);
                            assert_eq!(
                                evaluate(
                                    candidate,
                                    &[
                                        (ip, i, 64),
                                        (jp, j, 64),
                                        (agp, ag, 64),
                                        (avp, av, 8),
                                        (bgp, bg, 64),
                                        (bvp, bv, 8),
                                    ]
                                ),
                                expected,
                                "i={i} j={j} a={av} b={bv} ag={ag} bg={bg}"
                            );
                        }
                    }
                }
            }
        }
    }
    // This is symbolic certification over all 64-bit keys, not enumeration of
    // the small sample above. The acceptance boundary checks the original CHCs.
    let sealed = seal(&problem).expect("symbolic BV64 array invariant must seal");
    assert!(recheck_ghost_pair_certificate(
        &problem,
        &sealed.certificate,
        Some(Duration::from_secs(10)),
        false
    ));
    assert_eq!(format!("{:?}", problem.clauses()), original);
}

#[test]
#[timeout(120000)]
fn bv64_changed_store_byte_cannot_seal_the_false_original_query() {
    let source = wide_source();
    assert_eq!(source.matches("(store a i #x07)").count(), 1);
    let changed = source.replacen("(store a i #x07)", "(store a i #x08)", 1);
    let problem = ChcParser::parse(&changed).expect("typed wide wrong-byte source");
    let candidates = batch(&problem);
    assert_eq!(
        candidates.len(),
        2,
        "negative is still admitted for candidate generation"
    );
    let key = u64::MAX as u128;
    for candidate in &candidates {
        let [ip, jp, agp, avp, bgp, bvp] = positions(&problem, candidate);
        assert!(
            !evaluate(
                candidate,
                &[
                    (ip, key, 64),
                    (jp, key, 64),
                    (agp, key, 64),
                    (avp, 7, 8),
                    (bgp, key, 64),
                    (bvp, 9, 8),
                ]
            ),
            "reachable i=j=MAX violates the proposed safe property"
        );
    }
    // Refusal is not an independently reconstructed Unsafe verdict. It proves
    // that candidate synthesis does not authorize a false Safe certificate.
    assert!(seal(&problem).is_none());
}
