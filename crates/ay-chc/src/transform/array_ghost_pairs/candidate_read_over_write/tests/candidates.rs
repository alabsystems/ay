// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::time::Duration;

use ay_core::time::Instant;
use ntest::timeout;

use super::*;
use crate::smt::SmtValue;
use crate::transform::array_ghost_pairs::candidate::{
    query_anchored_ghost_candidates, QueryAnchoredGhostCandidate,
};
use crate::transform::array_ghost_pairs::candidate_houdini::QueryAnchoredSeal;
use crate::transform::array_ghost_pairs::{
    recheck_ghost_pair_certificate, try_query_anchored_and_seal, GhostPairSpec,
};
use crate::transform::{ArrayGhostPairTransformer, Transformer};
use crate::{CancellationToken, ChcProblem};

const TWO_ARRAYS: &str = r#"
(set-logic HORN)
(declare-fun P ((Array (_ BitVec 2) (_ BitVec 8))
                (Array (_ BitVec 2) (_ BitVec 8)) (_ BitVec 2) (_ BitVec 2)) Bool)
(declare-fun Q ((_ BitVec 2) (Array (_ BitVec 2) (_ BitVec 8))
                (_ BitVec 2) (Array (_ BitVec 2) (_ BitVec 8))) Bool)
(assert (forall ((i (_ BitVec 2)) (j (_ BitVec 2)))
  (P ((as const (Array (_ BitVec 2) (_ BitVec 8))) #x07)
     ((as const (Array (_ BitVec 2) (_ BitVec 8))) #x09) i j)))
(assert (forall ((a (Array (_ BitVec 2) (_ BitVec 8)))
                 (b (Array (_ BitVec 2) (_ BitVec 8)))
                 (i (_ BitVec 2)) (j (_ BitVec 2)))
  (=> (P a b i j) (Q j b i a))))
(assert (forall ((a (Array (_ BitVec 2) (_ BitVec 8)))
                 (b (Array (_ BitVec 2) (_ BitVec 8)))
                 (i (_ BitVec 2)) (j (_ BitVec 2)))
  (=> (and (Q j b i a)
           (or (distinct (select (store a i #x07) j) #x07)
               (distinct (select (store b j #x09) i) #x09))) false)))
(check-sat)
"#;

fn batch(problem: &ChcProblem) -> Vec<QueryAnchoredGhostCandidate> {
    query_anchored_ghost_candidates(problem, &GhostPairSpec::analyze(problem, 1))
        .expect("normalized query has one observed slot per array")
}

fn evaluate(candidate: &QueryAnchoredGhostCandidate, values: &[(usize, u128, u32)]) -> bool {
    let environment = values
        .iter()
        .map(|(position, value, width)| {
            (
                candidate.vars[*position].name.clone(),
                SmtValue::BitVec(*value, *width),
            )
        })
        .collect();
    match crate::expr::evaluate::evaluate_expr(&candidate.formula, &environment) {
        Some(SmtValue::Bool(value)) => value,
        other => panic!("scalar candidate did not evaluate: {other:?}"),
    }
}

#[test]
fn two_symbolic_arrays_preserve_hit_miss_and_permuted_argument_identity() {
    let problem = ChcParser::parse(TWO_ARRAYS).expect("typed two-array fixture");
    let raw = Box::new(ArrayGhostPairTransformer::new(1))
        .transform(problem.clone())
        .problem;
    let original_query = problem.clauses().last().expect("original query");
    let raw_query = raw.clauses().last().expect("raw query");
    let original_args = &original_query.body.predicates[0].1;
    let raw_args = &raw_query.body.predicates[0].1;
    assert_eq!(
        raw_args[4], original_args[2],
        "B must observe read i, not write j"
    );
    assert_eq!(
        raw_args[6], original_args[0],
        "A must observe read j, not write i"
    );
    assert_eq!(
        raw_query.body.constraint, original_query.body.constraint,
        "probe discovery must not rewrite or weaken the raw query"
    );
    let candidates = batch(&problem);
    assert_eq!(candidates.len(), 2);
    for candidate in candidates {
        let name = &problem.get_predicate(candidate.predicate).unwrap().name;
        let (ip, jp, agp, avp, bgp, bvp) = match name.as_str() {
            "P" => (2, 3, 4, 5, 6, 7),
            "Q" => (2, 0, 6, 7, 4, 5),
            other => panic!("unexpected candidate {other}"),
        };
        for i in 0..4u128 {
            for j in 0..4u128 {
                for av in [0, 7] {
                    for bv in [0, 9] {
                        for ag in [j, (j + 1) % 4] {
                            for bg in [i, (i + 1) % 4] {
                                let expected = ag != j
                                    || bg != i
                                    || ((if i == j { 7 } else { av }) == 7
                                        && (if j == i { 9 } else { bv }) == 9);
                                assert_eq!(
                                    evaluate(
                                        &candidate,
                                        &[
                                            (ip, i, 2),
                                            (jp, j, 2),
                                            (agp, ag, 2),
                                            (avp, av, 8),
                                            (bgp, bg, 2),
                                            (bvp, bv, 8),
                                        ]
                                    ),
                                    expected,
                                    "{name}: i={i} j={j} a={av} b={bv} ag={ag} bg={bg}"
                                );
                            }
                        }
                    }
                }
            }
        }
    }
}

#[test]
fn normalized_bare_reads_still_authenticate_a_shared_clause_local_bv_index() {
    let source = r#"
      (set-logic HORN)
      (declare-fun P ((Array (_ BitVec 2) (_ BitVec 8))
                      (Array (_ BitVec 2) (_ BitVec 8)) (_ BitVec 2)) Bool)
      (assert (forall ((a (Array (_ BitVec 2) (_ BitVec 8)))
                       (b (Array (_ BitVec 2) (_ BitVec 8)))
                       (i (_ BitVec 2)) (j (_ BitVec 2)))
        (=> (and (P a b i)
                 (distinct (select (store a i #x07) j) (select b j))) false)))
    "#;
    let problem = ChcParser::parse(source).expect("local index fixture");
    let candidates = batch(&problem);
    assert_eq!(candidates.len(), 1);
    let candidate = &candidates[0];
    assert_eq!(
        candidate.vars.len(),
        7,
        "j must not become a new formal parameter"
    );
    assert!(!candidate
        .formula
        .vars()
        .iter()
        .any(|variable| variable.name == "j"));
    for i in 0..4u128 {
        for j in 0..4u128 {
            for other in 0..4u128 {
                assert_eq!(
                    evaluate(
                        candidate,
                        &[(2, i, 2), (3, j, 2), (4, 5, 8), (5, other, 2), (6, 7, 8)]
                    ),
                    j != other || i == j
                );
            }
        }
    }
    let signature = "(Array (_ BitVec 2) (_ BitVec 8)) (_ BitVec 2)) Bool)";
    assert_eq!(source.matches(signature).count(), 1);
    let local_write = source
        .replacen(signature, "(Array (_ BitVec 2) (_ BitVec 8))) Bool)", 1)
        .replacen("(P a b i)", "(P a b)", 1);
    let unmapped = ChcParser::parse(&local_write).expect("unobserved local write index is typed");
    assert!(
        query_anchored_ghost_candidates(&unmapped, &GhostPairSpec::analyze(&unmapped, 1)).is_none(),
        "write-only local i must not be invented, defaulted, or bound to read j"
    );
}

fn seal(problem: &ChcProblem) -> Option<QueryAnchoredSeal> {
    let spec = GhostPairSpec::analyze(problem, 1);
    let raw = Box::new(ArrayGhostPairTransformer::new(1))
        .transform(problem.clone())
        .problem;
    let now = Instant::now();
    try_query_anchored_and_seal(
        problem,
        &raw,
        &spec,
        now + Duration::from_secs(40),
        now + Duration::from_secs(80),
        &CancellationToken::new(),
        None,
    )
}

#[test]
#[timeout(120000)]
fn read_over_write_candidates_seal_and_recheck_every_original_clause() {
    let problem = ChcParser::parse(TWO_ARRAYS).expect("safe source");
    let original = format!("{:?}", problem.clauses());
    let sealed = seal(&problem).expect("both original array properties must seal");
    assert_eq!(
        format!("{:?}", problem.clauses()),
        original,
        "normalization is candidate-local"
    );
    assert!(recheck_ghost_pair_certificate(
        &problem,
        &sealed.certificate,
        Some(Duration::from_secs(10)),
        false,
    ));
}

#[test]
#[timeout(120000)]
fn changing_only_the_symbolic_store_value_cannot_seal_the_false_original_query() {
    assert_eq!(TWO_ARRAYS.matches("(store a i #x07)").count(), 1);
    let changed = TWO_ARRAYS.replacen("(store a i #x07)", "(store a i #x08)", 1);
    let problem = ChcParser::parse(&changed).expect("well-typed, genuinely unsafe changed source");
    assert_eq!(
        batch(&problem).len(),
        2,
        "negative is not unsupported admission"
    );
    // The reachable initial state with i=j reads the changed value 8, not 7.
    // Candidate generation is not authority: raw-query/original-clause checks
    // must refuse a Safe seal rather than adopting this candidate.
    assert!(seal(&problem).is_none());
}

#[path = "candidates/wide.rs"]
mod wide;
