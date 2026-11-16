// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The unchanged consumer input through the CLI's actual BV-native pipeline.

use super::*;
use crate::portfolio::PreprocessSummary;
use crate::transform::ClauseInliner;
use crate::{CancellationToken, ChcParser, ClauseHead, PredicateId};
use sha2::{Digest, Sha256};
use std::time::Duration;

const INPUT: &str = include_str!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/tests/fixtures/model_checker_consumer_arith_equal_original.smt2"
));

fn contains_zero_shift_binding(formula: &ChcExpr, keep: &[ChcVar]) -> bool {
    let ChcExpr::Op(operation, args) = formula else {
        return false;
    };
    if *operation == ChcOp::Eq && args.len() == 2 {
        for (value, image) in [
            (args[0].as_ref(), args[1].as_ref()),
            (args[1].as_ref(), args[0].as_ref()),
        ] {
            if matches!(value, ChcExpr::BitVec(0, 32)) {
                if let ChcExpr::Op(ChcOp::BvLShr, operands) = image {
                    if operands.len() == 2
                        && matches!(operands[0].as_ref(), ChcExpr::Var(var) if !keep.contains(var))
                        && matches!(operands[1].as_ref(), ChcExpr::BitVec(1, 32))
                    {
                        return true;
                    }
                }
            }
        }
    }
    args.iter()
        .any(|arg| contains_zero_shift_binding(arg, keep))
}

/// (nodes, simplified nodes, existential locals) of the two survivors. The
/// merged survivor retains the zero-image constraint after constant-column
/// projection removes two existential locals. Keep this capture bound to the
/// unchanged original input and check exact projection closure below.
const SURVIVORS: [(usize, usize, usize); 2] = [(58, 58, 2), (192, 190, 35)];

#[test]
fn original_parsed_preprocessed_survivors_close_without_model_enumeration() {
    assert_eq!(
        format!("{:x}", Sha256::digest(INPUT.as_bytes())),
        "7173c651e75ac70e6770e01b1a910435c430f986742eb5f2dabc0a9d46239e48"
    );
    let _switches = crate::ab_switches::TestOverride::set(Default::default());
    let original = ChcParser::parse(INPUT).unwrap();
    assert_eq!(
        (original.predicates().len(), original.clauses().len()),
        (39, 48)
    );
    let cancellation = CancellationToken::new();
    let deadline = ay_core::time::Instant::now() + Duration::from_secs(30);
    // The bounded entrypoint selects the uncached condense stage, just like
    // adaptive_multi_pred::try_acyclic_bmc_probe's BV-native lane.
    let summary = PreprocessSummary::build_bv_native_with_limits(
        original,
        false,
        Some(deadline),
        &cancellation,
    )
    .expect("bounded production preprocessing");
    let problem = &summary.transformed_problem;
    assert_eq!(
        (problem.predicates().len(), problem.clauses().len()),
        (1, 8)
    );
    assert_eq!(problem.predicates()[0].name, "main__bb11");
    let definitions: Vec<_> = problem
        .clauses()
        .iter()
        .filter(|clause| matches!(clause.head, ClauseHead::Predicate(..)))
        .map(ClauseInliner::normalize_head_for_back_translation)
        .collect();
    assert_eq!(definitions.len(), 2);
    let mut sizes = Vec::new();
    for definition in &definitions {
        assert_eq!(
            definition.body.predicates,
            [] as [(PredicateId, Vec<ChcExpr>); 0]
        );
        let ClauseHead::Predicate(_, arguments) = &definition.head else {
            unreachable!()
        };
        let keep: Vec<_> = arguments
            .iter()
            .map(|arg| match arg {
                ChcExpr::Var(var) => var.clone(),
                _ => panic!("normalized head must contain only variables"),
            })
            .collect();
        assert_eq!(keep.len(), 12);
        assert!(keep
            .iter()
            .enumerate()
            .all(|(i, var)| { keep[..i].iter().all(|earlier| earlier.name != var.name) }));
        let formula = definition.body.constraint.as_ref().unwrap();
        let nodes = formula.node_count(1000);
        let normalized = formula.simplify_constants();
        let normalized_nodes = normalized.node_count(1000);
        let locals = normalized
            .vars()
            .iter()
            .filter(|var| !keep.contains(var))
            .count();
        sizes.push((nodes, normalized_nodes, locals));
        // This test-only capture preserves the actual typed variables and full
        // formula. It is intentionally before projection, not an alpha-reduced
        // re-authored fixture and not a production diagnostic or proof claim.
        eprintln!(
            "consumer survivor nodes={nodes}/{normalized_nodes} keep={keep:?} formula={formula:?}"
        );
        if locals == SURVIVORS[1].2 {
            assert!(
                contains_zero_shift_binding(formula, &keep),
                "actual merged definition must retain the constant-valued image equality"
            );
        }
        let mut scope = Scope::new(Limits::default(), &|| true);
        let result = run(formula, &keep, &mut scope);
        assert!(
            matches!(result, Projection::Closed(_)),
            "actual {nodes}/{normalized_nodes}-node survivor did not close"
        );
    }
    sizes.sort_unstable();
    assert_eq!(sizes, SURVIVORS);
}
