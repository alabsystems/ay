// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Value mappings remain hints; exact originals still require authentication.

use super::*;
use crate::SatProofManager;
use ay_core::{AletheRule, ProofStep};
use std::collections::BTreeMap;

fn trace(positive: bool) -> ClauseTrace {
    let mut solver = SatSolver::new(4);
    solver.enable_clause_trace();
    let variable = SatVariable::new(2);
    solver.add_clause(vec![if positive {
        SatLiteral::positive(variable)
    } else {
        SatLiteral::negative(variable)
    }]);
    assert!(matches!(solver.solve().into_inner(), SatResult::Sat(_)));
    solver
        .take_clause_trace()
        .expect("actual sealed solver trace")
}

#[test]
fn retained_actual_constant_authenticates_only_its_true_negative_unit() {
    for positive in [false, true] {
        let mut executor = Executor::new();
        executor.save_bv_unsat_proof_state(Some(trace(positive)), &BTreeMap::new(), Some(3));
        let map = executor.last_var_to_term.take().expect("proof map");
        assert_eq!(map[&2], executor.ctx.terms.false_term());
        let trace = executor.last_clause_trace.take().expect("trace");
        let result = SatProofManager::new(&map, &mut executor.ctx.terms)
            .build_exact_original_proof_fragment(&trace, &[]);
        if positive {
            assert!(
                result.is_err(),
                "a positive false unit has no source/intrinsic authority"
            );
        } else {
            let fragment = result.expect("closed true unit uses the existing intrinsic");
            assert_eq!(fragment.proof().steps.len(), 1);
            assert!(matches!(
                fragment.proof().steps[0],
                ProofStep::Step {
                    rule: AletheRule::True,
                    ..
                }
            ));
            let binding = fragment.binding(1).expect("actual stable original ID");
            assert_eq!(
                binding.source_sat_clause(),
                &[SatLiteral::negative(SatVariable::new(2))]
            );
        }
    }
}

#[test]
fn stale_missing_and_colliding_namespace_hints_do_not_register() {
    for hint in [None, Some(0), Some(5), Some(u32::MAX)] {
        let mut executor = Executor::new();
        executor.save_bv_unsat_proof_state(Some(trace(false)), &BTreeMap::new(), hint);
        assert!(executor.last_var_to_term.as_ref().expect("map").is_empty());
    }
    let mut executor = Executor::new();
    executor.save_bv_unsat_proof_state(None, &BTreeMap::new(), Some(3));
    assert!(executor.last_var_to_term.as_ref().expect("map").is_empty());

    let p = executor.ctx.terms.mk_var("p", Sort::Bool);
    let source = BTreeMap::from([(3, p)]);
    executor.save_bv_unsat_proof_state(Some(trace(false)), &source, Some(3));
    assert_eq!(executor.last_var_to_term.as_ref().expect("map")[&2], p);
    assert_eq!(source[&3], p, "source/model mapping remains unchanged");
}
