// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

pub(super) struct Fixture {
    pub executor: Executor,
    pub originals: Vec<TermId>,
    pub guard: TermId,
}

impl Fixture {
    pub(super) fn parsed() -> Self {
        // Exact QF3 source, including the extra guarded-read root absent from
        // the earlier direct-planner fixtures. No check-sat or solver call.
        let source = r#"
(set-logic ALL)
(declare-fun f (Bool (_ BitVec 8)) (_ BitVec 8))
(declare-fun x () (_ BitVec 8))
(declare-fun fill () (_ BitVec 8))
(declare-fun length () (_ BitVec 64))
(declare-fun a () (Array (_ BitVec 64) (_ BitVec 8)))
(declare-fun __gpc1 () (_ BitVec 64))
(assert (and (= fill (f true x)) (= length #x0000000000000041)))
(assert (or (= (f true x) (select a __gpc1)) (not (bvult __gpc1 length))))
(assert (or (and (bvult __gpc1 length) (bvule #x0000000000000020 __gpc1) (not (= fill (select a __gpc1)))) (= length #x0000000000000000)))
"#;
        let commands = ay_frontend::parse(source).unwrap();
        let mut executor = Executor::new();
        assert!(executor.execute_all(&commands).unwrap().is_empty());
        let originals = executor.ctx.assertions.clone();
        assert_eq!(originals.len(), 3);
        let mut working = originals.clone();
        let mut sources: Vec<_> = originals.iter().map(|&root| vec![root]).collect();
        let (mut preprocessing, _, propagation) =
            crate::preprocess::Preprocessor::new_with_recorded_subst_and_propagation(Box::new(
                |_, _| true,
            ));
        preprocessing.preprocess_with_sources(&mut executor.ctx.terms, &mut working, &mut sources);
        executor.extend_propagated_value_provenance(&propagation);
        let index = executor.ctx.symbol_info("__gpc1").unwrap().term.unwrap();
        let sixty_five = executor.ctx.terms.mk_bitvec(65.into(), 64);
        let guard = executor.ctx.terms.mk_bvult(index, sixty_five);
        assert!(working.contains(&guard));
        assert!(executor.propagated_value_provenance.entries.len() <= 32);
        assert!(executor.propagated_value_provenance.rewrites.len() <= 32);
        assert!(!executor.propagated_value_provenance.rewrites.is_empty());
        assert!(!executor
            .propagated_value_provenance
            .rewrites
            .iter()
            .any(|record| record.after == guard));
        assert_eq!(executor.ctx.assertions, originals);
        Self {
            executor,
            originals,
            guard,
        }
    }

    pub(super) fn pending(&self) -> Proof {
        Proof::from_steps(vec![ProofStep::Assume(self.guard)])
    }

    pub(super) fn authenticate(&self, proof: &Proof) {
        assert!(!proof.steps.contains(&ProofStep::Assume(self.guard)));
        ay_proof::validate_reachable_assumes_in_problem_scope(proof, &self.originals).unwrap();
        let checked = ay_proof::authenticate_premise_clauses_strict_with_context_and_progress(
            proof,
            &self.executor.ctx.terms,
            None,
            None,
            &self.originals,
            &mut |_, _| true,
        )
        .expect("presentation repair uses only original-source checked rules");
        assert_eq!(
            checked.clause(ProofId(proof.steps.len() as u32 - 1)),
            Some([self.guard].as_slice())
        );
    }
}
