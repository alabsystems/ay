// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The SAT-trace replay stops on its caller's stop predicate and replays
//! exactly as before when the predicate has not fired.

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::{Proof, ProofId, ProofStep, Sort, TermId, TermStore};
use ay_sat::{ClauseTrace, Literal, Variable};

use crate::SatProofManager;

/// Replay `p`, `(not p)`, and the hinted empty clause under `should_stop`.
fn replay(should_stop: Option<&dyn Fn() -> bool>) -> (Option<ProofId>, Proof) {
    let mut terms = TermStore::new();
    let p = terms.mk_var("replay_stop_p", Sort::Bool);
    let not_p = terms.mk_not(p);
    let var_to_term: HashMap<u32, TermId> = [(0, p)].into_iter().collect();
    let mut proof = Proof::new();
    proof.add_assume(p, None);
    proof.add_assume(not_p, None);
    let mut trace = ClauseTrace::new();
    trace.add_clause(1, vec![Literal::positive(Variable::new(0))], true);
    trace.add_clause(2, vec![Literal::negative(Variable::new(0))], true);
    trace.add_clause_with_hints(3, Vec::new(), false, vec![1, 2]);
    let mut manager = SatProofManager::new(&var_to_term, &mut terms);
    if let Some(should_stop) = should_stop {
        manager.set_should_stop(should_stop);
    }
    let derived = manager.process_trace(&trace, &mut proof);
    (derived, proof)
}

fn derives_empty(derived: Option<ProofId>, proof: &Proof) -> bool {
    derived
        .and_then(|id| proof.get_step(id))
        .is_some_and(|step| {
            matches!(
                step,
                ProofStep::Resolution { clause, .. } | ProofStep::Step { clause, .. }
                    if clause.is_empty()
            )
        })
}

#[test]
fn a_fired_stop_abandons_the_replay_and_an_idle_one_changes_nothing() {
    let (derived, proof) = replay(None);
    assert!(
        derives_empty(derived, &proof),
        "the unstopped replay derives"
    );

    let idle = || false;
    let (derived, idle_proof) = replay(Some(&idle));
    assert!(
        derives_empty(derived, &idle_proof),
        "an idle stop changes nothing"
    );
    assert_eq!(
        format!("{:?}", idle_proof.steps),
        format!("{:?}", proof.steps)
    );

    let fired = || true;
    let (derived, stopped_proof) = replay(Some(&fired));
    assert!(derived.is_none(), "a fired stop abandons the replay");
    assert_eq!(stopped_proof.steps.len(), 2, "no trace entry was replayed");
}
