// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

pub(super) fn wide(choices: &[&str]) -> Executor {
    let mut executor = Executor::new();
    let mut found_query = false;
    for command in ay_frontend::parse(WIDE).unwrap() {
        if matches!(command, ay_frontend::Command::CheckSat) {
            found_query = true;
            break;
        }
        executor.execute(&command).unwrap();
    }
    assert!(found_query);
    for choice in choices {
        let command = ay_frontend::parse(&format!("(assert {choice})")).unwrap();
        assert_eq!(executor.execute_all(&command).unwrap(), [] as [String; 0]);
    }
    executor
}

pub(super) fn app(terms: &mut TermStore, name: &str, args: &[TermId]) -> TermId {
    terms.mk_app(Symbol::named(name), args, Sort::Bool)
}

pub(super) struct Chain {
    pub(super) terms: TermStore,
    pub(super) roots: Vec<TermId>,
    pub(super) guard: TermId,
    pub(super) other_guard: TermId,
    pub(super) source: TermId,
    pub(super) body: TermId,
    pub(super) goal: TermId,
    pub(super) edges: [TermId; 2],
    pub(super) vars: [TermId; 3],
}

impl Chain {
    pub(super) fn new() -> Self {
        let mut terms = TermStore::new();
        let guard = terms.mk_var("actual activation", Sort::Bool);
        let other_guard = terms.mk_var("unasserted activation", Sort::Bool);
        let vars = ["x", "middle", "y"].map(|name| terms.mk_var(name, Sort::bitvec(129)));
        // Deliberately reversed edges: the graph must use exact symmetry.
        let edges = [
            app(&mut terms, "=", &[vars[1], vars[0]]),
            app(&mut terms, "=", &[vars[2], vars[1]]),
        ];
        let nested = app(&mut terms, "and", &[edges[1], edges[0]]);
        let body = app(&mut terms, "and", &[edges[0], nested]);
        let negative_guard = terms.mk_not_raw(guard);
        let source = app(&mut terms, "or", &[negative_guard, body]);
        let equality = app(&mut terms, "=", &[vars[0], vars[2]]);
        let goal = terms.mk_not_raw(equality);
        Self {
            terms,
            roots: vec![source, guard, goal],
            guard,
            other_guard,
            source,
            body,
            goal,
            edges,
            vars,
        }
    }
}

pub(super) fn assert_refutation(terms: &TermStore, roots: &[TermId], proof: &Proof) {
    let quality = ay_proof::check_proof_strict(proof, terms).unwrap();
    assert_eq!(quality.trust_count, 0, "{quality}");
    assert!(quality.is_complete(), "{quality}");
    for step in &proof.steps {
        if let ProofStep::Assume(term) = step {
            assert!(roots.contains(term), "only original roots may be assumed");
        }
    }
    let checked = ay_proof::authenticate_premise_clauses_strict_with_context_and_progress(
        proof,
        terms,
        None,
        None,
        roots,
        &mut |_, _| true,
    )
    .unwrap();
    let last = ProofId(u32::try_from(proof.steps.len().checked_sub(1).unwrap()).unwrap());
    assert_eq!(checked.clause(last), Some([].as_slice()));
}
