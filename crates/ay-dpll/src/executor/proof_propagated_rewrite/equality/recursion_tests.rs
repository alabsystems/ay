// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

struct Fixture {
    terms: TermStore,
    roots: Vec<TermId>,
    entries: HashMap<TermId, (TermId, TermId, u32)>,
    variables: Vec<TermId>,
    value: TermId,
}

impl Fixture {
    fn chain(length: usize) -> Self {
        let mut terms = TermStore::new();
        let mut variables: Vec<_> = (0..length)
            .map(|index| terms.mk_var(format!("chain_{index}"), Sort::Int))
            .collect();
        // This is also the real producer's variable-to-variable orientation.
        variables.reverse();
        let value = terms.mk_int(7.into());
        let mut roots = Vec::new();
        let mut entries = HashMap::default();
        for (index, &variable) in variables.iter().enumerate() {
            let replacement = variables.get(index + 1).copied().unwrap_or(value);
            let source = terms.mk_app(Symbol::named("="), [variable, replacement], Sort::Bool);
            roots.push(source);
            entries.insert(variable, (replacement, source, 1));
        }
        Self {
            terms,
            roots,
            entries,
            variables,
            value,
        }
    }
}

fn assert_strict_equality(
    terms: &mut TermStore,
    roots: &[TermId],
    mut proof: Proof,
    result: EqRes,
    expected: TermId,
) {
    let EqRes::Changed { to, eq_term, id } = result else {
        panic!("fixture must derive a changed equality");
    };
    assert_eq!(to, expected);
    ay_proof::validate_reachable_assumes_in_problem_scope(&proof, roots)
        .expect("only current defining equalities authorize the chain");
    let not_equality = terms.mk_not_raw(eq_term);
    let contrary = proof.add_assume(not_equality, None);
    proof.add_resolution(Vec::new(), eq_term, id, contrary);
    let quality = ay_proof::check_proof_strict(&proof, terms)
        .expect("unchanged strict checker replays the complete chain");
    assert!(quality.is_complete());
    assert_eq!(quality.trust_count, 0);
}

#[test]
fn equality_cycle_retains_only_a_checked_uncomposed_license() {
    let mut fixture = Fixture::chain(2);
    fixture.roots.truncate(1);
    let [x, y] = fixture.variables.as_slice() else {
        unreachable!()
    };
    let (x, y) = (*x, *y);
    // Each exact equality orientation is locally valid; their combination is
    // deliberately not a graph emitted by the cycle-safe substitution pass.
    fixture.entries.insert(y, (x, fixture.roots[0], 1));
    let source_set = fixture.roots.iter().copied().collect();
    let records = HashMap::default();
    let mut cx = PlanCx::new(
        &source_set,
        &fixture.roots,
        &records,
        &fixture.entries,
        &[],
        false,
    );
    let result = PropagationChainPlanner {
        terms: &mut fixture.terms,
    }
    .plan_derive_eq(&mut cx, x, 1)
    .expect("the existing uncomposed fallback remains available");
    assert!(cx.eq_in_progress.is_empty());
    assert!(cx.in_progress.is_empty());
    assert_eq!(cx.eq_memo.len(), 2);
    assert!(
        cx.budget > PLAN_NODE_BUDGET - 16,
        "cycle stops on its first repeated key"
    );
    assert_strict_equality(&mut fixture.terms, &fixture.roots, cx.chain, result, y);
}

#[test]
fn equality_active_depth_bounds_a_chain_of_shallow_entries() {
    let mut fixture = Fixture::chain(MAX_ACTIVE_EQUALITY_DEPTH + 4);
    let source_set = fixture.roots.iter().copied().collect();
    let records = HashMap::default();
    let mut cx = PlanCx::new(
        &source_set,
        &fixture.roots,
        &records,
        &fixture.entries,
        &[],
        false,
    );
    let result = PropagationChainPlanner {
        terms: &mut fixture.terms,
    }
    .plan_derive_eq(&mut cx, fixture.variables[0], 1)
    .expect("bounded prefix retains its exact uncomposed endpoint");
    assert!(cx.eq_in_progress.is_empty());
    assert!(cx.in_progress.is_empty());
    assert_eq!(cx.eq_memo.len(), MAX_ACTIVE_EQUALITY_DEPTH);
    assert!(
        cx.budget > 0,
        "depth refusal is independent of total node exhaustion"
    );
    // A depth-limited replay must not invent the unvisited terminal value.
    assert_ne!(fixture.variables[MAX_ACTIVE_EQUALITY_DEPTH], fixture.value);
    assert_strict_equality(
        &mut fixture.terms,
        &fixture.roots,
        cx.chain,
        result,
        fixture.variables[MAX_ACTIVE_EQUALITY_DEPTH],
    );
}

#[test]
fn equality_short_chain_replays_strictly_and_completed_memo_wins() {
    let mut fixture = Fixture::chain(4);
    let source_set = fixture.roots.iter().copied().collect();
    let records = HashMap::default();
    let mut cx = PlanCx::new(
        &source_set,
        &fixture.roots,
        &records,
        &fixture.entries,
        &[],
        false,
    );
    let mut planner = PropagationChainPlanner {
        terms: &mut fixture.terms,
    };
    let result = planner
        .plan_derive_eq(&mut cx, fixture.variables[0], 1)
        .unwrap();
    assert!(cx.eq_in_progress.is_empty());
    let steps = cx.chain.steps.len();
    let remaining = cx.budget;
    // Completed results need no new recursive descent even when the caller's
    // active stack has reached its cap. These keys model unrelated callers.
    for stamp in 100..100 + MAX_ACTIVE_EQUALITY_DEPTH as u32 {
        cx.eq_in_progress
            .insert((fixture.variables[0], stamp, ScalarEqualityMode::Legacy));
    }
    let replayed = planner
        .plan_derive_eq(&mut cx, fixture.variables[0], 1)
        .unwrap();
    assert!(matches!((result, replayed),
        (EqRes::Changed { to: a, id: i, .. }, EqRes::Changed { to: b, id: j, .. }) if a == b && i == j));
    assert_eq!(cx.chain.steps.len(), steps);
    assert_eq!(cx.budget, remaining);
    cx.eq_in_progress.clear();
    assert_strict_equality(
        planner.terms,
        &fixture.roots,
        cx.chain,
        result,
        fixture.value,
    );
}
