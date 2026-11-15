// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

fn scoped_fixture() -> Fixture {
    let mut terms = TermStore::new();
    let p = terms.mk_var("p", Sort::Bool);
    let q = terms.mk_var("q", Sort::Bool);
    let not_p = terms.mk_not_raw(p);
    let not_q = terms.mk_not_raw(q);
    let disjunction = terms.mk_app(ay_core::Symbol::named("or"), [not_p, q], Sort::Bool);
    let roots = vec![p, disjunction, not_q];
    let map = [(0, p), (1, q), (2, disjunction)].into_iter().collect();
    let positive = |n| Literal::positive(Variable::new(n));
    let scope = [positive(3).negated(), positive(4).negated()];
    let mut trace = ClauseTrace::new();
    trace.add_clause(41, vec![positive(0), positive(3)], true);
    trace.add_clause(
        7,
        vec![
            positive(2).negated(),
            positive(0).negated(),
            positive(1),
            positive(4),
        ],
        true,
    );
    trace.add_clause(
        92,
        vec![positive(1).negated(), positive(3), positive(4)],
        true,
    );
    trace.add_clause(101, vec![positive(2), positive(4)], true);
    trace.add_clause_with_hints(
        102,
        vec![positive(1), positive(3), positive(4)],
        false,
        vec![41, 101, 7],
    );
    trace.add_clause_with_hints(103, Vec::new(), false, vec![102, 92]);
    let validated = validate_clause_trace_resolution_with_unit_premises_interruptible(
        &trace,
        5,
        &scope,
        &ResolutionValidationLimits::unbounded(),
        &mut || false,
    )
    .unwrap();
    let mut annotations = vec![None; 7];
    annotations[6] = Some(ay_core::ClausificationProof {
        rule: ay_core::AletheRule::OrPos(0),
        source_term: disjunction,
    });
    let mut manager = SatProofManager::new(&map, &mut terms);
    manager.set_scope_assumptions(&scope).unwrap();
    manager.set_clausification_proofs(&annotations);
    let fragment = manager
        .build_exact_original_proof_fragment(&trace, &roots)
        .unwrap();
    Fixture {
        terms,
        roots,
        map,
        fragment,
        validated,
        trace,
    }
}

#[test]
fn scoped_materialization_projects_original_and_derived_guards() {
    let mut f = scoped_fixture();
    let proof = materialize(
        f.fragment,
        &f.validated,
        &f.map,
        &mut f.terms,
        &mut CheckedRefutationMeter::unbounded(),
    )
    .unwrap();
    assert!(ay_proof::check_proof_strict_with_context_and_progress(
        &proof,
        &f.terms,
        None,
        None,
        Some(&f.roots),
        &mut |_, _| true,
    )
    .unwrap()
    .is_complete());
    assert!(ay_proof::check_proof_strict_with_context_and_progress(
        &proof,
        &f.terms,
        None,
        None,
        Some(&f.roots[1..]),
        &mut |_, _| true,
    )
    .is_err());
    let text = ay_proof::try_export_alethe_with_problem_scope_and_overrides(
        &proof, &f.terms, &f.roots, None,
    )
    .unwrap();
    assert!(!text.contains(":rule hole"));
    let packet = std::env::temp_dir().join(format!("ay-scoped-rup-{}.json", std::process::id()));
    std::fs::write(&packet, serde_json::to_vec(&serde_json::json!({
        "type": "alethe_certificate", "version": "1.0",
        "problem": "(set-logic QF_UF)\n(declare-const p Bool)\n(declare-const q Bool)\n(assert p)\n(assert (or (not p) q))\n(assert (not q))\n(check-sat)\n",
        "proof": text,
    })).unwrap()).unwrap();
    println!(
        "independent scoped materialization certificate: {}",
        packet.display()
    );
}

#[test]
fn scoped_materialization_refuses_missing_scope_or_mapped_user_premise() {
    let mut f = scoped_fixture();
    for scope in [
        vec![],
        vec![Literal::negative(Variable::new(3))],
        vec![
            Literal::positive(Variable::new(3)),
            Literal::negative(Variable::new(4)),
        ],
    ] {
        assert!(
            validate_clause_trace_resolution_with_unit_premises_interruptible(
                &f.trace,
                5,
                &scope,
                &ResolutionValidationLimits::unbounded(),
                &mut || false,
            )
            .is_err()
        );
    }
    f.map.insert(3, f.roots[0]);
    assert!(materialize(
        f.fragment,
        &f.validated,
        &f.map,
        &mut f.terms,
        &mut CheckedRefutationMeter::unbounded()
    )
    .is_none());
}

#[test]
fn scoped_materialization_refuses_satisfied_guard_targets() {
    let p = Literal::positive(Variable::new(0));
    let s = Literal::positive(Variable::new(1));
    let mut trace = ClauseTrace::new();
    trace.add_clause(1, vec![p, s], true);
    trace.add_clause(2, vec![p.negated(), s], true);
    trace.add_clause_with_hints(3, vec![s.negated()], false, vec![]);
    trace.add_clause_with_hints(4, vec![], false, vec![1, 2]);
    let validated = validate_clause_trace_resolution_with_unit_premises_interruptible(
        &trace,
        2,
        &[s.negated()],
        &ResolutionValidationLimits::unbounded(),
        &mut || false,
    )
    .unwrap();
    // Normally this irrelevant satisfied row is outside the empty-clause cone.
    // Forcing it into the projected set must refuse, never turn it into false.
    assert!(scope::project(
        &validated,
        &[false, true, true, true, true],
        &HashMap::default(),
        &mut CheckedRefutationMeter::unbounded()
    )
    .is_none());
    assert!(scope::project(
        &validated,
        &[false, true, true, false, true],
        &HashMap::default(),
        &mut CheckedRefutationMeter::unbounded()
    )
    .is_some());
}
