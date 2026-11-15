// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_core::Sort;
use ay_sat::ClauseTrace;

mod scoped;

struct Fixture {
    terms: TermStore,
    roots: Vec<TermId>,
    map: HashMap<u32, TermId>,
    fragment: ExactOriginalProofFragment,
    validated: ValidatedPremisedClauseTraceResolution,
    trace: ClauseTrace,
}

fn fixture() -> Fixture {
    let mut terms = TermStore::new();
    let p = terms.mk_var("p", Sort::Bool);
    let q = terms.mk_var("q", Sort::Bool);
    let not_p = terms.mk_not_raw(p);
    let not_q = terms.mk_not_raw(q);
    let disjunction = terms.mk_app(ay_core::Symbol::named("or"), [not_p, q], Sort::Bool);
    let roots = vec![p, disjunction, not_q];
    let mut map = HashMap::default();
    map.insert(0, p);
    map.insert(1, q);
    map.insert(2, disjunction);
    let positive = |n| Literal::positive(Variable::new(n));
    let mut trace = ClauseTrace::new();
    trace.add_clause(41, vec![positive(0)], true);
    trace.add_clause(
        7,
        vec![positive(2).negated(), positive(0).negated(), positive(1)],
        true,
    );
    trace.add_clause(92, vec![positive(1).negated()], true);
    trace.add_clause(101, vec![positive(2)], true);
    trace.add_clause_with_hints(103, Vec::new(), false, vec![41, 101, 7, 92]);
    let validated = validate_clause_trace_resolution_with_unit_premises_interruptible(
        &trace,
        3,
        &[],
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
fn materialization_reconstructs_a_checked_chain_from_stable_original_ids() {
    let mut f = fixture();
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
    let text = ay_proof::try_export_alethe_with_problem_scope_and_overrides(
        &proof, &f.terms, &f.roots, None,
    )
    .unwrap();
    assert!(!text.contains(":rule hole") && text.contains(":rule resolution"));
    let packet =
        std::env::temp_dir().join(format!("ay-materialized-rup-{}.json", std::process::id()));
    std::fs::write(&packet, serde_json::to_vec(&serde_json::json!({
        "type": "alethe_certificate", "version": "1.0",
        "problem": "(set-logic QF_UF)\n(declare-const p Bool)\n(declare-const q Bool)\n(assert p)\n(assert (or (not p) q))\n(assert (not q))\n(check-sat)\n",
        "proof": text,
    })).unwrap()).unwrap();
    println!(
        "independent materialization certificate: {}",
        packet.display()
    );
}

#[test]
fn materialization_declines_missing_mapping_and_exhausted_aggregate_budget() {
    let mut f = fixture();
    f.map.remove(&1);
    assert!(materialize(
        f.fragment,
        &f.validated,
        &f.map,
        &mut f.terms,
        &mut CheckedRefutationMeter::unbounded()
    )
    .is_none());
    for work in [true, false] {
        let mut f = fixture();
        let mut meter = CheckedRefutationMeter::unbounded();
        if work {
            meter.limits.max_work = 1;
        } else {
            meter.limits.max_bytes = 1;
        }
        assert!(materialize(f.fragment, &f.validated, &f.map, &mut f.terms, &mut meter).is_none());
    }
}

#[test]
fn reverse_resolution_declines_forged_hints_and_tautological_targets() {
    let p = Literal::positive(Variable::new(0));
    let positive = [p];
    let negative = [p.negated()];
    let clauses: Vec<&[Literal]> = vec![&[], &positive, &negative];
    let mut row = ay_sat::RupStep {
        id: 3,
        clause: vec![],
        rup_hints: vec![1, 99],
    };
    assert!(rup::propagate(
        &row.clause,
        &row.rup_hints,
        &clauses,
        1,
        &mut CheckedRefutationMeter::unbounded()
    )
    .is_none());
    row.rup_hints = vec![1, 2];
    row.clause = vec![p, p.negated()];
    assert!(rup::propagate(
        &row.clause,
        &row.rup_hints,
        &clauses,
        1,
        &mut CheckedRefutationMeter::unbounded()
    )
    .is_none());
}

#[test]
fn materialization_keeps_fixed_premises_and_source_scope_explicit() {
    let mut f = fixture();
    let premised = validate_clause_trace_resolution_with_unit_premises_interruptible(
        &f.trace,
        3,
        &[Literal::positive(Variable::new(0))],
        &ResolutionValidationLimits::unbounded(),
        &mut || false,
    )
    .unwrap();
    assert!(materialize(
        f.fragment,
        &premised,
        &f.map,
        &mut f.terms,
        &mut CheckedRefutationMeter::unbounded()
    )
    .is_none());
    let mut f = fixture();
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
        Some(&f.roots[1..]),
        &mut |_, _| true,
    )
    .is_err());
}
