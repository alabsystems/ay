// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! #aig-bridged-empty: an empty clause whose traced hints run through
//! bit-level (term-less) variables closes by failed-literal probing over the
//! clauses that DID translate, and only when those clauses refute.
//!
//! The fixture is the r1/r3 shape reduced to Booleans. There are `n`
//! asserted `or_i = (or a_i b_i)` units, their Tseitin `and_i = (and ¬a_i
//! ¬b_i)` gates, and the asserted `big = (or and_1 .. and_n)`. The SAT core
//! refutes through per-gate bit-level nodes `u_i`: the original unit `¬u_i`
//! and the link `(¬and_i ∨ u_i)`. Both are untranslatable, so hint replay
//! ends on a residual. Twelve gates is the measured r3 count. r3 also
//! asserts a thirteenth disjunction, the b8/b46 pair, which the authored
//! inner `and` omits. The fixture's `distractor` gate is that disjunction.
//! Its case split doubles the learning-free bounded DPLL's tree past the
//! node cap (4097 nodes against 4096; without it the tree has 4095 nodes and
//! the search closes).

use super::*;

const GATES: usize = 12;

struct Fixture {
    terms: TermStore,
    var_to_term: HashMap<u32, TermId>,
    trace: ClauseTrace,
}

/// Build the fixture. `drop_and_pos_of` removes gate `k`'s `(¬and_k ∨ ¬a_k)`
/// clause, which makes the translatable clauses satisfiable (`and_k`, `a_k`,
/// `¬b_k`): the negative twin.
fn fixture(drop_and_pos_of: Option<usize>) -> Fixture {
    let mut terms = TermStore::new();
    let mut var_to_term: HashMap<u32, TermId> = HashMap::default();
    let pos = |v: u32| Literal::positive(Variable::new(v));
    let neg = |v: u32| Literal::negative(Variable::new(v));
    // Variables: 4i a_i, 4i+1 b_i, 4i+2 or_i, 4i+3 and_i; then big; then the
    // distractor's c, d and `(or c d)`; then the unmapped bit-level nodes u_i.
    let big_var = (4 * GATES) as u32;
    let (c_var, d_var, cd_var) = (big_var + 1, big_var + 2, big_var + 3);
    let node_var = |i: usize| big_var + 4 + i as u32;
    let mut gates = Vec::with_capacity(GATES);
    for i in 0..GATES {
        let a = terms.mk_var(format!("probe_a{i}"), Sort::Bool);
        let b = terms.mk_var(format!("probe_b{i}"), Sort::Bool);
        let or = terms.mk_app(Symbol::named("or"), vec![a, b], Sort::Bool);
        let not_a = terms.mk_not_raw(a);
        let not_b = terms.mk_not_raw(b);
        let and = terms.mk_app(Symbol::named("and"), vec![not_a, not_b], Sort::Bool);
        let base = (4 * i) as u32;
        var_to_term.insert(base, a);
        var_to_term.insert(base + 1, b);
        var_to_term.insert(base + 2, or);
        var_to_term.insert(base + 3, and);
        gates.push(and);
    }
    let big = terms.mk_app(Symbol::named("or"), gates, Sort::Bool);
    var_to_term.insert(big_var, big);
    let c = terms.mk_var("probe_c", Sort::Bool);
    let d = terms.mk_var("probe_d", Sort::Bool);
    let cd = terms.mk_app(Symbol::named("or"), vec![c, d], Sort::Bool);
    var_to_term.insert(c_var, c);
    var_to_term.insert(d_var, d);
    var_to_term.insert(cd_var, cd);

    let mut trace = ClauseTrace::new();
    let mut id = 0u64;
    let mut add = |trace: &mut ClauseTrace, clause: Vec<Literal>| {
        id += 1;
        trace.add_clause(id, clause, true);
        id
    };
    let mut hints = Vec::new();
    for i in 0..GATES {
        let base = (4 * i) as u32;
        let (a, b, or, and) = (base, base + 1, base + 2, base + 3);
        add(&mut trace, vec![pos(or)]);
        add(&mut trace, vec![neg(or), pos(a), pos(b)]);
        if drop_and_pos_of != Some(i) {
            add(&mut trace, vec![neg(and), neg(a)]);
        }
        add(&mut trace, vec![neg(and), neg(b)]);
        add(&mut trace, vec![pos(and), pos(a), pos(b)]);
        if i == 0 {
            // The distractor, in r3's place: right after the first gate.
            add(&mut trace, vec![pos(cd_var)]);
            add(&mut trace, vec![neg(cd_var), pos(c_var), pos(d_var)]);
        }
    }
    hints.push(add(&mut trace, vec![pos(big_var)]));
    let mut big_pos = vec![neg(big_var)];
    big_pos.extend((0..GATES).map(|i| pos((4 * i + 3) as u32)));
    hints.push(add(&mut trace, big_pos));
    for i in 0..GATES {
        let and = (4 * i + 3) as u32;
        hints.push(add(&mut trace, vec![neg(node_var(i))]));
        hints.push(add(&mut trace, vec![neg(and), pos(node_var(i))]));
    }
    id += 1;
    trace.add_clause_with_hints(id, Vec::new(), false, hints);
    Fixture {
        terms,
        var_to_term,
        trace,
    }
}

fn is_trust(proof: &Proof, id: ProofId) -> bool {
    matches!(
        proof.get_step(id),
        Some(ProofStep::Step {
            rule: AletheRule::Trust,
            ..
        })
    )
}

/// The translatable originals as a clause database: each SAT clause with the
/// proof node `add_original_clause_step` gives it.
fn translatable_versions(fx: &mut Fixture, proof: &mut Proof) -> Vec<SatClauseVersion> {
    let mut existing: HashMap<Vec<TermId>, ProofId> = HashMap::default();
    let mut versions = Vec::new();
    for entry in fx.trace.entries() {
        if !entry.is_original {
            continue;
        }
        let terms: Option<Vec<TermId>> = entry
            .clause
            .iter()
            .map(|lit| {
                let atom = *fx.var_to_term.get(&(lit.variable().index() as u32))?;
                Some(if lit.is_positive() {
                    atom
                } else {
                    fx.terms.mk_not_raw(atom)
                })
            })
            .collect();
        let Some(terms) = terms else {
            continue;
        };
        let pid = SatProofManager::add_original_clause_step(
            &mut fx.terms,
            proof,
            &terms,
            &mut existing,
            None,
            None,
        );
        versions.push((entry.clause.to_vec(), pid));
    }
    versions
}

#[test]
fn bit_level_hint_chain_closes_by_probing_and_passes_the_strict_checker() {
    let mut fx = fixture(None);
    let mut proof = Proof::new();
    let mut manager = SatProofManager::new(&fx.var_to_term, &mut fx.terms);
    let empty = manager
        .process_trace(&fx.trace, &mut proof)
        .expect("the translatable clauses refute");
    assert_eq!(
        manager.trust_fallback_count(),
        0,
        "the empty clause must not fall back to trust"
    );
    let Some(ProofStep::Resolution { clause, .. }) = proof.get_step(empty) else {
        panic!("expected a resolution step for the empty clause");
    };
    assert_eq!(clause.as_slice(), []);
    assert!(
        !proof.steps.iter().any(|step| matches!(
            step,
            ProofStep::Step {
                rule: AletheRule::Trust,
                ..
            }
        )),
        "no trust step anywhere in the replayed proof"
    );
    drop(manager);
    ay_proof::check_proof_strict(&proof, &fx.terms)
        .unwrap_or_else(|error| panic!("strict checker rejected the probed proof: {error}"));
}

/// Why the closer exists: on this database level-0 RUP stalls and the bounded
/// DPLL runs out of nodes, and probing alone derives `(cl)`.
#[test]
fn probing_closes_where_level0_rup_and_bounded_dpll_decline() {
    let mut fx = fixture(None);
    let mut proof = Proof::new();
    let versions = translatable_versions(&mut fx, &mut proof);
    let mut manager = SatProofManager::new(&fx.var_to_term, &mut fx.terms);
    assert!(manager
        .derive_empty_via_level0_rup(&versions, &mut proof)
        .is_none());
    assert!(manager
        .derive_empty_via_bounded_dpll_theory(&versions, &mut proof)
        .is_none());
    let empty = manager
        .derive_empty_via_failed_literal_probing(&versions, &mut proof)
        .expect("probing derives the empty clause");
    assert!(!is_trust(&proof, empty));
    drop(manager);
    ay_proof::check_proof_strict(&proof, &fx.terms)
        .unwrap_or_else(|error| panic!("strict checker rejected the probed proof: {error}"));
}

/// Negative twin: with one `and_pos` clause missing the translatable clauses
/// are satisfiable. Probing still learns the other gates' units, but it must
/// not close, must leave no step behind, and replay keeps the honest trust
/// fallback.
#[test]
fn satisfiable_translatable_clauses_are_never_closed() {
    let mut fx = fixture(Some(GATES / 2));
    let mut proof = Proof::new();
    let versions = translatable_versions(&mut fx, &mut proof);
    let mut manager = SatProofManager::new(&fx.var_to_term, &mut fx.terms);
    let entry_len = proof.steps.len();
    assert!(manager
        .derive_empty_via_failed_literal_probing(&versions, &mut proof)
        .is_none());
    assert_eq!(
        proof.steps.len(),
        entry_len,
        "a declined probe leaves no step"
    );
    drop(manager);

    let mut fx = fixture(Some(GATES / 2));
    let mut proof = Proof::new();
    let mut manager = SatProofManager::new(&fx.var_to_term, &mut fx.terms);
    let empty = manager
        .process_trace(&fx.trace, &mut proof)
        .expect("the weak empty clause is still returned");
    assert_eq!(manager.trust_fallback_count(), 1);
    assert!(is_trust(&proof, empty), "no derivation is fabricated");
}

/// The caller's stop wins: a fired stop declines before any probe.
#[test]
fn a_fired_stop_declines_without_steps() {
    let mut fx = fixture(None);
    let mut proof = Proof::new();
    let versions = translatable_versions(&mut fx, &mut proof);
    let fired = || true;
    let mut manager = SatProofManager::new(&fx.var_to_term, &mut fx.terms);
    manager.set_should_stop(&fired);
    let entry_len = proof.steps.len();
    assert!(manager
        .derive_empty_via_failed_literal_probing(&versions, &mut proof)
        .is_none());
    assert_eq!(proof.steps.len(), entry_len);
}

/// End to end: model-checker-consumer's reduced realloc validation query (r3) under an
/// explicit proof request, the `ay --proof` posture, whose mandatory strict
/// certification refused the probe-less replay with "step t7 uses unverified
/// trust rule" and answered `unknown`. The default-posture twin is
/// `reduced_realloc_validation_query_publishes_unsat_in_the_default_posture`.
#[test]
fn reduced_realloc_validation_query_publishes_unsat_under_an_explicit_proof_request() {
    let script = include_str!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/tests/fixtures/closed_fold_wide_bv_pin_with_array_conjunct.smt2"
    ));
    let commands = ay_frontend::parse(script).expect("fixture must parse");
    let mut executor = crate::executor::Executor::new();
    executor.set_produce_proofs(true);
    let mut outputs = Vec::new();
    for command in &commands {
        if let Some(line) = executor
            .execute_authored(command)
            .expect("fixture must execute")
        {
            outputs.push(line);
        }
    }
    let admission = executor.last_command_unsat_admission_tag();
    let reason = executor
        .execute(&ay_frontend::Command::GetInfo(
            ":reason-unknown".to_string(),
        ))
        .ok()
        .flatten();
    assert_eq!(outputs, ["unsat"], "reason-unknown: {reason:?}");
    assert_eq!(
        admission,
        Some("strict-proof"),
        "the published unsat must be admitted by a strict proof"
    );
}
