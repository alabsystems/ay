// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! c7 fragment-channel tests (#ppp-c7, L2): sealed `PropagateValues` replay
//! and qpf premise-forced instance roots. Environments here are supplied
//! directly (the executor-side seal path has its own token tests in
//! `derivation_evidence`); what these tests pin down is that the BUILDER
//! replays independently — a tampered map entry can only decline, and every
//! accepted chain terminates in exactly the traced unit.

use num_bigint::BigInt;

use super::*;

/// Shared c7 fixture: authored root `(and src before)` where
/// `src = (= (f one) two)` is the defining equality and
/// `before = (g (f one))` is rewritten by the pass to `after = (g two)`.
fn propagation_fixture() -> (
    TermStore,
    HashMap<u32, TermId>,
    TermId,
    TermId,
    TermId,
    FragmentPropagationEnvironment,
) {
    let mut terms = TermStore::new();
    let one = terms.mk_int(BigInt::from(1));
    let two = terms.mk_int(BigInt::from(2));
    let f_one = terms.mk_app(Symbol::named("pua_f"), [one], Sort::Int);
    let src = terms.mk_app(Symbol::named("="), [f_one, two], Sort::Bool);
    let before = terms.mk_app(Symbol::named("pua_g"), [f_one], Sort::Bool);
    let after = terms.mk_app(Symbol::named("pua_g"), [two], Sort::Bool);
    let root = terms.mk_app(Symbol::named("and"), [src, before], Sort::Bool);
    let mut var_to_term: HashMap<u32, TermId> = HashMap::default();
    var_to_term.insert(0, after);
    let mut environment = FragmentPropagationEnvironment::default();
    environment.entry_by_expr.insert(f_one, (two, src, 1));
    environment.record_by_after.insert(after, (before, 1));
    (terms, var_to_term, root, after, before, environment)
}

/// (L2, c7 positive) A propagation-rewritten unit is derived from the
/// authored root through the replayed cong/equiv chain, terminating in
/// exactly the traced unit and assuming only the authored root.
#[test]
fn exact_original_fragment_derives_propagation_rewritten_unit() {
    let (mut terms, var_to_term, root, after, _before, environment) = propagation_fixture();
    let mut trace = ClauseTrace::new();
    trace.add_clause(1, vec![Literal::positive(Variable::new(0))], true);

    let fragment = {
        let mut manager = SatProofManager::new(&var_to_term, &mut terms);
        manager.set_propagation_environment(&environment);
        manager
            .build_exact_original_proof_fragment(&trace, &[root])
            .expect("the replayed propagation rewrite has chain authority")
    };
    let binding = fragment.bindings.get(&1).expect("binding for ID 1");
    let step_clause = match fragment.proof.get_step(binding.proof_id) {
        Some(ProofStep::Step { clause, .. }) | Some(ProofStep::Resolution { clause, .. }) => {
            clause.clone()
        }
        other => panic!("expected a derived step, got {other:?}"),
    };
    assert_eq!(step_clause, vec![after]);
    let assumed: Vec<TermId> = fragment
        .proof
        .steps
        .iter()
        .filter_map(|step| match step {
            ProofStep::Assume(term) => Some(*term),
            _ => None,
        })
        .collect();
    assert_eq!(assumed, vec![root], "only the authored root may be assumed");
}

/// (L2, c7 dedup) Duplicate rewritten-unit originals share ONE emitted chain
/// (the P3b duplicate-precharge blowout guard), with distinct bindings.
#[test]
fn exact_original_fragment_memoizes_duplicate_propagation_units() {
    let (mut terms, var_to_term, root, _after, _before, environment) = propagation_fixture();
    let mut trace = ClauseTrace::new();
    trace.add_clause(1, vec![Literal::positive(Variable::new(0))], true);
    trace.add_clause(2, vec![Literal::positive(Variable::new(0))], true);

    let fragment = {
        let mut manager = SatProofManager::new(&var_to_term, &mut terms);
        manager.set_propagation_environment(&environment);
        manager
            .build_exact_original_proof_fragment(&trace, &[root])
            .expect("duplicate rewritten units share one chain")
    };
    let first = fragment.bindings.get(&1).expect("binding for ID 1");
    let second = fragment.bindings.get(&2).expect("binding for ID 2");
    assert_eq!(
        first.proof_id, second.proof_id,
        "duplicate originals must share one emitted chain"
    );
}

/// (L2, c7 negative) A record whose claimed `after` does not match the
/// independent replay is refused: the environment is a hint, and the builder
/// re-derives the rewrite from the licensing entries before emitting
/// anything.
#[test]
fn exact_original_fragment_rejects_tampered_propagation_record() {
    let (mut terms, var_to_term_ignored, root, _after, before, mut environment) =
        propagation_fixture();
    drop(var_to_term_ignored);
    let three = terms.mk_int(BigInt::from(3));
    let forged_after = terms.mk_app(Symbol::named("pua_g"), [three], Sort::Bool);
    environment.record_by_after.clear();
    environment
        .record_by_after
        .insert(forged_after, (before, 1));
    let mut var_to_term: HashMap<u32, TermId> = HashMap::default();
    var_to_term.insert(0, forged_after);
    let mut trace = ClauseTrace::new();
    trace.add_clause(1, vec![Literal::positive(Variable::new(0))], true);

    let error = {
        let mut manager = SatProofManager::new(&var_to_term, &mut terms);
        manager.set_propagation_environment(&environment);
        manager
            .build_exact_original_proof_fragment(&trace, &[root])
            .expect_err("a forged after-term must not gain chain authority")
    };
    assert_eq!(
        error,
        ExactOriginalProofError::UnauthenticatedOriginalClause {
            clause_id: 1,
            clause: vec![forged_after],
        }
    );
}

/// (L2, c7 negative) A record licensed by an entry whose defining equality is
/// NOT derivable from the authored roots is refused — the licensing source
/// must itself carry chain authority.
#[test]
fn exact_original_fragment_rejects_unlicensed_propagation_source() {
    let (mut terms, var_to_term, _root, after, _before, environment) = propagation_fixture();
    // The authored root is now an unrelated assertion: the defining equality
    // `src` is no longer reachable, so deriving `(cl src)` must fail.
    let unrelated = terms.mk_var("pua_unrelated", Sort::Bool);
    let mut trace = ClauseTrace::new();
    trace.add_clause(1, vec![Literal::positive(Variable::new(0))], true);

    let error = {
        let mut manager = SatProofManager::new(&var_to_term, &mut terms);
        manager.set_propagation_environment(&environment);
        manager
            .build_exact_original_proof_fragment(&trace, &[unrelated])
            .expect_err("an underivable licensing source must decline the chain")
    };
    assert_eq!(
        error,
        ExactOriginalProofError::UnauthenticatedOriginalClause {
            clause_id: 1,
            clause: vec![after],
        }
    );
}

/// Shared qpf instance-root fixture: authored `F = forall x:BV8. (or C (not
/// (= x #x01)))` with `C = (and (= (h x) #x01) (= (h2 x) #x02))`; the raw
/// exact instance at `x := #x01` has survivor `C[x:=#x01]` and one closed
/// refuted premise disjunct `(not (= #x01 #x01))`.
fn instance_root_fixture() -> (
    TermStore,
    TermId,
    Vec<TermId>,
    TermId,
    TermId,
    Vec<TermId>,
    Vec<TermId>,
) {
    let mut terms = TermStore::new();
    let width = 8u32;
    let bv_sort = Sort::BitVec(ay_core::BitVecSort::new(width));
    let x = terms.mk_var("ira_x", bv_sort.clone());
    let one = terms.mk_bitvec(BigInt::from(1), width);
    let two = terms.mk_bitvec(BigInt::from(2), width);
    let h_x = terms.mk_app(Symbol::named("ira_h"), [x], bv_sort.clone());
    let h2_x = terms.mk_app(Symbol::named("ira_h2"), [x], bv_sort.clone());
    let c1 = terms.mk_app(Symbol::named("="), [h_x, one], Sort::Bool);
    let c2 = terms.mk_app(Symbol::named("="), [h2_x, two], Sort::Bool);
    let conjunction = terms.mk_app(Symbol::named("and"), [c1, c2], Sort::Bool);
    let x_eq_one = terms.mk_app(Symbol::named("="), [x, one], Sort::Bool);
    let premise = terms.mk_not_raw(x_eq_one);
    let body = terms.mk_app(Symbol::named("or"), [conjunction, premise], Sort::Bool);
    let quantifier = terms.mk_forall(vec![("ira_x".to_string(), bv_sort)], body);
    let mut substitution: HashMap<String, TermId> = HashMap::default();
    substitution.insert("ira_x".to_string(), one);
    let instance = crate::ematching::subst_vars_exact_qf(&mut terms, body, &substitution)
        .expect("closed substitution succeeds");
    let TermData::App(_, disjuncts) = terms.get(instance).clone() else {
        panic!("raw instance is an or application");
    };
    let survivor = disjuncts[0];
    let refuted = vec![disjuncts[1]];
    let TermData::App(_, conjuncts) = terms.get(survivor).clone() else {
        panic!("survivor is an and application");
    };
    (
        terms,
        quantifier,
        vec![one],
        instance,
        survivor,
        refuted,
        conjuncts.to_vec(),
    )
}

/// (L2, c7 instance root positive) A survivor conjunct of the sealed qpf
/// instance is derived through assume-F + forall_inst + or + closed-disjunct
/// elimination + and_pos, assuming only the authored quantifier, and the
/// closed premise refutation is a zero-variable `BvBitBlast` lemma.
#[test]
fn exact_original_fragment_derives_instance_root_conjunct() {
    let (mut terms, quantifier, values, instance, survivor, refuted, conjuncts) =
        instance_root_fixture();
    let unit = conjuncts[1];
    let mut var_to_term: HashMap<u32, TermId> = HashMap::default();
    var_to_term.insert(0, unit);
    let roots = [FragmentInstanceRootDerivation {
        quantifier,
        values,
        instance,
        survivor,
        refuted_disjuncts: refuted,
    }];
    let mut trace = ClauseTrace::new();
    trace.add_clause(1, vec![Literal::positive(Variable::new(0))], true);

    let fragment = {
        let mut manager = SatProofManager::new(&var_to_term, &mut terms);
        manager.set_instance_root_derivations(&roots);
        manager
            .build_exact_original_proof_fragment(&trace, &[quantifier])
            .expect("a sealed instance-root conjunct has chain authority")
    };
    let binding = fragment.bindings.get(&1).expect("binding for ID 1");
    let step_clause = match fragment.proof.get_step(binding.proof_id) {
        Some(ProofStep::Step { clause, .. }) | Some(ProofStep::Resolution { clause, .. }) => {
            clause.clone()
        }
        other => panic!("expected a derived step, got {other:?}"),
    };
    assert_eq!(step_clause, vec![unit]);
    let assumed: Vec<TermId> = fragment
        .proof
        .steps
        .iter()
        .filter_map(|step| match step {
            ProofStep::Assume(term) => Some(*term),
            _ => None,
        })
        .collect();
    assert_eq!(
        assumed,
        vec![quantifier],
        "only the authored quantifier may be assumed"
    );
    let closed_lemmas = fragment
        .proof
        .steps
        .iter()
        .filter(|step| {
            matches!(
                step,
                ProofStep::TheoryLemma {
                    kind: ay_core::TheoryLemmaKind::BvBitBlast,
                    ..
                }
            )
        })
        .count();
    assert_eq!(
        closed_lemmas, 1,
        "exactly one closed premise-disjunct refutation lemma"
    );
}

/// (L2, c7 instance root negative) When the sealed refuted-disjunct list
/// does not cover the raw premise disjunct, the survivor derivation must
/// decline — a disjunct is never dropped without its own refutation lemma.
#[test]
fn exact_original_fragment_rejects_instance_root_with_uncovered_disjunct() {
    let (mut terms, quantifier, values, instance, survivor, _refuted, conjuncts) =
        instance_root_fixture();
    let unit = conjuncts[1];
    let mut var_to_term: HashMap<u32, TermId> = HashMap::default();
    var_to_term.insert(0, unit);
    let roots = [FragmentInstanceRootDerivation {
        quantifier,
        values,
        instance,
        survivor,
        refuted_disjuncts: Vec::new(),
    }];
    let mut trace = ClauseTrace::new();
    trace.add_clause(1, vec![Literal::positive(Variable::new(0))], true);

    let error = {
        let mut manager = SatProofManager::new(&var_to_term, &mut terms);
        manager.set_instance_root_derivations(&roots);
        manager
            .build_exact_original_proof_fragment(&trace, &[quantifier])
            .expect_err("an uncovered premise disjunct must decline the chain")
    };
    assert_eq!(
        error,
        ExactOriginalProofError::UnauthenticatedOriginalClause {
            clause_id: 1,
            clause: vec![unit],
        }
    );
}

/// (L2, c7 instance root negative) An instance root whose quantifier is not
/// an authored problem root derives nothing.
#[test]
fn exact_original_fragment_rejects_unauthored_instance_root() {
    let (mut terms, quantifier, values, instance, survivor, refuted, conjuncts) =
        instance_root_fixture();
    let unit = conjuncts[1];
    let mut var_to_term: HashMap<u32, TermId> = HashMap::default();
    var_to_term.insert(0, unit);
    let roots = [FragmentInstanceRootDerivation {
        quantifier,
        values,
        instance,
        survivor,
        refuted_disjuncts: refuted,
    }];
    let unrelated = terms.mk_var("ira_unrelated", Sort::Bool);
    let mut trace = ClauseTrace::new();
    trace.add_clause(1, vec![Literal::positive(Variable::new(0))], true);

    let error = {
        let mut manager = SatProofManager::new(&var_to_term, &mut terms);
        manager.set_instance_root_derivations(&roots);
        manager
            .build_exact_original_proof_fragment(&trace, &[unrelated])
            .expect_err("an unauthored quantifier grants no instance-root authority")
    };
    assert_eq!(
        error,
        ExactOriginalProofError::UnauthenticatedOriginalClause {
            clause_id: 1,
            clause: vec![unit],
        }
    );
}

/// (L2, c7 swap bridge) A traced unit that is the exact binary-`=` argument
/// swap of a survivor conjunct is bridged with the premiseless
/// `eq_symmetric` tautology (the canonicalized respelling the simplifying
/// substituter mints).
#[test]
fn exact_original_fragment_bridges_swapped_conjunct_respelling() {
    let (mut terms, quantifier, values, instance, survivor, refuted, conjuncts) =
        instance_root_fixture();
    let raw = conjuncts[0];
    let TermData::App(_, args) = terms.get(raw).clone() else {
        panic!("conjunct is an equality application");
    };
    let swapped = terms.mk_app(Symbol::named("="), [args[1], args[0]], Sort::Bool);
    let mut var_to_term: HashMap<u32, TermId> = HashMap::default();
    var_to_term.insert(0, swapped);
    let roots = [FragmentInstanceRootDerivation {
        quantifier,
        values,
        instance,
        survivor,
        refuted_disjuncts: refuted,
    }];
    let mut trace = ClauseTrace::new();
    trace.add_clause(1, vec![Literal::positive(Variable::new(0))], true);

    let fragment = {
        let mut manager = SatProofManager::new(&var_to_term, &mut terms);
        manager.set_instance_root_derivations(&roots);
        manager
            .build_exact_original_proof_fragment(&trace, &[quantifier])
            .expect("the exact argument swap of a conjunct has chain authority")
    };
    let binding = fragment.bindings.get(&1).expect("binding for ID 1");
    let step_clause = match fragment.proof.get_step(binding.proof_id) {
        Some(ProofStep::Step { clause, .. }) | Some(ProofStep::Resolution { clause, .. }) => {
            clause.clone()
        }
        other => panic!("expected a derived step, got {other:?}"),
    };
    assert_eq!(step_clause, vec![swapped]);
    let has_eq_symmetric = fragment.proof.steps.iter().any(|step| {
        matches!(
            step,
            ProofStep::Step {
                rule: AletheRule::EqSymmetric,
                ..
            }
        )
    });
    assert!(has_eq_symmetric, "the swap bridge uses eq_symmetric");
}
