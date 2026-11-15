// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Actual producer, exact license, and strict original-root replay; no solver.

use super::*;
use ay_core::ProofStep;

fn replay_parsed(source: &str, variables: &[&str], query: usize, opaque: Option<usize>) {
    let mut executor = Executor::new();
    let commands = ay_frontend::parse(source).unwrap();
    assert!(executor.execute_all(&commands).unwrap().is_empty());
    let originals = executor.ctx.assertions.clone();
    assert_eq!(query, variables.len());
    assert_eq!(originals.len(), query + 1 + usize::from(opaque.is_some()));
    let variable_ids: Vec<_> = variables
        .iter()
        .map(|name| executor.ctx.symbol_info(name).unwrap().term.unwrap())
        .collect();
    for &variable in &variable_ids {
        assert!(matches!(
            executor.ctx.terms.get(variable),
            TermData::Var(_, _)
        ));
        assert!(matches!(
            executor.ctx.terms.sort(variable),
            Sort::Array(_) | Sort::Uninterpreted(_)
        ));
    }
    let propagation = Arc::new(Mutex::new(PropagateValues::new()));
    let mut pass = RecordedVariableSubstitution::new(
        Arc::new(Mutex::new(VariableSubstitution::new())),
        Arc::clone(&propagation),
        Box::new(|_, _| true),
    );
    let mut working = originals.clone();
    let mut sources: Vec<_> = originals.iter().map(|&root| vec![root]).collect();
    let original_sources = sources.clone();
    assert!(pass.apply_with_sources(&mut executor.ctx.terms, &mut working, &mut sources));
    assert_eq!(sources, original_sources);
    assert_eq!(executor.ctx.assertions, originals);
    let records = propagation
        .lock()
        .unwrap()
        .take_propagation_records()
        .unwrap();
    assert_eq!(records.entries.len(), variable_ids.len());
    let mut entries = HashMap::default();
    for (index, &variable) in variable_ids.iter().enumerate() {
        let entry = records
            .entries
            .iter()
            .find(|entry| entry.expr == variable)
            .unwrap();
        assert_eq!(entry.source_assertion, originals[index]);
        let (key, value) = CheckedPropagationEntry::seal(&executor, entry)
            .expect("real aggregate defining-equality hint")
            .into_current(&executor)
            .unwrap();
        entries.insert(key, value);
    }
    let record = records
        .rewrites
        .iter()
        .find(|record| record.before == originals[query])
        .unwrap();
    let target = working[query];
    assert_ne!(target, originals[query]);
    assert_eq!(
        record.after, target,
        "never replace the actual producer image"
    );
    assert!(records
        .entries
        .iter()
        .all(|entry| entry.stamp <= record.stamp));
    if let Some(index) = opaque {
        assert_eq!(working[index], originals[index]);
        assert!(!records
            .rewrites
            .iter()
            .any(|record| record.before == originals[index]));
    }
    let (key, value) = CheckedPropagationDerivation::seal(&mut executor, record, &records.entries)
        .expect("entry-only case needs no selector fold in exact-image replay")
        .into_current(&executor)
        .unwrap();
    let rewrites = HashMap::from_iter([(key, value)]);
    let source_set = originals.iter().copied().collect();
    let mut cx = PlanCx::new(&source_set, &originals, &rewrites, &entries, &[], true);
    let conclusion = PropagationChainPlanner {
        terms: &mut executor.ctx.terms,
    }
    .plan_derive_clause(&mut cx, target)
    .expect("derive rewritten aggregate arguments from exact original equalities");
    let proof = cx.chain;
    assert!(!proof.steps.contains(&ProofStep::Assume(target)));
    ay_proof::validate_reachable_assumes_in_problem_scope(&proof, &originals).unwrap();
    let datatypes = executor.datatype_decls_for_strict_proof();
    let selectors = executor.ctor_selector_decls_for_strict_proof();
    let signatures = executor
        .datatype_member_signatures_for_strict_proof()
        .unwrap();
    let checked = ay_proof::authenticate_premise_clauses_strict_with_typed_context_and_progress(
        &proof,
        &executor.ctx.terms,
        Some(&datatypes),
        Some(&selectors),
        &signatures,
        &originals,
        &mut |_, _| true,
    )
    .expect("unchanged strict typed checker must validate every equality step");
    assert_eq!(checked.clause(conclusion), Some([target].as_slice()));
    // The new shape admission does not bypass the existing final stop gate.
    assert!(
        ay_proof::authenticate_premise_clauses_strict_with_typed_context_and_progress(
            &proof,
            &executor.ctx.terms,
            Some(&datatypes),
            Some(&selectors),
            &signatures,
            &originals,
            &mut |_, _| false,
        )
        .is_err()
    );
    for omitted in 0..variables.len() {
        let roots: Vec<_> = originals
            .iter()
            .enumerate()
            .filter_map(|(i, &root)| (i != omitted).then_some(root))
            .collect();
        let source_set = roots.iter().copied().collect();
        let mut cx = PlanCx::new(&source_set, &roots, &rewrites, &entries, &[], true);
        assert!(
            PropagationChainPlanner {
                terms: &mut executor.ctx.terms
            }
            .plan_derive_clause(&mut cx, target)
            .is_none(),
            "retained sealed hints cannot replace missing original license {omitted}"
        );
    }
    if let Some(index) = opaque {
        let TermData::App(head, args) = executor.ctx.terms.get(originals[index]).clone() else {
            panic!("opaque row remains an authored UF application");
        };
        assert_eq!(args.len(), 1);
        let invented_length = executor.ctx.terms.mk_bitvec(65.into(), 64);
        let invented = executor
            .ctx
            .terms
            .mk_app(head, [invented_length], Sort::Bool);
        assert_ne!(invented, originals[index]);
        let source_set = originals.iter().copied().collect();
        let mut cx = PlanCx::new(&source_set, &originals, &rewrites, &entries, &[], true);
        assert!(
            PropagationChainPlanner {
                terms: &mut executor.ctx.terms
            }
            .plan_derive_clause(&mut cx, invented)
            .is_none(),
            "an opaque array-returned row has no authored constructor license"
        );
    }
    assert_eq!(executor.ctx.assertions, originals);
}

#[test]
fn parsed_vec_iter_arguments_replay_with_exact_aggregate_licenses() {
    // The preserved two-seam diagnostic used single-constructor products, whose
    // declared constants are eagerly elaborated to constructors. Second variants
    // keep these genuine aggregate Vars; replay_parsed asserts that precondition.
    // This is an entry regression, not a reproduction of a consumer failure.
    replay_parsed(
        "(set-logic ALL)
         (declare-datatype MCVec
           ((mkVec (vec_ptr (_ BitVec 64)) (vec_len (_ BitVec 64))
                   (vec_cap (_ BitVec 64))
                   (vec_data (Array (_ BitVec 64) (_ BitVec 8)))) (otherVec)))
         (declare-datatype MCVecIntoIter
           ((mkIter (iter_vec MCVec) (iter_pos (_ BitVec 64))) (otherIter)))
         (declare-const a (Array (_ BitVec 64) (_ BitVec 8)))
         (declare-const rows (Array (_ BitVec 64) MCVec))
         (declare-const k (_ BitVec 64))
         (declare-const v MCVec)
         (declare-const w MCVecIntoIter)
         (declare-fun keep (MCVec MCVecIntoIter) Bool)
         (declare-fun row_keep ((_ BitVec 64)) Bool)
         (assert (= v (mkVec #x0000000000000000 #x0000000000000041
                            #x0000000000000041 a)))
         (assert (= w (mkIter
           (mkVec #x0000000000000000 #x0000000000000041
                  #x0000000000000041 a) #x0000000000000020)))
         (assert (keep v w))
         (assert (row_keep (vec_len (select rows k))))",
        &["v", "w"],
        2,
        Some(3),
    );
}

#[test]
fn parsed_array_argument_replays_without_a_read_or_extensionality_theorem() {
    replay_parsed(
        "(set-logic ALL)
         (declare-const a (Array (_ BitVec 64) (_ BitVec 8)))
         (declare-fun keep_array ((Array (_ BitVec 64) (_ BitVec 8))) Bool)
         (assert (= a ((as const (Array (_ BitVec 64) (_ BitVec 8))) #x07)))
         (assert (keep_array a))",
        &["a"],
        1,
        None,
    );
}
