// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::preprocess::PropagatedRewriteRecord;

struct Fixture {
    executor: Executor,
    originals: [TermId; 2],
    record: PropagatedRewriteRecord,
    entries: Vec<PropagatedEntrySource>,
    guard: TermId,
}

impl Fixture {
    fn recorded() -> Self {
        let mut executor = Executor::new();
        let terms = &mut executor.ctx.terms;
        let length = terms.mk_var("length", Sort::bitvec(64));
        let fill = terms.mk_var("fill", Sort::bitvec(8));
        let x = terms.mk_var("x", Sort::bitvec(8));
        let index = terms.mk_var("__gpc1", Sort::bitvec(64));
        let array = terms.mk_var("a", Sort::array(Sort::bitvec(64), Sort::bitvec(8)));
        let function = terms.mk_app(Symbol::named("f"), [terms.true_term(), x], Sort::bitvec(8));
        let sixty_five = terms.mk_bitvec(65.into(), 64);
        let fill_source = terms.mk_app(Symbol::named("="), [fill, function], Sort::Bool);
        let length_source = terms.mk_app(Symbol::named("="), [length, sixty_five], Sort::Bool);
        let definitions = terms.mk_app(
            Symbol::named("and"),
            [fill_source, length_source],
            Sort::Bool,
        );
        let old_guard = terms.mk_app(Symbol::named("bvult"), [index, length], Sort::Bool);
        let thirty_two = terms.mk_bitvec(32.into(), 64);
        let lower = terms.mk_app(Symbol::named("bvule"), [thirty_two, index], Sort::Bool);
        let read = terms.mk_app(Symbol::named("select"), [array, index], Sort::bitvec(8));
        let old_equality = terms.mk_app(Symbol::named("="), [fill, read], Sort::Bool);
        let old_disagreement = terms.mk_not_raw(old_equality);
        let branch = terms.mk_app(
            Symbol::named("and"),
            [old_guard, lower, old_disagreement],
            Sort::Bool,
        );
        let zero = terms.mk_bitvec(0.into(), 64);
        let empty = terms.mk_app(Symbol::named("="), [length, zero], Sort::Bool);
        let before = terms.mk_app(Symbol::named("or"), [branch, empty], Sort::Bool);
        let originals = [definitions, before];
        let inputs = vec![fill_source, length_source, before];
        let propagation = Arc::new(Mutex::new(PropagateValues::new()));
        let mut pass = RecordedVariableSubstitution::new(
            Arc::new(Mutex::new(VariableSubstitution::new())),
            Arc::clone(&propagation),
            Box::new(|_, _| true),
        );
        let mut working = inputs.clone();
        assert!(pass.apply(terms, &mut working));
        // Compare against a fresh actual delegate on the same authored input.
        // No second PropagateValues pass manufactures the recorded endpoint.
        let mut direct = inputs;
        assert!(VariableSubstitution::new().apply(terms, &mut direct));
        assert_eq!(working, direct);
        let records = propagation
            .lock()
            .unwrap()
            .take_propagation_records()
            .unwrap();
        let record = records
            .rewrites
            .iter()
            .find(|record| record.before == before)
            .expect("the actual wrapper retains the A4 rewrite")
            .clone();
        assert_eq!(record.after, working[2]);
        let guard = terms.mk_bvult(index, sixty_five);
        let equality = terms.mk_eq_coerce_no_ite_expand(function, read);
        let disagreement = terms.mk_not(equality);
        let positional = vec![guard, lower, disagreement];
        assert_eq!(record.after, terms.mk_and(positional.clone()));
        let TermData::App(head, arguments) = terms.get(record.after) else {
            panic!("actual substitution must collapse A4 to canonical AND");
        };
        assert_eq!(head.name(), "and");
        assert_ne!(
            arguments, &positional,
            "exercise actual canonical reordering"
        );
        assert_eq!(arguments.len(), 3);
        assert!(!records.rewrites.iter().any(|record| record.after == guard));
        assert_eq!(records.entries.len(), 2);
        for (variable, value, source) in [
            (fill, function, fill_source),
            (length, sixty_five, length_source),
        ] {
            assert!(records.entries.iter().any(|entry| {
                entry.expr == variable
                    && entry.value == value
                    && entry.source_assertion == source
                    && entry.stamp <= record.stamp
            }));
        }
        Self {
            executor,
            originals,
            record,
            entries: records.entries,
            guard,
        }
    }
}

#[test]
fn actual_recorded_boolean_parent_seals_and_strictly_projects_its_guard() {
    let mut fixture = Fixture::recorded();
    let mut entries = HashMap::default();
    for entry in &fixture.entries {
        let (key, value) = CheckedPropagationEntry::seal(&fixture.executor, entry)
            .expect("actual scalar licensing entry seals")
            .into_current(&fixture.executor)
            .unwrap();
        entries.insert(key, value);
    }
    assert_eq!(entries.len(), 2);
    let (after, before) = CheckedPropagationDerivation::seal(
        &mut fixture.executor,
        &fixture.record,
        &fixture.entries,
    )
    .expect("the unchanged sealer accepts the ACTUAL wrapper record")
    .into_current(&fixture.executor)
    .unwrap();
    assert_eq!(after, fixture.record.after);
    assert_eq!(before, (fixture.record.before, fixture.record.stamp));
    let rewrites = HashMap::from_iter([(after, before)]);
    assert!(!rewrites.contains_key(&fixture.guard));
    let source_set = fixture.originals.into_iter().collect();
    for target in [after, fixture.guard] {
        let mut cx = PlanCx::new(
            &source_set,
            &fixture.originals,
            &rewrites,
            &entries,
            &[],
            true,
        );
        let conclusion = PropagationChainPlanner {
            terms: &mut fixture.executor.ctx.terms,
        }
        .plan_derive_clause(&mut cx, target)
        .expect("checked recorded parent, then checked conjunct projection");
        assert!(ay_proof::validate_reachable_assumes_in_problem_scope(
            &cx.chain,
            &fixture.originals
        )
        .is_ok());
        let checked = ay_proof::authenticate_premise_clauses_strict_with_context_and_progress(
            &cx.chain,
            &fixture.executor.ctx.terms,
            None,
            None,
            &fixture.originals,
            &mut |_, _| true,
        )
        .expect("all emitted steps pass the unchanged strict checker");
        assert_eq!(checked.clause(conclusion), Some([target].as_slice()));
        assert!(!cx.chain.steps.iter().any(
            |step| matches!(step, ay_proof::ProofStep::Assume(term) if *term == after || *term == target)
        ));
    }
    // Sealed metadata remains a hint: removing the authored definition root
    // cannot authorize either the canonical parent or its projected guard.
    let unlicensed_roots = [fixture.record.before];
    let unlicensed_set = unlicensed_roots.into_iter().collect();
    for target in [after, fixture.guard] {
        let mut cx = PlanCx::new(
            &unlicensed_set,
            &unlicensed_roots,
            &rewrites,
            &entries,
            &[],
            true,
        );
        assert!(PropagationChainPlanner {
            terms: &mut fixture.executor.ctx.terms,
        }
        .plan_derive_clause(&mut cx, target)
        .is_none());
    }
}

#[test]
fn actual_recorded_boolean_seal_rejects_altered_after_late_and_missing_licenses() {
    let mut fixture = Fixture::recorded();
    let mut altered = fixture.record.clone();
    altered.after = fixture.guard;
    assert!(
        CheckedPropagationDerivation::seal(&mut fixture.executor, &altered, &fixture.entries,)
            .is_none()
    );
    for index in 0..fixture.entries.len() {
        let mut late = fixture.entries.clone();
        late[index].stamp = fixture.record.stamp.checked_add(1).unwrap();
        assert!(
            CheckedPropagationDerivation::seal(&mut fixture.executor, &fixture.record, &late,)
                .is_none()
        );
        let mut missing = fixture.entries.clone();
        missing.remove(index);
        assert!(CheckedPropagationDerivation::seal(
            &mut fixture.executor,
            &fixture.record,
            &missing,
        )
        .is_none());
    }
    assert!(CheckedPropagationDerivation::seal(
        &mut fixture.executor,
        &fixture.record,
        &fixture.entries,
    )
    .is_some());
}
