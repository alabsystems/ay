// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
use super::*;
use ay_core::original_query::FiniteAdmissionGrant;
use ay_sat::{Literal, SatResult, Solver, Variable};
use std::collections::BTreeSet;
use std::sync::{
    atomic::{AtomicBool, Ordering},
    Arc,
};

fn owner(work: u64, bytes: usize) -> CountedAdmission {
    CountedAdmission::new(
        FiniteAdmissionGrant::new(work, bytes),
        None,
        Arc::new(|| false),
    )
    .unwrap()
}
fn ample() -> CountedAdmission {
    owner(100_000_000, 1 << 30)
}
fn app(terms: &mut TermStore, name: &str, args: &[TermId], sort: Sort) -> TermId {
    terms.mk_app(Symbol::named(name), args.to_vec(), sort)
}

fn indicator_family(n: usize, k: usize) -> (TermStore, TermId, Vec<TermId>) {
    let mut terms = TermStore::new();
    let zero = terms.mk_int(0.into());
    let one = terms.mk_int(1.into());
    let leaves: Vec<_> = (0..n)
        .map(|i| terms.mk_var(&format!("edge{i}"), Sort::Bool))
        .collect();
    let values: Vec<_> = leaves.iter().map(|&b| terms.mk_ite(b, one, zero)).collect();
    let sum = app(&mut terms, "+", &values, Sort::Int);
    let threshold = terms.mk_int(BigInt::from(k));
    let root = app(&mut terms, ">=", &[sum, threshold], Sort::Bool);
    (terms, root, leaves)
}

// SAT is an independent TEST oracle here. This validates compiler semantics
// and persistent-search feasibility, not a counted native SMT endpoint. The
// production endpoint still owes model/publication and source-proof authority.
fn enumerate_circuit(
    compiled: &Compiled,
    source_leaves: &[TermId],
) -> (Vec<(u64, u64)>, Vec<(u64, u64)>) {
    let grant = ample();
    let mut encoder = ay_bv::CountedBvEncoder::new(&compiled.terms, &grant).unwrap();
    encoder.assert_roots(&compiled.roots).unwrap();
    encoder.encode_terms(&compiled.projection).unwrap();
    encoder
        .encode_terms(
            &compiled
                .leaves
                .iter()
                .map(|&(_, translated)| translated)
                .collect::<Vec<_>>(),
        )
        .unwrap();
    let projection: Vec<_> = compiled
        .projection
        .iter()
        .map(|&id| encoder.literal(id).unwrap())
        .collect();
    let leaves: Vec<_> = source_leaves
        .iter()
        .map(|source| {
            let &(_, translated) = compiled.leaves.iter().find(|(id, _)| id == source).unwrap();
            encoder.literal(translated).unwrap()
        })
        .collect();
    let mut solver = Solver::new(encoder.num_vars().unwrap() as usize);
    for clause in encoder.clauses().unwrap() {
        solver.add_clause(
            clause
                .literals()
                .iter()
                .copied()
                .map(Literal::from_dimacs)
                .collect(),
        );
    }
    for &literal in projection.iter().chain(&leaves) {
        solver.freeze(Variable::new(literal.unsigned_abs() - 1));
    }
    encoder.finish().unwrap();
    let mut result = Vec::new();
    let mut counts = Vec::new();
    let mut previous = (0, 0);
    loop {
        match solver.solve().into_inner() {
            SatResult::Sat(model) => {
                let value =
                    |literal: i32| model[literal.unsigned_abs() as usize - 1] == (literal > 0);
                let mask = |literals: &[i32]| {
                    literals
                        .iter()
                        .enumerate()
                        .fold(0u64, |mask, (i, &lit)| mask | (u64::from(value(lit)) << i))
                };
                result.push((mask(&projection), mask(&leaves)));
                let current = (
                    solver.total_num_propagations(),
                    solver.total_num_conflicts(),
                );
                counts.push((current.0 - previous.0, current.1 - previous.1));
                previous = current;
                solver.add_clause(
                    projection
                        .iter()
                        .map(|&lit| Literal::from_dimacs(if value(lit) { -lit } else { lit }))
                        .collect(),
                );
            }
            SatResult::Unsat(_) => break,
            other => panic!("the finite circuit oracle stopped: {other:?}"),
        }
    }
    (result, counts)
}

#[test]
fn original_ty_indicator_sum_has_exactly_848_models_in_one_sat_session() {
    let (source, root, leaves) = indicator_family(10, 4);
    let grant = ample();
    let compiled = compile(&source, &[root], &leaves, &grant).unwrap();
    let (models, counts) = enumerate_circuit(&compiled, &leaves);
    let actual: BTreeSet<_> = models
        .iter()
        .map(|&(projection, model)| {
            assert_eq!(projection, model);
            assert!(model.count_ones() >= 4, "original indicator sum is false");
            projection
        })
        .collect();
    let expected: BTreeSet<_> = (0u64..1024).filter(|mask| mask.count_ones() >= 4).collect();
    assert_eq!(models.len(), 848);
    assert_eq!(actual, expected);
    let sum = |start: usize| {
        counts[start..start + 50]
            .iter()
            .fold((0, 0), |a, b| (a.0 + b.0, a.1 + b.1))
    };
    let early = sum(0);
    let late = sum(750);
    eprintln!("finite_bool candidate counts models1..50={early:?},751..800={late:?}; work_version={WORK_VERSION}");
    assert!(
        late.0 <= early.0 * 4,
        "persistent per-model propagations: {early:?} -> {late:?}"
    );
}

#[test]
fn partial_projection_deduplicates_extensions_and_registers_unused_booleans() {
    let (source, root, leaves) = indicator_family(10, 4);
    let compiled = compile(&source, &[root], &leaves[..3], &ample()).unwrap();
    let (models, _) = enumerate_circuit(&compiled, &leaves);
    assert_eq!(models.len(), 8);
    assert!(models.iter().all(|(_, mask)| mask.count_ones() >= 4));
    assert_eq!(
        models.iter().map(|row| row.0).collect::<BTreeSet<_>>(),
        (0..8).collect()
    );

    let mut source = TermStore::new();
    let p = source.mk_var("p", Sort::Bool);
    let unused = source.mk_var("unused", Sort::Bool);
    let compiled = compile(&source, &[p], &[p, unused], &ample()).unwrap();
    let (models, _) = enumerate_circuit(&compiled, &[p, unused]);
    assert_eq!(
        models.iter().map(|row| row.0).collect::<BTreeSet<_>>(),
        [1, 3].into_iter().collect()
    );
}

#[test]
fn signed_arbitrary_precision_arithmetic_keeps_the_original_boolean_twin() {
    let mut source = TermStore::new();
    let p = source.mk_var("p", Sort::Bool);
    let huge = BigInt::one() << 140usize;
    let positive = source.mk_int(huge.clone());
    let negative = source.mk_int(-huge);
    let selected = source.mk_ite(p, positive, negative);
    let three = source.mk_int(3.into());
    let product = app(&mut source, "*", &[selected, three], Sort::Int);
    let zero = source.mk_int(0.into());
    let root = app(&mut source, ">=", &[product, zero], Sort::Bool);
    let compiled = compile(&source, &[root], &[p], &ample()).unwrap();
    assert!(compiled.signed_width >= 143);
    let (models, _) = enumerate_circuit(&compiled, &[p]);
    assert_eq!(models, vec![(1, 1)]);
}

#[test]
fn unsupported_int_and_dead_arms_refuse_without_changing_the_source() {
    let mut source = TermStore::new();
    let x = source.mk_var("unbounded", Sort::Int);
    let zero = source.mk_int(0.into());
    let eq = app(&mut source, "=", &[x, zero], Sort::Bool);
    let false_term = source.mk_bool(false);
    let root = app(&mut source, "and", &[false_term, eq], Sort::Bool);
    let stamp = source.snapshot_stamp();
    assert!(matches!(
        compile(&source, &[root], &[], &ample()),
        Err(Error::Unsupported)
    ));
    assert_eq!(source.snapshot_stamp(), stamp);
}

#[test]
fn original_binding_is_ordered_and_rejects_mutation_or_another_store() {
    let (mut source, root, leaves) = indicator_family(3, 1);
    let roots = [root, leaves[0]];
    let compiled = compile(&source, &roots, &leaves, &ample()).unwrap();
    assert!(compiled.matches_source(&source, &roots));
    assert!(!compiled.matches_source(&source, &[leaves[0], root]));
    assert!(!compiled.matches_source(&source.clone(), &roots));
    source.mk_var("later", Sort::Bool);
    assert!(!compiled.matches_source(&source, &roots));
}

#[test]
fn preparation_spends_the_original_work_storage_and_cancellation_owner() {
    let (source, root, leaves) = indicator_family(3, 1);
    let stamp = source.snapshot_stamp();
    for grant in [owner(0, 1 << 20), owner(100_000, 0), owner(100, 1 << 20)] {
        assert!(matches!(
            compile(&source, &[root], &leaves, &grant),
            Err(Error::Stopped(_))
        ));
        assert!(grant.check().is_err());
        assert_eq!(source.snapshot_stamp(), stamp);
    }
    let stopped = Arc::new(AtomicBool::new(false));
    let observed = stopped.clone();
    let grant = CountedAdmission::new(
        FiniteAdmissionGrant::new(100_000, 1 << 20),
        None,
        Arc::new(move || observed.load(Ordering::SeqCst)),
    )
    .unwrap();
    stopped.store(true, Ordering::SeqCst);
    assert!(matches!(
        compile(&source, &[root], &leaves, &grant),
        Err(Error::Stopped(_))
    ));
    stopped.store(false, Ordering::SeqCst);
    assert!(
        grant.check().is_err(),
        "a later preparation cannot renew the original stopped owner"
    );
}
