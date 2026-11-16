// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! An enumeration session must preserve complete models, not just SAT answers.

use super::super::super::propagation::index_builds;
use super::*;

#[path = "../../propagation/legacy_localsat.rs"]
#[expect(
    clippy::duplicate_mod,
    reason = "this frozen oracle instance binds projection-specific observational hooks"
)]
mod original;
mod resources;
mod tree;

// The frozen original solver's observational hooks do not alter its algorithm.
fn visited() {}
fn assigned(_: T, _: usize) {}

type Model = HashMap<T, bool>;
type Solver = fn(&[Clause], &Model, &mut u64, &EmissionProgress<'_>) -> Option<Option<Model>>;

fn enumerate_fresh(
    db: &mut Vec<Clause>,
    fixed: &Model,
    proj: &[T],
    budget: &mut u64,
    progress: &EmissionProgress<'_>,
    solve: Solver,
) -> Option<Vec<Model>> {
    let base = db.len();
    for &atom in proj {
        db.push(vec![(atom, true), (atom, false)]);
    }
    let mut models = Vec::new();
    while let Some(model) = solve(db, fixed, budget, progress)? {
        let block: Clause = proj
            .iter()
            .map(|atom| (*atom, !model.get(atom).copied().unwrap_or(false)))
            .collect();
        models.push(model);
        if proj.is_empty() {
            break;
        }
        db.push(block);
    }
    db.truncate(base);
    Some(models)
}

fn enumerate_reused(
    db: &mut Vec<Clause>,
    fixed: &Model,
    proj: &[T],
    budget: &mut u64,
    progress: &EmissionProgress<'_>,
) -> Option<Vec<Model>> {
    let mut solver = localsat::Projection::new(db, fixed, budget, progress)?;
    for &atom in proj {
        solver.append([(atom, true), (atom, false)].into_iter())?;
    }
    let mut models = Vec::new();
    while let Some(model) = solver.solve()? {
        if !proj.is_empty() {
            solver.append(
                proj.iter()
                    .map(|atom| (*atom, !model.get(atom).copied().unwrap_or(false))),
            )?;
        }
        models.push(model);
        if proj.is_empty() {
            break;
        }
    }
    Some(models)
}

fn compare(db: &[Clause], fixed: &Model, proj: &[T]) {
    let progress = EmissionProgress::default();
    let mut original_db = db.to_vec();
    let original = enumerate_fresh(
        &mut original_db,
        fixed,
        proj,
        &mut 1_000_000,
        &progress,
        original::solve,
    )
    .unwrap();
    let mut fresh_db = db.to_vec();
    let fresh = enumerate_fresh(
        &mut fresh_db,
        fixed,
        proj,
        &mut 1_000_000,
        &progress,
        localsat::solve,
    )
    .unwrap();
    let mut reused_db = db.to_vec();
    let reused = enumerate_reused(&mut reused_db, fixed, proj, &mut 1_000_000, &progress).unwrap();
    assert_eq!(
        reused, original,
        "original: db={db:?}, fixed={fixed:?}, proj={proj:?}"
    );
    assert_eq!(
        reused, fresh,
        "fresh: db={db:?}, fixed={fixed:?}, proj={proj:?}"
    );
    assert_eq!(original_db, db);
    assert_eq!(fresh_db, db);
    assert_eq!(reused_db, db);
    let expected: HashSet<_> = reused
        .iter()
        .map(|model| {
            proj.iter()
                .map(|atom| model.get(atom).copied().unwrap_or(false))
                .collect::<Vec<_>>()
        })
        .collect();
    let actual = Chain::project(&reused_db, fixed, proj, &mut 1_000_000, &progress);
    assert_eq!(actual, Some(expected));
    assert_eq!(reused_db, db);
}

#[test]
fn reused_index_matches_fresh_and_original_ordered_models_exhaustively() {
    let literals = [(1, true), (1, false), (2, true), (2, false)];
    let mut clauses = vec![vec![]];
    for literal in literals {
        clauses.push(vec![literal]);
        for other in literals {
            clauses.push(vec![literal, other]);
        }
    }
    for left in &clauses {
        for right in &clauses {
            let db = [left.clone(), right.clone()];
            for a in [None, Some(false), Some(true)] {
                for b in [None, Some(false), Some(true)] {
                    let fixed: Model = [(1, a), (2, b)]
                        .into_iter()
                        .filter_map(|(atom, v)| v.map(|v| (atom, v)))
                        .collect();
                    for proj in [&[][..], &[1][..], &[2][..], &[2, 1][..], &[1, 1][..]] {
                        compare(&db, &fixed, proj);
                    }
                }
            }
        }
    }
}

#[test]
fn sessions_do_not_retain_fixed_assignments_or_databases() {
    let free = Model::default();
    for fixed in [
        free,
        Model::from_iter([(1, false)]),
        Model::from_iter([(2, true)]),
    ] {
        for db in [vec![], vec![vec![(1, true), (2, true)]], vec![vec![]]] {
            compare(&db, &fixed, &[1, 2, 3]);
        }
    }
}

#[test]
fn enumeration_builds_once_not_once_per_model_and_final_unsat() {
    let fixed = Model::default();
    let progress = EmissionProgress::default();
    let mut db = vec![];
    let before = index_builds();
    let reused = enumerate_reused(&mut db, &fixed, &[1, 2, 3], &mut 1_000_000, &progress).unwrap();
    assert_eq!(reused.len(), 8);
    assert_eq!(index_builds() - before, 1);
    let before = index_builds();
    let fresh = enumerate_fresh(
        &mut db,
        &fixed,
        &[1, 2, 3],
        &mut 1_000_000,
        &progress,
        localsat::solve,
    )
    .unwrap();
    assert_eq!(fresh, reused);
    assert_eq!(index_builds() - before, 9);
    assert_eq!(db.as_slice(), &[] as &[Clause]);
}

#[test]
fn projection_keeps_invariant_steps_and_proof_bytes() {
    let mut old = new_proof();
    let mut new = new_proof();
    let atoms: Vec<_> = (0..3)
        .map(|i| old.t.var(&format!("s{i}"), Sort::Bool))
        .collect();
    for (i, &atom) in atoms.iter().enumerate() {
        assert_eq!(new.t.var(&format!("s{i}"), Sort::Bool), atom);
    }
    let db = vec![
        vec![(atoms[0], true), (atoms[1], true)],
        vec![(atoms[1], false), (atoms[2], true)],
        vec![(atoms[0], true), (atoms[0], false), (atoms[0], true)],
    ];
    let models = enumerate_fresh(
        &mut db.clone(),
        &Model::default(),
        &atoms,
        &mut 1_000_000,
        &EmissionProgress::default(),
        original::solve,
    )
    .unwrap();
    let expected: HashSet<_> = models
        .iter()
        .map(|model| {
            atoms
                .iter()
                .map(|atom| model.get(atom).copied().unwrap_or(false))
                .collect::<Vec<_>>()
        })
        .collect();
    let actual = Chain::project(
        &db,
        &Model::default(),
        &atoms,
        &mut 1_000_000,
        &EmissionProgress::default(),
    )
    .unwrap();
    let (old_atoms, old_premises) = premise_fixture(&mut old, 3, &expected);
    let (new_atoms, new_premises) = premise_fixture(&mut new, 3, &actual);
    let old_steps = invariant(&mut old, &old_atoms, &expected, &old_premises, &old_atoms).unwrap();
    let new_steps = invariant(&mut new, &new_atoms, &actual, &new_premises, &new_atoms).unwrap();
    assert_eq!(new_steps, old_steps);
    assert_eq!(new.out, old.out);
}
