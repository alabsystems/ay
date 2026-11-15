// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn every_small_projection_keeps_exact_invariant_steps_and_proof_bytes() {
    for k in 1..=3 {
        for mask in 0..1usize << (1usize << k) {
            let mut old = new_proof();
            let mut new = new_proof();
            let atoms: Vec<_> = (0..k)
                .map(|j| old.t.var(&format!("s{j}"), Sort::Bool))
                .collect();
            for (j, &atom) in atoms.iter().enumerate() {
                assert_eq!(new.t.var(&format!("s{j}"), Sort::Bool), atom);
            }
            let db: Vec<Clause> = (0..1usize << k)
                .filter(|bits| (mask >> bits) & 1 == 0)
                .map(|bits| {
                    atoms
                        .iter()
                        .enumerate()
                        .map(|(j, &a)| (a, bits & (1 << j) == 0))
                        .collect()
                })
                .collect();
            let models = enumerate_fresh(
                &mut db.clone(),
                &Model::default(),
                &atoms,
                &mut 1_000_000,
                &EmissionProgress::default(),
                original::solve,
            )
            .unwrap();
            let expected: HashSet<Vec<bool>> = models
                .iter()
                .map(|model| {
                    atoms
                        .iter()
                        .map(|a| model.get(a).copied().unwrap_or(false))
                        .collect()
                })
                .collect();
            let actual = Chain::project(
                &mut db.clone(),
                &Model::default(),
                &atoms,
                &mut 1_000_000,
                &EmissionProgress::default(),
            )
            .unwrap();
            assert_eq!(actual, expected, "k={k}, mask={mask}");
            let (old_atoms, old_premises) = premise_fixture(&mut old, k, &expected);
            let (new_atoms, new_premises) = premise_fixture(&mut new, k, &actual);
            let old_steps =
                invariant(&mut old, &old_atoms, &expected, &old_premises, &old_atoms).unwrap();
            let new_steps =
                invariant(&mut new, &new_atoms, &actual, &new_premises, &new_atoms).unwrap();
            assert_eq!(new_steps, old_steps, "k={k}, mask={mask}");
            assert_eq!(new.out, old.out, "k={k}, mask={mask}");
            assert_eq!(
                new.budget, old.budget,
                "actual CDCL proof derivation is unchanged"
            );
        }
    }
}

#[test]
fn the_original_state_bound_is_enforced_before_enumeration() {
    let owner = EmissionProgress::default();
    let atoms: Vec<T> = (1..=MAX_STATE as T).collect();
    let fixed = atoms.iter().map(|&a| (a, true)).collect();
    assert_eq!(
        Chain::project(&mut vec![], &fixed, &atoms, &mut 100_000, &owner),
        Some(HashSet::from_iter([vec![true; MAX_STATE]]))
    );
    let oversized = vec![1; MAX_STATE + 1];
    assert_eq!(
        Chain::project(&mut vec![], &fixed, &oversized, &mut 100_000, &owner),
        None
    );
}
