// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use ay_core::ProofStep;

pub(super) mod fixtures;
use fixtures::{app, Fixture};

#[test]
fn discovers_wide_store_definitions_and_exact_activated_array_and_scalar_aliases() {
    for width in [2, 129] {
        let mut fixture = Fixture::new(width);
        let original = fixture.roots.clone();
        let batch = fixture.discover().expect("source-derived complete batch");
        assert_eq!(batch.original_roots(), original);
        assert_eq!(
            fixture.roots, original,
            "never substitute or discard branches"
        );
        assert_eq!(batch.definitions().len(), 1);
        let definition = &batch.definitions()[0];
        assert_eq!(definition.variable(), fixture.variable);
        assert!(fixture.authenticate(
            definition.proof().0,
            definition.proof().1,
            definition.definition()
        ));
        assert_eq!(batch.activated_units().len(), 3);
        for target in [fixture.aliases[0], fixture.aliases[1], fixture.cover] {
            let unit = batch
                .activated_units()
                .iter()
                .find(|unit| unit.unit() == target)
                .unwrap();
            assert!(fixture.authenticate(unit.proof().0, unit.proof().1, target));
        }
        let TermData::App(_, args) = fixture.terms.get(definition.replacement()) else {
            panic!("whole store replacement")
        };
        assert!(
            matches!(fixture.terms.get(args[2]), TermData::Ite(g, _, _) if *g == fixture.guards[0])
        );
    }
}

#[test]
fn actual_outer_conjunction_and_duplicate_roots_do_not_invent_source_facts() {
    let mut fixture = Fixture::new(129);
    let source = fixture.roots[2];
    let inner = app(&mut fixture.terms, "and", &[fixture.roots[0], source]);
    let outer = app(
        &mut fixture.terms,
        "and",
        &[inner, fixture.roots[1], fixture.activation],
    );
    fixture.roots = vec![outer, source];
    let batch = fixture
        .discover()
        .expect("checker admits exact authored AND conjuncts");
    assert_eq!(batch.original_roots(), fixture.roots);
    assert_eq!(
        batch.definitions().len(),
        1,
        "one deterministic definition per variable"
    );
    assert_eq!(
        batch.activated_units().len(),
        6,
        "duplicate originals remain exact occurrences"
    );
    for unit in batch.activated_units() {
        assert!(fixture.authenticate(unit.proof().0, unit.proof().1, unit.unit()));
    }
}

#[test]
fn common_guards_do_not_conflate_distinct_array_owners_or_stale_arena_cases() {
    let mut fixture = Fixture::new(129);
    let sort = fixture.terms.sort(fixture.variable).clone();
    let second = fixture
        .terms
        .mk_var("independent second owner", sort.clone());
    let archived = fixture.terms.mk_var("never asserted owner", sort);
    for owner in [second, archived] {
        for position in 0..2 {
            let equality = raw_eq(&mut fixture.terms, owner, fixture.stores[position]);
            let not_guard = fixture.terms.mk_not_raw(fixture.guards[position]);
            let source = app(&mut fixture.terms, "or", &[not_guard, equality]);
            if owner == second {
                fixture.roots.push(source);
            }
        }
    }
    let batch = fixture.discover().unwrap();
    assert_eq!(batch.definitions().len(), 2);
    assert_eq!(batch.definitions()[0].variable(), fixture.variable);
    assert_eq!(batch.definitions()[1].variable(), second);
    for definition in batch.definitions() {
        assert!(fixture.authenticate(
            definition.proof().0,
            definition.proof().1,
            definition.definition()
        ));
    }
    assert_eq!(batch.original_roots(), fixture.roots);
}

#[test]
fn only_original_positive_activation_enables_guarded_covers() {
    for negative in [false, true] {
        let mut fixture = Fixture::new(2);
        fixture.roots.pop();
        if negative {
            let not_active = fixture.terms.mk_not_raw(fixture.activation);
            fixture.roots.push(not_active);
        }
        let batch = fixture.discover().unwrap();
        assert!(batch.definitions().is_empty());
        assert!(batch.activated_units().is_empty());
        fixture.roots.push(fixture.cover);
        let batch = fixture
            .discover()
            .expect("direct source cover needs no activation");
        assert_eq!(batch.definitions().len(), 1);
        assert!(batch.activated_units().is_empty());
    }
}

#[test]
fn boolean_alias_units_do_not_recursively_activate_unasserted_guards() {
    let mut fixture = Fixture::new(2);
    fixture.roots.pop();
    let actual = fixture.terms.mk_var("actually asserted", Sort::Bool);
    let equality = raw_eq(&mut fixture.terms, actual, fixture.activation);
    let not_actual = fixture.terms.mk_not_raw(actual);
    let source = app(&mut fixture.terms, "or", &[not_actual, equality]);
    fixture.roots.extend([actual, source]);
    let batch = fixture.discover().unwrap();
    assert!(
        batch.definitions().is_empty(),
        "only original positive variables activate discovery"
    );
    assert_eq!(batch.activated_units().len(), 1);
    assert_eq!(batch.activated_units()[0].unit(), equality);
    assert!(fixture.authenticate(
        batch.activated_units()[0].proof().0,
        batch.activated_units()[0].proof().1,
        equality
    ));
}

#[test]
fn disjunctive_aliases_and_branch_covers_are_not_projected_as_units() {
    let mut fixture = Fixture::new(2);
    let decoy = fixture.terms.mk_var("alternative", Sort::Bool);
    let hidden = app(&mut fixture.terms, "or", &[decoy, fixture.cover]);
    let hidden_alias = app(&mut fixture.terms, "or", &[decoy, fixture.aliases[0]]);
    let body = app(&mut fixture.terms, "and", &[hidden, hidden_alias]);
    let not_activation = fixture.terms.mk_not_raw(fixture.activation);
    fixture.roots[2] = app(&mut fixture.terms, "or", &[not_activation, body]);
    let batch = fixture.discover().unwrap();
    assert!(batch.definitions().is_empty());
    assert!(batch.activated_units().is_empty());
}

#[test]
fn distinct_common_keys_do_not_match_and_malformed_matched_store_refuses_all() {
    for malformed in [false, true] {
        let mut fixture = Fixture::new(2);
        let TermData::App(_, args) = fixture.terms.get(fixture.stores[1]) else {
            panic!("store")
        };
        let mut args = args.clone();
        let sort = fixture.terms.sort(fixture.stores[1]).clone();
        if malformed {
            args[2] = fixture.terms.true_term();
        } else {
            args[1] = fixture.terms.true_term();
        }
        let store = fixture.terms.mk_app(Symbol::named("store"), args, sort);
        let equality = raw_eq(&mut fixture.terms, fixture.variable, store);
        let not_guard = fixture.terms.mk_not_raw(fixture.guards[1]);
        fixture.roots[1] = app(&mut fixture.terms, "or", &[not_guard, equality]);
        let result = fixture.discover();
        if malformed {
            assert!(
                result.is_none(),
                "no partial activated-unit batch after failed derivation"
            );
        } else {
            let batch = result.unwrap();
            assert!(batch.definitions().is_empty());
            assert_eq!(batch.activated_units().len(), 3);
        }
    }
}

#[test]
fn activated_unit_proof_and_full_original_source_mutations_refuse() {
    let mut fixture = Fixture::new(129);
    let batch = fixture.discover().unwrap();
    let unit = &batch.activated_units()[0];
    let (proof, conclusion) = unit.proof();
    let mut forged = proof.clone();
    let ProofStep::Step { clause, .. } = &mut forged.steps[conclusion.0 as usize] else {
        panic!("unit resolution")
    };
    clause[0] = fixture.terms.false_term();
    assert!(!fixture.authenticate(&forged, conclusion, unit.unit()));
    fixture.roots.pop();
    assert!(!fixture.authenticate(proof, conclusion, unit.unit()));
}

#[test]
fn cumulative_discovery_proof_and_publication_limits_are_exact_and_fail_closed() {
    let mut fixture = Fixture::new(2);
    let mut charges = Vec::new();
    assert!(
        discover(&mut fixture.terms, &fixture.roots, &mut |work, bytes| {
            charges.push((work, bytes));
            true
        })
        .is_some()
    );
    for stop in [0, 1, charges.len() / 2, charges.len() - 1] {
        let mut fixture = Fixture::new(2);
        let mut calls = 0;
        assert!(discover(&mut fixture.terms, &fixture.roots, &mut |_, _| {
            calls += 1;
            calls <= stop
        })
        .is_none());
        assert!(
            fixture.discover().is_some(),
            "fresh retry is independent of refused batch"
        );
    }
    let (work, bytes) = charges
        .iter()
        .fold((0, 0), |(w, b), &(dw, db)| (w + dw, b + db));
    for (mut work, mut bytes, success) in [
        (work, bytes, true),
        (work - 1, bytes, false),
        (work, bytes - 1, false),
    ] {
        let mut fixture = Fixture::new(2);
        let result = discover(&mut fixture.terms, &fixture.roots, &mut |dw, db| {
            let (Some(w), Some(b)) = (work.checked_sub(dw), bytes.checked_sub(db)) else {
                return false;
            };
            (work, bytes) = (w, b);
            true
        });
        assert_eq!(result.is_some(), success);
    }
}
