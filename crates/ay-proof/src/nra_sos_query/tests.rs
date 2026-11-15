// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use ay_core::{NraSosOrigin, NraSosRational, NraSosTerm, Sort, Symbol, TermData};
use num_rational::BigRational;

mod progress;

fn rat(value: i64) -> NraSosRational {
    NraSosRational {
        numerator: value.into(),
        denominator: 1.into(),
    }
}

fn factor(position: u32) -> NraSosTerm {
    NraSosTerm {
        origin: NraSosOrigin::ClauseLiteral { position },
        multiplier: rat(1),
    }
}

fn real(terms: &mut TermStore, value: i64) -> TermId {
    terms.mk_rational(BigRational::from_integer(value.into()))
}

struct Fixture {
    terms: TermStore,
    roots: Vec<TermId>,
    candidate: ProofStep,
}

impl Fixture {
    fn linear() -> Self {
        let mut terms = TermStore::new();
        let x = terms.mk_var("query_x", Sort::Real);
        let zero = real(&mut terms, 0);
        let one = real(&mut terms, 1);
        let lower = terms.mk_ge(x, one);
        let upper = terms.mk_le(x, zero);
        let roots = vec![lower, upper];
        let clause = roots.iter().map(|&root| terms.mk_not_raw(root)).collect();
        let certificate = NraSosCertificate {
            basis: vec![vec![]],
            gram: vec![vec![rat(0)]],
            terms: vec![factor(0), factor(1)],
            rhs: rat(-1),
        };
        Self {
            terms,
            roots,
            candidate: ProofStep::NraSos {
                clause,
                certificate,
            },
        }
    }

    fn check(&self, split: usize) -> CheckResult<CheckedNraSosQuery> {
        check_nra_sos_query_with_progress(
            &self.terms,
            &self.roots[..split],
            &self.roots[split..],
            &self.candidate,
            &mut |_, _| true,
        )
    }

    fn payload(&mut self) -> (&mut Vec<TermId>, &mut NraSosCertificate) {
        let ProofStep::NraSos {
            clause,
            certificate,
        } = &mut self.candidate
        else {
            panic!("fixture always has an SOS step")
        };
        (clause, certificate)
    }

    fn replace_entries(&mut self, entries: Vec<(TermData, Sort)>) {
        let (yes, no) = self.terms.boolean_constant_ids();
        self.terms = TermStore::from_entries(entries, yes, no, self.terms.var_counter());
    }
}

#[test]
fn checks_all_assertion_assumption_partitions_without_mutating_source() {
    let fixture = Fixture::linear();
    let stamp = fixture.terms.snapshot_stamp();
    let entries = fixture.terms.entries_snapshot();
    for split in 0..=fixture.roots.len() {
        let checked = fixture.check(split).expect("exact linear refutation");
        assert!(checked
            .is_current_for_with_progress(
                &fixture.terms,
                &fixture.roots[..split],
                &fixture.roots[split..],
                &mut |_, _| true,
            )
            .unwrap());
        let other = (split + 1) % (fixture.roots.len() + 1);
        assert!(!checked
            .is_current_for_with_progress(
                &fixture.terms,
                &fixture.roots[..other],
                &fixture.roots[other..],
                &mut |_, _| true,
            )
            .unwrap());
    }
    assert_eq!(fixture.terms.snapshot_stamp(), stamp);
    assert_eq!(fixture.terms.entries_snapshot(), entries);
}

#[test]
fn preserves_constant_and_duplicate_factor_positions() {
    let mut fixture = Fixture::linear();
    let one = real(&mut fixture.terms, 1);
    let tautology = fixture
        .terms
        .mk_app(Symbol::named("="), [one, one], Sort::Bool);
    fixture.roots.insert(0, tautology);
    fixture.roots.push(fixture.roots[1]);
    let clause = fixture
        .roots
        .iter()
        .map(|&root| fixture.terms.mk_not_raw(root))
        .collect();
    let (slots, certificate) = fixture.payload();
    *slots = clause;
    certificate.terms = vec![factor(1), factor(2)];
    fixture
        .check(2)
        .expect("all four source positions retained");
    fixture.payload().1.terms[0].origin = NraSosOrigin::ClauseLiteral { position: 0 };
    assert!(matches!(
        fixture.check(2),
        Err(NraSosQueryCheckError::Kernel(_))
    ));
}

#[test]
fn rejects_reordered_roots_and_missing_duplicate_slots() {
    let mut fixture = Fixture::linear();
    fixture.roots.swap(0, 1);
    assert!(matches!(
        fixture.check(1),
        Err(NraSosQueryCheckError::SourceMismatch { position: 0 })
    ));
    fixture.roots.swap(0, 1);
    fixture.roots.push(fixture.roots[0]);
    assert!(matches!(
        fixture.check(2),
        Err(NraSosQueryCheckError::SourceArity)
    ));
}

#[test]
fn accepts_raw_double_negation_but_rejects_simplified_clause_polarity() {
    let mut fixture = Fixture::linear();
    let x = fixture.terms.mk_var("query_x", Sort::Real);
    let one = real(&mut fixture.terms, 1);
    let below = fixture.terms.mk_lt(x, one);
    let source = fixture.terms.mk_not_raw(below);
    fixture.roots[0] = source;
    let complement = fixture.terms.mk_not_raw(source);
    fixture.payload().0[0] = complement;
    fixture
        .check(1)
        .expect("not(not(x<1)) clause retains raw source slot");
    fixture.payload().0[0] = below;
    assert!(matches!(
        fixture.check(1),
        Err(NraSosQueryCheckError::SourceMismatch { position: 0 })
    ));
}

#[test]
fn rejects_a_bound_but_satisfiable_source() {
    let mut fixture = Fixture::linear();
    let x = fixture.terms.mk_var("query_x", Sort::Real);
    let minus_one = real(&mut fixture.terms, -1);
    let lower = fixture.terms.mk_ge(x, minus_one);
    fixture.roots[0] = lower;
    let complement = fixture.terms.mk_not_raw(lower);
    fixture.payload().0[0] = complement;
    assert!(matches!(
        fixture.check(1),
        Err(NraSosQueryCheckError::Kernel(_))
    ));
}

#[test]
fn rejects_wrong_step_empty_source_and_source_count_limit() {
    let fixture = Fixture::linear();
    assert!(matches!(
        check_nra_sos_query_with_progress(
            &fixture.terms,
            &[],
            &[],
            &fixture.candidate,
            &mut |_, _| true,
        ),
        Err(NraSosQueryCheckError::EmptyQuery)
    ));
    assert!(matches!(
        check_nra_sos_query_with_progress(
            &fixture.terms,
            &fixture.roots,
            &[],
            &ProofStep::Assume(fixture.roots[0]),
            &mut |_, _| true,
        ),
        Err(NraSosQueryCheckError::NotSos)
    ));
    let too_many = vec![fixture.roots[0]; NraSosCertificate::MAX_CLAUSE_SLOTS + 1];
    assert!(matches!(
        check_nra_sos_query_with_progress(
            &fixture.terms,
            &too_many,
            &[],
            &fixture.candidate,
            &mut |_, _| true,
        ),
        Err(NraSosQueryCheckError::ResourceLimit)
    ));
}

#[test]
fn rejects_missing_roots_literals_and_nested_arithmetic_children_without_panicking() {
    let mut fixture = Fixture::linear();
    let original = fixture.roots[0];
    fixture.roots[0] = TermId(u32::MAX);
    assert!(matches!(
        fixture.check(1),
        Err(NraSosQueryCheckError::InvalidRoot { .. })
    ));
    fixture.roots[0] = original;
    let original_literal = fixture.payload().0[0];
    fixture.payload().0[0] = TermId(u32::MAX);
    assert!(matches!(
        fixture.check(1),
        Err(NraSosQueryCheckError::InvalidRoot { .. })
    ));
    fixture.payload().0[0] = original_literal;
    let mut entries = fixture.terms.entries_snapshot();
    let TermData::App(_, args) = &mut entries[original.index()].0 else {
        panic!("comparison fixture")
    };
    args[0] = TermId(u32::MAX);
    fixture.replace_entries(entries);
    assert!(matches!(
        fixture.check(1),
        Err(NraSosQueryCheckError::Kernel(_))
    ));
}

#[test]
fn rejects_nonboolean_source_and_mistyped_numeric_descendant() {
    let mut fixture = Fixture::linear();
    let mut entries = fixture.terms.entries_snapshot();
    let original = entries[fixture.roots[0].index()].1.clone();
    entries[fixture.roots[0].index()].1 = Sort::Real;
    fixture.replace_entries(entries);
    assert!(matches!(
        fixture.check(1),
        Err(NraSosQueryCheckError::NonBooleanRoot { .. })
    ));
    let mut entries = fixture.terms.entries_snapshot();
    entries[fixture.roots[0].index()].1 = original;
    let TermData::App(_, args) = &entries[fixture.roots[0].index()].0 else {
        panic!("comparison fixture")
    };
    let variable = args[0];
    entries[variable.index()].1 = Sort::Bool;
    fixture.replace_entries(entries);
    assert!(matches!(
        fixture.check(1),
        Err(NraSosQueryCheckError::Kernel(_))
    ));
}

#[test]
fn missing_basis_handles_and_out_of_range_factor_positions_are_refused() {
    let mut fixture = Fixture::linear();
    fixture.payload().1.terms[0].origin = NraSosOrigin::ClauseLiteral { position: 2 };
    assert!(matches!(
        fixture.check(1),
        Err(NraSosQueryCheckError::Kernel(_))
    ));
    fixture.payload().1.terms[0].origin = NraSosOrigin::ClauseLiteral { position: 0 };
    let (_, cert) = fixture.payload();
    cert.basis.push(vec![TermId(u32::MAX)]);
    cert.gram = vec![vec![rat(0); 2]; 2];
    assert!(matches!(
        fixture.check(1),
        Err(NraSosQueryCheckError::Kernel(_))
    ));
}

#[test]
fn fresh_copy_preserves_raw_optional_boolean_metadata() {
    let fixture = Fixture::linear();
    for (yes, no) in [(None, None), (Some(TermId(u32::MAX)), None)] {
        let raw = TermStore::from_entries(fixture.terms.entries_snapshot(), yes, no, 123);
        let fresh = source::fresh_snapshot(&raw, &mut |_, _| true).unwrap();
        assert_eq!(fresh.boolean_constant_ids(), (yes, no));
        assert_eq!(fresh.var_counter(), 123);
        assert_eq!(fresh.entries_snapshot(), raw.entries_snapshot());
        assert_ne!(fresh.snapshot_stamp(), raw.snapshot_stamp());
        // No kernel operation consults these unused raw metadata handles.
        check_nra_sos_query_with_progress(
            &raw,
            &fixture.roots,
            &[],
            &fixture.candidate,
            &mut |_, _| true,
        )
        .expect("AST refutation does not claim metadata authentication");
    }
}

#[test]
fn source_replacement_append_and_metadata_mutation_retire_evidence() {
    let mut fixture = Fixture::linear();
    let checked = fixture.check(1).unwrap();
    let cloned = fixture.terms.clone();
    assert!(!checked
        .is_current_for_with_progress(
            &cloned,
            &fixture.roots[..1],
            &fixture.roots[1..],
            &mut |_, _| true,
        )
        .unwrap());
    let stamp = fixture.terms.snapshot_stamp();
    fixture.terms.mark_to_real_shadowed();
    assert_eq!(fixture.terms.snapshot_stamp(), stamp);
    assert!(!checked
        .is_current_for_with_progress(
            &fixture.terms,
            &fixture.roots[..1],
            &fixture.roots[1..],
            &mut |_, _| true,
        )
        .unwrap());
    let checked = fixture.check(1).unwrap();
    let _ = fixture.terms.mk_var("unrelated_new_entry", Sort::Real);
    assert!(!checked
        .is_current_for_with_progress(
            &fixture.terms,
            &fixture.roots[..1],
            &fixture.roots[1..],
            &mut |_, _| true,
        )
        .unwrap());
}

#[test]
fn cyclic_boolean_source_refuses_under_the_shared_callback() {
    let mut fixture = Fixture::linear();
    let root = fixture.roots[0];
    let mut entries = fixture.terms.entries_snapshot();
    entries[root.index()].0 = TermData::Not(root);
    fixture.replace_entries(entries);
    let mut calls = 0;
    let result = check_nra_sos_query_with_progress(
        &fixture.terms,
        &fixture.roots,
        &[],
        &fixture.candidate,
        &mut |_, _| {
            calls += 1;
            calls < 200
        },
    );
    assert!(matches!(result, Err(NraSosQueryCheckError::ResourceLimit)));
    assert_eq!(calls, 200);
}

#[test]
fn checks_a_quartic_strict_square_refutation() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("quartic_x", Sort::Real);
    let y = terms.mk_var("quartic_y", Sort::Real);
    let zero = real(&mut terms, 0);
    let one = real(&mut terms, 1);
    let xy = terms.mk_mul(vec![x, y]);
    let shifted = terms.mk_sub(vec![xy, one]);
    let square = terms.mk_mul(vec![shifted, shifted]);
    let assertion = terms.mk_lt(square, zero);
    let candidate = ProofStep::NraSos {
        clause: vec![terms.mk_not_raw(assertion)],
        certificate: NraSosCertificate {
            basis: vec![vec![], vec![x, y]],
            gram: vec![vec![rat(1), rat(-1)], vec![rat(-1), rat(1)]],
            terms: vec![factor(0)],
            rhs: rat(0),
        },
    };
    check_nra_sos_query_with_progress(&terms, &[], &[assertion], &candidate, &mut |_, _| true)
        .expect("positive SOS plus strict negative-square source equals zero");
}

#[test]
fn an_unused_deep_sort_refuses_before_recursive_snapshot_cloning() {
    let mut fixture = Fixture::linear();
    let mut sort = Sort::Real;
    for _ in 0..257 {
        sort = Sort::seq(sort);
    }
    let mut entries = fixture.terms.entries_snapshot();
    entries.push((TermData::Var("unused_deep".into(), 99), sort));
    fixture.replace_entries(entries);
    assert!(matches!(
        fixture.check(1),
        Err(NraSosQueryCheckError::ResourceLimit)
    ));
}
