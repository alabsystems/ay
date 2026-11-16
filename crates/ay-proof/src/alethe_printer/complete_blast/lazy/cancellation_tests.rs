// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Owner propagation controls, not an aggregate allocation-budget claim.

use super::*;
use ay_core::TermStore;
use num_bigint::BigInt;
use std::cell::Cell;

mod cache_tests;
mod sweep_tests;

struct Fixture {
    terms: TermStore,
    quotient: TermId,
    identity: TermId,
}

impl Fixture {
    fn new() -> Self {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::bitvec(2));
        let one = terms.mk_bitvec(BigInt::from(1), 2);
        let quotient = terms.mk_app(Symbol::named("bvudiv"), [x, one], Sort::bitvec(2));
        let identity = terms.mk_app(Symbol::named("="), [quotient, quotient], Sort::Bool);
        Self {
            terms,
            quotient,
            identity,
        }
    }

    fn blaster<'a, 'p>(
        &'a self,
        printer: &'p AlethePrinter<'a>,
    ) -> (Blaster<'a, 'p>, Vec<Vec<Literal>>) {
        let mut blaster = Blaster::new(printer, ProofId(1), "@ay_lazy_control_".to_string());
        blaster.opaque_divisions.insert(self.quotient);
        let root = blaster
            .prepare(self.identity)
            .expect("supported identity")
            .not()
            .expect("negation");
        let (cnf, _) = blaster.planned_cnf(root).expect("planned identity");
        (blaster, cnf)
    }
}

fn orient(_: &mut Blaster<'_, '_>, roots: &[SRef]) -> Option<SRef> {
    roots.first()?.not()
}

#[test]
fn refinement_polls_the_actual_counted_sat_child() {
    let f = Fixture::new();
    let calls = Cell::new(0usize);
    let mut callback = || {
        calls.set(calls.get() + 1);
        true
    };
    let printer = AlethePrinter::new(&f.terms).with_emission_progress(&mut callback);
    let (blaster, cnf) = f.blaster(&printer);
    calls.set(0);
    let clauses = blaster.model_clauses(&cnf).expect("same normalized CNF");
    let copied = calls.get();
    let mut child_polls = 0;
    let limits = ResolutionProofLimits {
        deadline: Some(std::time::Instant::now() + MODEL_WALL),
        max_conflicts: Some(MODEL_CONFLICTS),
        max_decisions: Some(MODEL_CONFLICTS * 64),
        ..ResolutionProofLimits::default()
    };
    let (outcome, _) =
        solve_resolution_dag_counted(blaster.circuit.len(), &clauses, &limits, &mut || {
            child_polls += 1;
            true
        });
    assert!(matches!(outcome, Ok(ResolutionSolveOutcome::Unsat(_))));
    assert!(child_polls > 0);
    calls.set(0);
    assert!(matches!(
        blaster.refinement(&cnf, &[f.identity]),
        Some(Refinement::Keep)
    ));
    assert_eq!(calls.get(), copied + 6 + 2 * child_polls);
}

#[test]
fn refusal_inside_the_refinement_child_is_not_a_keep_or_a_new_owner() {
    let f = Fixture::new();
    let calls = Cell::new(0usize);
    let stop_at = Cell::new(usize::MAX);
    let mut callback = || {
        calls.set(calls.get() + 1);
        calls.get() != stop_at.get()
    };
    let printer = AlethePrinter::new(&f.terms).with_emission_progress(&mut callback);
    let (blaster, cnf) = f.blaster(&printer);
    calls.set(0);
    blaster.model_clauses(&cnf).expect("same normalized CNF");
    let first_child_poll = calls.get() + 5;
    calls.set(0);
    stop_at.set(first_child_poll);
    assert!(blaster.refinement(&cnf, &[f.identity]).is_none());
    assert_eq!(calls.get(), first_child_poll);
    stop_at.set(usize::MAX);
    assert!(blaster.refinement(&cnf, &[f.identity]).is_none());
    assert_eq!(calls.get(), first_child_poll);
}

#[test]
fn every_division_census_poll_refuses_without_recovery() {
    let f = Fixture::new();
    let mut polls = 0;
    let mut accepted = || {
        polls += 1;
        true
    };
    let printer = AlethePrinter::new(&f.terms).with_emission_progress(&mut accepted);
    assert_eq!(
        division_terms(&printer, &[f.identity]),
        Some([f.quotient].into_iter().collect())
    );
    drop(printer);
    for stop in 1..=polls {
        let mut observed = 0;
        let mut callback = || {
            observed += 1;
            observed != stop
        };
        let printer = AlethePrinter::new(&f.terms).with_emission_progress(&mut callback);
        assert!(division_terms(&printer, &[f.identity]).is_none());
        assert!(division_terms(&printer, &[f.identity]).is_none());
        drop(printer);
        assert_eq!(observed, stop);
    }
}

#[test]
fn planned_opacity_is_not_retained_before_a_document_prints() {
    settled::reset();
    let f = Fixture::new();
    let printer = AlethePrinter::new(&f.terms);
    let key = settled_key(&printer, &[f.identity], None).expect("scheduling key");
    let planned = Blaster::plan_lemma(
        &printer,
        ProofId(1),
        "@ay_lazy_stage_",
        &[f.identity],
        &orient,
        true,
        None,
    )
    .expect("identity is planned");
    assert!(planned.abstracted);
    assert!(planned.settled.is_some());
    assert_eq!(settled::raw_lookup(&key), None);
    drop(planned);
    assert_eq!(settled::raw_lookup(&key), None);
}

#[test]
fn accepting_owner_preserves_exact_document_and_retains_only_after_printing() {
    settled::reset();
    let f = Fixture::new();
    let clause = format!(
        "(cl {})",
        AlethePrinter::new(&f.terms).format_term(f.identity)
    );
    let ordinary = Blaster::lemma_document(
        &AlethePrinter::new(&f.terms),
        ProofId(1),
        "@ay_lazy_bytes_",
        &[f.identity],
        &orient,
        &clause,
        None,
        None,
    )
    .expect("ordinary identity document");
    settled::reset();
    let mut callback = || true;
    let printer = AlethePrinter::new(&f.terms).with_emission_progress(&mut callback);
    let controlled = Blaster::lemma_document(
        &printer,
        ProofId(1),
        "@ay_lazy_bytes_",
        &[f.identity],
        &orient,
        &clause,
        None,
        None,
    )
    .expect("controlled identity document");
    assert_eq!(ordinary, controlled);
    assert!(!controlled.contains(":rule hole"));
    assert!(!controlled.contains(":rule trust"));
    let key = settled_key(&printer, &[f.identity], None).expect("scheduling key");
    assert_eq!(
        settled::raw_lookup(&key),
        Some([printer.format_term(f.quotient)].into_iter().collect())
    );
}

#[test]
fn an_observed_stop_after_planning_prevents_the_exact_retry() {
    settled::reset();
    let f = Fixture::new();
    let calls = Cell::new(0usize);
    let stop_at = Cell::new(usize::MAX);
    let mut callback = || {
        calls.set(calls.get() + 1);
        calls.get() != stop_at.get()
    };
    let printer = AlethePrinter::new(&f.terms).with_emission_progress(&mut callback);
    Blaster::plan_lemma(
        &printer,
        ProofId(1),
        "@ay_lazy_retry_",
        &[f.identity],
        &orient,
        true,
        None,
    )
    .expect("baseline plan");
    let plan_polls = calls.get();
    calls.set(0);
    stop_at.set(plan_polls + 5); // lemma entry + lazy-entry + finish entry.
    let orientations = Cell::new(0usize);
    let counted = |blaster: &mut Blaster<'_, '_>, roots: &[SRef]| {
        orientations.set(orientations.get() + 1);
        orient(blaster, roots)
    };
    assert!(Blaster::lemma_document(
        &printer,
        ProofId(1),
        "@ay_lazy_retry_",
        &[f.identity],
        &counted,
        "(cl false)",
        None,
        None
    )
    .is_none());
    assert_eq!(
        orientations.get(),
        1,
        "a stopped owner cannot replan every divider exactly"
    );
    assert_eq!(calls.get(), stop_at.get());
    assert_eq!(
        settled::raw_lookup(&format!("\n{}", printer.format_term(f.identity))),
        None
    );
}

#[test]
fn a_false_division_lemma_is_not_printed_or_settled() {
    settled::reset();
    let mut f = Fixture::new();
    let y = f.terms.mk_var("different", Sort::bitvec(2));
    let false_lemma = f
        .terms
        .mk_app(Symbol::named("="), [f.quotient, y], Sort::Bool);
    let printer = AlethePrinter::new(&f.terms);
    let key = settled_key(&printer, &[false_lemma], None).expect("scheduling key");
    let final_clause = format!("(cl {})", printer.format_term(false_lemma));
    assert!(Blaster::lemma_document(
        &printer,
        ProofId(1),
        "@ay_false_lazy_",
        &[false_lemma],
        &orient,
        &final_clause,
        None,
        None
    )
    .is_none());
    assert_eq!(settled::raw_lookup(&key), None);
}

#[test]
fn local_lemma_retention_is_not_an_outer_export_acceptance() {
    // This characterizes the explicit scheduling-cache boundary, not outer
    // attempt closure: a valid local lemma can precede the outer final refusal.
    settled::reset();
    crate::resolution_dag_memo::reset_resolution_dag_memo();
    let f = Fixture::new();
    let calls = Cell::new(0usize);
    let mut callback = || {
        calls.set(calls.get() + 1);
        true
    };
    let printer = AlethePrinter::new(&f.terms).with_emission_progress(&mut callback);
    printer
        .format_bv_complete_blast_refutation(ProofId(1), &[f.identity])
        .expect("accepted local and outer render");
    let total = calls.get();
    let key = format!("\n{}", printer.format_term(f.identity));
    let expected = settled::raw_lookup(&key).expect("locally accepted scheduling choice");
    drop(printer);
    settled::reset();
    crate::resolution_dag_memo::reset_resolution_dag_memo();
    let observed = Cell::new(0usize);
    let mut callback = || {
        observed.set(observed.get() + 1);
        observed.get() != total
    };
    let printer = AlethePrinter::new(&f.terms).with_emission_progress(&mut callback);
    assert!(printer
        .format_bv_complete_blast_refutation(ProofId(1), &[f.identity])
        .is_none());
    assert_eq!(observed.get(), total);
    assert_eq!(
        settled::raw_lookup(&key),
        Some(expected),
        "retention is not permission to publish the outer document"
    );
}
