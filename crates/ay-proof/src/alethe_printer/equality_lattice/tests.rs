// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Printer-side tests for the all-equality lattice lowering. The positive
//! fixtures are also checked by pinned carcara in `ay-proof`'s
//! `group_proof::export_alethe_validation` (`equality_lattice.rs`); these pin
//! the refusals: a forged label, another kind, and a surface that changes a
//! row each keep the honest `hole`, never an `la_generic` claim.

use super::*;
use ay_core::{ProofStep, Sort, TheoryLemmaKind};
use num_bigint::BigInt;

fn int(terms: &mut TermStore, value: i64) -> TermId {
    terms.mk_int(BigInt::from(value))
}

fn app(terms: &mut TermStore, op: &str, args: &[TermId]) -> TermId {
    let sort = if op == "=" { Sort::Bool } else { Sort::Int };
    terms.mk_app(Symbol::named(op), args, sort)
}

/// The deep ring row's t20 as negated literals, with the THIRD row's target
/// as given (1000 is the lemma; 500 has the model `s1 = s2 = c2 = c3 = 0,
/// c1 = 1`). Also returns the second row's right side, stored `(* c1 4096)`.
fn deep_clause(terms: &mut TermStore, target: i64) -> (Vec<TermId>, TermId) {
    let s1 = terms.mk_var("s1", Sort::Int);
    let s2 = terms.mk_var("s2", Sort::Int);
    let c1 = terms.mk_var("c1", Sort::Int);
    let c2 = terms.mk_var("c2", Sort::Int);
    let c3 = terms.mk_var("c3", Sort::Int);
    let three = int(terms, 3);
    let modulus = int(terms, 4096);
    let three_s1 = app(terms, "*", &[three, s1]);
    let c2_scaled = app(terms, "*", &[modulus, c2]);
    let e1_rhs = app(terms, "+", &[c2_scaled, s2]);
    let e1 = app(terms, "=", &[three_s1, e1_rhs]);
    let c1_scaled = app(terms, "*", &[c1, modulus]);
    let e2_rhs = app(terms, "+", &[c1_scaled, s1]);
    let e2 = app(terms, "=", &[modulus, e2_rhs]);
    let five_hundred = int(terms, 500);
    let e3_lhs = app(terms, "+", &[s2, five_hundred]);
    let c3_scaled = app(terms, "*", &[modulus, c3]);
    let target = int(terms, target);
    let e3_rhs = app(terms, "+", &[c3_scaled, target]);
    let e3 = app(terms, "=", &[e3_lhs, e3_rhs]);
    let clause = [e1, e2, e3]
        .into_iter()
        .map(|equality| terms.mk_not_raw(equality))
        .collect();
    (clause, e2_rhs)
}

fn lemma(clause: Vec<TermId>, kind: TheoryLemmaKind) -> ProofStep {
    ProofStep::TheoryLemma {
        theory: "LIA".to_string(),
        clause,
        farkas: None,
        kind,
        lia: None,
    }
}

fn assert_hole(text: &str) {
    assert!(
        text.ends_with(":rule hole)") && !text.contains("la_generic"),
        "expected the honest hole: {text}"
    );
}

#[test]
fn the_strictly_certified_lemma_prints_checked_la_generic_steps() {
    let mut terms = TermStore::new();
    let (clause, _) = deep_clause(&mut terms, 1000);
    let step = lemma(clause.clone(), TheoryLemmaKind::IntGuardedSplitGap);
    let mut derived = Vec::new();
    crate::checker::validate_step(&terms, &mut derived, ProofId(0), &step, true, None)
        .expect("the rendered step is the strict checker's IntGuardedSplitGap");
    assert!(lia_equality_lattice_lowering_supported(
        &terms,
        &clause,
        &TheoryLemmaKind::IntGuardedSplitGap,
        None
    ));
    // The publication wire-gap screen asks the same question of the step.
    assert!(lia_lattice_lowering_supported(&terms, &step, None));
    let text = AlethePrinter::new(&terms)
        .format_step(&step, ProofId(7))
        .expect("renders");
    assert!(!text.contains(":rule hole"), "{text}");
    assert!(text.starts_with("(step t7.split (cl (<= (+ "), "{text}");
    assert!(
        text.contains(":rule la_generic :args (1 3 1 1))")
            || text.contains(":rule la_generic :args ((- 1) (- 3) (- 1) 1))"),
        "the second row enters three times: {text}"
    );
    assert!(
        text.ends_with(":rule resolution :premises (t7.r t7.hi))"),
        "{text}"
    );
}

/// NEGATIVE TWIN: the label on a clause whose negation has an integer model.
/// The strict checker refuses it, and the printer must not turn it into
/// checked-looking steps either.
#[test]
fn a_forged_label_on_a_satisfiable_clause_keeps_the_hole() {
    let mut terms = TermStore::new();
    let (clause, _) = deep_clause(&mut terms, 500);
    let step = lemma(clause.clone(), TheoryLemmaKind::IntGuardedSplitGap);
    let mut derived = Vec::new();
    assert!(
        crate::checker::validate_step(&terms, &mut derived, ProofId(0), &step, true, None).is_err(),
        "falsified at s1 = s2 = c2 = c3 = 0, c1 = 1"
    );
    assert!(!lia_equality_lattice_lowering_supported(
        &terms,
        &clause,
        &TheoryLemmaKind::IntGuardedSplitGap,
        None
    ));
    assert!(!lia_lattice_lowering_supported(&terms, &step, None));
    let text = AlethePrinter::new(&terms)
        .format_step(&step, ProofId(7))
        .expect("renders");
    assert_hole(&text);
}

/// The lowering is bound to the strictly validated kind: the same valid
/// clause filed as unvalidated `Generic` is not promoted by it.
#[test]
fn the_same_clause_under_an_unvalidated_kind_is_not_lowered() {
    let mut terms = TermStore::new();
    let (clause, _) = deep_clause(&mut terms, 1000);
    assert!(!lia_equality_lattice_lowering_supported(
        &terms,
        &clause,
        &TheoryLemmaKind::Generic,
        None
    ));
    let step = lemma(clause, TheoryLemmaKind::Generic);
    assert!(!lia_lattice_lowering_supported(&terms, &step, None));
    let text = AlethePrinter::new(&terms)
        .format_step(&step, ProofId(7))
        .expect("renders");
    assert_hole(&text);
}

/// A surface spelling that commutes a product keeps the row, so the lowering
/// stands over the re-spelled text; one that changes a coefficient changes
/// the row the checker would read, and the step keeps its hole.
#[test]
fn a_surface_that_changes_a_row_keeps_the_hole() {
    let mut terms = TermStore::new();
    let (clause, e2_rhs) = deep_clause(&mut terms, 1000);
    let kind = TheoryLemmaKind::IntGuardedSplitGap;
    let step = lemma(clause.clone(), kind);

    let mut same_row: HashMap<TermId, String> = HashMap::default();
    same_row.insert(e2_rhs, "(+ (* 4096 c1) s1)".to_string());
    assert!(lia_equality_lattice_lowering_supported(
        &terms,
        &clause,
        &kind,
        Some(&same_row)
    ));
    assert!(lia_lattice_lowering_supported(
        &terms,
        &step,
        Some(&same_row)
    ));
    let text = AlethePrinter::new_with_overrides(&terms, Some(&same_row))
        .format_step(&step, ProofId(7))
        .expect("renders");
    assert!(text.contains("(- 4096 (+ (* 4096 c1) s1))"), "{text}");
    assert!(!text.contains(":rule hole"), "{text}");

    let mut changed_row: HashMap<TermId, String> = HashMap::default();
    changed_row.insert(e2_rhs, "(+ (* 4095 c1) s1)".to_string());
    assert!(!lia_equality_lattice_lowering_supported(
        &terms,
        &clause,
        &kind,
        Some(&changed_row)
    ));
    assert!(!lia_lattice_lowering_supported(
        &terms,
        &step,
        Some(&changed_row)
    ));
    let text = AlethePrinter::new_with_overrides(&terms, Some(&changed_row))
        .format_step(&step, ProofId(7))
        .expect("renders");
    assert_hole(&text);
}

/// The printer's `la_generic` chokepoint replays every command of this
/// lowering, and the replay is what keeps a wrong lattice claim off the wire:
/// the rendered commands all hold, and the split with its lattice neighbours
/// moved by one (`D ≤ −499 ∨ 3597 ≤ D` for `D ∈ 11788 + 4096ℤ`) is refused,
/// because `−499 − 11788` is no multiple of 4096 and the checker's
/// strengthening no longer closes the gap.
#[test]
fn the_la_generic_replay_refuses_a_split_with_moved_neighbours() {
    use crate::alethe_printer::la_generic_surface::{
        printed_arith_commands, printed_la_generic_holds, PrintedArithCommand,
    };

    let mut terms = TermStore::new();
    let (clause, _) = deep_clause(&mut terms, 1000);
    let step = lemma(clause, TheoryLemmaKind::IntGuardedSplitGap);
    let text = AlethePrinter::new(&terms)
        .format_step(&step, ProofId(7))
        .expect("renders");
    let judge = |text: &str| -> Vec<(String, bool)> {
        printed_arith_commands(text)
            .expect("the lowering is a readable command sequence")
            .into_iter()
            .map(|command| match command {
                PrintedArithCommand::LaGeneric(command) => (
                    command.name.to_string(),
                    printed_la_generic_holds(&command.literals, &command.args),
                ),
                _ => panic!("the lowering prints only la_generic arithmetic"),
            })
            .collect()
    };
    let verdicts = judge(&text);
    assert_eq!(verdicts.len(), 3, "{text}");
    assert!(verdicts.iter().all(|(_, holds)| *holds), "{verdicts:?}");

    assert!(text.contains(" (- 500)) (<= 3596 "), "{text}");
    let moved = text
        .replace(" (- 500))", " (- 499))")
        .replace("(<= 3596 ", "(<= 3597 ");
    let verdicts = judge(&moved);
    assert!(
        verdicts
            .iter()
            .any(|(name, holds)| name == "t7.split" && !holds),
        "a split whose neighbours are not adjacent lattice values must be refused: {verdicts:?}"
    );
}
