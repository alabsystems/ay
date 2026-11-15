// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Printer-side tests for the cut-chain lowering. The corpus row it exists for
//! (`QF_LIA_ring_2exp16_5vars_cascade_unsat`) is checked by pinned carcara in
//! `ay-dpll`'s `group_proofs::carcara_external_check`; these pin the rendered
//! shape, the byte-level replay of every `la_generic`, and the refusals: a
//! forged label, another kind, and a surface that changes a row each keep the
//! honest `hole`.

use super::*;
use crate::alethe_printer::la_generic_surface::{
    printed_arith_commands, printed_la_generic_holds, PrintedArithCommand,
};
use ay_core::{ProofStep, Sort, TheoryLemmaKind};
use num_bigint::BigInt;

fn int(terms: &mut TermStore, value: i64) -> TermId {
    terms.mk_int(BigInt::from(value))
}

fn app(terms: &mut TermStore, op: &str, args: &[TermId]) -> TermId {
    let sort = if matches!(op, "=" | "<=") {
        Sort::Bool
    } else {
        Sort::Int
    };
    terms.mk_app(Symbol::named(op), args, sort)
}

/// t161 of the cascade row, reduced to the thirteen rows its chain uses plus
/// the carry lower bounds, in the solver's spelling. `tail = 1` is the lemma;
/// `tail = 2` has the model `m = (17476, 17476, 17476, 17477, 17477)`,
/// `c_i = 1`, `s = (39320, 52392, 65464)`. Also returns `(* m1 3)`.
fn cascade_clause(terms: &mut TermStore, tail: i64) -> (Vec<TermId>, TermId) {
    let var = |terms: &mut TermStore, name: &str| terms.mk_var(name, Sort::Int);
    let s: Vec<TermId> = ["s1", "s2", "s3"].iter().map(|n| var(terms, n)).collect();
    let c: Vec<TermId> = ["c1", "c2", "c3", "c4"]
        .iter()
        .map(|n| var(terms, n))
        .collect();
    let m: Vec<TermId> = ["m1", "m2", "m3", "m4", "m5"]
        .iter()
        .map(|n| var(terms, n))
        .collect();
    let (three, word) = (int(terms, 3), int(terms, 65536));
    let m3: Vec<TermId> = m.iter().map(|&mi| app(terms, "*", &[mi, three])).collect();
    let c16: Vec<TermId> = c.iter().map(|&ci| app(terms, "*", &[ci, word])).collect();
    let tail = int(terms, tail);
    let mut atoms = Vec::new();
    for (lhs, rhs) in [
        ([s[2], m3[4]], [c16[3], tail]),
        ([c16[2], s[2]], [s[1], m3[3]]),
        ([c16[0], s[0]], [m3[0], m3[1]]),
        ([c16[1], s[1]], [s[0], m3[2]]),
    ] {
        let lhs = app(terms, "+", &lhs);
        let rhs = app(terms, "+", &rhs);
        atoms.push(app(terms, "=", &[lhs, rhs]));
    }
    let (zero, one, lo, max) = (
        int(terms, 0),
        int(terms, 1),
        int(terms, 40000),
        int(terms, 65535),
    );
    for &si in &s {
        atoms.push(app(terms, "<=", &[si, max]));
        atoms.push(app(terms, "<=", &[zero, si]));
    }
    for &ci in &c {
        atoms.push(app(terms, "<=", &[ci, one]));
        atoms.push(app(terms, "<=", &[zero, ci]));
    }
    for &mi3 in &m3 {
        atoms.push(app(terms, "<=", &[lo, mi3]));
    }
    let clause = atoms
        .into_iter()
        .map(|atom| terms.mk_not_raw(atom))
        .collect();
    (clause, m3[0])
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

/// `(command name, holds)` for every arithmetic command of `text`.
fn judge(text: &str) -> Vec<(String, bool)> {
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
}

#[test]
fn the_strictly_certified_chain_prints_checked_la_generic_steps() {
    let mut terms = TermStore::new();
    let (clause, _) = cascade_clause(&mut terms, 1);
    let step = lemma(clause.clone(), TheoryLemmaKind::IntCgCutChain);
    let mut derived = Vec::new();
    crate::checker::validate_step(&terms, &mut derived, ProofId(0), &step, true, None)
        .expect("the rendered step is the strict checker's IntCgCutChain");
    let kind = TheoryLemmaKind::IntCgCutChain;
    assert!(lia_cut_chain_lowering_supported(
        &terms, &clause, &kind, None
    ));
    assert!(lia_lattice_lowering_supported(&terms, &step, None));
    let text = AlethePrinter::new(&terms)
        .format_step(&step, ProofId(7))
        .expect("renders");
    assert!(!text.contains(":rule hole"), "{text}");
    assert!(text.starts_with("(step t7.c1 (cl (not (= "), "{text}");
    assert!(
        text.contains(" (>= (+ c1 c2 c3 c4) ") || text.contains(" (<= (+ c1 c2 c3 c4) "),
        "the carry total is rounded: {text}"
    );
    assert!(
        text.ends_with(":rule resolution :premises (t7.r2 t7.c1))"),
        "{text}"
    );
    let verdicts = judge(&text);
    assert!(verdicts.len() >= 2, "{text}");
    assert!(verdicts.iter().all(|(_, holds)| *holds), "{verdicts:?}");
}

/// NEGATIVE TWIN: the label on a clause whose negation has an integer model.
#[test]
fn a_forged_label_on_a_satisfiable_clause_keeps_the_hole() {
    let mut terms = TermStore::new();
    let (clause, _) = cascade_clause(&mut terms, 2);
    let step = lemma(clause.clone(), TheoryLemmaKind::IntCgCutChain);
    let mut derived = Vec::new();
    assert!(
        crate::checker::validate_step(&terms, &mut derived, ProofId(0), &step, true, None).is_err(),
        "the tail-2 cascade has an integer model"
    );
    assert!(!lia_lattice_lowering_supported(&terms, &step, None));
    let text = AlethePrinter::new(&terms)
        .format_step(&step, ProofId(7))
        .expect("renders");
    assert_hole(&text);
}

/// The lowering is bound to the strictly validated kind.
#[test]
fn the_same_clause_under_an_unvalidated_kind_is_not_lowered() {
    let mut terms = TermStore::new();
    let (clause, _) = cascade_clause(&mut terms, 1);
    let step = lemma(clause, TheoryLemmaKind::Generic);
    assert!(!lia_lattice_lowering_supported(&terms, &step, None));
    let text = AlethePrinter::new(&terms)
        .format_step(&step, ProofId(7))
        .expect("renders");
    assert_hole(&text);
}

/// A surface that commutes a product keeps every row, so the lowering stands
/// over the re-spelled text; one that changes a coefficient changes the row
/// the checker would read, and the step keeps its hole.
#[test]
fn a_surface_that_changes_a_row_keeps_the_hole() {
    let mut terms = TermStore::new();
    let (clause, m1_times_three) = cascade_clause(&mut terms, 1);
    let step = lemma(clause, TheoryLemmaKind::IntCgCutChain);
    let mut same_row: HashMap<TermId, String> = HashMap::default();
    same_row.insert(m1_times_three, "(* 3 m1)".to_string());
    let text = AlethePrinter::new_with_overrides(&terms, Some(&same_row))
        .format_step(&step, ProofId(7))
        .expect("renders");
    assert!(text.contains("(<= 40000 (* 3 m1))"), "{text}");
    assert!(!text.contains(":rule hole"), "{text}");
    let mut changed_row: HashMap<TermId, String> = HashMap::default();
    changed_row.insert(m1_times_three, "(* 4 m1)".to_string());
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

/// The replay is what keeps a wrong rounding off the wire: every rendered cut
/// holds, and the same cut with its bound moved one step further (a cut the
/// combination does not round to) is refused.
#[test]
fn the_la_generic_replay_refuses_a_cut_rounded_one_step_too_far() {
    let mut terms = TermStore::new();
    let (clause, _) = cascade_clause(&mut terms, 1);
    let step = lemma(clause, TheoryLemmaKind::IntCgCutChain);
    let text = AlethePrinter::new(&terms)
        .format_step(&step, ProofId(7))
        .expect("renders");
    let first = text.lines().next().expect("a first cut step");
    let (literal, bound, tightened) = {
        let open = first
            .rfind(" (>= ")
            .or_else(|| first.rfind(" (<= "))
            .expect("cut");
        let close = first.find(") :rule").expect("clause end");
        let literal = &first[open + 1..close];
        let (head, bound) = literal.rsplit_once(' ').expect("bound");
        let bound = bound.trim_end_matches(')');
        let value: i64 = bound.parse().expect("an unsigned bound");
        let tightened = if literal.starts_with("(>=") {
            value + 1
        } else {
            value - 1
        };
        (
            literal.to_string(),
            format!("{head} {bound})"),
            format!("{head} {tightened})"),
        )
    };
    assert_eq!(literal, bound);
    assert!(judge(first).iter().all(|(_, holds)| *holds), "{first}");
    let moved = first.replace(&bound, &tightened);
    assert!(
        judge(&moved).iter().all(|(_, holds)| !*holds),
        "a cut past its rounding must be refused: {moved}"
    );
}

/// The publication screen replays the rendering it admits. The cascade plan
/// holds, so the screen admits it; the same plan with one cut bound moved one
/// step past its rounding still parses — rows and atom keys match — but
/// renders an `la_generic` the pinned checker rejects, which the screen now
/// refuses instead of admitting a step the printer would hole.
#[test]
fn the_screen_refuses_a_plan_whose_rendering_does_not_replay() {
    let mut terms = TermStore::new();
    let (clause, _) = cascade_clause(&mut terms, 1);
    let printer = AlethePrinter::new_with_overrides_and_budget(&terms, None, Some(MAX_WORK));
    let mut plan = printer.cut_chain_plan(&clause).expect("the cascade plan");
    assert!(plan.printed_steps_hold());
    let first = plan.cuts[0].clone();
    let (head, bound) = first.trim_end_matches(')').rsplit_once(' ').expect("bound");
    let value: i64 = bound.parse().expect("an unsigned bound");
    // The edit must keep the cut readable, so the refusal below is the
    // `la_generic` replay's and not the reader's.
    assert_eq!(format!("{head} {value})"), first);
    let moved = if first.starts_with("(>=") {
        value + 1
    } else {
        value - 1
    };
    plan.cuts[0] = format!("{head} {moved})");
    assert!(!plan.printed_steps_hold());
    assert!(!screen_admits(&printer, Some(plan)));
}
