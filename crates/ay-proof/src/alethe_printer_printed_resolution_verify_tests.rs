// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Verification fixtures for the id-addressed printed-clause ledger
//! (`claude/printed-resolution-hole-classification`, verified 2026-09-19).
//!
//! Every NEGATIVE fixture below is a resolution step whose PRINTED premises do
//! not eliminate the printed pivot, or whose premise the judgement cannot
//! read. Each must hole (`Ok(Some(hole))`), be repaired by a checked bridge
//! (`Ok(Some(bridge))`), or decline the export (`Err`). None may render
//! UNCHANGED (`Ok(None)`) — that is the silent approval the ledger exists to
//! refuse. The POSITIVE controls must render unchanged, so the refusals above
//! are not "refuse everything".

use super::super::{AlethePrintError, AlethePrinter};
use super::PrintedClause;
use ay_core::kani_compat::DetHashMap;
use ay_core::{Proof, ProofId, ProofStep, Sort, TermId, TermStore};

/// What the judgement answered for one fixture.
#[derive(Debug, PartialEq, Eq)]
enum Answer {
    /// `Ok(None)`: the step ships exactly as rendered — APPROVED.
    Unchanged,
    /// `Ok(Some(text))` ending in `:rule hole)`: the honest hole.
    Hole,
    /// `Ok(Some(text))` that is not a hole: a bridge repair.
    Repaired,
    /// `Err(..)`: the export is declined.
    Declined,
}

enum Premise<'a> {
    Text(&'a [&'a str]),
    Unreadable,
    Unbounded,
    Missing,
}

/// Judge one printed resolution: `premises` are the printed clauses the
/// ledger holds for `t0..tN`, `conclusion` the printed literals of the judged
/// step `tN`, spelled through the wire-override channel so the step's own
/// clause prints exactly the text under test.
fn judge(premises: &[Premise<'_>], conclusion: &[&str]) -> (Answer, String) {
    let mut terms = TermStore::new();
    let mut overrides: DetHashMap<TermId, String> = DetHashMap::default();
    let mut clause = Vec::new();
    for (index, text) in conclusion.iter().enumerate() {
        let var = terms.mk_var(format!("c{index}"), Sort::Bool);
        overrides.insert(var, (*text).to_string());
        clause.push(var);
    }
    // A proof with one assume per premise, so the ledger is ACTIVE and every
    // premise id is a step of the proof.
    let mut proof = Proof::new();
    let filler = terms.mk_var("filler", Sort::Bool);
    for _ in premises {
        proof.add_step(ProofStep::Assume(filler));
    }
    let printer = AlethePrinter::new_with_overrides(&terms, Some(&overrides));
    printer.prepare_proof(&proof).expect("prepare");
    let mut premise_ids = Vec::new();
    for (index, premise) in premises.iter().enumerate() {
        let id = ProofId(index as u32);
        premise_ids.push(id);
        let entry = match premise {
            Premise::Text(texts) => {
                let owned: Vec<String> = texts.iter().map(|s| (*s).to_string()).collect();
                PrintedClause::Literals(
                    printer
                        .record_interned_clause(&owned)
                        .expect("a fixture clause fits the ledger"),
                )
            }
            Premise::Unreadable => PrintedClause::Unreadable,
            Premise::Unbounded => PrintedClause::Unbounded,
            Premise::Missing => continue,
        };
        printer.printed_step_clauses.borrow_mut().insert(id, entry);
    }
    let step = ProofId(premises.len() as u32);
    // The step's own clause must print the text under test, or the fixture is
    // not testing what it says.
    let printed = printer.format_clause(&clause);
    let expected = if conclusion.is_empty() {
        "(cl)".to_string()
    } else {
        format!("(cl {})", conclusion.join(" "))
    };
    assert_eq!(
        printed, expected,
        "the conclusion must print the fixture's text"
    );
    match printer.judge_printed_resolution(step, &clause, &printed, &premise_ids) {
        Ok(None) => (Answer::Unchanged, printed),
        Ok(Some(text)) if text.trim_end().ends_with(":rule hole)") => (Answer::Hole, text),
        Ok(Some(text)) => (Answer::Repaired, text),
        Err(AlethePrintError::InvalidSurfaceStep { reason, .. }) => (Answer::Declined, reason),
        Err(other) => (Answer::Declined, format!("{other:?}")),
    }
}

fn t<'a>(literals: &'a [&'a str]) -> Premise<'a> {
    Premise::Text(literals)
}

/// Positive controls: a printed instance MUST render unchanged, or the
/// negative fixtures below prove nothing.
#[test]
fn printed_instances_render_unchanged() {
    let controls: Vec<(Vec<Premise<'_>>, Vec<&str>)> = vec![
        (vec![t(&["p", "q"]), t(&["(not p)"])], vec!["q"]),
        (vec![t(&["p", "q"]), t(&["(not p)", "r"])], vec!["q", "r"]),
        // Double negation: `(not (not p))` is the complement of `(not p)`.
        (vec![t(&["(not (not p))", "q"]), t(&["(not p)"])], vec!["q"]),
        // The bit-vector collapse the checker's parser performs.
        (
            vec![t(&["(= x #b0000)", "q"]), t(&["(not (= x (_ bv0 4)))"])],
            vec!["q"],
        ),
        // Whitespace inside an application is not a divergence.
        (vec![t(&["(P  a)", "q"]), t(&["(not (P a))"])], vec!["q"]),
        // A multi-line quoted symbol, spelled identically on both sides.
        (
            vec![t(&["(P |g\nh|)", "q"]), t(&["(not (P |g\nh|))"])],
            vec!["q"],
        ),
        // A string literal, identical on both sides.
        (
            vec![t(&["(= s \"a b\")", "q"]), t(&["(not (= s \"a b\"))"])],
            vec!["q"],
        ),
        // Three premises, two pivots.
        (
            vec![t(&["p", "q"]), t(&["(not p)", "r"]), t(&["(not r)"])],
            vec!["q"],
        ),
        // The empty clause from a unit and its complement.
        (vec![t(&["p"]), t(&["(not p)"])], vec![]),
    ];
    for (index, (premises, conclusion)) in controls.iter().enumerate() {
        let (answer, text) = judge(premises, conclusion);
        assert_eq!(
            answer,
            Answer::Unchanged,
            "control {index}: a printed instance must render unchanged, got {text}"
        );
    }
}

/// THE FIXTURES. Every one is a printed step the checker would refuse (or a
/// premise the judgement cannot read); every one must hole, bridge, or
/// decline — never render unchanged.
#[test]
fn printed_non_instances_never_render_unchanged() {
    let fixtures: Vec<(&str, Vec<Premise<'_>>, Vec<&str>)> = vec![
        // --- spelling divergences ---
        (
            "swapped equality operands",
            vec![t(&["(= a b)", "q"]), t(&["(not (= b a))"])],
            vec!["q"],
        ),
        (
            "arithmetic spelling `(- C 1)` vs `(+ C (- 1))`",
            vec![
                t(&["(<= 0 (- C 1))", "q"]),
                t(&["(not (<= 0 (+ C (- 1))))"]),
            ],
            vec!["q"],
        ),
        (
            "case of a function symbol",
            vec![t(&["(P a)", "q"]), t(&["(not (p a))"])],
            vec!["q"],
        ),
        (
            "numeral vs decimal",
            vec![t(&["(= x 1)", "q"]), t(&["(not (= x 1.0))"])],
            vec!["q"],
        ),
        (
            "`(- 1)` vs `-1`",
            vec![t(&["(= x (- 1))", "q"]), t(&["(not (= x -1))"])],
            vec!["q"],
        ),
        (
            "bit-vector VALUE differs under the parser collapse",
            vec![t(&["(= x #b0001)", "q"]), t(&["(not (= x (_ bv0 4)))"])],
            vec!["q"],
        ),
        (
            "bit-vector WIDTH differs under the parser collapse",
            vec![t(&["(= x #b0000)", "q"]), t(&["(not (= x (_ bv0 5)))"])],
            vec!["q"],
        ),
        // --- quoted symbols and string literals in operands ---
        (
            "quoted symbol vs bare symbol with a space",
            vec![t(&["(P |a b|)", "q"]), t(&["(not (P a))"])],
            vec!["q"],
        ),
        (
            "two different quoted symbols",
            vec![t(&["(P |a b|)", "q"]), t(&["(not (P |a c|))"])],
            vec!["q"],
        ),
        (
            "quoted symbol containing a close paren",
            vec![t(&["(P |a)b|)", "q"]), t(&["(not (P |a)c|))"])],
            vec!["q"],
        ),
        (
            "string literals that differ",
            vec![t(&["(= s \"x\")", "q"]), t(&["(not (= s \"y\"))"])],
            vec!["q"],
        ),
        (
            "string literals that differ only in inner whitespace",
            vec![t(&["(= s \"x  y\")", "q"]), t(&["(not (= s \"x y\"))"])],
            vec!["q"],
        ),
        (
            "string literal containing a close paren",
            vec![t(&["(= s \"a)\")", "q"]), t(&["(not (= s \"a(\"))"])],
            vec!["q"],
        ),
        (
            "string literal spelling the rule name",
            vec![
                t(&["(= s \":rule hole\")", "q"]),
                t(&["(not (= s \":rule or\"))"]),
            ],
            vec!["q"],
        ),
        // --- multi-line terms ---
        (
            "multi-line quoted symbol vs its single-line spelling",
            vec![t(&["(P |g\nh|)", "q"]), t(&["(not (P |g h|))"])],
            vec!["q"],
        ),
        (
            "multi-line string literal vs single-line",
            vec![t(&["(= s \"a\nb\")", "q"]), t(&["(not (= s \"a b\"))"])],
            vec!["q"],
        ),
        // --- pruned or unpaired literals ---
        (
            "a premise literal pruned from the conclusion",
            vec![t(&["p", "q", "r"]), t(&["(not p)"])],
            vec!["q"],
        ),
        (
            "same polarity on both sides: no pivot",
            vec![t(&["p", "q"]), t(&["p", "r"])],
            vec!["q", "r"],
        ),
        (
            "no complement anywhere",
            vec![t(&["p", "q"]), t(&["r"])],
            vec!["q"],
        ),
        (
            "empty clause from two unrelated units",
            vec![t(&["p"]), t(&["q"])],
            vec![],
        ),
        (
            "empty clause from `p` and `(not q)`",
            vec![t(&["p"]), t(&["(not q)"])],
            vec![],
        ),
        (
            "double negation with the SAME parity on both sides",
            vec![t(&["(not (not p))", "q"]), t(&["(not (not p))"])],
            vec!["q"],
        ),
        (
            "conclusion literal that no premise carries and no pivot supports",
            vec![t(&["p", "q"]), t(&["r"])],
            vec!["s"],
        ),
        (
            "three premises where the second pivot is never eliminated",
            vec![t(&["p", "q"]), t(&["(not p)", "r"]), t(&["r"])],
            vec!["q"],
        ),
        // --- premises the judgement cannot read ---
        (
            "a premise the ledger holds as Unreadable",
            vec![t(&["p", "q"]), Premise::Unreadable],
            vec!["q"],
        ),
        (
            "a premise past the ledger's bounds",
            vec![t(&["p", "q"]), Premise::Unbounded],
            vec!["q"],
        ),
        (
            "a premise never recorded while the ledger is active",
            vec![t(&["p", "q"]), Premise::Missing],
            vec!["q"],
        ),
        (
            "an Unreadable premise even when the readable premise alone would entail",
            vec![t(&["q"]), Premise::Unreadable],
            vec!["q"],
        ),
    ];
    assert!(
        fixtures.len() >= 20,
        "the brief asks for at least twenty fixtures"
    );
    let mut table = String::new();
    for (name, premises, conclusion) in &fixtures {
        let (answer, text) = judge(premises, conclusion);
        table.push_str(&format!(
            "{answer:?}\t{name}\t{}\n",
            text.replace('\n', "\\n")
        ));
        assert_ne!(
            answer,
            Answer::Unchanged,
            "fixture `{name}` rendered UNCHANGED: a printed non-instance was approved"
        );
    }
    // Read the table with `--nocapture`.
    eprintln!("{table}");
}

/// The unreachable-path hardening of `3027f9e84f`: an atom id the table does
/// not name makes BOTH judgements decline to the honest hole. Until
/// 2026-09-19 that was true of `judge_printed_resolution` only —
/// the `or` judgement's `?` on `printed_atom_texts` sat inside a `find_map`
/// closure, where `None` is "this command is fine", so it APPROVED. The path
/// is unreachable today (every id is minted against the same table and both
/// are cleared together in `prepare_proof`), which is exactly why it must be
/// the loud shape: if it ever becomes reachable, this test is what says so.
#[test]
fn an_unaddressable_atom_id_declines_both_judgements() {
    let mut terms = TermStore::new();
    let p = terms.mk_var("p", Sort::Bool);
    let q = terms.mk_var("q", Sort::Bool);
    let overrides: DetHashMap<TermId, String> = DetHashMap::default();
    let mut proof = Proof::new();
    proof.add_step(ProofStep::Assume(p));
    proof.add_step(ProofStep::Assume(q));
    let printer = AlethePrinter::new_with_overrides(&terms, Some(&overrides));
    printer.prepare_proof(&proof).expect("prepare");
    // An id no atom carries.
    printer
        .printed_step_clauses
        .borrow_mut()
        .insert(ProofId(0), PrintedClause::Literals(vec![u32::MAX]));
    // Resolution: the honest hole, as the commit says.
    let rendered = printer
        .judge_printed_resolution(ProofId(1), &[q], "(cl q)", &[ProofId(0)])
        .expect("published")
        .expect("a premise that names no atom is a hole");
    assert_eq!(rendered, "(step t1 (cl q) :rule hole)");
    // `or`: the same unaddressable premise, cited by a printed `or` command.
    let step = ProofStep::Step {
        rule: ay_core::AletheRule::Or,
        clause: vec![p, q],
        premises: vec![ProofId(0)],
        args: Vec::new(),
    };
    let or_rendered = "(step t1 (cl p q) :rule or :premises (t0))".to_string();
    let judged = printer
        .judge_printed_premise_rules(&step, ProofId(1), or_rendered.clone())
        .expect("published");
    assert_eq!(
        judged, "(step t1 (cl p q) :rule hole)",
        "judge_printed_premise_rules must decline a premise whose atom id the table does not name"
    );
    // Control: the same command over a premise the table DOES name renders
    // unchanged, so the decline above is the id, not the fixture.
    printer.printed_step_clauses.borrow_mut().insert(
        ProofId(0),
        PrintedClause::Literals(
            printer
                .record_interned_clause(&["(or p q)".to_string()])
                .expect("fits"),
        ),
    );
    let judged = printer
        .judge_printed_premise_rules(&step, ProofId(1), or_rendered.clone())
        .expect("published");
    assert_eq!(judged, or_rendered);
}

/// The `ite` projections are judged over the PRINTED premise, as `or` is.
/// The measured false green: the premise of the array-frame fixture's `ite1`
/// shipped as the AUTHORED equality `(= (select snew 0) (ite (= 0 1) val
/// (select s 0)))`, and pinned carcara refused the step ("is of the wrong
/// form, expected '(ite phi_1 phi_2 phi_3)'"). Whatever channel spelled the
/// premise that way, the step must decline to the honest hole; over the
/// printed canonical `ite` the same command renders unchanged.
#[test]
fn an_ite_projection_over_a_premise_that_does_not_print_as_an_ite_is_a_hole() {
    let mut terms = TermStore::new();
    let condition = terms.mk_var("c", Sort::Bool);
    let framed = terms.mk_var("e", Sort::Bool);
    let overrides: DetHashMap<TermId, String> = DetHashMap::default();
    let mut proof = Proof::new();
    proof.add_step(ProofStep::Assume(condition));
    let printer = AlethePrinter::new_with_overrides(&terms, Some(&overrides));
    printer.prepare_proof(&proof).expect("prepare");
    let step = ProofStep::Step {
        rule: ay_core::AletheRule::Ite1,
        clause: vec![condition, framed],
        premises: vec![ProofId(0)],
        args: Vec::new(),
    };
    let record = |premise: &str| {
        let interned = printer
            .record_interned_clause(&[premise.to_string()])
            .expect("fits");
        printer
            .printed_step_clauses
            .borrow_mut()
            .insert(ProofId(0), PrintedClause::Literals(interned));
    };
    let rendered =
        "(step t1 (cl (= 1 0) (= (select snew 0) (select s 0))) :rule ite1 :premises (t0))";
    record("(= (select snew 0) (ite (= 0 1) val (select s 0)))");
    let judged = printer
        .judge_printed_premise_rules(&step, ProofId(1), rendered.to_string())
        .expect("published");
    assert_eq!(judged, "(step t1 (cl c e) :rule hole)");
    // A re-oriented condition is not the condition (`assert_eq` is syntactic).
    record("(ite (= 0 1) (= val (select snew 0)) (= (select snew 0) (select s 0)))");
    let judged = printer
        .judge_printed_premise_rules(&step, ProofId(1), rendered.to_string())
        .expect("published");
    assert_eq!(judged, "(step t1 (cl c e) :rule hole)");
    // Control: the canonical `ite` premise approves the same command.
    record("(ite (= 1 0) (= val (select snew 0)) (= (select snew 0) (select s 0)))");
    let judged = printer
        .judge_printed_premise_rules(&step, ProofId(1), rendered.to_string())
        .expect("published");
    assert_eq!(judged, rendered);
}
