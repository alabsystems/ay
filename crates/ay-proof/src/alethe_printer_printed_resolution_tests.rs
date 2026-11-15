// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The printed-text judgement for premise-bearing resolution.
//!
//! Every test here is a MUTATION DIFFERENTIAL over the exact shape that shipped
//! the third false green of the z3-parity campaign: an internally complementary
//! pivot that prints as two spellings of one arithmetic atom, because the
//! authored spelling survives only on the assumed literal.
//!
//! Reproducer, AUFLIA `smt6101124544860517489`, build 9557 (`main`):
//!
//! ```text
//! unproved_steps=0 foreign_assumes=no trust_free=yes ay_self_checkable=yes
//! [ERROR] checking failed on step 't4' with rule 'th_resolution':
//!         pivot was not eliminated: '(<= 0 (+ C (- 1)))'
//! invalid
//! ```

use super::super::{AlethePrintError, AlethePrinter};
use super::{decode_printed_literal, printed_conclusion_of, PrintedClause};
use crate::{
    try_export_alethe_with_problem_scope_and_overrides,
    try_export_alethe_with_problem_scope_overrides_and_budget,
};
use ay_core::kani_compat::DetHashMap;
use ay_core::{AletheRule, Proof, ProofId, ProofStep, Sort, TermId, TermStore};
use num_bigint::BigInt;

/// `(< 0 C)`, `(<= 0 (+ C (- 1)))` and its negation, in one store.
struct Fixture {
    terms: TermStore,
    positive: TermId,
    atom: TermId,
    negated_atom: TermId,
}

fn fixture() -> Fixture {
    let mut terms = TermStore::new();
    let c = terms.mk_var("C", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));
    let one = terms.mk_int(BigInt::from(1));
    let positive = terms.mk_lt(zero, c);
    // `mk_sub` normalises `(- C 1)` to `(+ C (- 1))` at CONSTRUCTION, which is
    // why the authored spelling can only ever reach the document through the
    // override ledger.
    let shifted = terms.mk_sub(vec![c, one]);
    let atom = terms.mk_le(zero, shifted);
    let negated_atom = terms.mk_not_raw(atom);
    Fixture {
        terms,
        positive,
        atom,
        negated_atom,
    }
}

/// The proof AY builds for that query: a theory lemma, then two
/// `th_resolution` steps down to the empty clause.
fn full_proof(fixture: &mut Fixture) -> Proof {
    let not_positive = fixture.terms.mk_not_raw(fixture.positive);
    let mut built = Proof::new();
    built.add_step(ProofStep::Assume(fixture.positive));
    built.add_step(ProofStep::Assume(fixture.negated_atom));
    let lemma = built.add_rule_step(
        AletheRule::Hole,
        vec![not_positive, fixture.atom],
        Vec::new(),
        Vec::new(),
    );
    let derived = built.add_rule_step(
        AletheRule::ThResolution,
        vec![fixture.atom],
        vec![lemma, ProofId(0)],
        Vec::new(),
    );
    built.add_rule_step(
        AletheRule::ThResolution,
        Vec::new(),
        vec![derived, ProofId(1)],
        Vec::new(),
    );
    built
}

fn scope(proof: &Proof) -> Vec<TermId> {
    let mut scope = Vec::new();
    for step in &proof.steps {
        match step {
            ProofStep::Assume(term) => scope.push(*term),
            ProofStep::TheoryLemma { clause, .. } => scope.extend(clause.iter().copied()),
            ProofStep::Step { clause, args, .. } => {
                scope.extend(clause.iter().copied());
                scope.extend(args.iter().copied());
            }
            _ => {}
        }
    }
    scope
}

fn export(
    fixture: &Fixture,
    proof: &Proof,
    overrides: &DetHashMap<TermId, String>,
) -> Result<String, AlethePrintError> {
    try_export_alethe_with_problem_scope_and_overrides(
        proof,
        &fixture.terms,
        &scope(proof),
        Some(overrides),
    )
}

/// THE DEFECT. The authored spelling reaches the assumed literal and nothing
/// else, so the pivot prints two ways. Without the judgement this exported a
/// document the external checker refuses while every internal signal read
/// green; with it, the bridge states the missing link.
#[test]
fn a_pivot_that_prints_two_spellings_is_bridged_not_shipped() {
    let mut fixture = fixture();
    let proof = full_proof(&mut fixture);
    let mut overrides = DetHashMap::default();
    overrides.insert(fixture.negated_atom, "(not (<= 0 (- C 1)))".to_string());

    let output = export(&fixture, &proof, &overrides).expect("the bridged step must export");
    assert!(
        output.contains("(assume t1 (not (<= 0 (- C 1))))"),
        "the assumed literal must keep the problem's own spelling:\n{output}"
    );
    assert!(
        output.contains(
            "(step t4.p (cl (not (<= 0 (+ C (- 1)))) (<= 0 (- C 1))) :rule la_generic :args (1 1))"
        ),
        "the two spellings must be linked by a checked linear tautology:\n{output}"
    );
    assert!(
        output.contains("(step t4 (cl) :rule resolution :premises (t3 t4.p t1))"),
        "the repaired step must cite the bridge between its original premises:\n{output}"
    );
}

/// The differential. With the override absent, both occurrences print the
/// canonical spelling, the printed replay succeeds, and the step must render
/// byte-identically to what it rendered before this guard existed. A guard
/// that fires on correct steps destroys evidence.
#[test]
fn a_pivot_that_prints_one_spelling_renders_unchanged() {
    let mut fixture = fixture();
    let proof = full_proof(&mut fixture);
    let overrides = DetHashMap::default();

    let output = export(&fixture, &proof, &overrides).expect("an aligned pivot must export");
    assert!(
        output.contains("(step t4 (cl) :rule th_resolution :premises (t3 t1))"),
        "an aligned pivot must keep the stock rendering:\n{output}"
    );
    assert!(
        !output.contains("t4.p"),
        "no bridge may be inserted into a step that already replays:\n{output}"
    );
}

/// A divergence the linear-arithmetic bridge cannot reach must DECLINE, not
/// ship. An honest `no` outranks a green flag with nothing behind it.
#[test]
fn an_unbridgeable_printed_pivot_declines_the_export() {
    let mut fixture = fixture();
    let proof = full_proof(&mut fixture);
    let mut overrides = DetHashMap::default();
    // A spelling that is NOT a linear comparison of the same content: the
    // bridge predicate refuses it, so there is nothing honest left to emit.
    overrides.insert(fixture.negated_atom, "(not (p C))".to_string());

    let error = export(&fixture, &proof, &overrides)
        .expect_err("an unbridgeable printed pivot must not export");
    assert!(
        matches!(
            &error,
            AlethePrintError::InvalidSurfaceStep { id, reason }
                if id.0 == 4 && reason.contains("printed resolution pivot")
        ),
        "expected a printed-pivot decline, got {error:?}"
    );
    // The decline NAMES the literal it could not discharge. Without it the
    // operator is left diffing two clauses of 43 literals by hand — which is
    // exactly the position QF_UF `iso_icl641` put this pass in on 2026-09-18.
    let AlethePrintError::InvalidSurfaceStep { reason, .. } = &error else {
        unreachable!("matched above")
    };
    assert!(
        reason.contains("starting at `"),
        "the decline must name the undischarged literal: {reason}"
    );
}

/// The OTHER differential, and the one that refuted the first version of this
/// guard. Two spellings of one bit-vector constant are one term to the external
/// checker's PARSER, so a step whose pivot prints `#b0000` on one side and
/// `(_ bv0 4)` on the other is `valid` and must render unchanged.
///
/// MEASURED on AY's own `bv_identity_collapse` refutation, which assumes the
/// problem's `(_ bv0 4)` spelling, derives the canonical `#b0000` one and
/// resolves the two: pinned carcara answers `valid`. A byte-wise judgement
/// declines that document. Delete the spelling normalisation and this test
/// fails with an export refusal.
#[test]
fn two_spellings_of_one_bitvector_constant_are_not_a_divergence() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::BitVec(ay_core::BitVecSort { width: 4 }));
    let zero = terms.mk_bitvec(BigInt::from(0), 4);
    let atom = terms.mk_eq(x, zero);
    let negated = terms.mk_not_raw(atom);

    let mut proof = Proof::new();
    proof.add_step(ProofStep::Assume(negated));
    let derived = proof.add_rule_step(AletheRule::Hole, vec![atom], Vec::new(), Vec::new());
    proof.add_rule_step(
        AletheRule::ThResolution,
        Vec::new(),
        vec![derived, ProofId(0)],
        Vec::new(),
    );

    let mut overrides = DetHashMap::default();
    overrides.insert(negated, "(not (= x (_ bv0 4)))".to_string());
    let output = try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        &terms,
        &[negated, atom],
        Some(&overrides),
    )
    .expect("two spellings of one constant are one term to the checker");
    assert!(
        output.contains("(assume t0 (not (= x (_ bv0 4))))"),
        "the assumed literal must keep the problem's own spelling:\n{output}"
    );
    assert!(
        output.contains("(step t2 (cl) :rule th_resolution :premises (t1 t0))"),
        "a spelling difference the checker's parser collapses is not a divergence:\n{output}"
    );
}

#[test]
fn printed_literals_decode_through_their_not_shells() {
    assert_eq!(
        decode_printed_literal("(not (not (<= 0 x)))"),
        Some(("(<= 0 x)".to_string(), 2))
    );
    assert_eq!(decode_printed_literal("p"), Some(("p".to_string(), 0)));
}

#[test]
fn the_recorded_conclusion_is_the_command_that_binds_the_id() {
    // A bridge emits several commands; only the one NAMED by the id is what an
    // external checker binds to it.
    let rendered = "(step t7.a (cl x) :rule hole)\n(step t7 (cl a (not b)) :rule resolution :premises (t7.a t3))";
    assert_eq!(
        printed_conclusion_of(ProofId(7), rendered),
        Some(vec!["a".to_string(), "(not b)".to_string()])
    );
    assert_eq!(
        printed_conclusion_of(ProofId(7), "(assume t7 (< 0 C))"),
        Some(vec!["(< 0 C)".to_string()])
    );
    // An `anchor` binds no clause to its own id here, and a missing record must
    // read as "unreadable" — a hole for whatever cites it — never as approval.
    assert_eq!(
        printed_conclusion_of(ProofId(7), "; t7 array_ext_diff_intro witness"),
        None
    );
}

/// The tenth false green, REOPENED by a newline (2026-09-16, build 9706): a
/// legal quoted symbol `|g\nh|` inside the clause of the command that binds
/// the id. The line scan this ledger used to run found no balanced clause on
/// the line beginning `(step t19 `, recorded nothing, and both ledger
/// consumers took their "premise not recorded → unchanged" path — the `or`
/// over the printed implication shipped under `unproved_steps=0
/// ay_self_checkable=yes` and pinned carcara refused it at `t20`. The
/// command reader sees one command, whatever lines it spans.
#[test]
fn a_conclusion_spanning_lines_is_recorded_as_one_command() {
    let rendered =
        "(step t19 (cl (=> (>= c 0) (P (|g\nh| c)))) :rule resolution :premises (t18 t16))";
    assert_eq!(
        printed_conclusion_of(ProofId(19), rendered),
        Some(vec!["(=> (>= c 0) (P (|g\nh| c)))".to_string()])
    );
    // A string literal spanning lines, likewise.
    assert_eq!(
        printed_conclusion_of(ProofId(0), "(assume t0 (= s \"a\nb\"))"),
        Some(vec!["(= s \"a\nb\")".to_string()])
    );
    // And the binding command is found whichever line it starts on.
    let rendered = "(step t7.a (cl (|x\ny|)) :rule hole)\n(step t7 (cl a (not b)) :rule resolution :premises (t7.a t3))";
    assert_eq!(
        printed_conclusion_of(ProofId(7), rendered),
        Some(vec!["a".to_string(), "(not b)".to_string()])
    );
}

/// Render the fixture proof's steps `0..n` through `format_step` on a
/// prepared printer, so the ledger holds exactly what the document would.
fn render_prefix(printer: &AlethePrinter<'_>, proof: &Proof, n: usize) {
    for (index, step) in proof.steps.iter().take(n).enumerate() {
        printer
            .format_step(step, ProofId(index as u32))
            .expect("the prefix renders");
    }
}

/// THE SECOND RULE. A premise the ledger holds as unreadable, or past its
/// bounds, or that it never recorded while active, is a premise this
/// judgement cannot read — and a step it cannot read it cannot approve. The
/// answer is the honest hole over the step's own clause, in a published
/// document; until 2026-09-16 it was the step UNCHANGED.
#[test]
fn an_unrecorded_premise_declines_the_judged_step_to_a_hole() {
    let mut fixture = fixture();
    let proof = full_proof(&mut fixture);
    let overrides = DetHashMap::default();
    let printer = AlethePrinter::new_with_overrides(&fixture.terms, Some(&overrides));
    printer.prepare_proof(&proof).expect("prepare");
    render_prefix(&printer, &proof, 3);
    let (clause, premises) = (vec![fixture.atom], [ProofId(2), ProofId(0)]);
    let clause_str = printer.format_clause(&clause);
    // Control: with both premises recorded the printed replay holds and the
    // step renders unchanged.
    assert_eq!(
        printer.judge_printed_resolution(ProofId(3), &clause, &clause_str, &premises),
        Ok(None)
    );
    for entry in [PrintedClause::Unreadable, PrintedClause::Unbounded] {
        printer
            .printed_step_clauses
            .borrow_mut()
            .insert(ProofId(2), entry.clone());
        let rendered = printer
            .judge_printed_resolution(ProofId(3), &clause, &clause_str, &premises)
            .expect("a published step, never a refused export")
            .expect("a hole, never unchanged");
        assert!(
            rendered.starts_with("(step t3 (cl ") && rendered.ends_with(":rule hole)"),
            "{entry:?}: {rendered}"
        );
    }
    printer
        .printed_step_clauses
        .borrow_mut()
        .remove(&ProofId(2));
    let rendered = printer
        .judge_printed_resolution(ProofId(3), &clause, &clause_str, &premises)
        .expect("published")
        .expect("a never-recorded premise while the ledger is active is a hole");
    assert!(rendered.ends_with(":rule hole)"), "{rendered}");
    // An inactive ledger — an isolated helper — records nothing and judges
    // nothing: behaviour unchanged.
    let isolated = AlethePrinter::new_with_overrides(&fixture.terms, Some(&overrides));
    assert_eq!(
        isolated.judge_printed_resolution(ProofId(3), &clause, &clause_str, &premises),
        Ok(None)
    );
}

/// THE FLOOR `surface_and_pos` got on 2026-09-16, on the other judgement a
/// carried authored body reaches: when the diverging pivot is spelled by the
/// printer's own Skolem channel, the answer is the honest hole in a
/// PUBLISHED document, never a refused export. The producer's own spellings
/// (the test above this one's sibling, `an_unbridgeable_printed_pivot_declines_the_export`)
/// keep failing loud.
#[test]
fn a_printer_spelled_pivot_that_cannot_be_bridged_is_a_hole_not_a_refused_export() {
    let mut fixture = fixture();
    let proof = full_proof(&mut fixture);
    let mut overrides = DetHashMap::default();
    overrides.insert(fixture.negated_atom, "(not (p C))".to_string());
    let printer = AlethePrinter::new_with_overrides(&fixture.terms, Some(&overrides));
    printer.prepare_proof(&proof).expect("prepare");
    render_prefix(&printer, &proof, 4);
    let premises = [ProofId(3), ProofId(1)];
    // The producer's spelling: refused, as before.
    assert!(matches!(
        printer.judge_printed_resolution(ProofId(4), &[], "(cl)", &premises),
        Err(AlethePrintError::InvalidSurfaceStep { id, .. }) if id.0 == 4
    ));
    // The same divergence on a term the Skolem channel spells: the floor.
    printer
        .skolem_overrides
        .borrow_mut()
        .insert(fixture.atom, "(<= 0 (- C 1))".to_string());
    assert_eq!(
        printer.judge_printed_resolution(ProofId(4), &[], "(cl)", &premises),
        Ok(Some("(step t4 (cl) :rule hole)".to_string()))
    );
}

/// THE LEDGER'S CHARGE IS ITS RESIDENCY, not the document's repetition.
///
/// Until 2026-09-18 `record_printed_conclusion` charged every literal
/// OCCURRENCE its full text, so a clause naming one atom thirty times paid for
/// thirty copies of it. MEASURED on today's main, that is what closed the
/// ledger on the corpus's biggest refutations: over the nine worst documents of
/// `2026-09-17-printed-judgement-hole-cost.jsonl`, 4,838 of 4,883
/// judgement-caused holes read `premise ... is past the ledger's bounds` and
/// every other decline class was zero — while on `iso_icl1279` the same ledger
/// holds 1,133 distinct literals against 35,692 occurrences.
///
/// Three properties, each a one-line refutation of a way the charge could go
/// back to counting repetition.
#[test]
fn the_ledger_charges_distinct_literal_text_once() {
    let mut fixture = fixture();
    let proof = full_proof(&mut fixture);
    let overrides = DetHashMap::default();
    let printer = AlethePrinter::new_with_overrides(&fixture.terms, Some(&overrides));
    printer.prepare_proof(&proof).expect("prepare");

    // One atom, repeated. The text is charged once; the repetitions cost a
    // pointer each. A per-occurrence charge would read 40 * 64 bytes.
    let atom = "a".repeat(64);
    let repeated: Vec<String> = vec![atom.clone(); 40];
    let before = printer.printed_clause_bytes.get();
    let interned = printer
        .record_interned_clause(&repeated)
        .expect("a 40-literal clause fits");
    let one_atom = super::OwnedText::cost(atom.len()).unwrap()
        + printer.printed_clause_atom_texts.borrow().capacity()
            * std::mem::size_of::<super::PrintedAtomSlot>()
        + printer.printed_clause_atom_index.borrow().allocation_size()
        + printer.printed_clause_bodies.borrow().allocation_size();
    let per_occurrence = 40 * std::mem::size_of::<super::PrintedAtomId>();
    assert_eq!(
        printer.printed_clause_bytes.get() - before,
        one_atom + per_occurrence
    );
    assert_eq!(printer.printed_clause_atom_texts.borrow().len(), 1);
    // And the interned clause still has all forty literals, in order, every
    // one of them resolving back to the text that was recorded.
    assert_eq!(interned.len(), 40);
    let texts = printer
        .printed_atom_texts(&interned)
        .expect("every recorded id names an atom");
    assert_eq!(texts.len(), 40);
    assert!(texts.iter().all(|literal| &**literal == atom.as_str()));

    // A second clause over the SAME atom charges no text at all.
    let before = printer.printed_clause_bytes.get();
    printer
        .record_interned_clause(&[atom.clone(), atom.clone()])
        .expect("fits");
    assert_eq!(
        printer.printed_clause_bytes.get() - before,
        2 * std::mem::size_of::<super::PrintedAtomId>()
    );
    assert_eq!(printer.printed_clause_atom_texts.borrow().len(), 1);

    // A clause that does not fit interns NOTHING: the count and the table it
    // describes stay in step, so the next clause is judged against the truth.
    printer
        .printed_clause_bytes
        .set(super::MAX_RECORDED_PRINTED_BYTES);
    let atoms_before = printer.printed_clause_atom_texts.borrow().len();
    let bytes_before = printer.printed_clause_bytes.get();
    assert_eq!(
        printer.record_interned_clause(&["fresh-atom".to_string()]),
        None
    );
    assert_eq!(
        printer.printed_clause_atom_texts.borrow().len(),
        atoms_before
    );
    assert_eq!(printer.printed_clause_bytes.get(), bytes_before);
}

/// The two shapes a judged resolution reaches the printer in: the tracker's
/// own `ProofStep::Resolution` (rendered by `format_resolution_step`) and a
/// generic `th_resolution` step (rendered by `format_generic_step`). The
/// export loop's per-step exhaustion check sits in the generic arm only, so
/// the misreport this module guards against lived on the first shape.
#[derive(Clone, Copy, Debug)]
enum Shape {
    Tracker,
    Generic,
}

/// Three Boolean steps whose resolution the judgement approves outright:
/// `(cl p q)`, `(cl (not p) r)`, then `(cl q r)` from the two.
fn boolean_resolution_proof(terms: &mut TermStore, shape: Shape) -> (Proof, &'static str) {
    let p = terms.mk_var("p", Sort::Bool);
    let q = terms.mk_var("q", Sort::Bool);
    let r = terms.mk_var("r", Sort::Bool);
    let not_p = terms.mk_not_raw(p);
    let mut proof = Proof::new();
    let left = proof.add_rule_step(AletheRule::Hole, vec![p, q], Vec::new(), Vec::new());
    let right = proof.add_rule_step(AletheRule::Hole, vec![not_p, r], Vec::new(), Vec::new());
    let expected = match shape {
        Shape::Tracker => {
            proof.add_resolution(vec![q, r], p, left, right);
            "(step t2 (cl q r) :rule resolution :premises (t0 t1))"
        }
        Shape::Generic => {
            proof.add_rule_step(
                AletheRule::ThResolution,
                vec![q, r],
                vec![left, right],
                Vec::new(),
            );
            "(step t2 (cl q r) :rule th_resolution :premises (t0 t1))"
        }
    };
    (proof, expected)
}

/// THE CHARGE. A judged resolution's conclusion is rendered ONCE and the
/// emission work budget is charged once for it. Until 2026-09-19 the
/// judgement rendered the clause to read it and the caller rendered it again
/// to ship it, and on a document sitting at 98 % of the synthesized-default
/// budget the second charge destroyed the export (QF_UF
/// `QG-classification/qg5/iso_icl641`, 20.7 MB, published by the base).
///
/// Measured as a differential on one printer: the step rendered with the
/// judgement ACTIVE must cost exactly what it costs with the ledger switched
/// off — the specialized bridges and the one rendering — once the literal
/// identities are memoised; and the judgement's one-time cost is exactly the
/// distinct premise literal text it reads.
#[test]
fn a_judged_resolution_charges_its_conclusion_once() {
    for shape in [Shape::Tracker, Shape::Generic] {
        let mut terms = TermStore::new();
        let (proof, expected) = boolean_resolution_proof(&mut terms, shape);
        let overrides = DetHashMap::default();
        let printer = AlethePrinter::new_with_overrides(&terms, Some(&overrides));
        printer.prepare_proof(&proof).expect("prepare");
        render_prefix(&printer, &proof, 2);
        let step = &proof.steps[2];
        let charge = |render: &dyn Fn() -> String| {
            let before = printer.work_used();
            let rendered = render();
            assert_eq!(rendered, expected, "{shape:?}");
            printer.work_used() - before
        };
        let render = || printer.format_step(step, ProofId(2)).expect("renders");

        // First rendering: the judgement reads each distinct premise literal
        // for the first time — `p`, `q`, `(not p)`, `r` — charged once each
        // where the text is read (`printed_literal_identity`), never again.
        let first = charge(&render);
        // Second rendering: every identity is a memo hit.
        let second = charge(&render);
        assert_eq!(
            first - second,
            ("p".len() + "q".len() + "(not p)".len() + "r".len()) as u64,
            "{shape:?}"
        );

        // The same step with the judgement switched off: the caller's own
        // bridges and its ONE rendering of the conclusion.
        printer.printed_clause_ledger_active.set(false);
        let unjudged = charge(&render);
        printer.printed_clause_ledger_active.set(true);
        assert!(unjudged > 0);
        assert_eq!(
            second, unjudged,
            "{shape:?}: a judged resolution charges its conclusion once; the judgement adds no \
             rendering"
        );
    }
}

/// THE REPORT. Whatever budget the export runs under, an exhausted budget is
/// reported as `EmissionBudgetExhausted` — never as a printed divergence.
/// Past exhaustion the renderer writes `@a2b_emission_budget_exhausted` in
/// place of every term, and until 2026-09-19 a judgement that ran over such
/// a conclusion refused the export as "the printed premises do not eliminate
/// the printed resolution pivot": a diagnosis of a divergence that did not
/// exist, in place of the exhaustion that did (iso_icl641, `t4482`, 32 of 43
/// literals placeholders). The sweep covers every budget from zero up to the
/// first one the document fits in, so every exhaustion point — inside the
/// conclusion, inside a premise, at a step boundary — is exercised, on both
/// shapes.
#[test]
fn an_exhausted_budget_is_reported_as_exhaustion_at_every_budget() {
    for shape in [Shape::Tracker, Shape::Generic] {
        let mut terms = TermStore::new();
        let (proof, expected) = boolean_resolution_proof(&mut terms, shape);
        let overrides = DetHashMap::default();
        let scope = scope(&proof);
        let mut published_at = None;
        for budget in 0..4096u64 {
            match try_export_alethe_with_problem_scope_overrides_and_budget(
                &proof,
                &terms,
                &scope,
                Some(&overrides),
                Some(budget),
            ) {
                Ok(document) => {
                    assert!(
                        document.contains(expected),
                        "{shape:?} budget {budget}: {document}"
                    );
                    published_at = Some(budget);
                    break;
                }
                Err(AlethePrintError::EmissionBudgetExhausted {
                    budget: reported, ..
                }) => {
                    assert_eq!(reported, budget);
                }
                Err(other) => panic!(
                    "{shape:?} budget {budget}: an exhausted budget must be reported as \
                     exhaustion, got {other:?}"
                ),
            }
        }
        let published_at = published_at.expect("the document fits in some budget under 4096");
        assert!(published_at > 0, "a zero budget must exhaust");
        // And the unbudgeted export is the same document.
        let unbudgeted = try_export_alethe_with_problem_scope_overrides_and_budget(
            &proof,
            &terms,
            &scope,
            Some(&overrides),
            None,
        )
        .expect("unbudgeted");
        let budgeted = try_export_alethe_with_problem_scope_overrides_and_budget(
            &proof,
            &terms,
            &scope,
            Some(&overrides),
            Some(published_at),
        )
        .expect("fits");
        assert_eq!(budgeted, unbudgeted);
    }
}
