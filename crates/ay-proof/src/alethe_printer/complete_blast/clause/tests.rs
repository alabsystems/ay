// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The multi-literal lemma is the refuted conjunction, opened by `and_neg`.

use super::*;
use crate::ProofStep;
use ay_core::kani_compat::DetHashMap;
use ay_core::{TermStore, TheoryLemmaKind};
use num_bigint::BigInt;

struct ClauseFixture {
    terms: TermStore,
    x: TermId,
    zero: TermId,
    /// `(= x 0)`
    pinned: TermId,
    /// `(bvult 0 (bvmul x y))`
    positive_product: TermId,
}

/// `QF_ABV_wide_mul_unsat`'s internal lemma at width 8:
/// `(cl (not (= x 0)) (not (bvult 0 (bvmul x y))))`.
fn fixture() -> ClauseFixture {
    let mut terms = TermStore::new();
    let word = Sort::bitvec(8);
    let x = terms.mk_var("x", word.clone());
    let y = terms.mk_var("y", word.clone());
    let zero = terms.mk_bitvec(BigInt::from(0), 8);
    // Raw applications: the smart constructors would fold the identity.
    let product = terms.mk_app(Symbol::named("bvmul"), [x, y], word);
    let pinned = terms.mk_app(Symbol::named("="), [x, zero], Sort::Bool);
    let positive_product = terms.mk_app(Symbol::named("bvult"), [zero, product], Sort::Bool);
    ClauseFixture {
        terms,
        x,
        zero,
        pinned,
        positive_product,
    }
}

fn negated(terms: &mut TermStore, atoms: &[TermId]) -> Vec<TermId> {
    atoms.iter().map(|atom| terms.mk_not_raw(*atom)).collect()
}

fn blast(printer: &AlethePrinter<'_>, clause: &[TermId]) -> Option<String> {
    printer.format_bv_complete_blast_clause(ProofId(2), clause, &TheoryLemmaKind::BvBitBlast)
}

fn lemma_step(clause: Vec<TermId>, kind: TheoryLemmaKind) -> ProofStep {
    ProofStep::TheoryLemma {
        theory: "bv".to_string(),
        clause,
        farkas: None,
        kind,
        lia: None,
    }
}

#[test]
fn a_negative_conflict_clause_is_the_refuted_conjunction_opened_by_and_neg() {
    let mut f = fixture();
    let clause = negated(&mut f.terms, &[f.pinned, f.positive_product]);
    let printer = AlethePrinter::new(&f.terms);
    let document =
        blast(&printer, &clause).expect("x = 0 forces x * y = 0, so the conjunction is refuted");
    assert!(!document.contains(":rule hole"), "{document}");
    assert!(!document.contains(":rule trust"), "{document}");
    assert!(document.contains(":rule bitblast_mult"));
    let conjunction = "(and (= x #b00000000) (bvult #b00000000 (bvmul x y)))";
    assert!(document.contains(&format!(
        "(step t2.cbu (cl (not {conjunction})) :rule resolution"
    )));
    let tail: Vec<&str> = document.lines().rev().take(2).collect();
    assert_eq!(
        tail,
        [
            "(step t2 (cl (not (= x #b00000000)) (not (bvult #b00000000 (bvmul x y)))) :rule resolution :premises (t2.cban t2.cbu))",
            &format!(
                "(step t2.cban (cl {conjunction} (not (= x #b00000000)) (not (bvult #b00000000 (bvmul x y)))) :rule and_neg)"
            ),
        ]
    );
}

/// NEGATIVE TWIN: a clause that is not a theorem, a positive literal, a
/// repeated atom, or a single literal outside the unit lowering's shape never
/// reaches the conjunction lowering's output.
#[test]
fn non_theorems_and_unsupported_literals_decline() {
    let mut f = fixture();
    let one = f.terms.mk_bitvec(BigInt::from(1), 8);
    // `x = 1 /\ 0 < x` is satisfiable: the lemma is FALSE.
    let pinned_one = f.terms.mk_app(Symbol::named("="), [f.x, one], Sort::Bool);
    let positive_x = f
        .terms
        .mk_app(Symbol::named("bvult"), [f.zero, f.x], Sort::Bool);
    let false_lemma = negated(&mut f.terms, &[pinned_one, positive_x]);
    let not_pinned = f.terms.mk_not_raw(f.pinned);
    let positive_literal = vec![not_pinned, f.positive_product];
    let repeated = vec![not_pinned, not_pinned];
    let printer = AlethePrinter::new(&f.terms);
    for clause in [false_lemma, positive_literal, repeated] {
        assert_eq!(blast(&printer, &clause), None, "{clause:?}");
    }
    // Never through the unit-only entry point, and only for a bit-blast
    // lemma: another kind keeps its honest unchecked wire rule.
    let clause = negated(&mut f.terms, &[f.pinned, f.positive_product]);
    let printer = AlethePrinter::new(&f.terms);
    assert_eq!(
        printer.format_bv_complete_blast_refutation(ProofId(2), &clause),
        None
    );
    assert_eq!(
        printer.format_bv_complete_blast_clause(ProofId(2), &clause, &TheoryLemmaKind::Generic),
        None
    );
    let output = printer
        .format_step(&lemma_step(clause, TheoryLemmaKind::Generic), ProofId(2))
        .expect("the generic lemma renders");
    assert!(!output.contains(":rule and_neg"), "{output}");
    assert!(
        output.contains(":rule hole") || output.contains(":rule trust"),
        "{output}"
    );
}

/// Through the ordinary theory-lemma path the clause is the last resort
/// before the hole, and the hole is gone; a false lemma keeps it.
///
/// The shared capability predicate the executor's wire-gap screen asks does
/// NOT include this printer-only fallback (see the module docs): moving the
/// lowering into it changes which proof the executor publishes.
#[test]
fn the_bit_blast_lemma_step_prints_the_opened_conjunction_not_a_hole() {
    let mut f = fixture();
    let clause = negated(&mut f.terms, &[f.pinned, f.positive_product]);
    for kind in [
        TheoryLemmaKind::BvBitBlast,
        TheoryLemmaKind::BvBitBlastGate {
            gate_type: ay_core::BvGateType::Mul,
            width: 8,
        },
    ] {
        assert!(!crate::checked_bv_bitblast_lowering_supported(
            &f.terms, &kind, &clause, None
        ));
        let output = AlethePrinter::new(&f.terms)
            .format_step(&lemma_step(clause.clone(), kind), ProofId(2))
            .expect("the lemma renders");
        assert!(!output.contains(":rule hole"), "{output}");
        assert!(output.contains(":rule and_neg"), "{output}");
    }
    let one = f.terms.mk_bitvec(BigInt::from(1), 8);
    let pinned_one = f.terms.mk_app(Symbol::named("="), [f.x, one], Sort::Bool);
    let positive_x = f
        .terms
        .mk_app(Symbol::named("bvult"), [f.zero, f.x], Sort::Bool);
    let false_lemma = negated(&mut f.terms, &[pinned_one, positive_x]);
    let output = AlethePrinter::new(&f.terms)
        .format_step(
            &lemma_step(false_lemma, TheoryLemmaKind::BvBitBlast),
            ProofId(2),
        )
        .expect("the false lemma renders");
    assert!(output.contains(":rule hole"), "{output}");
    assert!(!output.contains(":rule and_neg"), "{output}");
}

/// An authored override that only re-spells a bit-vector literal is the SAME
/// parsed term; one that changes a value is refused at every literal.
#[test]
fn literal_respelling_binds_and_a_changed_value_is_refused() {
    let mut f = fixture();
    let clause = negated(&mut f.terms, &[f.pinned, f.positive_product]);
    for (spelling, accepted) in [("(= x #x00)", true), ("(= x #x01)", false)] {
        let mut overrides = DetHashMap::default();
        overrides.insert(f.pinned, spelling.to_string());
        let printer = AlethePrinter::new_with_overrides(&f.terms, Some(&overrides));
        let document = blast(&printer, &clause);
        assert_eq!(document.is_some(), accepted, "{spelling}");
        if let Some(document) = document {
            assert!(document.ends_with(
                "(step t2 (cl (not (= x #x00)) (not (bvult #b00000000 (bvmul x y)))) :rule resolution :premises (t2.cban t2.cbu))"
            ));
        }
    }
}

/// The clause lane, like the unit lane, is not blasted where no document is
/// observable, nor past the stop of a render asked from inside a solve
/// (`try_export_alethe_with_authored_surfaces_until`): it checked neither and
/// blasted the clause whatever its caller asked. The twin: a stop that never
/// fires leaves the exporter's document.
#[test]
fn an_unasked_or_stopped_clause_is_not_blasted() {
    use crate::alethe_printer::CompleteBlastAsk;
    use crate::resolution_dag_memo::{reset_resolution_dag_memo, resolution_dag_memo_counters};

    let mut f = fixture();
    let clause = negated(&mut f.terms, &[f.pinned, f.positive_product]);
    let exported = blast(&AlethePrinter::new(&f.terms), &clause).expect("the exporter blasts it");
    let idle = || false;
    let printer =
        AlethePrinter::new(&f.terms).asking_complete_blast(CompleteBlastAsk::AskedUntil(&idle));
    assert_eq!(blast(&printer, &clause), Some(exported));

    let stopped = || true;
    for ask in [
        CompleteBlastAsk::NotAsked,
        CompleteBlastAsk::AskedUntil(&stopped),
    ] {
        reset_resolution_dag_memo();
        let printer = AlethePrinter::new(&f.terms).asking_complete_blast(ask);
        assert_eq!(blast(&printer, &clause), None, "{ask:?}");
        assert_eq!(resolution_dag_memo_counters(), (0, 0), "{ask:?}");
    }
}
