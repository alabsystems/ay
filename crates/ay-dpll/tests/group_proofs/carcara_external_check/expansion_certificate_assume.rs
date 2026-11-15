// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The nested-CEGQI expansion certificate's `assume`, end to end.
//!
//! `(forall ((q Bool)) q)` is Trust's `forall-bool`. The QLRA lane publishes
//! it through its expansion certificate (`qlra.cert` = `expansion-installed`),
//! which installs its proof AFTER the ordinary assembly restored the authored
//! `assume` spellings for a different proof. The lane never paid that debt,
//! so the root printed AY's freshened binder, `(forall ((q_0 Bool)) q_0)`,
//! and every external checker refused the document at its first `assume`
//! (carcara matches premises without alpha-equivalence): measured on
//! origin/main `db768acbd`, `foreign_assumes=yes`, and Trust's checker
//! (`clean cert verify-external`) answered "assumption not present in the
//! problem".
//!
//! Every document here is judged against the INPUT TEXT, never against AY's
//! own `alethe_problem_smt2`, which renders the problem through the same
//! override table as the proof and so agrees with it by construction.

use super::run_carcara_trust_free;
use super::vacuous_binder_constant::{clean_bin, clean_verdict};
use ay_dpll::{normalize_premise_surface, Executor};
use ay_frontend::parse;
use ntest::timeout;
use std::io::Write;

/// What one `unsat` published: its document, the lane that built it, and
/// the premise `assume`s the input does not state verbatim.
struct Published {
    proof: String,
    cert: Option<String>,
    foreign: Vec<String>,
}

fn publish(problem: &str, label: &str) -> Published {
    let script = format!("(set-option :produce-proofs true)\n{problem}(get-proof)\n");
    let commands = parse(&script).expect("parse SMT-LIB script");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute SMT-LIB script");
    assert_eq!(
        outputs.first().map(String::as_str),
        Some("unsat"),
        "{label}: {outputs:?}; unknown_reason={:?}",
        exec.unknown_reason()
    );
    let proof = outputs.last().cloned().expect("proof output");
    let cert = exec
        .statistics()
        .get_string("qlra.cert")
        .map(str::to_string);
    let authored = exec
        .authored_premise_surfaces()
        .expect("every assertion is parsed, so the premise reference is complete");
    let mut scan = ay_proof::AletheDocumentScan::default();
    scan.write_all(proof.as_bytes()).expect("scan the document");
    assert!(!scan.overflowed, "{label}: premises past the scan bound");
    let foreign = scan
        .premise_assumes
        .into_iter()
        .filter(|assume| !authored.contains(&normalize_premise_surface(assume)))
        .collect();
    Published {
        proof,
        cert,
        foreign,
    }
}

/// The document is complete, assumes only the input as written, and every
/// checker on this host accepts it against the input text.
fn assert_authored_and_valid(label: &str, problem: &str, published: &Published) {
    let proof = &published.proof;
    assert!(
        published.foreign.is_empty(),
        "{label}: assumes {:?}, which the input does not state:\n{proof}",
        published.foreign
    );
    assert!(
        !proof.contains(":rule hole") && !proof.contains(":rule trust"),
        "{label}: an unchecked step is left:\n{proof}"
    );
    let scope = ay_proof::ProblemScope::from_smtlib_source(problem);
    ay_proof::check_alethe_document(proof, &scope).unwrap_or_else(|defect| {
        panic!("{label}: the Alethe document check refused: {defect:?}\n{proof}")
    });
    if let Some(carcara) = super::find_carcara() {
        assert!(
            run_carcara_trust_free(&carcara, label, problem, proof),
            "{label}: Carcara must answer a literal `valid`:\n{proof}"
        );
    }
    if let Some(clean) = clean_bin() {
        let (valid, diagnostic) = clean_verdict(&clean, label, problem, proof);
        assert!(
            valid,
            "{label}: Trust's checker refused:\n{diagnostic}\n{proof}"
        );
    }
}

/// `(label, problem, the authored binder, AY's canonical binder)`.
const AUTHORED_BINDERS: [(&str, &str, &str, &str); 3] = [
    (
        "forall-bool",
        "(set-logic UF)\n(assert (forall ((q Bool)) q))\n(check-sat)\n",
        "q",
        "q_0",
    ),
    (
        "forall-bool-trust-spelling",
        "(set-logic UF)\n(assert (forall ((__trust_u_q Bool)) __trust_u_q))\n(check-sat)\n",
        "__trust_u_q",
        "__trust_u_q_0",
    ),
    // A constant declared and asserted first moves the internal name to
    // `q_1`: the restored spelling does not depend on the variable id.
    (
        "forall-bool-after-constant",
        "(set-logic UF)\n(declare-const p Bool)\n(assert p)\n\
         (assert (forall ((q Bool)) q))\n(check-sat)\n",
        "q",
        "q_1",
    ),
];

#[test]
#[timeout(120_000)]
fn the_expansion_certificate_assumes_the_authored_binder() {
    let clean = clean_bin();
    if clean.is_none() && super::find_carcara().is_none() {
        eprintln!(
            "expansion_certificate_assume: no Carcara and no CLEAN_BIN; the documents are \
             checked in-process only"
        );
    }
    for (label, problem, binder, canonical) in AUTHORED_BINDERS {
        let published = publish(problem, label);
        let proof = &published.proof;
        assert_eq!(
            published.cert.as_deref(),
            Some("expansion-installed"),
            "{label}: the expansion certificate no longer publishes this shape:\n{proof}"
        );
        let authored = format!("(forall (({binder} Bool)) {binder})");
        let first = proof.lines().find(|line| line.starts_with("(assume "));
        assert_eq!(
            first,
            Some(format!("(assume t0 {authored})").as_str()),
            "{label}: the root is not assumed as the input wrote it:\n{proof}"
        );
        assert_authored_and_valid(label, problem, &published);

        // The document as origin/main printed it, the canonical binder in
        // place of the authored one: Trust's checker refuses it at `t0`.
        let canonical_twin = proof.replace(
            &authored,
            &format!("(forall (({canonical} Bool)) {canonical})"),
        );
        assert_ne!(&canonical_twin, proof, "{label}: twin target missing");
        if let Some(clean) = clean.as_deref() {
            let (valid, diagnostic) = clean_verdict(
                clean,
                &format!("{label}-canonical"),
                problem,
                &canonical_twin,
            );
            assert!(
                !valid,
                "{label}: Trust's checker accepted the canonical binder:\n{diagnostic}\n\
                 {canonical_twin}"
            );
        }
    }
}

/// The document origin/main `db768acbd` published for every Bool shape below
/// whose body the store folds to the binder itself.
const FOLDED_BOOL_DOCUMENT: &str = "\
(assume t0 (forall ((q_0 Bool)) q_0))
(step t1 (cl (or (not (forall ((q_0 Bool)) q_0)) false)) :rule forall_inst :args (false))
(step t2 (cl (not false)) :rule false)
(step t3 (cl (not (or (not (forall ((q_0 Bool)) q_0)) false)) (not (forall ((q_0 Bool)) q_0)) false) :rule or_pos)
(step t4 (cl (not (or (not (forall ((q_0 Bool)) q_0)) false)) false) :rule resolution :premises (t3 t0))
(step t5 (cl false) :rule resolution :premises (t4 t1))
(step t6 (cl) :rule resolution :premises (t5 t2))
";

/// The same for the Real shapes, whose body the store folds to `false`.
const FOLDED_REAL_DOCUMENT: &str = "\
(assume t0 (forall ((q_0 Real)) false))
(step t1 (cl (or (not (forall ((q_0 Real)) false)) false)) :rule forall_inst :args (0.0))
(step t2 (cl (not false)) :rule false)
(step t3 (cl (not (or (not (forall ((q_0 Real)) false)) false)) (not (forall ((q_0 Real)) false)) false) :rule or_pos)
(step t4 (cl (not (forall ((q_0 Real)) false)) false) :rule resolution :premises (t3 t1))
(step t5 (cl false) :rule resolution :premises (t4 t0))
(step t6 (cl) :rule resolution :premises (t5 t2))
";

/// The document origin/main `db768acbd` published for `(forall ((x Real))
/// (= (+ x 1) x))`: the canonical binder, numerals realified. The authored
/// spelling would assume `(+ x 1)`, which pinned carcara's proof parser
/// refuses (a numeral is `Real` only in a real-only logic's PROBLEM).
const REALIFY_PLUS_ONE_DOCUMENT: &str = "\
(assume t0 (forall ((x_0 Real)) (= x_0 (+ x_0 1.0))))
(step t1 (cl (or (not (forall ((x_0 Real)) (= x_0 (+ x_0 1.0)))) (= 0.0 (+ 0.0 1.0)))) :rule forall_inst :args (0.0))
(step t2 (cl (not (= 0.0 (+ 0.0 1.0)))) :rule la_generic :args (1))
(step t3 (cl (not (or (not (forall ((x_0 Real)) (= x_0 (+ x_0 1.0)))) (= 0.0 (+ 0.0 1.0)))) (not (forall ((x_0 Real)) (= x_0 (+ x_0 1.0)))) (= 0.0 (+ 0.0 1.0))) :rule or_pos)
(step t4 (cl (not (or (not (forall ((x_0 Real)) (= x_0 (+ x_0 1.0)))) (= 0.0 (+ 0.0 1.0)))) (not (forall ((x_0 Real)) (= x_0 (+ x_0 1.0))))) :rule resolution :premises (t3 t2))
(step t5 (cl (not (forall ((x_0 Real)) (= x_0 (+ x_0 1.0))))) :rule resolution :premises (t4 t1))
(step t6 (cl) :rule resolution :premises (t5 t0))
";

/// The same for `(forall ((x Real)) (= (+ x 2) (+ x 1)))`.
const REALIFY_PLUS_TWO_DOCUMENT: &str = "\
(assume t0 (forall ((x_0 Real)) (= (+ x_0 2.0) (+ x_0 1.0))))
(step t1 (cl (or (not (forall ((x_0 Real)) (= (+ x_0 2.0) (+ x_0 1.0)))) (= (+ 0.0 2.0) (+ 0.0 1.0)))) :rule forall_inst :args (0.0))
(step t2 (cl (not (= (+ 0.0 2.0) (+ 0.0 1.0)))) :rule la_generic :args (-1))
(step t3 (cl (not (or (not (forall ((x_0 Real)) (= (+ x_0 2.0) (+ x_0 1.0)))) (= (+ 0.0 2.0) (+ 0.0 1.0)))) (not (forall ((x_0 Real)) (= (+ x_0 2.0) (+ x_0 1.0)))) (= (+ 0.0 2.0) (+ 0.0 1.0))) :rule or_pos)
(step t4 (cl (not (forall ((x_0 Real)) (= (+ x_0 2.0) (+ x_0 1.0)))) (= (+ 0.0 2.0) (+ 0.0 1.0))) :rule resolution :premises (t3 t1))
(step t5 (cl (not (forall ((x_0 Real)) (= (+ x_0 2.0) (+ x_0 1.0))))) :rule resolution :premises (t4 t2))
(step t6 (cl) :rule resolution :premises (t5 t0))
";

/// An LRA certificate that carries one `hole` on origin/main `db768acbd`
/// (a `forall_inst` instance's arithmetic consequence). Restored, it
/// assumed the authored binder `z1` and kept the `hole`; clean refused it
/// ("accepted only as holey or incomplete"), so it keeps these bytes.
const LRA_HOLEY_PROBLEM: &str =
    include_str!("../../fixtures/expansion_certificate_assume/lra_holey_certificate.smt2");
const LRA_HOLEY_DOCUMENT: &str =
    include_str!("../../fixtures/expansion_certificate_assume/lra_holey_certificate.today.alethe");

/// Which document a family row ships.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Ships {
    /// The input's own premises, complete and accepted by every checker.
    Authored,
    /// Exactly the bytes origin/main `db768acbd` printed.
    Today(&'static str),
}

/// `(label, problem, what ships)`.
///
/// The contract for each row is EITHER an authored, valid document OR
/// today's exact bytes: the restoration is kept only when its document is
/// complete (no `hole`, no `trust`), assumes only the input as written, and
/// states no integer numeral the realify lane leaves in a `Real` binder body;
/// otherwise it is reverted. MEASURED reverts: on the composite bodies the
/// instance is the shared `false` while the authored body prints otherwise,
/// so the authored document demotes `forall_inst` to a `hole` (a bridge for
/// constant instances, as `constant_skolem_bridge.rs` gives Skolem
/// instances, is what would make them `Authored`); an LRA certificate that
/// already carried a `hole` kept it under the authored binder, which clean
/// accepts "only as holey"; and `(+ x 1)` in a `Real` binder body is a sort
/// error to pinned carcara's proof parser. A row moving from `Today` to
/// `Authored` is progress; the reverse is a regression.
const FAMILY: [(&str, &str, Ships); 10] = [
    (
        "forall-and-q-q",
        "(set-logic UF)\n(assert (forall ((q Bool)) (and q q)))\n(check-sat)\n",
        Ships::Today(FOLDED_BOOL_DOCUMENT),
    ),
    (
        "forall-eq-q-true",
        "(set-logic UF)\n(assert (forall ((q Bool)) (= q true)))\n(check-sat)\n",
        Ships::Today(FOLDED_BOOL_DOCUMENT),
    ),
    (
        "forall-not-not-q",
        "(set-logic UF)\n(assert (forall ((q Bool)) (not (not q))))\n(check-sat)\n",
        Ships::Today(FOLDED_BOOL_DOCUMENT),
    ),
    (
        "and-p-forall-bool",
        "(set-logic UF)\n(declare-const p Bool)\n\
         (assert (and p (forall ((q Bool)) q)))\n(check-sat)\n",
        Ships::Authored,
    ),
    (
        "forall-real-lt",
        "(set-logic LRA)\n(assert (forall ((q Real)) (< q q)))\n(check-sat)\n",
        Ships::Today(FOLDED_REAL_DOCUMENT),
    ),
    (
        "forall-real-not-eq",
        "(set-logic LRA)\n(assert (forall ((q Real)) (not (= q q))))\n(check-sat)\n",
        Ships::Today(FOLDED_REAL_DOCUMENT),
    ),
    (
        "lra-holey-certificate",
        LRA_HOLEY_PROBLEM,
        Ships::Today(LRA_HOLEY_DOCUMENT),
    ),
    (
        "forall-real-plus-one-numeral",
        "(set-logic LRA)\n(assert (forall ((x Real)) (= (+ x 1) x)))\n(check-sat)\n",
        Ships::Today(REALIFY_PLUS_ONE_DOCUMENT),
    ),
    (
        "forall-real-plus-two-numerals",
        "(set-logic LRA)\n(assert (forall ((x Real)) (= (+ x 2) (+ x 1))))\n(check-sat)\n",
        Ships::Today(REALIFY_PLUS_TWO_DOCUMENT),
    ),
    // The decimal twin of the row above needs no realification: authored.
    (
        "forall-real-plus-one-decimal",
        "(set-logic LRA)\n(assert (forall ((x Real)) (= (+ x 1.0) x)))\n(check-sat)\n",
        Ships::Authored,
    ),
];

#[test]
#[timeout(120_000)]
fn the_folded_family_ships_an_authored_valid_document_or_todays_bytes() {
    for (label, problem, ships) in FAMILY {
        let published = publish(problem, label);
        let proof = &published.proof;
        assert_eq!(
            published.cert.as_deref(),
            Some("expansion-installed"),
            "{label}: the expansion certificate no longer publishes this shape:\n{proof}"
        );
        // Never a respelled `false`: an authored instance keyed on the shared
        // constant would print the `false` axiom over the instance text.
        for line in proof.lines().filter(|line| line.contains(":rule false)")) {
            assert!(
                line.ends_with(" (cl (not false)) :rule false)"),
                "{label}: the `false` axiom is respelled: {line}\n{proof}"
            );
        }
        match ships {
            Ships::Today(document) => assert_eq!(
                proof.trim_end(),
                document.trim_end(),
                "{label}: neither today's document nor a valid authored one"
            ),
            Ships::Authored => assert_authored_and_valid(label, problem, &published),
        }
    }
}
