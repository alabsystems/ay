// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Negated goal conjunctions the raw-root ground closure refutes
//! (`executor/proof/authored_ground_closure/goal.rs`): `and_neg` states one
//! `(not ci)` per conjunct POSITION, and each distinct conjunct is resolved
//! away once against the unit the closure derived for it.

use super::ground_closure::trust_free_document;
use super::{
    carcara_verdict_without_allowances, require_carcara_or_skip, run_carcara_trust_free,
    CarcaraVerdict,
};
use ntest::timeout;

/// model-checker-consumer's `realloc` validation queries (`repro_w41/r2.smt2`, reduced and
/// renamed) restate authored conjuncts inside their negated claim:
/// `(not (= sb8 #x0..0))` is a NEGATED conjunct and `(= f12 f3)` occurs
/// twice. Under the pin `f3 = #x0000004200000000` the early array/BV
/// preprocessing folds the claim's guarded `ite` chains into `f5`, `(not f6)`
/// and a short disjunction that no recorded rewrite reaches, so the incumbent
/// rests on premiseless `trust` steps. The closure decided the claim, but its
/// emission declined both conjunct shapes, and the answer under
/// `:produce-proofs` was `unknown (incomplete self-check-rejected)` (`step t7
/// uses unverified trust rule`, a628c3b2a). The `Opt` declaration only mirrors
/// r2's prelude: without it the fixture answers and certifies the same.
const RESTATED_CLAIM: &str = r#"
(set-logic ALL)
(declare-datatype Opt ((None) (Some (val (_ BitVec 64)))))
(declare-fun f2 () (_ BitVec 64))
(declare-fun f3 () (_ BitVec 64))
(declare-fun f12 () (_ BitVec 64))
(declare-fun f5 () Bool)
(declare-fun f6 () Bool)
(declare-fun sb8 () (_ BitVec 64))
(declare-fun sb36 () (_ BitVec 64))
(declare-const ov (Array (_ BitVec 32) Bool))
(assert (and (= f12 f3) (= f2 f3) (= f2 #x0000004200000000)
  (ite (= ((_ extract 63 32) f3) (_ bv9 32)) (= f5 (not (= (bvadd sb8 ((_ zero_extend 32) ((_ extract 31 0) f3))) (_ bv0 64)))) (ite (= ((_ extract 63 32) f3) (_ bv68 32)) (= f5 (not (= (bvadd sb36 ((_ zero_extend 32) ((_ extract 31 0) f3))) (_ bv0 64)))) (= f5 (not (= f3 (_ bv0 64))))))
  (ite (= ((_ extract 63 32) f3) (_ bv9 32)) (= f6 (= (bvadd sb8 ((_ zero_extend 32) ((_ extract 31 0) f3))) (_ bv0 64))) (ite (= ((_ extract 63 32) f3) (_ bv68 32)) (= f6 (= (bvadd sb36 ((_ zero_extend 32) ((_ extract 31 0) f3))) (_ bv0 64))) (= f6 (= f3 (_ bv0 64)))))
  (not (= sb8 (_ bv0 64)))
  (not (= sb36 (_ bv0 64)))
  (or (bvule (bvadd sb8 (_ bv16 64)) sb36) (bvule (bvadd sb36 (_ bv16 64)) sb8))
  (= ov (store ((as const (Array (_ BitVec 32) Bool)) true) (_ bv66 32) true))
  (not (and (= (concat (_ bv67 32) (_ bv0 32)) (_ bv287762808832 64))
            (= (store ov ((_ extract 63 32) (concat (_ bv66 32) (_ bv0 32))) false) (store (store ((as const (Array (_ BitVec 32) Bool)) true) (_ bv66 32) true) (_ bv66 32) false))
            (= f12 f3)
            (ite (= ((_ extract 63 32) f3) (_ bv9 32)) (= f5 (not (= (bvadd sb8 ((_ zero_extend 32) ((_ extract 31 0) f3))) (_ bv0 64)))) (ite (= ((_ extract 63 32) f3) (_ bv68 32)) (= f5 (not (= (bvadd sb36 ((_ zero_extend 32) ((_ extract 31 0) f3))) (_ bv0 64)))) (= f5 (not (= f3 (_ bv0 64))))))
            (ite (= ((_ extract 63 32) f3) (_ bv9 32)) (= f6 (= (bvadd sb8 ((_ zero_extend 32) ((_ extract 31 0) f3))) (_ bv0 64))) (ite (= ((_ extract 63 32) f3) (_ bv68 32)) (= f6 (= (bvadd sb36 ((_ zero_extend 32) ((_ extract 31 0) f3))) (_ bv0 64))) (= f6 (= f3 (_ bv0 64)))))
            (not (= sb8 (_ bv0 64)))
            (not (= sb36 (_ bv0 64)))
            (or (bvule (bvadd sb8 (_ bv16 64)) sb36) (bvule (bvadd sb36 (_ bv16 64)) sb8))
            (= f2 f3)
            (= f12 f3)))))
(check-sat)
"#;

#[test]
#[timeout(120_000)]
fn a_claim_restating_negated_and_repeated_conjuncts_is_carcara_valid() {
    let label = "ground_closure_restated_claim";
    let proof = trust_free_document(RESTATED_CLAIM, label, &["and_neg", "and_pos"]);
    let Some(carcara) = require_carcara_or_skip() else {
        return;
    };
    assert!(
        run_carcara_trust_free(&carcara, label, RESTATED_CLAIM, &proof),
        "{label}: carcara must answer a literal `valid`"
    );
}

/// NEGATIVE TWIN of [`RESTATED_CLAIM`]: without the authored fact
/// `(not (= sb8 #x0..0))` the claim's restated negated conjunct can fail
/// (`sb8 = 0`), so the query is satisfiable (z3 5.1.0). The emission resolves
/// that conjunct against a unit the closure derived, never against the claim.
#[test]
#[timeout(120_000)]
fn a_restated_negated_conjunct_without_its_authored_fact_stays_sat() {
    let unpinned = RESTATED_CLAIM.replacen("  (not (= sb8 (_ bv0 64)))\n", "", 1);
    assert_ne!(unpinned, RESTATED_CLAIM);
    let commands = ay_frontend::parse(&format!("(set-option :produce-proofs true)\n{unpinned}"))
        .expect("parse SMT-LIB script");
    let mut exec = ay_dpll::Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute SMT-LIB script");
    assert_eq!(outputs, ["sat"], "the claim can fail at sb8 = 0");
}

/// At the checker boundary the `and_neg` step's double-negated literal is
/// re-derived by Carcara, not taken on faith: naming another conjunct there
/// is refused. It tampers with the certified [`RESTATED_CLAIM`] document, so
/// it needs the emission the positive test above pins.
#[test]
#[timeout(120_000)]
fn a_forged_double_negated_and_neg_literal_is_refused_by_carcara() {
    let label = "ground_closure_restated_claim_tamper";
    let proof = trust_free_document(RESTATED_CLAIM, label, &["and_neg"]);
    let Some(carcara) = require_carcara_or_skip() else {
        return;
    };
    let zero = "#b0000000000000000000000000000000000000000000000000000000000000000";
    let negated = format!("(not (not (= sb8 {zero})))");
    let (lines, forged): (Vec<&str>, Vec<String>) = proof
        .lines()
        .map(|line| {
            if line.contains(":rule and_neg") {
                (
                    line,
                    line.replacen(&negated, &format!("(not (not (= sb36 {zero})))"), 1),
                )
            } else {
                (line, line.to_string())
            }
        })
        .unzip();
    assert_ne!(lines.join("\n"), forged.join("\n"), "{proof}");
    assert_eq!(
        carcara_verdict_without_allowances(&carcara, label, RESTATED_CLAIM, &forged.join("\n")),
        CarcaraVerdict::Invalid
    );
}

/// NEGATIVE TWIN of the emission's one decline: two DISTINCT conjuncts over
/// one atom, `p` beside `(not (not p))`. Their `and_neg` literals `(not p)`
/// and `(not (not (not p)))` decode to ONE literal in the strict checker's
/// parity-decoded resolution, so resolving each against its own unit would
/// state a clause that is not the resolvent. The closure declines that shape
/// (the same facts with the claim `(and p p ..)` or `(and (not (not p)) ..)`
/// commit a Carcara-`valid` refutation); what is published instead must never
/// be a document Carcara refuses. The query is unsat (z3 5.1.0); measured with
/// the emission change, `ay --proof` publishes a `holey` document, as on
/// a628c3b2a, and `(get-proof)` refuses the export.
const ATOM_UNDER_BOTH_PARITIES: &str = r#"
(set-logic QF_UFBV)
(declare-const a (_ BitVec 8))
(declare-const b (_ BitVec 8))
(declare-fun f ((_ BitVec 8)) (_ BitVec 8))
(declare-const p Bool)
(assert (and (= a b) p (not (not p)) (not (and p (not (not p)) (= (f a) (f b))))))
(check-sat)
"#;

#[test]
#[timeout(120_000)]
fn an_atom_restated_under_both_parities_never_publishes_a_refused_document() {
    let label = "ground_closure_atom_under_both_parities";
    let script =
        format!("(set-option :produce-proofs true)\n{ATOM_UNDER_BOTH_PARITIES}\n(get-proof)\n");
    let commands = ay_frontend::parse(&script).expect("parse SMT-LIB script");
    let mut exec = ay_dpll::Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute SMT-LIB script");
    assert_eq!(
        outputs.first().map(String::as_str),
        Some("unsat"),
        "{outputs:?}"
    );
    let proof = outputs.last().expect("proof output");
    if proof.contains("UNVERIFIABLE PROOF") {
        // The exporter's fail-closed refusal publishes no document.
        return;
    }
    let Some(carcara) = require_carcara_or_skip() else {
        return;
    };
    assert_ne!(
        carcara_verdict_without_allowances(&carcara, label, ATOM_UNDER_BOTH_PARITIES, proof),
        CarcaraVerdict::Invalid,
        "{label}: a published document must never be one Carcara refuses:\n{proof}"
    );
}
