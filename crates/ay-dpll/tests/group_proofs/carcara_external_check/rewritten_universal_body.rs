// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Authored formulas whose elaboration rewrote them, checked by pinned
//! carcara (#screened-surface-gaps).
//!
//! Gaps the wire screen could not see, because they only appear after the
//! authored surface is restored. MEASURED at 938ec0327:
//!
//! * a top-level universal whose body is not an authored `or`/`=>` over
//!   canonical literals (`(not (and g (not E)))`, `(=> G (or C R))`, a double
//!   negation, a negated `distinct`): its `forall_inst` instance keeps the
//!   authored text, and the `or` that clausifies it met the canonical clause
//!   with no derived equality. `unsat` was published with one `hole` at that
//!   `or` (`unproved_steps=1 trust_free=no`, carcara `holey`);
//! * a universal CONJUNCT of an authored `and` root: `and_pos` projects the
//!   canonical `(forall ((i_1 ..)) (or ..))` from the authored
//!   `(forall ((i ..)) (=> ..))`. The export was refused (`and_pos indexed
//!   conjunct is absent from its effective source`, naming the re-spelled
//!   `(= (g k) #b00000000)` first) and the run failed with no certificate;
//! * the same equality under a GROUND authored `assume`
//!   (`authored_assume/document_canonical.rs`): `(not (and a (not b)))` was
//!   holed and `(not (and (> n 0) (not (= n 5))))` refused.
//!
//! Each refutable fixture must now publish a document carcara 1.1.0 checks
//! trust-free as a literal `valid`; each satisfiable twin differs in the one
//! fact the refutation needs and must never publish `unsat`; a body no checked
//! schema relates must keep its honest refusal, never a document carcara
//! rejects.

use super::{
    exact_carcara_verdict, parse, require_carcara_or_skip, solve_unsat_and_get_proof, Executor,
};
use ntest::timeout;

const DECLARE_G: &str = "(set-logic ALL)\n(declare-fun g ((_ BitVec 8)) (_ BitVec 8))\n";

/// `(not (and g (not E)))`: De Morgan and a double negation.
const NEGATED_CONJUNCTION_BODY: &str = r#"
(assert (forall ((i (_ BitVec 8))) (not (and (bvult i #x05) (not (= (g i) #x01))))))
(assert (= (g #x02) #x00))
(check-sat)
"#;

/// `(=> (not (bvuge i 5)) ..)`: the guard's double negation over an unsigned
/// reversal.
const DOUBLE_NEGATION_GUARD: &str = r#"
(assert (forall ((i (_ BitVec 8))) (=> (not (bvuge i #x05)) (= (g i) #x01))))
(assert (= (g #x02) #x00))
(check-sat)
"#;

/// `(not (distinct ..))` consequent.
const NEGATED_DISTINCT_CONSEQUENT: &str = r#"
(assert (forall ((i (_ BitVec 8))) (=> (bvult i #x05) (not (distinct (g i) #x01)))))
(assert (= (g #x02) #x00))
(check-sat)
"#;

/// A ternary negated conjunction over an uninterpreted guard.
const TERNARY_NEGATED_CONJUNCTION: &str = r#"
(declare-fun p ((_ BitVec 8)) Bool)
(assert (forall ((i (_ BitVec 8))) (not (and (p i) (bvult i #x05) (not (= (g i) #x01))))))
(assert (p #x02))
(assert (= (g #x02) #x00))
(check-sat)
"#;

/// `(=> G (or C R))`: the consequent's disjunction flattens into the clause.
const IMPLICATION_OVER_DISJUNCTION: &str = r#"
(declare-fun r ((_ BitVec 8)) Bool)
(assert (forall ((i (_ BitVec 8))) (=> (bvult i #x05) (or (= (g i) #x01) (r i)))))
(assert (= (g #x02) #x00))
(assert (not (r #x02)))
(check-sat)
"#;

/// `(not (and G (not (or C R))))`: a negated disjunction under De Morgan.
const NEGATED_CONJUNCTION_OVER_DISJUNCTION: &str = r#"
(declare-fun r ((_ BitVec 8)) Bool)
(assert (forall ((i (_ BitVec 8))) (not (and (bvult i #x05) (not (or (= (g i) #x01) (r i)))))))
(assert (= (g #x02) #x00))
(assert (not (r #x02)))
(check-sat)
"#;

/// `(=> G (not (and P Q)))` over an uninterpreted sort (the adversarial
/// reviewer's `n05`).
const IMPLICATION_OVER_NEGATED_CONJUNCTION: &str = r#"
(declare-sort U 0)
(declare-fun h (U) Bool)
(declare-fun p (U) Bool)
(declare-fun q (U) Bool)
(declare-const a U)
(assert (forall ((x U)) (=> (h x) (not (and (p x) (q x))))))
(assert (h a))
(assert (p a))
(assert (q a))
(check-sat)
"#;

/// A repeated conjunct elaboration keeps once.
const REPEATED_CONJUNCT: &str = r#"
(assert (forall ((i (_ BitVec 8))) (not (and (bvult i #x05) (bvult i #x05) (not (= (g i) #x01))))))
(assert (= (g #x02) #x00))
(check-sat)
"#;

/// The universal is a conjunct of the authored root (the reviewer's `b2`).
const AND_ROOT_UNIVERSAL: &str = r#"
(declare-const k (_ BitVec 8))
(assert (and (bvult k #x05) (forall ((i (_ BitVec 8))) (=> (bvult i #x05) (= (g i) #x01))) (= (g k) #x00)))
(check-sat)
"#;

/// Both gaps at once: a negated-conjunction body under an `and` root.
const AND_ROOT_NEGATED_CONJUNCTION: &str = r#"
(declare-const k (_ BitVec 8))
(assert (and (bvult k #x05) (forall ((i (_ BitVec 8))) (not (and (bvult i #x05) (not (= (g i) #x01))))) (= (g k) #x00)))
(check-sat)
"#;

/// The canonical binder cannot be `i_1`: a global already has that name.
const AND_ROOT_BINDER_CLASH: &str = r#"
(declare-const i_1 (_ BitVec 8))
(assert (and (bvult i_1 #x05) (forall ((i (_ BitVec 8))) (=> (bvult i #x05) (= (g i) #x01))) (= (g i_1) #x00)))
(check-sat)
"#;

/// A flattened `(=> G (or C R))` body under an `and` root.
const AND_ROOT_IMPLICATION_OVER_DISJUNCTION: &str = r#"
(declare-fun r ((_ BitVec 8)) Bool)
(declare-const k (_ BitVec 8))
(assert (and (bvult k #x05) (forall ((i (_ BitVec 8))) (=> (bvult i #x05) (or (= (g i) #x01) (r i)))) (= (g k) #x00) (not (r k))))
(check-sat)
"#;

/// A ground authored `assume` (the integrity reviewer's `G1`).
const GROUND_NEGATED_CONJUNCTION: &str = r#"
(declare-const a Bool)
(declare-const b Bool)
(assert (not (and a (not b))))
(assert a)
(assert (not b))
(check-sat)
"#;

/// A ground linear-integer `assume` (the integrity reviewer's `G7`).
const GROUND_ARITHMETIC_NEGATED_CONJUNCTION: &str = r#"
(declare-const n Int)
(assert (not (and (> n 0) (not (= n 5)))))
(assert (= n 3))
(check-sat)
"#;

/// A ground `(=> x (or y z))` `assume`.
const GROUND_IMPLICATION_OVER_DISJUNCTION: &str = r#"
(declare-const x Bool)
(declare-const y Bool)
(declare-const z Bool)
(assert (=> x (or y z)))
(assert x)
(assert (not y))
(assert (not z))
(check-sat)
"#;

/// The pinned cell 5 lies outside the guard.
const NEGATED_CONJUNCTION_BODY_SAT: &str = r#"
(assert (forall ((i (_ BitVec 8))) (not (and (bvult i #x05) (not (= (g i) #x01))))))
(assert (= (g #x05) #x00))
(check-sat)
"#;

/// The consequent under the wrong polarity forbids `g i = 1`, not `g i != 1`.
const NEGATED_CONJUNCTION_WRONG_POLARITY_SAT: &str = r#"
(declare-const k (_ BitVec 8))
(assert (and (bvult k #x05) (forall ((i (_ BitVec 8))) (not (and (bvult i #x05) (= (g i) #x01)))) (= (g k) #x00)))
(check-sat)
"#;

/// `(r 2)` is left free, so the disjunction holds through it.
const IMPLICATION_OVER_DISJUNCTION_SAT: &str = r#"
(declare-fun r ((_ BitVec 8)) Bool)
(assert (forall ((i (_ BitVec 8))) (=> (bvult i #x05) (or (= (g i) #x01) (r i)))))
(assert (= (g #x02) #x00))
(check-sat)
"#;

/// `(bvult k 6)` admits `k = 5`, which the universal does not constrain.
const AND_ROOT_UNIVERSAL_SAT: &str = r#"
(declare-const k (_ BitVec 8))
(assert (and (bvult k #x06) (forall ((i (_ BitVec 8))) (=> (bvult i #x05) (= (g i) #x01))) (= (g k) #x00)))
(check-sat)
"#;

/// `(bvult i_1 6)` admits `i_1 = 5`.
const AND_ROOT_BINDER_CLASH_SAT: &str = r#"
(declare-const i_1 (_ BitVec 8))
(assert (and (bvult i_1 #x06) (forall ((i (_ BitVec 8))) (=> (bvult i #x05) (= (g i) #x01))) (= (g i_1) #x00)))
(check-sat)
"#;

/// `z` is left free.
const GROUND_IMPLICATION_OVER_DISJUNCTION_SAT: &str = r#"
(declare-const x Bool)
(declare-const y Bool)
(declare-const z Bool)
(assert (=> x (or y z)))
(assert x)
(assert (not y))
(check-sat)
"#;

/// Unsat, but the body's term-level `ite` has no schema under `bind` (the
/// integrity reviewer's `N5`).
const AND_ROOT_ITE_BODY: &str = r#"
(declare-const k (_ BitVec 8))
(assert (and (bvult k #x05) (forall ((i (_ BitVec 8))) (ite (bvult i #x05) (= (g i) #x01) true)) (= (g k) #x00)))
(check-sat)
"#;

fn problem(body: &str) -> String {
    format!("{DECLARE_G}{body}")
}

fn assert_trust_free_valid(label: &str, body: &str, rules: &[&str]) {
    let problem = problem(body);
    let proof = solve_unsat_and_get_proof(&problem, label);
    for rule in [":rule hole", ":rule trust"] {
        assert!(
            !proof.contains(rule),
            "{label}: the document must carry no `{rule}` step:\n{proof}"
        );
    }
    for rule in rules {
        assert!(
            proof.contains(&format!(":rule {rule}")),
            "{label}: expected a `{rule}` step:\n{proof}"
        );
    }
    if let Some(carcara) = require_carcara_or_skip() {
        let (valid, diagnostic) = exact_carcara_verdict(&carcara, &problem, &proof);
        assert!(
            valid,
            "{label}: pinned carcara must check the document trust-free: {diagnostic}\n{proof}"
        );
    }
}

#[test]
#[timeout(120_000)]
fn negated_universal_bodies_publish_trust_free() {
    for (label, body, rules) in [
        (
            "negated_conjunction_body",
            NEGATED_CONJUNCTION_BODY,
            &["forall_inst", "and_neg", "and_pos"][..],
        ),
        (
            "double_negation_guard",
            DOUBLE_NEGATION_GUARD,
            &["forall_inst", "not_simplify"][..],
        ),
        (
            "negated_distinct_consequent",
            NEGATED_DISTINCT_CONSEQUENT,
            &["forall_inst", "distinct_elim", "not_simplify"][..],
        ),
        (
            "ternary_negated_conjunction",
            TERNARY_NEGATED_CONJUNCTION,
            &["forall_inst", "and_neg"][..],
        ),
    ] {
        assert_trust_free_valid(label, body, rules);
    }
}

#[test]
#[timeout(120_000)]
fn flattened_universal_bodies_publish_trust_free() {
    for (label, body, rules) in [
        (
            "implication_over_disjunction",
            IMPLICATION_OVER_DISJUNCTION,
            &["forall_inst", "implies_pos", "or_pos"][..],
        ),
        (
            "negated_conjunction_over_disjunction",
            NEGATED_CONJUNCTION_OVER_DISJUNCTION,
            &["forall_inst", "and_neg", "or_pos"][..],
        ),
        (
            "implication_over_negated_conjunction",
            IMPLICATION_OVER_NEGATED_CONJUNCTION,
            &["forall_inst", "implies_pos", "and_neg"][..],
        ),
        (
            "repeated_conjunct",
            REPEATED_CONJUNCT,
            &["forall_inst", "and_neg"][..],
        ),
    ] {
        assert_trust_free_valid(label, body, rules);
    }
}

#[test]
#[timeout(120_000)]
fn universal_conjuncts_of_an_authored_root_publish_through_bind() {
    for (label, body, rules) in [
        (
            "and_root_universal",
            AND_ROOT_UNIVERSAL,
            &["and_pos", "bind", "forall_inst"][..],
        ),
        (
            "and_root_negated_conjunction",
            AND_ROOT_NEGATED_CONJUNCTION,
            &["bind", "and_neg", "forall_inst"][..],
        ),
        (
            "and_root_binder_clash",
            AND_ROOT_BINDER_CLASH,
            &["bind", "forall_inst"][..],
        ),
        (
            "and_root_implication_over_disjunction",
            AND_ROOT_IMPLICATION_OVER_DISJUNCTION,
            &["bind", "implies_pos", "forall_inst"][..],
        ),
    ] {
        assert_trust_free_valid(label, body, rules);
    }
}

/// The retry reaches the authored-`assume` bridge too.
#[test]
#[timeout(120_000)]
fn ground_authored_assumes_publish_trust_free() {
    for (label, body, rules) in [
        (
            "ground_negated_conjunction",
            GROUND_NEGATED_CONJUNCTION,
            &["and_neg", "and_pos", "equiv_pos2"][..],
        ),
        (
            "ground_arithmetic_negated_conjunction",
            GROUND_ARITHMETIC_NEGATED_CONJUNCTION,
            &["and_neg", "equiv_pos2"][..],
        ),
        (
            "ground_implication_over_disjunction",
            GROUND_IMPLICATION_OVER_DISJUNCTION,
            &["implies_pos", "or_pos", "equiv_pos2"][..],
        ),
    ] {
        assert_trust_free_valid(label, body, rules);
    }
}

#[test]
#[timeout(120_000)]
fn satisfiable_twins_never_publish_unsat() {
    for (label, body) in [
        ("negated_conjunction_body_sat", NEGATED_CONJUNCTION_BODY_SAT),
        (
            "negated_conjunction_wrong_polarity_sat",
            NEGATED_CONJUNCTION_WRONG_POLARITY_SAT,
        ),
        (
            "implication_over_disjunction_sat",
            IMPLICATION_OVER_DISJUNCTION_SAT,
        ),
        ("and_root_universal_sat", AND_ROOT_UNIVERSAL_SAT),
        ("and_root_binder_clash_sat", AND_ROOT_BINDER_CLASH_SAT),
        (
            "ground_implication_over_disjunction_sat",
            GROUND_IMPLICATION_OVER_DISJUNCTION_SAT,
        ),
    ] {
        let script = format!("(set-option :produce-proofs true)\n{}", problem(body));
        let commands = parse(&script).expect("fixture parses");
        let mut exec = Executor::new();
        let outputs = exec.execute_all(&commands).expect("fixture runs");
        assert_ne!(
            outputs.first().map(String::as_str),
            Some("unsat"),
            "{label}: a satisfiable twin was refuted"
        );
    }
}

/// NEGATIVE TWIN of the `bind` bridge: the refutation stands, and the export
/// either publishes a document carcara checks or refuses at the QUANTIFIED
/// conjunct. At 938ec0327 it refused one step earlier, at the re-spelled
/// `(= (g k) #b00000000)`; a `bind` that accepted this body would publish a
/// document carcara rejects.
#[test]
#[timeout(120_000)]
fn a_body_no_schema_relates_keeps_its_honest_refusal() {
    let label = "and_root_ite_body";
    let problem = problem(AND_ROOT_ITE_BODY);
    let script = format!("(set-option :produce-proofs true)\n{problem}\n(get-proof)\n");
    let commands = parse(&script).expect("fixture parses");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("fixture runs");
    assert_eq!(
        outputs.first().map(String::as_str),
        Some("unsat"),
        "{label}: the refutation must stand; got {outputs:?}"
    );
    let proof = outputs.last().cloned().expect("get-proof output");
    if proof.contains("(assume ") || proof.contains("(step ") {
        if let Some(carcara) = require_carcara_or_skip() {
            let (valid, diagnostic) = exact_carcara_verdict(&carcara, &problem, &proof);
            assert!(
                valid,
                "{label}: a published refutation must be carcara-valid: {diagnostic}\n{proof}"
            );
        }
        return;
    }
    let refused_conjunct = proof
        .split_once("conjunct=")
        .map(|(_, rest)| rest.trim_start_matches(['"', '\\']));
    assert!(
        proof.contains("UNVERIFIABLE PROOF")
            && proof.contains("and_pos indexed conjunct is absent from its effective source")
            && refused_conjunct.is_some_and(|conjunct| conjunct.starts_with("(forall ((i_1")),
        "{label}: the refusal must name the quantified conjunct:\n{proof}"
    );
}
