// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use std::process::Command;

const ONES: &str = "#b1111111111111111111111111111111111111111111111111111111111111111";
const MINUS_TWO: &str = "#xfffffffffffffffe";
const TWO: &str = "#x0000000000000002";
const STORE: &str =
    "(store ((as const (Array (_ BitVec 64) (_ BitVec 8))) #x07) #xffffffffffffffff #x00)";

/// The guarded instance of `signed_range64_*` at index `index`.
fn instance(index: &str) -> String {
    format!(
        "(=> (and (bvsge {index} {MINUS_TWO}) (bvslt {index} {TWO})) (= (select a {index}) #x07))"
    )
}

/// The `signed_range64_fill` lemma: the consequent under the guard's truth.
fn fill_clause() -> String {
    format!(
        "(cl (= #b00000111 (select a {ONES})) (not {}))",
        instance(ONES)
    )
}

/// The `signed_range64_missing_negative` lemma over three instances.
fn missing_negative_clause() -> String {
    let second = format!("#b{}0", "1".repeat(63));
    let third = format!("#b{}10", "0".repeat(62));
    format!(
        "(cl (not {}) (not {}) (not {}))",
        instance(ONES),
        instance(&second),
        instance(&third)
    )
}

fn definitions(body: &str) -> HashMap<String, String> {
    let mut map = HashMap::default();
    map.insert("a".to_string(), body.to_string());
    map
}

fn assert_checkable(proof: &str) {
    for forbidden in [
        ":rule hole",
        ":rule trust",
        ":rule evaluate",
        ":rule lia_generic",
    ] {
        assert!(!proof.contains(forbidden), "{forbidden} in:\n{proof}");
    }
}

/// The negations of `clause`'s literals as problem assertions and `assume`s,
/// closed by one resolution against the lowered step `t9`.
fn refutation(clause: &str, prelude: &str, proof: &str) -> (String, String) {
    let literals = split_application(clause, "cl").unwrap();
    let mut problem = format!("(set-logic ALL)\n{prelude}\n");
    let mut document = String::new();
    let mut premises = vec!["t9".to_string()];
    for (index, literal) in literals.iter().enumerate() {
        problem.push_str(&format!("(assert (not {literal}))\n"));
        document.push_str(&format!("(assume h{index} (not {literal}))\n"));
        premises.push(format!("h{index}"));
    }
    problem.push_str("(check-sat)\n");
    document.push_str(proof);
    document.push_str(&format!(
        "\n(step done (cl) :rule resolution :premises ({}))\n",
        premises.join(" ")
    ));
    (problem, document)
}

/// Pinned carcara's verdict with no allowance, or `None` when it is absent.
fn carcara_verdict(case: &str, problem: &str, proof: &str) -> Option<String> {
    if let Err(misjudged) = ay_core::pinned_carcara::pinned_carcara_can_judge(problem, proof) {
        panic!("{case}: {misjudged}\n{proof}");
    }
    let probe = Command::new("carcara").arg("--version").output();
    if !probe.is_ok_and(|probe| probe.status.success()) {
        eprintln!("carcara not on PATH: the {case} replay is skipped");
        return None;
    }
    let dir = std::env::temp_dir().join(format!("ay-closed-guard-{}-{case}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    std::fs::write(dir.join("p.smt2"), problem).unwrap();
    std::fs::write(dir.join("p.alethe"), proof).unwrap();
    let output = Command::new("carcara")
        .arg("check")
        .arg("--expand-let-bindings")
        .arg("--")
        .arg(dir.join("p.alethe"))
        .arg(dir.join("p.smt2"))
        .output()
        .unwrap();
    let stdout = String::from_utf8_lossy(&output.stdout);
    let verdict = stdout.lines().last().unwrap_or("").trim().to_string();
    let stderr = String::from_utf8_lossy(&output.stderr);
    if verdict == "valid" {
        let _ = std::fs::remove_dir_all(&dir);
    }
    Some(format!("{verdict}\n{stderr}\nkept: {}", dir.display()))
}

/// AY's own document-layer round trip (`--proof-self-check`) must accept what
/// pinned carcara accepts: the reserved `@pbbterm` resolves undeclared.
fn assert_round_trips(case: &str, problem: &str, document: &str) {
    let scope = crate::ProblemScope::from_smtlib_source(problem);
    if let Err(defect) = crate::check_alethe_document(document, &scope) {
        panic!("{case}: round-trip self-check refused the lowering: {defect}");
    }
}

/// NEGATIVE CONTROL: the replay refuses, before the checker runs (so with or
/// without carcara on PATH), the pair pinned carcara prints `valid` for only
/// through its `evaluate` defect (`ay_core::pinned_carcara`).
#[test]
#[should_panic(expected = "is not evidence")]
fn the_carcara_replay_refuses_a_document_pinned_carcara_misjudges() {
    carcara_verdict(
        "false_valid_control",
        ay_core::pinned_carcara::FALSE_VALID_CONTROL_PROBLEM,
        ay_core::pinned_carcara::FALSE_VALID_CONTROL_PROOF,
    );
}

fn assert_carcara_valid(case: &str, problem: &str, proof: &str) {
    if let Some(verdict) = carcara_verdict(case, problem, proof) {
        let first = verdict.lines().next().unwrap_or("");
        assert_eq!(first, "valid", "{case}: {verdict}");
    }
}

#[test]
fn true_signed_guard_discharges_the_guarded_instance() {
    let terms = TermStore::new();
    let printer = AlethePrinter::new(&terms);
    let clause = fill_clause();
    let proof = printer
        .lower_closed_guard_clause(ProofId(9), &clause)
        .expect("a true guard decides the instance");
    assert_checkable(&proof);
    for rule in [
        "pbblast_bvsge",
        "pbblast_bvslt",
        "implies_pos",
        "eq_symmetric",
    ] {
        assert!(proof.contains(&format!(":rule {rule}")), "{rule}:\n{proof}");
    }
    let last = proof.lines().last().unwrap();
    assert!(
        last.starts_with(&format!("(step t9 {clause} :rule ")),
        "{last}"
    );
    let prelude = "(declare-const a (Array (_ BitVec 64) (_ BitVec 8)))";
    let (problem, document) = refutation(&clause, prelude, &proof);
    assert_round_trips("fill", &problem, &document);
    assert_carcara_valid("fill", &problem, &document);
}

#[test]
fn only_a_bit_blast_lemma_reaches_the_lowering() {
    let terms = TermStore::new();
    let printer = AlethePrinter::new(&terms);
    let clause = fill_clause();
    for kind in [
        ay_core::TheoryLemmaKind::BvBitBlast,
        ay_core::TheoryLemmaKind::BvBitBlastGate {
            gate_type: ay_core::BvGateType::And,
            width: 64,
        },
    ] {
        assert!(
            printer
                .lower_closed_guard_lemma(&kind, ProofId(9), &clause)
                .is_some(),
            "{kind:?}"
        );
    }
    // Negative twin: the same valid clause under a kind AY's bit-blast
    // checker did not validate keeps the honest hole.
    assert!(printer
        .lower_closed_guard_lemma(&ay_core::TheoryLemmaKind::Generic, ProofId(9), &clause)
        .is_none());
}

#[test]
fn false_signed_guard_keeps_the_hole() {
    let terms = TermStore::new();
    let printer = AlethePrinter::new(&terms);
    // -3 is outside [-2, 2): the instance is vacuous, so the clause is not
    // valid, and no document may claim it.
    let minus_three = format!("#b{}01", "1".repeat(62));
    let clause = format!(
        "(cl (= #b00000111 (select a {minus_three})) (not {}))",
        instance(&minus_three)
    );
    assert!(printer
        .lower_closed_guard_clause(ProofId(9), &clause)
        .is_none());
}

#[test]
fn every_comparison_is_decided_by_its_signed_or_unsigned_value() {
    let terms = TermStore::new();
    let printer = AlethePrinter::new(&terms);
    let values: [u8; 6] = [0x00, 0x01, 0x7f, 0x80, 0xfe, 0xff];
    for op in [
        "bvult", "bvule", "bvugt", "bvuge", "bvslt", "bvsle", "bvsgt", "bvsge",
    ] {
        for x in values {
            for y in values {
                let (sx, sy) = (i16::from(x as i8), i16::from(y as i8));
                let (ux, uy) = (u16::from(x), u16::from(y));
                let holds = match op {
                    "bvult" => ux < uy,
                    "bvule" => ux <= uy,
                    "bvugt" => ux > uy,
                    "bvuge" => ux >= uy,
                    "bvslt" => sx < sy,
                    "bvsle" => sx <= sy,
                    "bvsgt" => sx > sy,
                    _ => sx >= sy,
                };
                let atom = format!("({op} #x{x:02x} #x{y:02x})");
                for (claim, valid) in [(atom.clone(), holds), (format!("(not {atom})"), !holds)] {
                    let clause = format!("(cl {claim})");
                    let lowered = printer.lower_closed_guard_clause(ProofId(9), &clause);
                    assert_eq!(lowered.is_some(), valid, "{clause}");
                    if let Some(proof) = lowered {
                        assert_checkable(&proof);
                    }
                }
            }
        }
    }
    // One carcara replay per operator on the signed boundary: every
    // `pbblast_bv*` relation this lowering can state is re-derived once.
    for op in [
        "bvslt", "bvsle", "bvsgt", "bvsge", "bvult", "bvule", "bvugt", "bvuge",
    ] {
        let atom = format!("({op} #x80 #x7f)");
        let claim = if matches!(op, "bvslt" | "bvsle" | "bvugt" | "bvuge") {
            atom
        } else {
            format!("(not {atom})")
        };
        let clause = format!("(cl {claim})");
        let proof = printer
            .lower_closed_guard_clause(ProofId(9), &clause)
            .unwrap();
        let (problem, document) = refutation(&clause, "", &proof);
        assert_carcara_valid(op, &problem, &document);
    }
}

#[test]
fn nullary_definition_is_read_through_its_problem_premise() {
    let terms = TermStore::new();
    let table = definitions(STORE);
    let printer = AlethePrinter::new(&terms).with_nullary_definitions(Some(&table));
    let clause = missing_negative_clause();
    let proof = printer
        .lower_closed_guard_clause(ProofId(9), &clause)
        .expect("the store hit falsifies the first guarded instance");
    assert_checkable(&proof);
    assert!(proof.contains(&format!(" (= a {STORE}))")), "{proof}");
    for rule in ["arrays_idx", "pbblast_bveq", "weakening"] {
        assert!(proof.contains(&format!(":rule {rule}")), "{rule}:\n{proof}");
    }
    let prelude = format!("(define-fun a () (Array (_ BitVec 64) (_ BitVec 8)) {STORE})");
    let (problem, document) = refutation(&clause, &prelude, &proof);
    assert_round_trips("missing_negative", &problem, &document);
    assert_carcara_valid("missing_negative", &problem, &document);
}

#[test]
fn a_macro_is_opaque_without_its_premise_or_past_a_constant_base() {
    let terms = TermStore::new();
    let clause = missing_negative_clause();
    // Negative twin: the same clause with no definition table is not valid
    // over an uninterpreted `a`.
    let printer = AlethePrinter::new(&terms);
    assert!(printer
        .lower_closed_guard_clause(ProofId(9), &clause)
        .is_none());
    // A read that reaches `(as const ..)` has no pinned rule: the all-sevens
    // array falsifies no instance the printer can read.
    let table = definitions("((as const (Array (_ BitVec 64) (_ BitVec 8))) #x07)");
    let printer = AlethePrinter::new(&terms).with_nullary_definitions(Some(&table));
    assert!(printer
        .lower_closed_guard_clause(ProofId(9), &clause)
        .is_none());
}

#[test]
fn a_store_miss_is_skipped_with_arrays_row() {
    let terms = TermStore::new();
    let body = "(store (store b #x01 #x05) #x02 #x09)";
    let table = definitions(body);
    let printer = AlethePrinter::new(&terms).with_nullary_definitions(Some(&table));
    let clause = "(cl (= (select a #x01) #x05))";
    let proof = printer
        .lower_closed_guard_clause(ProofId(9), clause)
        .expect("the read skips index 2 and hits index 1");
    assert!(proof.contains(":rule arrays_row"), "{proof}");
    assert!(printer
        .lower_closed_guard_clause(ProofId(9), "(cl (not (= (select a #x01) #x05)))")
        .is_none());
    let prelude = format!(
        "(declare-const b (Array (_ BitVec 8) (_ BitVec 8)))\n(define-fun a () (Array (_ BitVec 8) (_ BitVec 8)) {body})"
    );
    let (problem, document) = refutation(clause, &prelude, &proof);
    assert_carcara_valid("store_miss", &problem, &document);
}

#[test]
fn every_connective_is_stated_with_its_exact_tautology_rule() {
    let terms = TermStore::new();
    let printer = AlethePrinter::new(&terms);
    for (case, clause, rule) in [
        (
            "and_pos",
            "(cl (not (and (bvult #x00 #x01) p)) p)",
            "and_pos",
        ),
        ("or_neg", "(cl (or (bvugt #x00 #x01) p) (not p))", "or_neg"),
        ("or_pos", "(cl (not (or (bvugt #x00 #x01) p)) p)", "or_pos"),
        (
            "implies_neg1",
            "(cl (=> (bvsgt #xff #x01) p))",
            "implies_neg1",
        ),
        (
            "implies_neg2",
            "(cl (=> p (bvsle #x80 #x00)))",
            "implies_neg2",
        ),
    ] {
        let proof = printer
            .lower_closed_guard_clause(ProofId(9), clause)
            .unwrap_or_else(|| panic!("{case}: {clause}"));
        assert_checkable(&proof);
        assert!(proof.contains(&format!(":rule {rule}")), "{case}:\n{proof}");
        let (problem, document) = refutation(clause, "(declare-const p Bool)", &proof);
        assert_carcara_valid(case, &problem, &document);
    }
}

#[test]
fn unsupported_shapes_decline() {
    let terms = TermStore::new();
    let printer = AlethePrinter::new(&terms);
    for clause in [
        "(cl)",
        "(cl p)",
        "(cl (bvslt #b1 #b0))",
        "(cl (bvsge x #x00))",
        "(cl (= #x01 #x0001))",
        "(cl (not (not (not (bvuge #x01 #x00)))))",
        "(cl (=> (bvult #x00 #x01) p q))",
    ] {
        assert!(
            printer
                .lower_closed_guard_clause(ProofId(9), clause)
                .is_none(),
            "{clause}"
        );
    }
}
