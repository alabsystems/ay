// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Authored spellings whose canonical term has a DIFFERENT Boolean shape are
//! confined to the one command that needs them, so the rest of the document
//! prints the canonical term its own clauses state.
//!
//! Three shapes kept four model-checker-consumer corpus rows from publishing a document at
//! all (the printer refused the export and the corpus gate stopped on "proof
//! lacks Alethe commands"):
//!
//! * a `forall_inst` instance printed with the substituted AUTHORED body
//!   `(=> A B)` document-wide, while later `cong`/`and_pos` steps consume the
//!   canonical `(or B' (not A'))`;
//! * an authored `assume` root `(or (distinct ..) (and (bvuge ..) ..))` over a
//!   canonical `(or (not (= ..)) (and (bvule ..) ..))`;
//! * datatype-flattened roots (`(distinct (select (data v) k) fill)` over the
//!   canonical `(not (= fill (select v!data k)))`, and `(= v2 v1)` over its
//!   field-wise expansion), whose override-free canonical text names the
//!   internal field variables no bridge can match.
//!
//! Each fixture must now publish a document pinned carcara 1.1.0 checks
//! trust-free as `valid`: no `hole`, no `trust`.
//!
//! The fourth row, `deep_vec_iteration_premise_false_unsat`, is unsatisfiable
//! only under the datatype theory (with `mkVec`/`len`/`data` uninterpreted it
//! is satisfiable), and pinned carcara has no datatype rule. Its refutation
//! assumes the selector-value expansion of `(= v0 (mkVec ..))`, which no stock
//! rule derives from the authored equation. It must keep its `unsat` verdict
//! and must NEVER publish a document the external checker rejects: at
//! 779076535 it published one refused at its first `assume`.

use super::{
    carcara_verdict_without_allowances, exact_carcara_verdict, parse, require_carcara_or_skip,
    solve_unsat_and_get_proof, workspace_root, CarcaraVerdict, Executor,
};
use ntest::timeout;

/// `v2 = v1` is flattened into four field equalities; the refutation assumes
/// that expansion and instantiates the authored implication at `k`.
const DATATYPE_EQUALITY_INSTANCE: &str = r#"
(set-logic ALL)
(declare-datatype Vec ((mkVec (ptr (_ BitVec 64)) (len (_ BitVec 64))
  (cap (_ BitVec 64)) (data (Array (_ BitVec 64) (_ BitVec 8))))))
(declare-const v1 Vec)
(declare-const v2 Vec)
(declare-const k (_ BitVec 64))
(assert (= v2 v1))
(assert (bvult k (len v1)))
(assert (forall ((i (_ BitVec 64))) (=> (bvult i (len v2)) (= (select (data v2) i) (_ bv7 8)))))
(assert (distinct (select (data v1) k) (_ bv7 8)))
(check-sat)
"#;

fn corpus_row(relative: &str) -> String {
    let path = workspace_root().join("benchmarks/smt").join(relative);
    std::fs::read_to_string(&path)
        .unwrap_or_else(|error| panic!("read corpus row {}: {error}", path.display()))
        .lines()
        .filter(|line| line.trim() != "(exit)")
        .collect::<Vec<_>>()
        .join("\n")
}

fn assert_trust_free_valid(label: &str, problem: &str) -> String {
    let proof = solve_unsat_and_get_proof(problem, label);
    for rule in [":rule hole", ":rule trust"] {
        assert!(
            !proof.contains(rule),
            "{label}: the document must carry no `{rule}` step:\n{proof}"
        );
    }
    if let Some(carcara) = require_carcara_or_skip() {
        let (valid, diagnostic) = exact_carcara_verdict(&carcara, problem, &proof);
        assert!(
            valid,
            "{label}: pinned carcara must check the document trust-free: {diagnostic}\n{proof}"
        );
    }
    proof
}

/// The authored instance appears ONLY in the `forall_inst` command; every
/// later step names the canonical disjunction.
fn instance_is_confined(proof: &str, authored_instance: &str) {
    let authored_lines: Vec<&str> = proof
        .lines()
        .filter(|line| line.contains(authored_instance))
        .collect();
    assert!(
        authored_lines
            .iter()
            .any(|line| line.contains(":rule forall_inst")),
        "the authored instance must be what `forall_inst` concludes:\n{proof}"
    );
    for line in authored_lines {
        let rule = line.split(":rule ").nth(1).unwrap_or_default();
        assert!(
            [
                "forall_inst",
                "implies_",
                "equiv_",
                "cong",
                "resolution",
                "or_",
                "and_",
                "refl",
                "trans",
                "symm",
                "pbblast_",
            ]
            .iter()
            .any(|allowed| rule.starts_with(allowed)),
            "the authored instance leaked past its bridge: {line}"
        );
        assert!(
            line.starts_with("(step t")
                && line
                    .split_whitespace()
                    .nth(1)
                    .is_some_and(|id| id.contains('.')),
            "only the bridge's own sub-steps may name the authored instance: {line}"
        );
    }
}

#[test]
#[timeout(120_000)]
fn authored_implication_instance_and_flattened_distinct_publish_trust_free() {
    let problem = corpus_row("model_checker_consumer_quantified_safety/uf_record_unsat.smt2");
    let proof = assert_trust_free_valid("instance_surface_uf_record", &problem);
    instance_is_confined(
        &proof,
        "(=> (bvult k (len v)) (= (select (data v) k) (f true x)))",
    );
    assert!(
        proof.lines().any(|line| line.starts_with("(assume ")
            && line.ends_with(" (distinct (select (data v) k) fill))")),
        "the authored `distinct` is the premise:\n{proof}"
    );
}

#[test]
#[timeout(120_000)]
fn authored_disjunction_with_unsigned_reversals_publishes_trust_free() {
    for row in [
        "model_checker_consumer_quantified_safety/wide_table72_shared_unsat.smt2",
        "model_checker_consumer_quantified_safety/wide_table136_shared_unsat.smt2",
    ] {
        let problem = corpus_row(row);
        let proof = assert_trust_free_valid(row, &problem);
        assert!(
            proof.contains(":rule pbblast_bvuge") && proof.contains(":rule pbblast_bvule"),
            "{row}: `bvuge` against the canonical `bvule` is bridged by blasting:\n{proof}"
        );
        instance_is_confined(
            &proof,
            "(and (=> (bvult j old) (= (select b j) (select a j))) (=> (and (bvuge j old) (bvult j new)) (= (select b j) ((_ extract 7 0) first))))",
        );
    }
}

#[test]
#[timeout(120_000)]
fn datatype_variable_equality_expansion_publishes_its_authored_equality() {
    let proof = assert_trust_free_valid(
        "instance_surface_datatype_equality",
        DATATYPE_EQUALITY_INSTANCE,
    );
    assert!(
        proof
            .lines()
            .any(|line| line.starts_with("(assume ") && line.ends_with(" (= v2 v1))")),
        "the authored datatype equality is the premise:\n{proof}"
    );
    assert!(
        !proof
            .lines()
            .any(|line| line.starts_with("(assume ") && line.contains("(and (= (ptr")),
        "the field-wise expansion is derived, never assumed:\n{proof}"
    );
}

#[test]
#[timeout(120_000)]
fn constructor_equation_expansion_never_publishes_a_rejected_document() {
    let label = "instance_surface_deep_vec";
    let problem = corpus_row(
        "model_checker_consumer_quantified_counterexample/deep_vec_iteration_premise_false_unsat.smt2",
    );
    let script = format!("(set-option :produce-proofs true)\n{problem}\n(get-proof)\n");
    let commands = parse(&script).expect("parse corpus row");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute corpus row");
    assert_eq!(
        outputs.first().map(String::as_str),
        Some("unsat"),
        "{label}: the strictly certified verdict is kept; got {outputs:?}"
    );
    let proof = outputs.last().cloned().expect("get-proof output");
    let published = proof.contains("(assume ") || proof.contains("(step ");
    if !published {
        assert!(
            proof.contains("UNVERIFIABLE PROOF") || proof.contains("(error"),
            "{label}: a withheld document must say so:\n{proof}"
        );
        return;
    }
    assert!(
        !proof
            .lines()
            .any(|line| line.starts_with("(assume ") && line.contains("(and (= (ptr")),
        "{label}: a datatype field expansion is no assertion of the problem:\n{proof}"
    );
    if let Some(carcara) = require_carcara_or_skip() {
        // Read with NO allowance: a `trust` step is a rejection here. A
        // `holey` document is not rejected, but it is not verification either.
        assert_ne!(
            carcara_verdict_without_allowances(&carcara, label, &problem, &proof),
            CarcaraVerdict::Invalid,
            "{label}: a published document must not be one pinned carcara rejects:\n{proof}"
        );
    }
}
