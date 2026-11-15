// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! #authored-fold-identity on the corpus: the QF_UFLIA `mathsat/Hash/hash_uns`
//! family's `preprocessor-fold-to-false` decline is closed by a derivation the
//! external checker accepts.
//!
//! `hash_uns_03_08` was one of the six `preprocessor-fold-to-false` refutations
//! of the 2026-09-12 headline conformance sweep (seed 5, build 9659): `unsat`
//! with a 26-byte `(step t0 (cl) :rule hole)` document. On the fix it publishes
//! a 24-line hole-free derivation whose `assume` is the authored `let` text,
//! `unproved_steps=0 ay_self_checkable=yes unsat_admission=strict-proof`, and
//! pinned carcara 1.1.0 answers `valid` (measured 2026-09-12).
//!
//! Corpus-backed, following the workspace convention (skip when absent, fail
//! under `AY_REQUIRE_CORPUS=1` so a vacuous run cannot pass as a pass).

use ay_dpll::Executor;
use ay_frontend::parse;

use crate::common;

const HASH_UNS_03_08: &str =
    "benchmarks/smtlib-all/QF_UFLIA/non-incremental__QF_UFLIA__mathsat__Hash__hash_uns_03_08.smt2";

fn run_with_proofs(body: &str) -> (Option<String>, Option<String>) {
    let script = format!("(set-option :produce-proofs true)\n{body}");
    let commands = parse(&script).expect("corpus file must parse");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("corpus file must run");
    // The corpus file ends in `(exit)`, so the verdict is the last VERDICT line,
    // not the last line.
    let verdict = outputs
        .iter()
        .rev()
        .map(|line| line.trim().to_string())
        .find(|line| matches!(line.as_str(), "sat" | "unsat" | "unknown"));
    let proof = if verdict.as_deref() == Some("unsat") {
        let get_proof = parse("(get-proof)").expect("(get-proof) must parse");
        exec.execute_all(&get_proof)
            .ok()
            .and_then(|out| out.last().cloned())
    } else {
        None
    };
    (verdict, proof)
}

#[test]
fn hash_uns_03_08_publishes_a_hole_free_derivation_over_the_authored_let() {
    let path = common::workspace_path(HASH_UNS_03_08);
    let Ok(smt) = std::fs::read_to_string(&path) else {
        assert!(
            std::env::var_os("AY_REQUIRE_CORPUS").is_none(),
            "AY_REQUIRE_CORPUS=1 is set and {HASH_UNS_03_08} is not on disk — this guard \
             checked NOTHING. Fetch with `ay-z3-parity fetch benchmarks/smtlib-all \
             --divisions QF_UFLIA`."
        );
        eprintln!("SKIP: {HASH_UNS_03_08} is not present.");
        return;
    };
    assert!(
        smt.contains("(set-info :status unsat)"),
        "corpus file no longer declares `:status unsat` — re-derive the ground truth \
         before trusting this guard"
    );
    // The family's fold conjunct, as authored: the identity the pass derives.
    assert!(
        smt.contains("(distinct (ite ?v_24 ?v_3 (+ ?v_0 ?v_0)) (ite ?v_24 ?v_3 (* 2 ?v_0)))"),
        "the fixture has stopped carrying the normalization-identity conjunct"
    );

    let (verdict, proof) = run_with_proofs(&smt);
    assert_eq!(
        verdict.as_deref(),
        Some("unsat"),
        "hash_uns_03_08 must refute under an explicit proof demand (the base withheld it)"
    );
    let proof = proof.expect("an unsat verdict under :produce-proofs must carry a proof");
    assert!(
        proof.starts_with("(assume t0.a (let ((?v_0 (hash_1 x1))"),
        "the assume must be the authored `let` text, not AY's eliminated rewriting; got: {}",
        proof.lines().next().unwrap_or("")
    );
    assert!(
        !proof.contains(":rule hole") && !proof.contains(":rule trust"),
        "the published document must carry no hole and no trust step"
    );
    for rule in [
        ":rule let",
        ":rule and_pos",
        ":rule la_generic",
        ":rule la_disequality",
        ":rule cong",
        ":rule distinct_elim",
    ] {
        assert!(
            proof.contains(rule),
            "the fold-identity derivation must carry {rule}; got:\n{proof}"
        );
    }
    assert!(
        proof
            .trim()
            .ends_with("(cl) :rule resolution :premises (t15 t11))"),
        "the derivation must end in the empty clause by resolution; got:\n{proof}"
    );
}
