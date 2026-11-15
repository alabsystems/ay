// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

/// `QF_LIA_ring_2exp16_5vars_cascade_unsat` ends in a 43-literal LIA lemma
/// that is satisfiable over ℚ and refuted only by a chain of Chvátal–Gomory
/// cuts. The funnel files it as `IntCgCutChain`, the strict checker re-derives
/// the chain, and the printer lowers it cut by cut, so under
/// `:check-proofs-strict` the row publishes `unsat` with a hole-free,
/// Carcara-`valid` document. Counterfactual (measured at 09b0371c6, before the
/// kind existed): the lemma stays `Generic` and mandatory strict certification
/// withholds the row as `unknown` ("step t161 uses unsupported theory lemma
/// kind Generic in strict mode").
#[test]
#[timeout(120_000)]
fn test_strict_publication_admits_the_cut_chain_cascade_row() {
    let carcara = required_carcara_for_corpus();
    let row = "ring_2exp16_5vars_cascade_unsat";
    let problem = benchmark_content(&format!("benchmarks/smt/QF_LIA/{row}.smt2"));
    let problem: String = problem
        .lines()
        .filter(|line| line.trim() != "(exit)")
        .collect::<Vec<_>>()
        .join("\n");
    let script = format!(
        "(set-option :produce-proofs true)\n(set-option :check-proofs-strict true)\n{problem}\n(get-proof)\n"
    );
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&parse(&script).expect("parse"))
        .expect("execute");
    assert_eq!(
        outputs.first().map(String::as_str),
        Some("unsat"),
        "{row}: strict proofs must publish the cut-chain lemma; unknown_reason={:?}",
        exec.unknown_reason()
    );
    assert!(!exec.unsat_proof_has_known_wire_gap(), "{row}");
    let proof = outputs.last().cloned().expect("proof output");
    assert!(unchecked_proof_steps(&proof).is_empty(), "{row}:\n{proof}");
    // The carry total appears nowhere in the problem: only a cut names it.
    assert!(
        proof.contains("(+ c1 c2 c3 c4)"),
        "{row}: the carry-total cut is printed"
    );
    assert!(
        run_carcara_trust_free(&carcara, row, &problem, &proof),
        "{row}: Carcara must say `valid`"
    );
}
