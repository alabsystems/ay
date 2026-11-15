// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

/// The publication wire-gap screen (`proof_has_known_wire_gap`) asks the same
/// question the printer answers for an all-equality `IntGuardedSplitGap`
/// lemma. Under `:check-proofs-strict` the two lattice rows must therefore
/// publish `unsat` with a hole-free, Carcara-`valid` document. Counterfactual
/// (measured): with the screen still asking only the unit divisibility
/// predicate, the strict funnel withholds both rows as `unknown`.
#[test]
#[timeout(120_000)]
fn test_strict_publication_admits_the_all_equality_lattice_rows() {
    let carcara = required_carcara_for_corpus();
    for row in [
        "ring_2exp12_3vars_deep_unsat",
        "ring_2exp8_5vars_modular_unsat",
    ] {
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
            "{row}: strict proofs must publish the lowered lattice lemma; unknown_reason={:?}",
            exec.unknown_reason()
        );
        assert!(!exec.unsat_proof_has_known_wire_gap(), "{row}");
        let proof = outputs.last().cloned().expect("proof output");
        assert!(unchecked_proof_steps(&proof).is_empty(), "{row}:\n{proof}");
        assert!(
            run_carcara_trust_free(&carcara, row, &problem, &proof),
            "{row}: Carcara must say `valid`"
        );
    }
}
