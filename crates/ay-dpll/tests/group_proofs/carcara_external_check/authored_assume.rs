// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Exact authored-source publication checks live outside corpus.rs so both
// files remain below the repository's source-size ratchet.

/// Exact checker-facing publication gate for the two divisibility rows whose
/// authored source spelling differs from AY's canonical term identity.
///
/// These are deliberately stronger than proof-shape unit tests: Carcara sees
/// the untouched benchmark bytes, validates each positive document without an
/// allowed-rule escape hatch, and must reject changes to the source binding or
/// any rule, premise, or conclusion in the local equivalence bridge.
#[test]
#[cfg_attr(debug_assertions, timeout(120_000))]
#[cfg_attr(not(debug_assertions), timeout(60_000))]
fn test_carcara_authored_assume_bridges_bind_exact_problem_and_reject_tampering() {
    let carcara = required_carcara_for_corpus();

    check_crt_authored_assume_bridge(&carcara);
    check_uflia_authored_assume_bridge(&carcara);
}

fn check_crt_authored_assume_bridge(carcara: &Path) {
    let crt_problem = benchmark_content("benchmarks/smt/QF_LIA/ring_2exp8_3vars_crt_unsat.smt2");
    let crt_proof = solve_unsat_and_get_proof(&crt_problem, "authored_assume_crt");
    assert!(
        !crt_proof.contains(":rule hole") && !crt_proof.contains(":rule trust"),
        "CRT publication must be fully checked:\n{crt_proof}"
    );
    assert!(
        crt_proof.contains("(assume t0.a (= x (+ (* 4 a) 1)))"),
        "CRT assumption must retain the exact authored operand order:\n{crt_proof}"
    );
    assert!(
        crt_proof.contains("(step t0.n.c1.c0 (cl (= (* 4 a) (* a 4))) :rule aci_simp)"),
        "CRT bridge must certify the multiplication commutation:\n{crt_proof}"
    );
    for line in crt_proof
        .lines()
        .filter(|line| line.contains(":rule la_generic"))
    {
        assert!(
            !line.contains("(* 4 a)") && !line.contains("(* 6 b)"),
            "synthesized lattice clauses must retain canonical identity spelling: {line}"
        );
    }
    let asserted = extract_asserted_terms(&crt_problem);
    for assumed in extract_assume_terms(&crt_proof) {
        assert!(
            asserted.contains(&assumed),
            "CRT proof assumption is not an exact problem assertion: {assumed}"
        );
    }
    let (valid, diagnostic) = exact_carcara_verdict(carcara, &crt_problem, &crt_proof);
    assert!(
        valid,
        "exact CRT artifact must be Carcara-valid: {diagnostic}"
    );

    let changed_crt_proof = crt_proof.replacen(
        "(assume t0.a (= x (+ (* 4 a) 1)))",
        "(assume t0.a (= x (+ (* 5 a) 1)))",
        1,
    );
    assert_ne!(
        changed_crt_proof, crt_proof,
        "CRT source tamper target missing"
    );
    let (valid, diagnostic) = exact_carcara_verdict(carcara, &crt_problem, &changed_crt_proof);
    assert!(
        !valid,
        "Carcara accepted a changed CRT source: {diagnostic}"
    );

    let canonicalized_crt_problem = crt_problem.replacen(
        "(assert (= x (+ (* 4 a) 1)))",
        "(assert (= x (+ (* a 4) 1)))",
        1,
    );
    assert_ne!(
        canonicalized_crt_problem, crt_problem,
        "CRT source-orientation tamper target missing"
    );
    let (valid, diagnostic) =
        exact_carcara_verdict(carcara, &canonicalized_crt_problem, &crt_proof);
    assert!(
        !valid,
        "Carcara accepted the proof against a semantically equal but differently authored CRT problem: {diagnostic}"
    );
}

fn check_uflia_authored_assume_bridge(carcara: &Path) {
    let uflia_problem = benchmark_content("benchmarks/smt/QF_UFLIA/unsat_congruence_to_lia.smt2");
    let uflia_proof = solve_unsat_and_get_proof(&uflia_problem, "authored_assume_uflia");
    assert!(
        !uflia_proof.contains(":rule hole") && !uflia_proof.contains(":rule trust"),
        "UFLIA publication must be fully checked:\n{uflia_proof}"
    );
    let comparison_bridge = "(step t5.n (cl (= (>= (f b) 0) (<= 0 (f b)))) :rule comp_simplify)";
    assert!(
        uflia_proof.contains("(assume t5.a (>= (f b) 0))")
            && uflia_proof.contains(comparison_bridge),
        "UFLIA assumption must retain and certify the exact authored orientation:\n{uflia_proof}"
    );
    let asserted = extract_asserted_terms(&uflia_problem);
    for assumed in extract_assume_terms(&uflia_proof) {
        assert!(
            asserted.contains(&assumed),
            "UFLIA proof assumption is not an exact problem assertion: {assumed}"
        );
    }
    let (valid, diagnostic) = exact_carcara_verdict(carcara, &uflia_problem, &uflia_proof);
    assert!(
        valid,
        "exact UFLIA artifact must be Carcara-valid: {diagnostic}"
    );

    let changed_uflia_proof = uflia_proof.replacen(
        "(assume t5.a (>= (f b) 0))",
        "(assume t5.a (>= (f b) 1))",
        1,
    );
    assert_ne!(
        changed_uflia_proof, uflia_proof,
        "UFLIA source tamper target missing"
    );
    let (valid, diagnostic) = exact_carcara_verdict(carcara, &uflia_problem, &changed_uflia_proof);
    assert!(
        !valid,
        "Carcara accepted a changed UFLIA source: {diagnostic}"
    );

    let canonicalized_uflia_problem =
        uflia_problem.replacen("(assert (>= (f b) 0))", "(assert (<= 0 (f b)))", 1);
    assert_ne!(
        canonicalized_uflia_problem, uflia_problem,
        "UFLIA source-orientation tamper target missing"
    );
    let (valid, diagnostic) =
        exact_carcara_verdict(carcara, &canonicalized_uflia_problem, &uflia_proof);
    assert!(
        !valid,
        "Carcara accepted the proof against a semantically equal but differently authored UFLIA problem: {diagnostic}"
    );

    let rule_tamper = uflia_proof.replacen(
        comparison_bridge,
        "(step t5.n (cl (= (>= (f b) 0) (<= 0 (f b)))) :rule refl)",
        1,
    );
    assert_ne!(
        rule_tamper, uflia_proof,
        "bridge rule tamper target missing"
    );
    let (valid, diagnostic) = exact_carcara_verdict(carcara, &uflia_problem, &rule_tamper);
    assert!(
        !valid,
        "Carcara accepted a tampered bridge rule: {diagnostic}"
    );

    let premise_tamper = uflia_proof.replacen(
        ":premises (t5.e t5.n t5.a))",
        ":premises (t5.e t5.n t5.n))",
        1,
    );
    assert_ne!(
        premise_tamper, uflia_proof,
        "bridge premise tamper target missing"
    );
    let (valid, diagnostic) = exact_carcara_verdict(carcara, &uflia_problem, &premise_tamper);
    assert!(
        !valid,
        "Carcara accepted tampered bridge premises: {diagnostic}"
    );

    let conclusion_tamper = uflia_proof.replacen(
        "(step t5 (cl (<= 0 (f b)))",
        "(step t5 (cl (<= 1 (f b)))",
        1,
    );
    assert_ne!(
        conclusion_tamper, uflia_proof,
        "bridge conclusion/pivot tamper target missing"
    );
    let (valid, diagnostic) = exact_carcara_verdict(carcara, &uflia_problem, &conclusion_tamper);
    assert!(
        !valid,
        "Carcara accepted a tampered bridge conclusion/pivot: {diagnostic}"
    );
}
