// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn closed_boolean_units_and_double_negation_export_checked_steps() {
    let terms = TermStore::new();
    let printer = AlethePrinter::new(&terms);
    for (case, literal) in [
        "(not (not (= (= #x10 #x20) false)))",
        "(= (= #x10 #b00010000) true)",
        "(not (= true false))",
        "(= (_ bv0 128) (_ bv0 128))",
    ]
    .into_iter()
    .enumerate()
    {
        let proof = printer
            .lower_closed_boolean_clause(ProofId(1), &format!("(cl {literal})"))
            .unwrap();
        let problem = format!("(set-logic QF_BV)(assert (not {literal}))(check-sat)");
        let proof = format!("(assume premise (not {literal}))\n{proof}\n(step done (cl) :rule resolution :premises (premise t1))\n");
        emit(case, &problem, &proof);
    }
    for (case, literal) in ["(= #x10 #x20)", "(= #x10 #x10)"].into_iter().enumerate() {
        let clause = format!("(cl (not (not (not {literal}))) {literal})");
        let proof = printer
            .lower_closed_boolean_clause(ProofId(1), &clause)
            .unwrap();
        let problem = format!(
            "(set-logic QF_BV)(assert (not (not {literal})))(assert (not {literal}))(check-sat)"
        );
        let proof = format!("(assume first (not (not {literal})))\n(assume second (not {literal}))\n{proof}\n(step mid (cl {literal}) :rule resolution :premises (t1 first))\n(step done (cl) :rule resolution :premises (mid second))\n");
        emit(case + 4, &problem, &proof);
    }
}

fn emit(case: usize, problem: &str, proof: &str) {
    assert!(!proof.contains(":rule hole") && !proof.contains(":rule trust"));
    let path = std::env::temp_dir().join(format!(
        "ay-closed-boolean-{case}-{}.json",
        std::process::id()
    ));
    std::fs::write(
        &path,
        serde_json::to_vec(&serde_json::json!({
            "type":"alethe_certificate","version":"1.0","problem":problem,"proof":proof
        }))
        .unwrap(),
    )
    .unwrap();
    println!("independent replay certificate: {}", path.display());
}

#[test]
fn closed_boolean_bridge_rejects_false_open_ill_sorted_or_unbounded_claims() {
    let terms = TermStore::new();
    let printer = AlethePrinter::new(&terms);
    for clause in [
        "(cl (= #x10 #x20))",
        "(cl (= #x10 true))",
        "(cl (= #x10 #x0010))",
        "(cl (not #b0))",
        "(cl (not (not p)))",
        "(cl (= (_ bv0 0) (_ bv0 0)))",
        "(cl (= (_ bv0 129) (_ bv0 129)))",
        "(cl (= (bvadd #x00 #x00) #x00))",
        "(cl (not (not (not true))) false)",
        "(cl true false true)",
        "(cl)",
        "(cl (not (not (not #b0))) #b0)",
    ] {
        assert!(
            printer
                .lower_closed_boolean_clause(ProofId(1), clause)
                .is_none(),
            "{clause}"
        );
    }
    let mut nested = "true".to_string();
    for _ in 0..18 {
        nested = format!("(not {nested})");
    }
    assert!(printer
        .lower_closed_boolean_clause(ProofId(1), &format!("(cl {nested})"))
        .is_none());
    assert!(printer
        .lower_closed_boolean_clause(ProofId(1), &format!("(cl {})", "x".repeat(8192)))
        .is_none());
    let printer = AlethePrinter::new_with_overrides_and_budget(&terms, None, Some(16));
    assert!(printer
        .lower_closed_boolean_clause(ProofId(1), "(cl (= #x10 #x10))")
        .is_none());
    assert!(printer.work_budget_exhausted());
}
