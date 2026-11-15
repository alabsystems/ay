// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::tests::{original, TestResult};
use super::*;
use std::process::Command;

/// `(bvadd a 1) = b` and `(bvadd b 15) = a` read one difference, so DR-30's
/// bridge gives both equalities one gate literal `x`, and the Boolean `=`
/// between them is `(= (not x) x)`: its `equiv_pos2` spells `(not (not x))`
/// beside `x`. Before the respelling, the circuit contracted that pair to
/// `(not (not x))`, a `contraction` Clean refused (fuzz seed 1613).
const RESPELLED: &str = include_str!("../fixtures/respelled-duplicate.smt2");

/// The top-level literals of the `(cl ..)` in a printed step line.
fn literals(line: &str) -> Option<Vec<&str>> {
    let start = line.find("(cl ")? + 4;
    let mut out = Vec::new();
    let (mut depth, mut from) = (0usize, start);
    for (offset, ch) in line[start..].char_indices() {
        let at = start + offset;
        match ch {
            '(' => depth += 1,
            ')' if depth == 0 => {
                if from < at {
                    out.push(&line[from..at]);
                }
                return Some(out);
            }
            ')' => {
                depth -= 1;
                if depth == 0 {
                    out.push(&line[from..=at]);
                    from = at + 1;
                }
            }
            ' ' if depth == 0 => {
                if from < at {
                    out.push(&line[from..at]);
                }
                from = at + 1;
            }
            _ => {}
        }
    }
    None
}

/// Every `contraction` in `proof` concludes its premise's literals with each
/// later repeat of an IDENTICAL spelling dropped, as carcara checks it.
fn contractions_are_syntactic(proof: &str) -> usize {
    let mut clauses: DetHashMap<&str, Vec<&str>> = DetHashMap::default();
    let mut checked = 0;
    for line in proof.lines().filter(|line| line.starts_with("(step ")) {
        let Some(name) = line.split_whitespace().nth(1) else {
            continue;
        };
        let Some(clause) = literals(line) else {
            continue;
        };
        if line.contains(":rule contraction ") {
            let premise = line
                .split(":premises (")
                .nth(1)
                .and_then(|rest| rest.split(')').next())
                .unwrap_or_else(|| panic!("a contraction names its premise: {line}"));
            let mut expected: Vec<&str> = Vec::new();
            for word in &clauses[premise] {
                if !expected.contains(word) {
                    expected.push(word);
                }
            }
            assert_eq!(
                clause, expected,
                "a contraction that is not syntactic: {line}"
            );
            checked += 1;
        }
        clauses.insert(name, clause);
    }
    checked
}

/// `clean cert verify-external` from `CLEAN_BIN`, and pinned Carcara from
/// `CARCARA_PATH`, when the environment names them.
fn replay_externally(problem: &str, proof: &str) {
    let dir = std::env::temp_dir().join(format!("ay-circuit-respell-{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("replay directory");
    if let Some(clean) = std::env::var_os("CLEAN_BIN") {
        let path = dir.join("certificate.json");
        let certificate = serde_json::json!({
            "type": "alethe_certificate",
            "version": "1.0",
            "problem": problem,
            "proof": proof,
        });
        std::fs::write(&path, certificate.to_string()).expect("write the certificate");
        let output = Command::new(clean)
            .args(["cert", "verify-external"])
            .arg(&path)
            .output()
            .expect("run clean cert verify-external");
        let stdout = String::from_utf8_lossy(&output.stdout);
        assert!(
            output.status.success() && stdout.contains("External certificate verification: PASSED"),
            "Clean refused:\n{stdout}{}\n{proof}",
            String::from_utf8_lossy(&output.stderr)
        );
    }
    if let Some(carcara) = std::env::var_os("CARCARA_PATH") {
        std::fs::write(dir.join("p.smt2"), problem).expect("write the problem");
        std::fs::write(dir.join("p.alethe"), proof).expect("write the proof");
        let output = Command::new(carcara)
            .args(["check", "--no-color", "--"])
            .arg(dir.join("p.alethe"))
            .arg(dir.join("p.smt2"))
            .output()
            .expect("run carcara");
        let stdout = String::from_utf8_lossy(&output.stdout);
        assert_eq!(
            stdout.lines().last().map(str::trim),
            Some("valid"),
            "pinned Carcara:\n{stdout}{}\n{proof}",
            String::from_utf8_lossy(&output.stderr)
        );
    }
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn a_literal_in_two_spellings_is_respelled_before_it_is_contracted() -> TestResult {
    let (context, root, negative) = original(RESPELLED)?;
    let printer = AlethePrinter::new(&context.terms);
    let text = printer
        .format_bv_circuit_refutation(ProofId(7), &[negative])
        .ok_or("the respelled lemma prints")?;
    assert!(
        text.contains(":rule poly_simp_rel"),
        "both equalities are bridged to one difference:\n{text}"
    );
    let proof = format!(
        "(assume a {})\n{text}(step done (cl) :rule resolution :premises (a t7))\n",
        printer.format_term(root)
    );
    assert!(contractions_are_syntactic(&proof) > 0, "{proof}");
    replay_externally(RESPELLED, &proof);
    assert!(
        text.contains(":rule not_not"),
        "the double negation is respelled:\n{text}"
    );
    Ok(())
}
