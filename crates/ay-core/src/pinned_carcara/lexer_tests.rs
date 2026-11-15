// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The shared lexer splits a document where pinned Carcara's lexer does, so
//! no scan can be blinded by a token Carcara reads apart.

use super::lexer::{command_atoms, LexedDocument, SexpToken};
use super::{
    pinned_carcara_can_judge, FALSE_VALID_ACI_SIMP_CONTROL_PROBLEM,
    FALSE_VALID_ACI_SIMP_CONTROL_PROOF, FALSE_VALID_CONTROL_PROBLEM, FALSE_VALID_CONTROL_PROOF,
};

/// Carcara ends a symbol at its first non-symbol character, a numeral after
/// its digits and a bit-vector literal after the digits of its base, and
/// skips every Unicode space; the atoms are read the same way, by both
/// readers. Literals, keywords, step ids, quoted symbols and strings stay
/// whole.
#[test]
fn atoms_end_where_pinned_carcara_ends_its_tokens() {
    let command = "(step\u{a0}t1.ac0 (cl (= (bvmul#x03\u{b}2m #b10x -5 2.0 1/2 a'b) |p q|)) \
                   :rule\u{2003}aci_simp :args (\"a \"\"b\"))";
    let expected = [
        "step",
        "t1.ac0",
        "cl",
        "=",
        "bvmul",
        "#x03",
        "2",
        "m",
        "#b10",
        "x",
        "-5",
        "2.0",
        "1/2",
        "a'b",
        "|p q|",
        ":rule",
        "aci_simp",
        ":args",
        "\"a \"\"b\"",
    ];
    let atoms: Vec<&str> = command_atoms(command)
        .into_iter()
        .map(|(_, atom)| atom)
        .collect();
    assert_eq!(atoms, expected);
    let lexed = LexedDocument::new(command);
    let tokens: Vec<&str> = lexed
        .tokens
        .iter()
        .filter_map(|token| match token {
            SexpToken::Atom(atom) => Some(*atom),
            SexpToken::Open | SexpToken::Close => None,
        })
        .collect();
    assert_eq!(tokens, expected);
}

/// Every spelling pinned Carcara was measured (2026-10-07) printing `valid`
/// for, on a SATISFIABLE problem, while a reader splitting only at ASCII
/// spaces and parentheses saw no deduplicated operator, no misjudged name and
/// no `aci_simp` or `evaluate` step: a non-ASCII or vertical-tab space around
/// the operator, the rule or the `step` keyword, a bit-vector literal glued
/// to the operator, a numeral glued to a `:named` label over `+`, and the
/// `evaluate` control with a non-ASCII space after its operator.
#[test]
fn a_token_carcara_reads_apart_is_read_apart() {
    let label = "(set-logic QF_LIA)\n(assert (not (= 2 (! (+ 2 2) :named m))))\n(check-sat)\n";
    let label_proof = "(assume h1 (not (= 2 m)))\n(step t1 (cl (= 2m)) :rule aci_simp)\n\
                       (step t2 (cl) :rule resolution :premises (h1 t1))\n";
    let misjudged = [
        (
            FALSE_VALID_ACI_SIMP_CONTROL_PROBLEM,
            FALSE_VALID_ACI_SIMP_CONTROL_PROOF
                .replace("(bvmul a a) a))", "(bvmul\u{a0}a\u{a0}a) a))"),
        ),
        (
            FALSE_VALID_ACI_SIMP_CONTROL_PROBLEM,
            FALSE_VALID_ACI_SIMP_CONTROL_PROOF
                .replace("(bvmul a a) a))", "(bvmul\u{b}a\u{b}a) a))"),
        ),
        (
            FALSE_VALID_ACI_SIMP_CONTROL_PROBLEM,
            FALSE_VALID_ACI_SIMP_CONTROL_PROOF.replace(":rule aci_simp", ":rule\u{a0}aci_simp"),
        ),
        (
            FALSE_VALID_ACI_SIMP_CONTROL_PROBLEM,
            FALSE_VALID_ACI_SIMP_CONTROL_PROOF.replace("(step t1", "(step\u{a0}t1"),
        ),
        (
            "(declare-const a (_ BitVec 8))\n",
            "(step t1 (cl (= (bvmul#x03 #x03 a) (bvmul#x03 a))) :rule aci_simp)\n".to_string(),
        ),
        (label, label_proof.to_string()),
        (
            FALSE_VALID_CONTROL_PROBLEM,
            FALSE_VALID_CONTROL_PROOF.replace("(= (bvsge #xf", "(= (bvsge\u{a0}#xf"),
        ),
    ];
    for (problem, proof) in &misjudged {
        assert!(
            pinned_carcara_can_judge(problem, proof).is_err(),
            "{proof:?}"
        );
    }
    // NEGATIVE twin: the same spacing around a TRUE swap is still judged.
    let swap = FALSE_VALID_ACI_SIMP_CONTROL_PROOF.replace(
        "(cl (= (bvmul a a) a))",
        "(cl (= (bvmul\u{a0}a#x02) (bvmul #x02\u{b}a)))",
    );
    assert_eq!(
        pinned_carcara_can_judge(FALSE_VALID_ACI_SIMP_CONTROL_PROBLEM, &swap),
        Ok(())
    );
}
