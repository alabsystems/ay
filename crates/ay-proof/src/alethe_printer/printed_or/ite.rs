// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Whether a printed `ite1` / `ite2` / `not_ite1` / `not_ite2` command is an
//! instance of its rule over the printed term of its premise.
//!
//! # The false green
//!
//! `group_quantifiers::frame_quantifier_instance_resolve`'s array-frame
//! fixture (`snew = s.update(1, val)`, goal `forall j < 3. snew[j] >= 0`)
//! published a document under `unproved_steps=0 trust_free=yes
//! ay_self_checkable=yes`, and pinned carcara 1.1.0 refused it:
//!
//! ```text
//! [ERROR] checking failed on step 't7' with rule 'ite1': term
//!         '(= (select snew 0) (ite (= 0 1) val (select s 0)))' is of the wrong
//!         form, expected '(ite phi_1 phi_2 phi_3)'
//! ```
//!
//! AY's instance of the update axiom is the Shannon-lifted FORMULA
//! `(ite (= 1 0) (= val (select snew 0)) (= (select snew 0) (select s 0)))`,
//! and its `ite1` over that term is correct, which is all the strict checker
//! reads. The producer's `forall_inst` surface override spells the same
//! `TermId` with the substituted AUTHORED body, document-wide, so the `ite1`
//! shipped over an equality: the object AY verified and the object it shipped
//! were not the same object, and no judgement read the shipped one for these
//! four rules.
//!
//! # The check
//!
//! Pinned carcara (`checker/rules/tautology.rs`): exactly one premise whose
//! clause is a unit, that unit `(ite p1 p2 p3)` (`(not (ite p1 p2 p3))` for
//! the `not_` pair), and a two-literal conclusion equal, POSITIONALLY and by
//! `assert_eq`, to
//!
//! * `ite1`: `p1`, `p3`;
//! * `ite2`: `(not p1)`, `p2`;
//! * `not_ite1`: `p1`, `(not p3)`;
//! * `not_ite2`: `(not p1)`, `(not p2)`.
//!
//! `assert_eq` is syntactic, so `(= 1 0)` is NOT `(= 0 1)` here, and the
//! order matters even though AY's own checker matches the two literals as a
//! set; only the parser-level collapse of [`normalised`] is identified.

use super::super::split_application;
use super::normalised;

/// The operand of a printed `(not X)`, or `None`.
fn negated(text: &str) -> Option<String> {
    let inner = split_application(text, "not")?;
    let [inner] = inner.as_slice() else {
        return None;
    };
    Some(inner.clone())
}

fn same(left: &str, right: &str) -> bool {
    normalised(left) == normalised(right)
}

/// Whether the printed conclusion `literals` is an instance of `rule` over the
/// printed premise clause `premise`. Any other rule name is refused.
pub(super) fn printed_ite_holds(rule: &str, premise: &[&str], literals: &[&str]) -> bool {
    let [premise_term] = premise else {
        // `get_premise_term`: the premise clause must be a unit.
        return false;
    };
    let [first, second] = literals else {
        return false;
    };
    let source = match rule {
        "ite1" | "ite2" => (*premise_term).to_string(),
        "not_ite1" | "not_ite2" => match negated(premise_term) {
            Some(inner) => inner,
            None => return false,
        },
        _ => return false,
    };
    let Some(parts) = split_application(&source, "ite") else {
        return false;
    };
    let [condition, then_branch, else_branch] = parts.as_slice() else {
        return false;
    };
    let negative = |literal: &str, expected: &str| {
        negated(literal).is_some_and(|inner| same(&inner, expected))
    };
    match rule {
        "ite1" => same(first, condition) && same(second, else_branch),
        "ite2" => negative(first, condition) && same(second, then_branch),
        "not_ite1" => same(first, condition) && negative(second, else_branch),
        _ => negative(first, condition) && negative(second, then_branch),
    }
}

#[cfg(test)]
mod tests {
    use super::printed_ite_holds;

    const LIFTED: &str = "(ite (= 1 0) (= val (select snew 0)) (= (select snew 0) (select s 0)))";
    const AUTHORED: &str = "(= (select snew 0) (ite (= 0 1) val (select s 0)))";
    const ELSE_CLAUSE: [&str; 2] = ["(= 1 0)", "(= (select snew 0) (select s 0))"];
    const THEN_CLAUSE: [&str; 2] = ["(not (= 1 0))", "(= val (select snew 0))"];

    #[test]
    fn each_projection_of_a_printed_ite_premise_holds() {
        assert!(printed_ite_holds("ite1", &[LIFTED], &ELSE_CLAUSE));
        assert!(printed_ite_holds("ite2", &[LIFTED], &THEN_CLAUSE));
        let negated = format!("(not {LIFTED})");
        assert!(printed_ite_holds(
            "not_ite1",
            &[&negated],
            &["(= 1 0)", "(not (= (select snew 0) (select s 0)))"]
        ));
        assert!(printed_ite_holds(
            "not_ite2",
            &[&negated],
            &["(not (= 1 0))", "(not (= val (select snew 0)))"]
        ));
    }

    /// The measured false green: the premise PRINTS as the authored equality.
    #[test]
    fn a_premise_printed_as_its_authored_equality_is_refused() {
        assert!(!printed_ite_holds("ite1", &[AUTHORED], &ELSE_CLAUSE));
        assert!(!printed_ite_holds("ite2", &[AUTHORED], &THEN_CLAUSE));
        let negated = format!("(not {AUTHORED})");
        assert!(!printed_ite_holds(
            "not_ite1",
            &[&negated],
            &["(= 1 0)", "(not (= (select snew 0) (select s 0)))"]
        ));
    }

    /// Carcara's `assert_eq` is syntactic and positional: a re-oriented
    /// condition, swapped literals, the wrong branch, a non-unit premise, a
    /// missing negation shell and an unknown rule are all refused.
    #[test]
    fn near_miss_instances_are_refused() {
        let reoriented = ["(= 0 1)", "(= (select snew 0) (select s 0))"];
        assert!(!printed_ite_holds("ite1", &[LIFTED], &reoriented));
        let swapped = ["(= (select snew 0) (select s 0))", "(= 1 0)"];
        assert!(!printed_ite_holds("ite1", &[LIFTED], &swapped));
        let wrong_branch = ["(= 1 0)", "(= val (select snew 0))"];
        assert!(!printed_ite_holds("ite1", &[LIFTED], &wrong_branch));
        assert!(!printed_ite_holds("ite2", &[LIFTED], &wrong_branch));
        assert!(!printed_ite_holds("ite1", &[LIFTED, "p"], &ELSE_CLAUSE));
        assert!(!printed_ite_holds("ite1", &[], &ELSE_CLAUSE));
        assert!(!printed_ite_holds("ite1", &[LIFTED], &ELSE_CLAUSE[..1]));
        assert!(!printed_ite_holds("not_ite1", &[LIFTED], &ELSE_CLAUSE));
        assert!(!printed_ite_holds("ite_pos1", &[LIFTED], &ELSE_CLAUSE));
    }

    /// Only the bit-vector literal family is collapsed, as the pinned parser
    /// does: `#b01` and `(_ bv1 2)` are one constant.
    #[test]
    fn a_parser_collapsed_literal_spelling_is_one_term() {
        let premise = ["(ite (= x #b01) (= y #b10) (= y #b00))"];
        assert!(printed_ite_holds(
            "ite1",
            &premise,
            &["(= x (_ bv1 2))", "(= y (_ bv0 2))"]
        ));
    }
}
