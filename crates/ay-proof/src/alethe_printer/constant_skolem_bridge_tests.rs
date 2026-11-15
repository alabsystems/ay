// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The constant Skolem bridge: the exact sub-steps each catalogue row ships,
//! the shapes it declines, and the judgement that admits the closing
//! `sko_forall` / `sko_ex` over a bridge.
//!
//! The expected lines are the ones MEASURED valid on 2026-10-01 with Trust's
//! checker (`clean cert verify-external`) inside the full documents for
//! `(forall ((q Int)) (not (= q q)))`, its `__trust_u_q` and `U` twins,
//! `(forall ((q Int)) (< q q))`, `(forall ((q Int)) (> q q))`,
//! `(not (forall ((q Int)) (= q q)))`, the `<=` and `>=` twins of that, and
//! `(exists ((q Int)) (not (= q q)))`.

use super::super::quantifier_surface::{
    printed_constant_skolem_step_holds, printed_skolem_step_holds, PrintedSkolemStep,
};
use super::*;

fn bridge(body: &str) -> Option<ConstantSkolemBridge> {
    constant_skolem_bridge(body)
}

fn lines(body: &str) -> (Vec<String>, bool) {
    let bridge = bridge(body).unwrap_or_else(|| panic!("{body} must bridge"));
    let lines = bridge
        .lines(ProofId(1))
        .unwrap_or_else(|| panic!("{body}: every catalogue rule is checkable"));
    (lines, bridge.value)
}

#[test]
fn a_reflexive_equality_is_true_by_eq_simplify() {
    assert_eq!(
        lines("(= q q)"),
        (
            vec!["(step t1.t1 (cl (= (= q q) true)) :rule eq_simplify)".to_string()],
            true
        )
    );
}

#[test]
fn a_negated_reflexive_equality_is_false_through_cong_not_simplify_and_trans() {
    let expected = [
        "(step t1.t1 (cl (= (= q q) true)) :rule eq_simplify)",
        "(step t1.t2 (cl (= (not (= q q)) (not true))) :rule cong :premises (t1.t1))",
        "(step t1.t3 (cl (= (not true) false)) :rule not_simplify)",
        "(step t1.t4 (cl (= (not (= q q)) false)) :rule trans :premises (t1.t2 t1.t3))",
    ];
    assert_eq!(
        lines("(not (= q q))"),
        (expected.map(str::to_string).to_vec(), false)
    );
    // Trust's own spelling of `forall-int-unsat`.
    let (trust, value) = lines("(not (= __trust_u_q __trust_u_q))");
    assert!(!value);
    assert_eq!(
        trust[3],
        "(step t1.t4 (cl (= (not (= __trust_u_q __trust_u_q)) false)) :rule trans \
         :premises (t1.t2 t1.t3))"
    );
}

#[test]
fn reflexive_comparisons_rewrite_by_comp_simplify() {
    for (body, value) in [("(< q q)", false), ("(<= q q)", true), ("(>= q q)", true)] {
        assert_eq!(
            lines(body),
            (
                vec![format!(
                    "(step t1.t1 (cl (= {body} {})) :rule comp_simplify)",
                    bool_text(value)
                )],
                value
            ),
            "{body}"
        );
    }
}

#[test]
fn a_reflexive_strict_greater_goes_through_its_non_strict_twin() {
    // One `comp_simplify` from `(> q q)` to `false` is REFUSED by the
    // checker (it stops at `(not (<= q q))`); this chain is accepted.
    let expected = [
        "(step t1.t1 (cl (= (> q q) (not (<= q q)))) :rule comp_simplify)",
        "(step t1.t2 (cl (= (<= q q) true)) :rule comp_simplify)",
        "(step t1.t3 (cl (= (not (<= q q)) (not true))) :rule cong :premises (t1.t2))",
        "(step t1.t4 (cl (= (not true) false)) :rule not_simplify)",
        "(step t1.t5 (cl (= (> q q) false)) :rule trans :premises (t1.t1 t1.t3 t1.t4))",
    ];
    assert_eq!(
        lines("(> q q)"),
        (expected.map(str::to_string).to_vec(), false)
    );
}

#[test]
fn a_negation_of_a_bridged_body_flips_its_constant() {
    let expected = [
        "(step t1.t1 (cl (= (< q q) false)) :rule comp_simplify)",
        "(step t1.t2 (cl (= (not (< q q)) (not false))) :rule cong :premises (t1.t1))",
        "(step t1.t3 (cl (= (not false) true)) :rule not_simplify)",
        "(step t1.t4 (cl (= (not (< q q)) true)) :rule trans :premises (t1.t2 t1.t3))",
    ];
    assert_eq!(
        lines("(not (< q q))"),
        (expected.map(str::to_string).to_vec(), true)
    );
    let (double, value) = lines("(not (not (= q q)))");
    assert!(value);
    assert_eq!(double.len(), 7);
    assert_eq!(
        double[4],
        "(step t1.t5 (cl (= (not (not (= q q))) (not false))) :rule cong :premises (t1.t4))"
    );
    assert_eq!(
        double[6],
        "(step t1.t7 (cl (= (not (not (= q q))) true)) :rule trans :premises (t1.t5 t1.t6))"
    );
}

#[test]
fn every_other_body_declines() {
    for body in [
        // Not reflexive.
        "(= q r)",
        "(< q r)",
        "(> q r)",
        // The store identifies these sides; the printed text does not.
        "(not (= q (+ q 0)))",
        "(= q |q|)",
        "(= #x01 #b00000001)",
        "(<= 1 1.0)",
        // A fold outside the catalogue.
        "(and p (not p))",
        "(or p (not p))",
        "(=> p p)",
        // Arity, constants and malformed text.
        "(= q q q)",
        "(not (= q q) p)",
        "(not true)",
        "true",
        "false",
        "q",
        "(not (= q q)",
        "",
    ] {
        assert_eq!(bridge(body), None, "{body}");
    }
    // The negation depth is capped.
    let deep = (0..9).fold("(= q q)".to_string(), |inner, _| format!("(not {inner})"));
    assert_eq!(bridge(&deep), None);
    let shallow = (0..8).fold("(= q q)".to_string(), |inner, _| format!("(not {inner})"));
    assert!(bridge(&shallow).is_some());
}

#[test]
fn the_instance_has_to_be_the_constant_the_body_derives() {
    let mut terms = TermStore::new();
    let q = terms.mk_var("q", Sort::Int);
    let falsity = terms.false_term();
    let truth = terms.true_term();
    let printer = AlethePrinter::new(&terms);
    assert!(printer
        .constant_skolem_bridge_for_instance(falsity, "(not (= q q))")
        .is_some());
    assert!(printer
        .constant_skolem_bridge_for_instance(truth, "(= q q)")
        .is_some());
    // A body that derives the OTHER constant is not this instance's bridge.
    assert!(printer
        .constant_skolem_bridge_for_instance(truth, "(not (= q q))")
        .is_none());
    // An instance that is not a Bool constant has no bridge.
    assert!(printer
        .constant_skolem_bridge_for_instance(q, "(= q q)")
        .is_none());
    // A body already spelled as the constant needs none.
    assert!(printer
        .constant_skolem_bridge_for_instance(falsity, "false")
        .is_none());
}

#[test]
fn only_a_recorded_bridge_is_charged_to_the_emission_budget() {
    let terms = TermStore::new();
    let falsity = terms.false_term();
    let printer = AlethePrinter::new_with_overrides_and_budget(&terms, None, Some(4));
    // Matching is pure: a body that declines (and one that bridges) leaves
    // the budget exactly where the base left it, so a declined body cannot
    // push a tight-budget document into exhaustion.
    assert!(printer
        .constant_skolem_bridge_for_instance(falsity, "(not (= q (+ q 0)))")
        .is_none());
    let bridge = printer
        .constant_skolem_bridge_for_instance(falsity, "(not (= q q))")
        .expect("the catalogue body bridges");
    assert_eq!(printer.work_used(), 0);
    assert!(!printer.work_budget_exhausted());
    // Recording is the charge: the body read and the text it will write.
    let expected = "(not (= q q))".len() + bridge.bytes();
    printer.record_constant_skolem_bridge(ProofId(1), "(not (= q q))", bridge);
    assert_eq!(printer.work_used(), expected as u64);
    assert!(printer.work_budget_exhausted());
}

#[test]
fn a_rule_outside_the_checkable_table_is_never_written() {
    let premises = ["t1.t1".to_string()];
    assert_eq!(
        bridge_command("t1.t2", "(= a b)", "trans", &premises).as_deref(),
        Some("(step t1.t2 (cl (= a b)) :rule trans :premises (t1.t1))")
    );
    // The bound is the checker's VOCABULARY (`hole` is in it): a name the
    // wire-rule probe has not covered is what it keeps out.
    for rule in ["trust", "eq_simplify_typo", "sko_choice", ""] {
        assert_eq!(
            bridge_command("t1.t1", "(= a b)", rule, &[]),
            None,
            "{rule}"
        );
    }
    // One such sub-step and the whole bridge prints nothing; the closing
    // step falls back to the hole (`format_certified_skolem_step`).
    let mut tampered = bridge("(not (= q q))").expect("the catalogue body bridges");
    tampered.steps[0].rule = "eq_simplify_typo";
    assert_eq!(tampered.lines(ProofId(1)), None);
    let step = step("sko_forall", FORALL, FORALL_CHOICE, "false");
    assert!(format_bridged_skolem_step(ProofId(1), &step, &tampered).is_none());
    let honest = bridge("(not (= q q))").expect("the catalogue body bridges");
    let printed =
        format_bridged_skolem_step(ProofId(1), &step, &honest).expect("the honest bridge prints");
    assert!(
        printed.ends_with(&format!(
            "(step t1 (cl (= {FORALL} false)) :rule sko_forall)"
        )),
        "{printed}"
    );
    // A judged step whose rule is not a Skolem rule is refused by the
    // judgement before any command is written.
    let renamed = PrintedSkolemStep {
        rule: "sko_choice",
        ..step
    };
    assert!(format_bridged_skolem_step(ProofId(1), &renamed, &honest).is_none());
}

fn step<'a>(
    rule: &'a str,
    quantified: &'a str,
    choice: &'a str,
    instance: &'a str,
) -> PrintedSkolemStep<'a> {
    PrintedSkolemStep {
        rule,
        quantified,
        binder: "q",
        sort: "Int",
        choice,
        body: "(not (= q q))",
        instance,
    }
}

const FORALL: &str = "(forall ((q Int)) (not (= q q)))";
const FORALL_CHOICE: &str = "(choice ((q Int)) (not (not (= q q))))";

#[test]
fn the_constant_judgement_admits_exactly_the_bridged_step() {
    let last = "(= (not (= q q)) false)";
    assert!(printed_constant_skolem_step_holds(
        &step("sko_forall", FORALL, FORALL_CHOICE, "false"),
        last
    ));
    assert!(printed_constant_skolem_step_holds(
        &step(
            "sko_ex",
            "(exists ((q Int)) (not (= q q)))",
            "(choice ((q Int)) (not (= q q)))",
            "false"
        ),
        last
    ));
}

#[test]
fn the_constant_judgement_refuses_every_mismatch() {
    let last = "(= (not (= q q)) false)";
    // psi mentions the binder: not a constant, and Clean's export guard
    // refuses it (N3).
    assert!(!printed_constant_skolem_step_holds(
        &step("sko_forall", FORALL, FORALL_CHOICE, "(not (= q q))"),
        "(= (not (= q q)) (not (= q q)))"
    ));
    // `b` is not a constant.
    assert!(!printed_constant_skolem_step_holds(
        &step("sko_forall", FORALL, FORALL_CHOICE, "p"),
        "(= (not (= q q)) p)"
    ));
    // The bridge's left side is not the printed body.
    assert!(!printed_constant_skolem_step_holds(
        &step("sko_forall", FORALL, FORALL_CHOICE, "false"),
        "(= (not (= q  q)) false)"
    ));
    assert!(!printed_constant_skolem_step_holds(
        &step("sko_forall", FORALL, FORALL_CHOICE, "false"),
        "(= (not (= r r)) false)"
    ));
    // The bridge proves the other constant than the step concludes.
    assert!(!printed_constant_skolem_step_holds(
        &step("sko_forall", FORALL, FORALL_CHOICE, "false"),
        "(= (not (= q q)) true)"
    ));
    // The bridge's last command is not an equality.
    assert!(!printed_constant_skolem_step_holds(
        &step("sko_forall", FORALL, FORALL_CHOICE, "false"),
        "(not (= q q))"
    ));
    // The frame checks still hold: wrong quantifier, binder, sort, choice.
    assert!(!printed_constant_skolem_step_holds(
        &step("sko_ex", FORALL, FORALL_CHOICE, "false"),
        last
    ));
    assert!(!printed_constant_skolem_step_holds(
        &PrintedSkolemStep {
            binder: "r",
            ..step("sko_forall", FORALL, FORALL_CHOICE, "false")
        },
        last
    ));
    assert!(!printed_constant_skolem_step_holds(
        &PrintedSkolemStep {
            sort: "Real",
            ..step("sko_forall", FORALL, FORALL_CHOICE, "false")
        },
        last
    ));
    assert!(!printed_constant_skolem_step_holds(
        &step(
            "sko_forall",
            FORALL,
            "(choice ((q Int)) (not (= q q)))",
            "false"
        ),
        last
    ));
    // The anchored body the step prints must be the quantifier's body.
    assert!(!printed_constant_skolem_step_holds(
        &PrintedSkolemStep {
            body: "(= q q)",
            ..step("sko_forall", FORALL, FORALL_CHOICE, "false")
        },
        last
    ));
}

#[test]
fn a_bridged_step_is_judged_only_by_the_bridge_and_never_falls_to_refl() {
    // The base's respelled form: the instance IS `BODY[q := choice]`, so the
    // `refl` judgement accepts it on its own.
    let respelled = format!("(not (= {FORALL_CHOICE} {FORALL_CHOICE}))");
    let refl_shaped = step("sko_forall", FORALL, FORALL_CHOICE, &respelled);
    assert!(printed_skolem_step_holds(&refl_shaped));
    assert_eq!(
        skolem_step_form(ProofId(1), &refl_shaped, None),
        SkolemStepForm::Refl
    );
    // With a recorded bridge the same text is the hole: the bridge's
    // judgement refuses an instance that is not its constant, and the step
    // does not get a second judgement.
    let honest = bridge("(not (= q q))").expect("the catalogue body bridges");
    assert_eq!(
        skolem_step_form(ProofId(1), &refl_shaped, Some(&honest)),
        SkolemStepForm::Hole
    );
    // A tampered bridge refuses as well, again without the `refl` form.
    let mut tampered = honest.clone();
    tampered.steps[0].rule = "eq_simplify_typo";
    let constant = step("sko_forall", FORALL, FORALL_CHOICE, "false");
    assert_eq!(
        skolem_step_form(ProofId(1), &constant, Some(&tampered)),
        SkolemStepForm::Hole
    );
    // The bridged instance prints the bridge; without a bridge the constant
    // is not `BODY[q := choice]` and is the hole, as at the base.
    let SkolemStepForm::Bridged(printed) = skolem_step_form(ProofId(1), &constant, Some(&honest))
    else {
        panic!("the honest bridge prints");
    };
    assert!(
        printed.ends_with(&format!(
            "(step t1 (cl (= {FORALL} false)) :rule sko_forall)"
        )),
        "{printed}"
    );
    assert_eq!(
        skolem_step_form(ProofId(1), &constant, None),
        SkolemStepForm::Hole
    );
}
