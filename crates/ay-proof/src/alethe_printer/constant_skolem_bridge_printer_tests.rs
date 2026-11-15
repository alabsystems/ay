// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! A whole vacuous-collapse document, rendered: `(forall ((q Int)) (not (= q
//! q)))`, whose body the store folds to `false`, refuted through its Skolem
//! instance and the `false` axiom.
//!
//! Before the bridge the authored instance text was keyed on the shared
//! `false` term, so the axiom printed as `(cl (not (not (= c c))))` and was
//! demoted to a hole. The bridged document prints every `false` as `false`
//! and the only new lines are inside the anchor. A body outside the bridge
//! catalogue keeps exactly the bytes the base printed, under an authored
//! `forall` and an authored `exists` alike. A bridged binder whose constant
//! ANOTHER Skolem step respelled is refused by the bridge's judgement and
//! prints the hole.

use super::*;
use ay_core::{AletheRule, Proof, Symbol};

const CHOICE: &str = "(choice ((q Int)) (not (not (= q q))))";

/// The proof AY's quantifier lane produces for an authored `forall` whose
/// body folded to `false`, rendered with `quantifier` as the authored
/// spelling of the quantified term.
fn render(quantifier: &str) -> String {
    let mut terms = TermStore::new();
    let q = terms.mk_var("q", Sort::Int);
    let reflexive = terms.mk_eq(q, q);
    let body = terms.mk_not(reflexive);
    let falsity = terms.false_term();
    assert_eq!(body, falsity, "the store folds `(not (= q q))` to `false`");
    let quantified = terms.mk_forall(vec![("q".to_string(), Sort::Int)], body);
    let witness = terms.mk_var("sk!q_vacuous", Sort::Int);
    terms.mark_skolem_symbol("sk!q_vacuous");
    let equality = terms.mk_app(Symbol::named("="), [quantified, falsity], Sort::Bool);
    let not_equality = terms.mk_not_raw(equality);
    let not_quantified = terms.mk_not_raw(quantified);
    let not_false = terms.mk_not_raw(falsity);

    let mut proof = Proof::new();
    let assumed = proof.add_assume(quantified, None);
    let skolem = proof.add_rule_step(AletheRule::Skolem, vec![equality], vec![], vec![witness]);
    let equivalence = proof.add_rule_step(
        AletheRule::EquivPos2,
        vec![not_equality, not_quantified, falsity],
        vec![],
        vec![],
    );
    let implied =
        proof.add_resolution(vec![not_quantified, falsity], equality, equivalence, skolem);
    let derived = proof.add_resolution(vec![falsity], quantified, implied, assumed);
    let axiom = proof.add_rule_step(AletheRule::False, vec![not_false], vec![], vec![]);
    proof.add_resolution(vec![], falsity, derived, axiom);

    let mut overrides: HashMap<TermId, String> = HashMap::default();
    overrides.insert(quantified, quantifier.to_string());
    crate::try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        &terms,
        &[quantified],
        Some(&overrides),
    )
    .unwrap_or_else(|error| panic!("{quantifier} must export: {error}"))
}

#[test]
fn a_vacuous_collapse_proof_prints_the_bridge_and_keeps_false_false() {
    let output = render("(forall ((q Int)) (not (= q q)))");
    assert!(!output.contains(":rule hole"), "{output}");
    assert!(!output.contains(":rule trust"), "{output}");
    assert!(
        output.contains("(step t5 (cl (not false)) :rule false)"),
        "{output}"
    );
    // `(not (= c c))` is nowhere: not as a respelled `false`, and not as an
    // instance.
    assert!(
        !output.contains(&format!("(not (= {CHOICE} {CHOICE}))")),
        "{output}"
    );
    let anchored = format!(
        "(anchor :step t1 :args ((:= (q Int) {CHOICE})))\n\
         (step t1.t1 (cl (= (= q q) true)) :rule eq_simplify)\n\
         (step t1.t2 (cl (= (not (= q q)) (not true))) :rule cong :premises (t1.t1))\n\
         (step t1.t3 (cl (= (not true) false)) :rule not_simplify)\n\
         (step t1.t4 (cl (= (not (= q q)) false)) :rule trans :premises (t1.t2 t1.t3))\n\
         (step t1 (cl (= (forall ((q Int)) (not (= q q))) false)) :rule sko_forall)\n"
    );
    assert!(output.contains(&anchored), "{output}");
    // Outside the anchor the authored body occurs only inside the
    // quantifier itself.
    for line in output.lines() {
        if line.starts_with("(anchor ") || line.starts_with("(step t1.") {
            continue;
        }
        let without_quantifier = line.replace("(forall ((q Int)) (not (= q q)))", "");
        assert!(!without_quantifier.contains("(= q q)"), "{line}");
        assert!(!without_quantifier.contains("(choice "), "{line}");
    }
}

#[test]
fn a_body_outside_the_catalogue_keeps_the_bytes_the_base_printed() {
    // `(+ q 0)` is `q` to the store, so the IR is the same, but the printed
    // sides differ and no bridge is offered: the instance text is keyed on
    // `false` exactly as before, and the axiom stays the honest hole.
    // These are the base's bytes (measured at bca3b7c78 with this proof).
    let output = render("(forall ((q Int)) (not (= q (+ q 0))))");
    let choice = "(choice ((q Int)) (not (not (= q (+ q 0)))))";
    let instance = format!("(not (= {choice} (+ {choice} 0)))");
    let quantifier = "(forall ((q Int)) (not (= q (+ q 0))))";
    let expected = format!(
        "(assume t0 {quantifier})\n\
         (anchor :step t1 :args ((:= (q Int) {choice})))\n\
         (step t1.t1 (cl (= (not (= q (+ q 0))) {instance})) :rule refl)\n\
         (step t1 (cl (= {quantifier} {instance})) :rule sko_forall)\n\
         (step t2 (cl (not (= {quantifier} {instance})) (not {quantifier}) {instance}) :rule equiv_pos2)\n\
         (step t3 (cl (not {quantifier}) {instance}) :rule resolution :premises (t2 t1))\n\
         (step t4 (cl {instance}) :rule resolution :premises (t3 t0))\n\
         (step t5 (cl (not {instance})) :rule hole)\n\
         (step t6 (cl) :rule resolution :premises (t4 t5))\n"
    );
    assert_eq!(output, expected);
}

const BRIDGED: &str = "(forall ((q Int)) (not (= q q)))";
const DECLINED: &str = "(forall ((x Int)) (and (= x x) (< x x)))";
const DECLINED_CHOICE: &str = "(choice ((x Int)) (not (and (= x x) (< x x))))";

/// Two Skolemized binders in one proof whose bodies BOTH fold to the shared
/// `false`: [`BRIDGED`], in the catalogue, and [`DECLINED`], outside it.
/// `(assume (or A B))`, each Skolem instance resolved against its
/// quantifier, then the `false` axiom. `bridged_first` orders the two
/// Skolem chains. Returns the document and the bridged Skolem step's id.
fn render_mixed(bridged_first: bool) -> (String, ProofId) {
    let mut terms = TermStore::new();
    let falsity = terms.false_term();
    let bridged = terms.mk_forall(vec![("q".to_string(), Sort::Int)], falsity);
    let declined = terms.mk_forall(vec![("x".to_string(), Sort::Int)], falsity);
    assert_ne!(bridged, declined, "two binders, two quantifiers");
    let bridged_witness = terms.mk_var("sk!q_bridged", Sort::Int);
    terms.mark_skolem_symbol("sk!q_bridged");
    let declined_witness = terms.mk_var("sk!x_declined", Sort::Int);
    terms.mark_skolem_symbol("sk!x_declined");
    let either = terms.mk_app(Symbol::named("or"), [bridged, declined], Sort::Bool);
    let not_false = terms.mk_not_raw(falsity);

    let mut proof = Proof::new();
    let assumed = proof.add_assume(either, None);
    let split = proof.add_rule_step(
        AletheRule::Or,
        vec![bridged, declined],
        vec![assumed],
        vec![],
    );
    // `(cl (not Q) false)` through `sko_forall`, `equiv_pos2` and a
    // resolution; returns the resolution and the Skolem step.
    let chain = |terms: &mut TermStore, proof: &mut Proof, quantified, witness| {
        let equality = terms.mk_app(Symbol::named("="), [quantified, falsity], Sort::Bool);
        let not_equality = terms.mk_not_raw(equality);
        let not_quantified = terms.mk_not_raw(quantified);
        let skolem = proof.add_rule_step(AletheRule::Skolem, vec![equality], vec![], vec![witness]);
        let equivalence = proof.add_rule_step(
            AletheRule::EquivPos2,
            vec![not_equality, not_quantified, falsity],
            vec![],
            vec![],
        );
        let implied =
            proof.add_resolution(vec![not_quantified, falsity], equality, equivalence, skolem);
        (implied, skolem)
    };
    let (first, second) = if bridged_first {
        ((bridged, bridged_witness), (declined, declined_witness))
    } else {
        ((declined, declined_witness), (bridged, bridged_witness))
    };
    let (first_implied, first_skolem) = chain(&mut terms, &mut proof, first.0, first.1);
    let (second_implied, second_skolem) = chain(&mut terms, &mut proof, second.0, second.1);
    let bridged_skolem = if bridged_first {
        first_skolem
    } else {
        second_skolem
    };
    let without_first =
        proof.add_resolution(vec![second.0, falsity], first.0, split, first_implied);
    let only_false = proof.add_resolution(vec![falsity], second.0, without_first, second_implied);
    let axiom = proof.add_rule_step(AletheRule::False, vec![not_false], vec![], vec![]);
    proof.add_resolution(vec![], falsity, only_false, axiom);

    let mut overrides: HashMap<TermId, String> = HashMap::default();
    overrides.insert(bridged, BRIDGED.to_string());
    overrides.insert(declined, DECLINED.to_string());
    overrides.insert(either, format!("(or {BRIDGED} {DECLINED})"));
    let output = crate::try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        &terms,
        &[either],
        Some(&overrides),
    )
    .unwrap_or_else(|error| panic!("the mixed proof must export: {error}"));
    (output, bridged_skolem)
}

/// The declined binder keys its authored instance on the SHARED `false`
/// (today's path, unchanged), so the bridged binder's instance prints as
/// that text, not as `false`. The bridge's judgement must refuse the step:
/// its last sub-step concludes `(= (not (= q q)) false)`, and a
/// `sko_forall` over `(= BRIDGED (and (= c c) (< c c)))` after it is
/// invalid. The step is the honest hole, and nothing of the bridge is
/// printed.
///
/// The base printer (`bca3b7c78`) refused this export outright
/// (`InvalidSkolemStep`: both Skolem steps keyed DIFFERENT instance text on
/// `false`, "acquired incompatible choice renderings"); now only the
/// declined binder keys it, so the document exports, still fail-closed.
#[test]
fn a_bridged_step_whose_constant_another_skolem_step_respelled_is_the_hole() {
    for bridged_first in [true, false] {
        let (output, bridged) = render_mixed(bridged_first);
        let instance = format!(
            "(and (= {DECLINED_CHOICE} {DECLINED_CHOICE}) (< {DECLINED_CHOICE} {DECLINED_CHOICE}))"
        );
        assert!(
            output.contains(&format!(
                "(step {bridged} (cl (= {BRIDGED} {instance})) :rule hole)\n"
            )),
            "bridged_first={bridged_first}: the judgement must refuse:\n{output}"
        );
        assert!(
            !output.contains(&format!("(anchor :step {bridged} ")),
            "bridged_first={bridged_first}: no anchor for the refused step:\n{output}"
        );
        for rule in [
            "eq_simplify",
            "comp_simplify",
            "not_simplify",
            "cong",
            "trans",
        ] {
            assert!(
                !output.contains(&format!(":rule {rule}")),
                "bridged_first={bridged_first}: a bridge command was printed:\n{output}"
            );
        }
        // The declined binder keeps the base's certified step.
        assert_eq!(
            output.matches(":rule sko_forall)").count(),
            1,
            "bridged_first={bridged_first}:\n{output}"
        );
        assert!(
            output.contains(&format!("(step {bridged} ")),
            "bridged_first={bridged_first}:\n{output}"
        );
    }
}

/// A positive authored `exists` whose body the store folded to `false`:
/// `skolem_surface_binder_and_body` carries the AUTHORED body (there is no
/// skeleton to compare against a constant), so the anchor binds `q` to
/// `(choice ((q Int)) (not (= q q)))` and the bridge closes the `sko_ex`
/// over `false`. Read through the internal body instead, the step would
/// print `false` as the body, no bridge would be offered, and the authored
/// instance text would be keyed on the shared `false` again.
#[test]
fn an_authored_exists_whose_body_folded_closes_its_sko_ex_over_the_bridge() {
    use ay_core::SkolemChoice;

    let mut terms = TermStore::new();
    let falsity = terms.false_term();
    let quantified = terms.mk_exists(vec![("q".to_string(), Sort::Int)], falsity);
    let witness = terms.mk_var("sk!q_exists", Sort::Int);
    terms.mark_skolem_symbol("sk!q_exists");
    terms.register_skolem_choice(
        witness,
        SkolemChoice {
            binder: "q".to_string(),
            sort: Sort::Int,
            body: falsity,
        },
    );
    let equality = terms.mk_app(Symbol::named("="), [quantified, falsity], Sort::Bool);
    let mut proof = Proof::new();
    proof.add_rule_step(AletheRule::Skolem, vec![equality], vec![], vec![witness]);

    let authored = "(exists ((q Int)) (not (= q q)))";
    let mut overrides: HashMap<TermId, String> = HashMap::default();
    overrides.insert(quantified, authored.to_string());
    let output = crate::try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        &terms,
        &[quantified],
        Some(&overrides),
    )
    .unwrap_or_else(|error| panic!("{authored} must export: {error}"));
    let expected = format!(
        "(anchor :step t0 :args ((:= (q Int) (choice ((q Int)) (not (= q q))))))\n\
         (step t0.t1 (cl (= (= q q) true)) :rule eq_simplify)\n\
         (step t0.t2 (cl (= (not (= q q)) (not true))) :rule cong :premises (t0.t1))\n\
         (step t0.t3 (cl (= (not true) false)) :rule not_simplify)\n\
         (step t0.t4 (cl (= (not (= q q)) false)) :rule trans :premises (t0.t2 t0.t3))\n\
         (step t0 (cl (= {authored} false)) :rule sko_ex)\n"
    );
    assert_eq!(output, expected);
}

/// The refutation of an authored `exists` whose body the store folded to
/// `false`, rendered with `authored` as its spelling: the Skolem step,
/// `equiv_pos2`, resolution against the assumption, then the `false` axiom.
fn render_exists(authored: &str) -> String {
    use ay_core::SkolemChoice;

    let mut terms = TermStore::new();
    let falsity = terms.false_term();
    let quantified = terms.mk_exists(vec![("q".to_string(), Sort::Int)], falsity);
    let witness = terms.mk_var("sk!q_exists", Sort::Int);
    terms.mark_skolem_symbol("sk!q_exists");
    terms.register_skolem_choice(
        witness,
        SkolemChoice {
            binder: "q".to_string(),
            sort: Sort::Int,
            body: falsity,
        },
    );
    let equality = terms.mk_app(Symbol::named("="), [quantified, falsity], Sort::Bool);
    let not_equality = terms.mk_not_raw(equality);
    let not_quantified = terms.mk_not_raw(quantified);
    let not_false = terms.mk_not_raw(falsity);

    let mut proof = Proof::new();
    let assumed = proof.add_assume(quantified, None);
    let skolem = proof.add_rule_step(AletheRule::Skolem, vec![equality], vec![], vec![witness]);
    let equivalence = proof.add_rule_step(
        AletheRule::EquivPos2,
        vec![not_equality, not_quantified, falsity],
        vec![],
        vec![],
    );
    let implied =
        proof.add_resolution(vec![not_quantified, falsity], equality, equivalence, skolem);
    let derived = proof.add_resolution(vec![falsity], quantified, implied, assumed);
    let axiom = proof.add_rule_step(AletheRule::False, vec![not_false], vec![], vec![]);
    proof.add_resolution(vec![], falsity, derived, axiom);

    let mut overrides: HashMap<TermId, String> = HashMap::default();
    overrides.insert(quantified, authored.to_string());
    crate::try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        &terms,
        &[quantified],
        Some(&overrides),
    )
    .unwrap_or_else(|error| panic!("{authored} must export: {error}"))
}

/// An authored `exists` body is taken without the skeleton check ONLY when
/// the internal body is a Bool constant AND the bridge derives it. A folded
/// body outside the catalogue keeps the base's bytes (measured at
/// `bca3b7c78` with this proof): the Skolem step is the hole, and the axiom
/// still prints `(cl (not false))`. Admitting every folded body instead
/// would key the authored instance text on the shared `false` again and
/// print the axiom as `(cl (not (not (= c (+ c 0)))))`, a hole.
#[test]
fn an_authored_exists_outside_the_catalogue_keeps_the_bytes_the_base_printed() {
    for authored in [
        "(exists ((q Int)) (not (= q (+ q 0))))",
        "(exists ((q Int)) (and (= q q) (< q q)))",
    ] {
        let expected = format!(
            "(assume t0 {authored})\n\
             (step t1 (cl (= {authored} false)) :rule hole)\n\
             (step t2 (cl (not (= {authored} false)) (not {authored}) false) :rule equiv_pos2)\n\
             (step t3 (cl (not {authored}) false) :rule resolution :premises (t2 t1))\n\
             (step t4 (cl false) :rule resolution :premises (t3 t0))\n\
             (step t5 (cl (not false)) :rule false)\n\
             (step t6 (cl) :rule resolution :premises (t4 t5))\n"
        );
        assert_eq!(render_exists(authored), expected, "{authored}");
    }
}

/// The same refutation over a catalogue body has no hole: the `sko_ex`
/// closes over the bridge and the axiom prints `(cl (not false))`.
#[test]
fn an_authored_exists_in_the_catalogue_refutes_without_a_hole() {
    let authored = "(exists ((q Int)) (not (= q q)))";
    let expected = format!(
        "(assume t0 {authored})\n\
         (anchor :step t1 :args ((:= (q Int) (choice ((q Int)) (not (= q q))))))\n\
         (step t1.t1 (cl (= (= q q) true)) :rule eq_simplify)\n\
         (step t1.t2 (cl (= (not (= q q)) (not true))) :rule cong :premises (t1.t1))\n\
         (step t1.t3 (cl (= (not true) false)) :rule not_simplify)\n\
         (step t1.t4 (cl (= (not (= q q)) false)) :rule trans :premises (t1.t2 t1.t3))\n\
         (step t1 (cl (= {authored} false)) :rule sko_ex)\n\
         (step t2 (cl (not (= {authored} false)) (not {authored}) false) :rule equiv_pos2)\n\
         (step t3 (cl (not {authored}) false) :rule resolution :premises (t2 t1))\n\
         (step t4 (cl false) :rule resolution :premises (t3 t0))\n\
         (step t5 (cl (not false)) :rule false)\n\
         (step t6 (cl) :rule resolution :premises (t4 t5))\n"
    );
    assert_eq!(render_exists(authored), expected);
}
