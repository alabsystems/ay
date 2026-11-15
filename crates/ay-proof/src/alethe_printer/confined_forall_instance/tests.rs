// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::try_export_alethe_with_problem_scope_and_overrides;

/// `(forall ((i Int)) (or (= (f i) x) (not (p i))))` instantiated at `k`, split
/// with `or` and resolved against its `assume`, so `t3` concludes the
/// canonical instance. `authored_function` names the function the AUTHORED
/// spellings use.
fn export(authored_function: &str) -> Result<String, AlethePrintError> {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let k = terms.mk_var("k", Sort::Int);
    let bound = terms.mk_var("i", Sort::Int);
    let body = {
        let p = terms.mk_app(Symbol::named("p"), [bound], Sort::Bool);
        let f = terms.mk_app(Symbol::named("f"), [bound], Sort::Int);
        let equality = terms.mk_app(Symbol::named("="), [f, x], Sort::Bool);
        let guard = terms.mk_not_raw(p);
        terms.mk_app(Symbol::named("or"), [equality, guard], Sort::Bool)
    };
    let forall = terms.mk_forall(vec![("i".to_string(), Sort::Int)], body);
    // `k` must be a problem symbol: the scope below carries `(p k)`.
    let p_k = terms.mk_app(Symbol::named("p"), [k], Sort::Bool);
    let instance = {
        let p = p_k;
        let f = terms.mk_app(Symbol::named("f"), [k], Sort::Int);
        let equality = terms.mk_app(Symbol::named("="), [f, x], Sort::Bool);
        let guard = terms.mk_not_raw(p);
        terms.mk_app(Symbol::named("or"), [equality, guard], Sort::Bool)
    };
    let negated_forall = terms.mk_not_raw(forall);
    let literal = terms.mk_app(Symbol::named("or"), [negated_forall, instance], Sort::Bool);
    let mut proof = Proof::new();
    let assumed = proof.add_assume(forall, None);
    let instantiated = proof.add_rule_step(
        ay_core::AletheRule::ForallInst,
        vec![literal],
        Vec::new(),
        vec![k],
    );
    let split = proof.add_rule_step(
        ay_core::AletheRule::Or,
        vec![negated_forall, instance],
        vec![instantiated],
        Vec::new(),
    );
    proof.add_resolution(vec![instance], forall, split, assumed);
    let g = authored_function;
    let mut overrides: HashMap<TermId, String> = HashMap::default();
    overrides.insert(
        forall,
        format!("(forall ((i Int)) (=> (p i) (= x ({g} i))))"),
    );
    overrides.insert(instance, format!("(=> (p k) (= x ({g} k)))"));
    try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        &terms,
        &[forall, p_k],
        Some(&overrides),
    )
}

#[test]
fn an_equivalent_authored_instance_is_confined_to_its_forall_inst() {
    let document = export("f").expect("the confined document renders");
    assert!(
        document.contains(
            "(step t1.fi (cl (or (not (forall ((i Int)) (=> (p i) (= x (f i))))) (=> (p k) (= x (f k))))) :rule forall_inst :args (k))"
        ),
        "{document}"
    );
    assert!(
        document.contains(
            "(step t1 (cl (or (not (forall ((i Int)) (=> (p i) (= x (f i))))) (or (= (f k) x) (not (p k))))) :rule resolution :premises (t1.e t1.c t1.fi))"
        ),
        "{document}"
    );
    // Every later step names the canonical instance.
    assert!(
        document.contains(
            "(step t2 (cl (not (forall ((i Int)) (=> (p i) (= x (f i))))) (or (= (f k) x) (not (p k)))) :rule or :premises (t1))"
        ),
        "{document}"
    );
    assert!(
        document.contains("(step t3 (cl (or (= (f k) x) (not (p k)))) :rule resolution"),
        "{document}"
    );
    assert!(!document.contains(":rule hole"), "{document}");
}

/// An authored instance that is NOT the canonical instance's formula (here a
/// different function symbol) has no checked bridge: nothing is confined and
/// the step renders exactly as it did before this pass existed.
#[test]
fn an_inequivalent_authored_instance_is_left_to_the_ordinary_rendering() {
    let document = export("g").expect("the unconfined document renders");
    assert!(!document.contains("t1.fi"), "{document}");
    assert!(
        document.contains(
            "(step t1 (cl (or (not (forall ((i Int)) (=> (p i) (= x (g i))))) (=> (p k) (= x (g k))))) :rule forall_inst :args (k))"
        ),
        "{document}"
    );
}

/// The array-frame update axiom `forall k. snew[k] = ite(k = 1, val, s[k])`
/// as AY stores it (Shannon-lifted, atoms re-oriented), instantiated at `0`,
/// split with `or`, resolved against its `assume`, and consumed by the `ite1`
/// the frame refutation uses: `t4 (cl (= 1 0) (= (select snew 0) (select s
/// 0)))`. `branches` is the authored `ite`'s `(then else)` text.
fn export_frame_update(branches: (&str, &str)) -> Result<String, AlethePrintError> {
    let mut terms = TermStore::new();
    let array = Sort::array(Sort::Int, Sort::Int);
    let s = terms.mk_var("s", array.clone());
    let snew = terms.mk_var("snew", array);
    let val = terms.mk_var("val", Sort::Int);
    let one = terms.mk_int(num_bigint::BigInt::from(1));
    let lifted = |terms: &mut TermStore, index: TermId| {
        let condition = terms.mk_app(Symbol::named("="), [one, index], Sort::Bool);
        let read_new = terms.mk_app(Symbol::named("select"), [snew, index], Sort::Int);
        let read_old = terms.mk_app(Symbol::named("select"), [s, index], Sort::Int);
        let updated = terms.mk_app(Symbol::named("="), [val, read_new], Sort::Bool);
        let framed = terms.mk_app(Symbol::named("="), [read_new, read_old], Sort::Bool);
        (
            terms.mk_ite_raw(condition, updated, framed),
            condition,
            framed,
        )
    };
    let bound = terms.mk_var("k", Sort::Int);
    let (body, _, _) = lifted(&mut terms, bound);
    let forall = terms.mk_forall(vec![("k".to_string(), Sort::Int)], body);
    let zero = terms.mk_int(num_bigint::BigInt::from(0));
    let (instance, condition, framed) = lifted(&mut terms, zero);
    let negated_forall = terms.mk_not_raw(forall);
    let literal = terms.mk_app(Symbol::named("or"), [negated_forall, instance], Sort::Bool);
    let mut proof = Proof::new();
    let assumed = proof.add_assume(forall, None);
    let instantiated = proof.add_rule_step(
        ay_core::AletheRule::ForallInst,
        vec![literal],
        Vec::new(),
        vec![zero],
    );
    let split = proof.add_rule_step(
        ay_core::AletheRule::Or,
        vec![negated_forall, instance],
        vec![instantiated],
        Vec::new(),
    );
    let resolved = proof.add_resolution(vec![instance], forall, split, assumed);
    proof.add_rule_step(
        ay_core::AletheRule::Ite1,
        vec![condition, framed],
        vec![resolved],
        Vec::new(),
    );
    let (then_text, else_text) = branches;
    let body = |index: &str| {
        let pick = |text: &str| text.replace("INDEX", index);
        format!(
            "(= (select snew {index}) (ite (= {index} 1) {} {}))",
            pick(then_text),
            pick(else_text)
        )
    };
    let mut overrides: HashMap<TermId, String> = HashMap::default();
    overrides.insert(forall, format!("(forall ((k Int)) {})", body("k")));
    overrides.insert(instance, body("0"));
    try_export_alethe_with_problem_scope_and_overrides(&proof, &terms, &[forall], Some(&overrides))
}

/// The measured false green, closed at its root: the authored update
/// instance is confined to its `forall_inst` by the `ite` lift, so the `ite1`
/// reads the canonical `ite` it was verified over. At ad60a0707 the authored
/// equality was the instance's text document-wide and pinned carcara refused
/// `t7` of the frame fixture's document: "term '(= (select snew 0) (ite (= 0
/// 1) val (select s 0)))' is of the wrong form, expected '(ite phi_1 phi_2
/// phi_3)'".
#[test]
fn an_authored_ite_instance_is_confined_and_its_ite1_reads_the_canonical_ite() {
    let document = export_frame_update(("val", "(select s INDEX)")).expect("renders");
    assert!(
        document.contains(
            "(step t1.fi (cl (or (not (forall ((k Int)) (= (select snew k) (ite (= k 1) val (select s k))))) \
             (= (select snew 0) (ite (= 0 1) val (select s 0))))) :rule forall_inst :args (0))"
        ),
        "{document}"
    );
    assert!(document.contains(":rule ite_intro"), "{document}");
    assert!(
        document.contains(
            "(step t3 (cl (ite (= 1 0) (= val (select snew 0)) (= (select snew 0) (select s 0)))) :rule resolution"
        ),
        "{document}"
    );
    assert!(
        document.contains(
            "(step t4 (cl (= 1 0) (= (select snew 0) (select s 0))) :rule ite1 :premises (t3))"
        ),
        "{document}"
    );
    assert!(!document.contains(":rule hole"), "{document}");
}

/// Negative twin: an authored instance whose `ite` is NOT the canonical
/// formula (branches exchanged) has no checked bridge, so its authored
/// equality stays the instance's text, and the `ite1` over it is not an
/// instance of the rule. The printer must decline that step to the honest
/// hole over its own clause, never ship `ite1` over an equality.
#[test]
fn an_ite1_over_an_unbridged_authored_equality_is_declined_to_a_hole() {
    let document = export_frame_update(("(select s INDEX)", "val")).expect("renders");
    assert!(!document.contains("t1.fi"), "{document}");
    assert!(
        document.contains("(step t3 (cl (= (select snew 0) (ite (= 0 1) (select s 0) val)))"),
        "{document}"
    );
    assert!(
        document.contains(&format!(
            "(step t4 (cl (= 1 0) (= (select snew 0) (select s 0))) :rule {})",
            ay_core::UNPROVED_STEP_RULE
        )),
        "{document}"
    );
    assert!(
        !document.contains(":rule ite1 :premises (t3)"),
        "{document}"
    );
}

/// The same update axiom instantiated at a Skolem WITNESS, as the `u64`
/// frame fixture's refutation does: a certified `sko_forall` gives
/// `sk!j_frame` its `choice` rendering, and the producer spells the instance
/// with the witness's internal name, which the printer re-spells. `branches`
/// is the authored `ite`'s `(then else)` text.
fn export_frame_update_at_witness(branches: (&str, &str)) -> Result<String, AlethePrintError> {
    let mut terms = TermStore::new();
    let array = Sort::array(Sort::Int, Sort::Int);
    let s = terms.mk_var("s", array.clone());
    let snew = terms.mk_var("snew", array);
    let val = terms.mk_var("val", Sort::Int);
    let zero = terms.mk_int(num_bigint::BigInt::from(0));
    let one = terms.mk_int(num_bigint::BigInt::from(1));
    let lifted = |terms: &mut TermStore, index: TermId| {
        let condition = terms.mk_app(Symbol::named("="), [one, index], Sort::Bool);
        let read_new = terms.mk_app(Symbol::named("select"), [snew, index], Sort::Int);
        let read_old = terms.mk_app(Symbol::named("select"), [s, index], Sort::Int);
        let updated = terms.mk_app(Symbol::named("="), [val, read_new], Sort::Bool);
        let framed = terms.mk_app(Symbol::named("="), [read_new, read_old], Sort::Bool);
        (
            terms.mk_ite_raw(condition, updated, framed),
            condition,
            framed,
        )
    };
    let nonnegative = |terms: &mut TermStore, index: TermId| {
        let read = terms.mk_app(Symbol::named("select"), [snew, index], Sort::Int);
        terms.mk_app(Symbol::named("<="), [zero, read], Sort::Bool)
    };
    let z = terms.mk_var("z", Sort::Int);
    let skolem_body = nonnegative(&mut terms, z);
    let skolemized = terms.mk_forall(vec![("z".to_string(), Sort::Int)], skolem_body);
    let witness = terms.mk_var("sk!j_frame", Sort::Int);
    terms.mark_skolem_symbol("sk!j_frame");
    let skolem_instance = nonnegative(&mut terms, witness);
    let skolem_equality = terms.mk_app(
        Symbol::named("="),
        [skolemized, skolem_instance],
        Sort::Bool,
    );
    let bound = terms.mk_var("k", Sort::Int);
    let (body, _, _) = lifted(&mut terms, bound);
    let forall = terms.mk_forall(vec![("k".to_string(), Sort::Int)], body);
    let (instance, condition, framed) = lifted(&mut terms, witness);
    let negated_forall = terms.mk_not_raw(forall);
    let literal = terms.mk_app(Symbol::named("or"), [negated_forall, instance], Sort::Bool);
    let mut proof = Proof::new();
    let assumed = proof.add_assume(forall, None);
    proof.add_rule_step(
        ay_core::AletheRule::Skolem,
        vec![skolem_equality],
        Vec::new(),
        vec![witness],
    );
    let instantiated = proof.add_rule_step(
        ay_core::AletheRule::ForallInst,
        vec![literal],
        Vec::new(),
        vec![witness],
    );
    let split = proof.add_rule_step(
        ay_core::AletheRule::Or,
        vec![negated_forall, instance],
        vec![instantiated],
        Vec::new(),
    );
    let resolved = proof.add_resolution(vec![instance], forall, split, assumed);
    proof.add_rule_step(
        ay_core::AletheRule::Ite1,
        vec![condition, framed],
        vec![resolved],
        Vec::new(),
    );
    let (then_text, else_text) = branches;
    let body = |index: &str| {
        let pick = |text: &str| text.replace("INDEX", index);
        format!(
            "(= (select snew {index}) (ite (= {index} 1) {} {}))",
            pick(then_text),
            pick(else_text)
        )
    };
    let mut overrides: HashMap<TermId, String> = HashMap::default();
    overrides.insert(forall, format!("(forall ((k Int)) {})", body("k")));
    overrides.insert(instance, body("sk!j_frame"));
    try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        &terms,
        &[forall, skolemized],
        Some(&overrides),
    )
}

const FRAME_WITNESS: &str = "(choice ((z Int)) (not (<= 0 (select snew z))))";

/// The `u64` frame fixture's witness projections, closed at their root: the
/// plan runs after Skolem preparation, confines the RE-SPELLED authored
/// instance to its `forall_inst`, and the `ite1` reads the canonical `ite`
/// over the witness's `choice` term. At c57bd8481 the plan ran first and
/// declined, and the `ite1` over the authored equality was holed.
#[test]
fn an_authored_instance_at_a_skolem_witness_is_confined_under_its_choice_spelling() {
    let document = export_frame_update_at_witness(("val", "(select s INDEX)")).expect("renders");
    let w = FRAME_WITNESS;
    assert!(
        document.contains(&format!(
            "(step t2.fi (cl (or (not (forall ((k Int)) (= (select snew k) (ite (= k 1) val (select s k))))) \
             (= (select snew {w}) (ite (= {w} 1) val (select s {w}))))) :rule forall_inst :args ({w}))"
        )),
        "{document}"
    );
    assert!(
        document.contains(&format!(
            "(step t4 (cl (ite (= 1 {w}) (= val (select snew {w})) (= (select snew {w}) (select s {w})))) :rule resolution"
        )),
        "{document}"
    );
    assert!(
        document.contains(&format!(
            "(step t5 (cl (= 1 {w}) (= (select snew {w}) (select s {w}))) :rule ite1 :premises (t4))"
        )),
        "{document}"
    );
    assert!(document.contains(":rule sko_forall"), "{document}");
    assert!(!document.contains("sk!j_frame"), "{document}");
    assert!(!document.contains(":rule hole"), "{document}");
}

/// Negative twin: at the witness too, an authored instance whose `ite` is
/// NOT the canonical formula has no checked bridge. It keeps its re-spelled
/// authored text, and the `ite1` over it declines to the honest hole.
#[test]
fn an_unbridged_authored_instance_at_a_skolem_witness_keeps_its_hole() {
    let document = export_frame_update_at_witness(("(select s INDEX)", "val")).expect("renders");
    let w = FRAME_WITNESS;
    assert!(!document.contains("t2.fi"), "{document}");
    assert!(
        document.contains(&format!(
            "(step t4 (cl (= (select snew {w}) (ite (= {w} 1) (select s {w}) val)))"
        )),
        "{document}"
    );
    assert!(
        document.contains(&format!(
            "(step t5 (cl (= 1 {w}) (= (select snew {w}) (select s {w}))) :rule {})",
            ay_core::UNPROVED_STEP_RULE
        )),
        "{document}"
    );
    assert!(!document.contains("sk!j_frame"), "{document}");
}
