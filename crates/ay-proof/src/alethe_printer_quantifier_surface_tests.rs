// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The printed-surface judgements for `forall_inst` and `sko_forall`.
//!
//! Every case here is stated against pinned carcara 1.1.0's own rules
//! (`carcara/src/checker/rules/quantifier.rs`, `subproof.rs`) and its
//! `Polyeq` (`carcara/src/ast/polyeq.rs`), because the only thing these
//! predicates are allowed to mean is "the pinned checker will accept this
//! exact text".

use super::{
    printed_forall_inst_holds, printed_skolem_step_holds, printed_terms_alpha_equivalent,
    PrintedSkolemStep,
};

const CHOICE: &str = "(choice ((z Int)) (not (or (< z 0) (>= (g z) z))))";

#[test]
fn an_instance_that_is_the_body_under_the_printed_args_holds() {
    assert!(printed_forall_inst_holds(
        "(or (not (forall ((w Int)) (> (f w) w))) (> (f a0) a0))",
        &["a0"],
    ));
}

#[test]
fn the_eighth_false_green_reduced_does_not_hold() {
    // The `:args` spell the witness as its `choice` term; the instance body
    // spells it by the internal name. carcara refuses the document at the
    // parser, and this predicate refuses the step over the same text.
    assert!(!printed_forall_inst_holds(
        "(or (not (forall ((w Int)) (> (f w) w))) (> (f sk!z_11_12) sk!z_11_12))",
        &[CHOICE],
    ));
}

#[test]
fn the_same_step_with_one_spelling_holds() {
    // The mutation differential for the case above: with the choice term at
    // both sites the step is exactly `forall_inst`.
    let literal = format!("(or (not (forall ((w Int)) (> (f w) w))) (> (f {CHOICE}) {CHOICE}))");
    assert!(printed_forall_inst_holds(&literal, &[CHOICE]));
}

#[test]
fn a_binder_left_in_the_instance_does_not_hold() {
    assert!(!printed_forall_inst_holds(
        "(or (not (forall ((w Int)) (> (f w) w))) (> (f a0) w))",
        &["a0"],
    ));
}

#[test]
fn a_reoriented_instance_does_not_hold() {
    // `(< a0 (f a0))` is the same atom to AY's term store and a different
    // term to carcara's parser: polyeq reorders equalities, nothing else.
    assert!(!printed_forall_inst_holds(
        "(or (not (forall ((w Int)) (> (f w) w))) (< a0 (f a0)))",
        &["a0"],
    ));
}

#[test]
fn a_reordered_equality_in_the_instance_holds() {
    assert!(printed_forall_inst_holds(
        "(or (not (forall ((w Int)) (= (f w) w))) (= a0 (f a0)))",
        &["a0"],
    ));
}

#[test]
fn multiple_binders_substitute_simultaneously() {
    // `x := y, y := 0` must not turn `x` into `0`.
    assert!(printed_forall_inst_holds(
        "(or (not (forall ((x Int) (y Int)) (< x y))) (< y 0))",
        &["y", "0"],
    ));
    assert!(!printed_forall_inst_holds(
        "(or (not (forall ((x Int) (y Int)) (< x y))) (< 0 0))",
        &["y", "0"],
    ));
}

#[test]
fn an_argument_count_that_differs_from_the_binder_count_does_not_hold() {
    assert!(!printed_forall_inst_holds(
        "(or (not (forall ((x Int) (y Int)) (< x y))) (< 1 2))",
        &["1"],
    ));
    assert!(!printed_forall_inst_holds(
        "(or (not (forall ((x Int)) (< x 2))) (< 1 2))",
        &["1", "2"],
    ));
}

#[test]
fn the_wrong_literal_shape_does_not_hold() {
    // `(not (not (not (forall ..))))` — the fourth shape's document — is not
    // `(or (not (forall ..)) result)` to a syntactic rule.
    assert!(!printed_forall_inst_holds(
        "(or (not (not (not (forall ((x Int)) (P x))))) (P a))",
        &["a"],
    ));
    assert!(!printed_forall_inst_holds("(P a)", &["a"]));
    assert!(!printed_forall_inst_holds(
        "(or (not (exists ((x Int)) (P x))) (P a))",
        &["a"],
    ));
}

#[test]
fn a_nested_binder_shadows_the_substituted_variable() {
    // The inner `x` is bound by the `exists`, so the substitution stops at it
    // (carcara's `Substitution::apply` does the same).
    assert!(printed_forall_inst_holds(
        "(or (not (forall ((x Int)) (and (P x) (exists ((x Int)) (Q x))))) (and (P a) (exists ((x Int)) (Q x))))",
        &["a"],
    ));
    assert!(!printed_forall_inst_holds(
        "(or (not (forall ((x Int)) (and (P x) (exists ((x Int)) (Q x))))) (and (P a) (exists ((x Int)) (Q a))))",
        &["a"],
    ));
}

#[test]
fn a_nested_binder_the_argument_would_capture_is_compared_modulo_renaming() {
    // Substituting the free constant `y` under `(exists ((y Int)) ..)` must
    // rename the bound `y`; the printed instance may spell the fresh binder
    // however it likes and still be alpha-equivalent.
    assert!(printed_forall_inst_holds(
        "(or (not (forall ((x Int)) (exists ((y Int)) (= y x)))) (exists ((y!1 Int)) (= y!1 y)))",
        &["y"],
    ));
    // An instance that let the capture happen is NOT the substitution image.
    assert!(!printed_forall_inst_holds(
        "(or (not (forall ((x Int)) (exists ((y Int)) (= y x)))) (exists ((y Int)) (= y y)))",
        &["y"],
    ));
}

#[test]
fn literal_spellings_carcara_parses_to_one_term_still_hold() {
    assert!(printed_forall_inst_holds(
        "(or (not (forall ((x (_ BitVec 8))) (= x #xAA))) (= (_ bv170 8) #xAA))",
        &["(_ bv170 8)"],
    ));
    assert!(printed_forall_inst_holds(
        "(or (not (forall ((x Real)) (< x 1.0))) (< 2 1))",
        &["2"],
    ));
    assert!(printed_forall_inst_holds(
        "(or (not (forall ((x Int)) (< x  1))) (<   2 1))",
        &["2"],
    ));
}

#[test]
fn a_pattern_annotation_on_the_body_is_transparent() {
    assert!(printed_forall_inst_holds(
        "(or (not (forall ((w Int)) (! (> (f w) w) :pattern ((g w))))) (> (f a0) a0))",
        &["a0"],
    ));
}

#[test]
fn alpha_equivalence_is_carcara_s_and_not_looser() {
    assert!(printed_terms_alpha_equivalent(
        "(forall ((x Int)) (= x 0))",
        "(forall ((y Int)) (= 0 y))"
    ));
    // Two binders swapped in the list are NOT alpha-equivalent: positions
    // differ (the example carcara's own comment gives).
    assert!(!printed_terms_alpha_equivalent(
        "(forall ((x Int) (y Int)) (< x y))",
        "(forall ((y Int) (x Int)) (< x y))"
    ));
    // A bound variable is never equal to a free one.
    assert!(!printed_terms_alpha_equivalent(
        "(forall ((x Int)) (P x))",
        "(forall ((y Int)) (P x))"
    ));
    // Binder sorts must agree.
    assert!(!printed_terms_alpha_equivalent(
        "(forall ((x Int)) (P x))",
        "(forall ((x Real)) (P x))"
    ));
    // Reordering is for binary equalities only.
    assert!(!printed_terms_alpha_equivalent("(< a b)", "(< b a)"));
    assert!(!printed_terms_alpha_equivalent("(= a b c)", "(= c b a)"));
}

fn fixture_skolem_step<'a>(choice: &'a str, instance: &'a str) -> PrintedSkolemStep<'a> {
    PrintedSkolemStep {
        rule: "sko_forall",
        quantified: "(forall ((z Int)) (or (< z 0) (>= (g z) z)))",
        binder: "z",
        sort: "Int",
        choice,
        body: "(or (< z 0) (>= (g z) z))",
        instance,
    }
}

#[test]
fn the_fixture_s_sko_forall_holds() {
    let instance = format!("(or (< {CHOICE} 0) (>= (g {CHOICE}) {CHOICE}))");
    assert!(printed_skolem_step_holds(&fixture_skolem_step(
        CHOICE, &instance
    )));
}

#[test]
fn a_sko_forall_whose_instance_spells_the_witness_raw_does_not_hold() {
    assert!(!printed_skolem_step_holds(&fixture_skolem_step(
        CHOICE,
        "(or (< sk!z_11_12 0) (>= (g sk!z_11_12) sk!z_11_12))",
    )));
}

#[test]
fn a_sko_forall_whose_choice_is_not_the_negated_body_does_not_hold() {
    let wrong = "(choice ((z Int)) (or (< z 0) (>= (g z) z)))";
    let instance = format!("(or (< {wrong} 0) (>= (g {wrong}) {wrong}))");
    assert!(!printed_skolem_step_holds(&fixture_skolem_step(
        wrong, &instance
    )));
}

#[test]
fn a_sko_forall_whose_anchor_binds_another_name_does_not_hold() {
    // carcara: `BindingIsNotInContext` — the anchor must assign the printed
    // quantifier's own binder.
    let instance = format!("(or (< {CHOICE} 0) (>= (g {CHOICE}) {CHOICE}))");
    let mut step = fixture_skolem_step(CHOICE, &instance);
    step.binder = "z0";
    assert!(!printed_skolem_step_holds(&step));
}

#[test]
fn a_sko_forall_whose_refl_body_is_not_the_quantifier_body_does_not_hold() {
    // `assert_eq(previous_equality.0, phi)` is syntactic identity: a
    // reoriented body in the `refl` is refused even though AY's term store
    // holds one atom.
    let instance = format!("(or (< {CHOICE} 0) (>= (g {CHOICE}) {CHOICE}))");
    let mut step = fixture_skolem_step(CHOICE, &instance);
    step.body = "(or (> 0 z) (>= (g z) z))";
    assert!(!printed_skolem_step_holds(&step));
}

#[test]
fn a_sko_ex_holds_with_the_unnegated_body() {
    let choice = "(choice ((x Int)) (P x))";
    let instance = format!("(P {choice})");
    assert!(printed_skolem_step_holds(&PrintedSkolemStep {
        rule: "sko_ex",
        quantified: "(exists ((x Int)) (P x))",
        binder: "x",
        sort: "Int",
        choice,
        body: "(P x)",
        instance: &instance,
    }));
    assert!(!printed_skolem_step_holds(&PrintedSkolemStep {
        rule: "sko_ex",
        quantified: "(exists ((x Int)) (P x))",
        binder: "x",
        sort: "Int",
        choice: "(choice ((x Int)) (not (P x)))",
        body: "(P x)",
        instance: "(P (choice ((x Int)) (not (P x))))",
    }));
}

#[test]
fn a_two_binder_quantifier_is_outside_the_single_anchor_shape() {
    assert!(!printed_skolem_step_holds(&PrintedSkolemStep {
        rule: "sko_forall",
        quantified: "(forall ((x Int) (y Int)) (P x y))",
        binder: "x",
        sort: "Int",
        choice: "(choice ((x Int)) (not (forall ((y Int)) (P x y))))",
        body: "(P x y)",
        instance: "(forall ((y Int)) (P (choice ((x Int)) (not (forall ((y Int)) (P x y)))) y))",
    }));
}

/// The one-spelling document for `(not (forall ((z Int)) (or (< z 0) (let
/// ((gz (g z))) (>= gz z)))))`, exactly as build 9666 shipped it under
/// `unproved_steps=0 ay_self_checkable=yes`, and pinned carcara 1.1.0's
/// verdict on it: `checking failed on step 't1.t1' with rule 'refl':
/// reflexivity failed` — its substitution leaves the `let`'s value `(g z)`
/// untouched, so the image it computes is not the instance AY prints (which
/// is the correct one under SMT-LIB semantics; the checker's is the one that
/// decides). The step has no printed form the checker accepts, so it declines.
#[test]
fn a_sko_forall_over_a_body_holding_a_let_does_not_hold() {
    let choice = "(choice ((z Int)) (not (or (< z 0) (let ((gz (g z))) (>= gz z)))))";
    let instance = format!("(or (< {choice} 0) (let ((gz (g {choice}))) (>= gz {choice})))");
    assert!(!printed_skolem_step_holds(&PrintedSkolemStep {
        rule: "sko_forall",
        quantified: "(forall ((z Int)) (or (< z 0) (let ((gz (g z))) (>= gz z))))",
        binder: "z",
        sort: "Int",
        choice,
        body: "(or (< z 0) (let ((gz (g z))) (>= gz z)))",
        instance: &instance,
    }));
    // The image carcara computes is not accepted either: the step is not
    // relabelled to match the checker's substitution, it declines.
    let checker_image = format!("(or (< {choice} 0) (let ((gz (g z))) (>= gz {choice})))");
    assert!(!printed_skolem_step_holds(&PrintedSkolemStep {
        rule: "sko_forall",
        quantified: "(forall ((z Int)) (or (< z 0) (let ((gz (g z))) (>= gz z))))",
        binder: "z",
        sort: "Int",
        choice,
        body: "(or (< z 0) (let ((gz (g z))) (>= gz z)))",
        instance: &checker_image,
    }));
}

/// Same substitution, `forall_inst`: a quantifier body holding a `let` has no
/// instance the pinned checker computes, with the binder in the `let`'s value
/// or only in its body (the latter aborts the checker outright — measured).
#[test]
fn a_forall_inst_over_a_body_holding_a_let_does_not_hold() {
    assert!(!printed_forall_inst_holds(
        "(or (not (forall ((w Int)) (let ((fw (f w))) (> fw w)))) (let ((fw (f a0))) (> fw a0)))",
        &["a0"],
    ));
    assert!(!printed_forall_inst_holds(
        "(or (not (forall ((w Int)) (let ((one 1)) (> (f w) (+ w one))))) (let ((one 1)) (> (f a0) (+ a0 one))))",
        &["a0"],
    ));
}

/// A `let` INSIDE a substituted argument is a different thing: carcara inserts
/// the argument verbatim and compares the `let` structurally. Measured on the
/// same document — with the two refused steps holed, its `forall_inst` steps
/// at the `choice` whose body holds the `let` were accepted (`holey`).
#[test]
fn a_let_inside_a_substituted_argument_still_holds() {
    let choice = "(choice ((z Int)) (not (or (< z 0) (let ((gz (g z))) (>= gz z)))))";
    let literal = format!("(or (not (forall ((w Int)) (> (f w) w))) (> (f {choice}) {choice}))");
    assert!(printed_forall_inst_holds(&literal, &[choice]));
}

/// The judgement must sit on the generic rule-step path: a `forall_inst`
/// whose instance the producer's override table spells with a raw witness
/// while the `:args` print the `choice` term must decline to `hole`, and the
/// same proof with one spelling must export the rule byte-identically.
#[test]
fn a_forall_inst_rule_step_is_judged_over_its_printed_surface() {
    use ay_core::kani_compat::DetHashMap;
    use ay_core::{AletheRule, Proof, Sort, Symbol, TermStore};

    let mut terms = TermStore::new();
    let w = terms.mk_var("w", Sort::Int);
    let f_w = terms.mk_app(Symbol::named("f"), [w], Sort::Int);
    let body = terms.mk_app(Symbol::named("<"), [w, f_w], Sort::Bool);
    let quantified = terms.mk_forall(vec![("w".to_string(), Sort::Int)], body);
    let a0 = terms.mk_var("a0", Sort::Int);
    let f_a0 = terms.mk_app(Symbol::named("f"), [a0], Sort::Int);
    let instance = terms.mk_app(Symbol::named("<"), [a0, f_a0], Sort::Bool);
    let not_q = terms.mk_not_raw(quantified);
    let implication = terms.mk_app(Symbol::named("or"), [not_q, instance], Sort::Bool);

    let mut proof = Proof::new();
    proof.add_rule_step(
        AletheRule::ForallInst,
        vec![implication],
        Vec::new(),
        vec![a0],
    );

    let clean = crate::try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        &terms,
        &[quantified, a0],
        None,
    )
    .expect("a spec-shaped forall_inst must still export");
    assert!(
        clean.contains(
            "(step t0 (cl (or (not (forall ((w Int)) (< w (f w)))) (< a0 (f a0)))) :rule forall_inst :args (a0))"
        ),
        "{clean}"
    );

    // The authored spelling `(> (f w) w)` for the canonical `(< w (f w))`,
    // propagated to the instance the way the producer does it — and the
    // instance's argument spelled differently from the `:args`.
    let mut overrides = DetHashMap::default();
    overrides.insert(quantified, "(forall ((w Int)) (> (f w) w))".to_string());
    overrides.insert(instance, "(> (f a1) a1)".to_string());
    let mutated = crate::try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        &terms,
        &[quantified, a0],
        Some(&overrides),
    )
    .expect("the declining export must still produce a document");
    assert!(mutated.contains(":rule hole"), "{mutated}");
    assert!(!mutated.contains(":rule forall_inst"), "{mutated}");

    // With the instance spelled as the body under the printed argument the
    // authored orientation ships as `forall_inst`. Since the printed
    // equivalence relates an operand-swapped comparison
    // (`surface_equivalence/comparison.rs`), that instance is confined to its
    // `forall_inst` and the canonical instance is derived from it with
    // `comp_simplify`.
    overrides.insert(instance, "(> (f a0) a0)".to_string());
    let faithful = crate::try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        &terms,
        &[quantified, a0],
        Some(&overrides),
    )
    .expect("a faithful override must export");
    assert!(
        faithful.contains(
            "(step t0.fi (cl (or (not (forall ((w Int)) (> (f w) w))) (> (f a0) a0))) :rule forall_inst :args (a0))"
        ),
        "{faithful}"
    );
    assert!(
        faithful.contains(
            "(step t0 (cl (or (not (forall ((w Int)) (> (f w) w))) (< a0 (f a0)))) :rule resolution"
        ),
        "{faithful}"
    );
    assert!(!faithful.contains(":rule hole"), "{faithful}");
}

/// The eighth false green, end to end: a certified Skolem step gives the
/// witness its `choice` rendering, and a `forall_inst` over ANOTHER
/// quantifier instantiated at that witness carries a producer override that
/// spells the witness by its internal name. The export must ship ONE
/// spelling — the `choice` term — at the instance, the `:args`, and every
/// downstream occurrence, and the raw name must appear nowhere.
#[test]
fn a_producer_override_naming_a_resugared_witness_is_respelled_to_its_choice() {
    use ay_core::kani_compat::DetHashMap;
    use ay_core::{AletheRule, Proof, Sort, Symbol, TermStore};

    let mut terms = TermStore::new();
    let z = terms.mk_var("z", Sort::Int);
    let zero = terms.mk_int(num_bigint::BigInt::from(0));
    let g_z = terms.mk_app(Symbol::named("g"), [z], Sort::Int);
    let lt = terms.mk_app(Symbol::named("<"), [z, zero], Sort::Bool);
    let ge = terms.mk_app(Symbol::named(">="), [g_z, z], Sort::Bool);
    let body = terms.mk_app(Symbol::named("or"), [lt, ge], Sort::Bool);
    let quantified = terms.mk_forall(vec![("z".to_string(), Sort::Int)], body);
    let witness = terms.mk_var("sk!z_test", Sort::Int);
    terms.mark_skolem_symbol("sk!z_test");
    let g_w = terms.mk_app(Symbol::named("g"), [witness], Sort::Int);
    let lt_w = terms.mk_app(Symbol::named("<"), [witness, zero], Sort::Bool);
    let ge_w = terms.mk_app(Symbol::named(">="), [g_w, witness], Sort::Bool);
    let instance = terms.mk_app(Symbol::named("or"), [lt_w, ge_w], Sort::Bool);
    let equality = terms.mk_app(Symbol::named("="), [quantified, instance], Sort::Bool);

    // A second, triggered quantifier `(forall ((w Int)) (> (f w) w))`, stored
    // as `(< w (f w))`, instantiated at the witness.
    let w = terms.mk_var("w", Sort::Int);
    let f_w = terms.mk_app(Symbol::named("f"), [w], Sort::Int);
    let other_body = terms.mk_app(Symbol::named("<"), [w, f_w], Sort::Bool);
    let other = terms.mk_forall(vec![("w".to_string(), Sort::Int)], other_body);
    let f_sk = terms.mk_app(Symbol::named("f"), [witness], Sort::Int);
    let other_instance = terms.mk_app(Symbol::named("<"), [witness, f_sk], Sort::Bool);
    let not_other = terms.mk_not_raw(other);
    let implication = terms.mk_app(Symbol::named("or"), [not_other, other_instance], Sort::Bool);

    let mut proof = Proof::new();
    proof.add_rule_step(AletheRule::Skolem, vec![equality], vec![], vec![witness]);
    proof.add_rule_step(
        AletheRule::ForallInst,
        vec![implication],
        Vec::new(),
        vec![witness],
    );

    // The producer's table: the authored spellings, and the instance rendered
    // through a printer that knows no choice term — the witness raw.
    let mut overrides: DetHashMap<ay_core::TermId, String> = DetHashMap::default();
    overrides.insert(other, "(forall ((w Int)) (> (f w) w))".to_string());
    overrides.insert(other_instance, "(> (f sk!z_test) sk!z_test)".to_string());

    let output = crate::try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        &terms,
        &[quantified, other],
        Some(&overrides),
    )
    .expect("one spelling per TermId must export");
    let choice = "(choice ((z Int)) (not (or (< z 0) (>= (g z) z))))";
    // The authored instance is confined to its `forall_inst` (`t1.fi`), and
    // the canonical `(< w (f w))` instance is derived from it, both over the
    // `choice` spelling (`surface_equivalence/comparison.rs`).
    assert!(
        output.contains(&format!(
            "(step t1.fi (cl (or (not (forall ((w Int)) (> (f w) w))) (> (f {choice}) {choice}))) \
             :rule forall_inst :args ({choice}))"
        )),
        "{output}"
    );
    assert!(
        output.contains(&format!(
            "(step t1 (cl (or (not (forall ((w Int)) (> (f w) w))) (< {choice} (f {choice})))) \
             :rule resolution"
        )),
        "{output}"
    );
    assert!(output.contains(":rule sko_forall"), "{output}");
    assert!(!output.contains("sk!z_test"), "{output}");
    assert!(!output.contains(":rule hole"), "{output}");
}

/// The bytes-level backstop: a rendering channel the re-spelling pass does
/// not know about still cannot ship a resugared witness raw — the export
/// declines instead of writing an unparseable document.
#[test]
fn a_raw_witness_reaching_the_wire_declines_the_export() {
    use ay_core::{AletheRule, Proof, Sort, Symbol, TermStore};

    let mut terms = TermStore::new();
    let i = terms.mk_var("i", Sort::Int);
    let p_i = terms.mk_app(Symbol::named("P"), [i], Sort::Bool);
    let quantified = terms.mk_forall(vec![("i".to_string(), Sort::Int)], p_i);
    let witness = terms.mk_var("sk!i_leak", Sort::Int);
    terms.mark_skolem_symbol("sk!i_leak");
    let p_w = terms.mk_app(Symbol::named("P"), [witness], Sort::Bool);
    let equality = terms.mk_app(Symbol::named("="), [quantified, p_w], Sort::Bool);
    let mut proof = Proof::new();
    proof.add_rule_step(AletheRule::Skolem, vec![equality], vec![], vec![witness]);
    let not_p_w = terms.mk_not_raw(p_w);
    proof.add_rule_step(AletheRule::Trust, vec![not_p_w], vec![], vec![]);

    let printer = crate::alethe_printer::AlethePrinter::new_with_overrides(&terms, None);
    printer.prepare_proof(&proof).expect("preparation succeeds");
    // A channel outside the re-spelling pass, simulated: the printer's own
    // rendering table acquires a raw spelling AFTER preparation.
    printer
        .skolem_overrides
        .borrow_mut()
        .insert(not_p_w, "(not (P sk!i_leak))".to_string());
    let error = printer
        .format_step(&proof.steps[1], ay_core::ProofId(1))
        .expect_err("a raw resugared witness must not reach the wire");
    assert!(
        matches!(
            &error,
            crate::AlethePrintError::ResugaredWitnessPrintedRaw { id, name }
                if *id == ay_core::ProofId(1) && name == "sk!i_leak"
        ),
        "{error}"
    );
}

#[test]
fn a_quoted_simple_symbol_is_the_bare_symbol_and_a_quoted_keyword_is_not() {
    // `|x|` and `x` are one symbol to every SMT-LIB reader; carcara's parser
    // drops the bars. A quoted RESERVED word stays a symbol distinct from the
    // keyword it spells, so `|true|` is never the constant `true`.
    assert!(printed_terms_alpha_equivalent("(P |x|)", "(P x)"));
    assert!(printed_terms_alpha_equivalent(
        "(forall ((|x| |S|)) (P x))",
        "(forall ((x S)) (P |x|))"
    ));
    assert!(!printed_terms_alpha_equivalent("|true|", "true"));
    assert!(!printed_terms_alpha_equivalent("(P |a b|)", "(P a)"));
    assert!(printed_forall_inst_holds(
        "(or (not (forall ((|w| Int)) (> (f w) |w|))) (> (f a0) a0))",
        &["a0"],
    ));
}

#[test]
fn an_authored_quoted_binder_sort_matches_the_anchor_s_bare_spelling() {
    // The authored quantifier may quote a sort name the anchor prints bare;
    // the judgement must not hole a step the checker accepts.
    let choice = "(choice ((x S)) (not (P x)))";
    let instance = format!("(P {choice})");
    assert!(printed_skolem_step_holds(&PrintedSkolemStep {
        rule: "sko_forall",
        quantified: "(forall ((|x| |S|)) (P x))",
        binder: "x",
        sort: "S",
        choice,
        body: "(P x)",
        instance: &instance,
    }));
}

/// One positive authored `exists` over the store's renamed binder and
/// canonicalized body, ready for the two tests below.
#[cfg(test)]
fn renamed_exists_skolem_proof(
    witness_name: &str,
) -> (ay_core::TermStore, ay_core::Proof, ay_core::TermId) {
    use ay_core::{AletheRule, Proof, SkolemChoice, Sort, Symbol, TermStore};

    let mut terms = TermStore::new();
    let z = terms.mk_var("z_3", Sort::Int);
    let zero = terms.mk_int(0.into());
    let g_z = terms.mk_app(Symbol::named("g"), [z], Sort::Int);
    let le = terms.mk_app(Symbol::named("<="), [zero, z], Sort::Bool);
    let lt = terms.mk_app(Symbol::named("<"), [g_z, z], Sort::Bool);
    let body = terms.mk_app(Symbol::named("and"), [le, lt], Sort::Bool);
    let quantified = terms.mk_exists(vec![("z_3".to_string(), Sort::Int)], body);
    let witness = terms.mk_var(witness_name, Sort::Int);
    terms.mark_skolem_symbol(witness_name);
    terms.register_skolem_choice(
        witness,
        SkolemChoice {
            binder: "z_3".to_string(),
            sort: Sort::Int,
            body,
        },
    );
    let g_w = terms.mk_app(Symbol::named("g"), [witness], Sort::Int);
    let le_w = terms.mk_app(Symbol::named("<="), [zero, witness], Sort::Bool);
    let lt_w = terms.mk_app(Symbol::named("<"), [g_w, witness], Sort::Bool);
    let instance = terms.mk_app(Symbol::named("and"), [le_w, lt_w], Sort::Bool);
    let equality = terms.mk_app(Symbol::named("="), [quantified, instance], Sort::Bool);
    let mut proof = Proof::new();
    proof.add_rule_step(AletheRule::Skolem, vec![equality], vec![], vec![witness]);
    (terms, proof, quantified)
}

/// The shape a hand probe found live on main beside the eighth: a positive
/// authored `exists` whose binder the store renamed (`z` → `z_3`) and whose
/// body it canonicalized (`(>= z 0)` → `(<= 0 z_3)`). On main the printed
/// quantifier was the AUTHORED spelling, the anchor bound the INTERNAL binder
/// to a `choice` over the canonical body, and carcara refused the `sko_ex`
/// (`BindingIsNotInContext`) under a green flag; the eighth fix declined it
/// to `hole`. Now the anchor binds the printed quantifier's own binder to a
/// `choice` over the printed body, the `refl` equates that body with its
/// image, and the step ships as `sko_ex` — one spelling, judged over the
/// text. The structural spelling is untouched.
#[test]
fn a_sko_ex_over_an_authored_exists_ships_the_authored_binder_and_body_under_the_anchor() {
    use ay_core::kani_compat::DetHashMap;

    let (terms, proof, quantified) = renamed_exists_skolem_proof("sk!z_3_ex");

    let structural = crate::try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        &terms,
        &[quantified],
        None,
    )
    .expect("a structural sko_ex exports");
    assert!(
        structural.contains(
            "(anchor :step t0 :args ((:= (z_3 Int) (choice ((z_3 Int)) (and (<= 0 z_3) (< (g z_3) z_3))))))"
        ),
        "{structural}"
    );
    assert!(structural.contains(":rule sko_ex"), "{structural}");
    assert!(!structural.contains(":rule hole"), "{structural}");

    let mut overrides: DetHashMap<ay_core::TermId, String> = DetHashMap::default();
    overrides.insert(
        quantified,
        "(exists ((z Int)) (and (>= z 0) (< (g z) z)))".to_string(),
    );
    let authored = crate::try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        &terms,
        &[quantified],
        Some(&overrides),
    )
    .expect("the authored sko_ex exports");
    let choice = "(choice ((z Int)) (and (>= z 0) (< (g z) z)))";
    assert!(
        authored.contains(&format!("(anchor :step t0 :args ((:= (z Int) {choice})))")),
        "{authored}"
    );
    assert!(
        authored.contains(&format!(
            "(step t0.t1 (cl (= (and (>= z 0) (< (g z) z)) (and (>= {choice} 0) (< (g {choice}) {choice})))) :rule refl)"
        )),
        "{authored}"
    );
    assert!(
        authored.contains(&format!(
            "(step t0 (cl (= (exists ((z Int)) (and (>= z 0) (< (g z) z))) (and (>= {choice} 0) (< (g {choice}) {choice})))) :rule sko_ex)"
        )),
        "{authored}"
    );
    assert!(!authored.contains(":rule hole"), "{authored}");
    assert!(
        !authored.contains("z_3"),
        "one spelling of the binder: {authored}"
    );
}

/// An authored `exists` body the store De Morgan'd — `(not (or A B))` for the
/// internal `(and (not A) (not B))` — is NOT carried under the anchor: the
/// instance's `and_pos` projections are read structurally by the checker,
/// and carrying the authored shape declined the whole export at the first
/// projection (measured on the `g13` fixture, 2026-09-13). The internal
/// spelling is kept and the `sko_ex` declines to the honest hole, exactly
/// as before the repair.
#[test]
fn a_sko_ex_whose_authored_body_has_another_head_keeps_the_internal_spelling_and_holes() {
    use ay_core::kani_compat::DetHashMap;

    let (terms, proof, quantified) = renamed_exists_skolem_proof("sk!z_3_dm");
    let mut overrides: DetHashMap<ay_core::TermId, String> = DetHashMap::default();
    overrides.insert(
        quantified,
        "(exists ((z Int)) (not (or (< z 0) (>= (g z) z))))".to_string(),
    );
    let authored = crate::try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        &terms,
        &[quantified],
        Some(&overrides),
    )
    .expect("the declining export still produces a document");
    assert!(
        authored.contains("(exists ((z Int)) (not (or (< z 0) (>= (g z) z))))"),
        "{authored}"
    );
    assert!(authored.contains(":rule hole"), "{authored}");
    assert!(!authored.contains(":rule sko_ex"), "{authored}");
    assert!(!authored.contains("(anchor "), "{authored}");
}
