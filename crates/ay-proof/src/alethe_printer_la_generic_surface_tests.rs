// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The `la_generic` replay against shapes measured on pinned carcara 1.1.0.
//!
//! Every accepted row below is a step carcara answered `valid` on; every
//! refused row is one it answered `invalid` on (or a shape its parser or
//! `negate_disequality` refuses). The eighth shape's own `t14` is the load-
//! bearing case: it is accepted by the checker ONLY through the integer
//! strengthening the replay mirrors.

use super::{
    printed_arith_commands, printed_la_generic_holds, printed_poly_simp_holds,
    printed_poly_simp_holds_under, printed_step_definitions, rendered_rule_field_names_arith,
    PrintedArithCommand,
};

const C: &str = "(choice ((z Int)) (not (or (< z 0) (>= (g z) z))))";

fn holds(literals: &[&str], args: &[&str]) -> bool {
    printed_la_generic_holds(literals, args)
}

#[test]
fn the_eighth_shapes_bound_adapter_is_accepted_through_integer_strengthening() {
    // fx8 `t14`: the rational sum is `1 > 0`; carcara strengthens both strict
    // rows over an integral constant and answers `valid`.
    let ge = format!("(>= (g {C}) {C})");
    let le = format!("(<= (+ (g {C}) 1) {C})");
    assert!(holds(&[&ge, &le], &["1", "1"]));
    // Bare symbols, the same relation.
    assert!(holds(&["(>= (g c) c)", "(<= (+ (g c) 1) c)"], &["1", "1"]));
}

#[test]
fn the_eighth_shapes_three_row_farkas_conflict_is_accepted() {
    // fx8 `t24`.
    let a = format!("(not (<= (f {C}) (g {C})))");
    let b = format!("(not (> (f {C}) {C}))");
    let c = format!("(not (<= (+ (g {C}) 1) {C}))");
    assert!(holds(&[&a, &b, &c], &["1", "1", "1"]));
}

#[test]
fn the_ninth_shape_ite_spelling_of_the_witness_is_refused() {
    // m01 `t14`: `(ite (= c c) c 0)` is one opaque atom to the checker and
    // `c` is another; the rows never cancel. carcara: "final disequality is
    // not contradictory".
    let ge = format!("(>= (g {C}) (ite (= {C} {C}) {C} 0))");
    let le = format!("(<= (+ (g {C}) 1) {C})");
    assert!(!holds(&[&ge, &le], &["1", "1"]));
}

#[test]
fn the_ninth_shape_select_store_spelling_of_the_witness_is_refused() {
    // g12 `t14`.
    let ge = format!("(>= (g {C}) (select (store A {C} {C}) {C}))");
    let le = format!("(<= (+ (g {C}) 1) {C})");
    assert!(!holds(&[&ge, &le], &["1", "1"]));
}

#[test]
fn a_plus_zero_spelling_of_the_witness_still_cancels() {
    // m02 `t14`: `LinearComb` flattens `+` and reads `0` as a constant, so
    // `(+ c 0)` IS `c` to the checker (measured `valid`).
    assert!(holds(
        &["(>= (g c) (+ c 0))", "(<= (+ (g c) 1) c)"],
        &["1", "1"]
    ));
}

#[test]
fn a_let_spelled_literal_is_refused() {
    // greenflag10's `t14`: `(let ..)` is not an arithmetic atom the checker
    // reads; carcara refuses the step.
    assert!(!holds(
        &["(let ((gz (g c))) (>= gz c))", "(<= (+ (g c) 1) c)"],
        &["1", "1"]
    ));
}

#[test]
fn arity_and_literal_shape_are_the_checkers() {
    // One argument per literal.
    assert!(!holds(&["(>= (g c) c)", "(<= (+ (g c) 1) c)"], &["1"]));
    // A positive equality has no negation the rule reads.
    assert!(!holds(&["(= x 1)", "(not (>= x 2))"], &["1", "1"]));
    // A doubled `not` is not a comparison.
    assert!(!holds(
        &["(not (not (<= x 1)))", "(not (>= x 2))"],
        &["1", "1"]
    ));
    // `distinct` is not a relation the rule reads.
    assert!(!holds(&["(distinct x 1)", "(not (>= x 2))"], &["1", "1"]));
    // A non-binary relation.
    assert!(!holds(&["(not (<= x y 1))", "(not (>= x 2))"], &["1", "1"]));
    // An argument that is not a number.
    assert!(!holds(&["(not (<= x 1))", "(not (>= x 2))"], &["1", "a"]));
}

#[test]
fn equality_rows_are_signed_and_inequality_rows_are_not() {
    // `x = 1` scaled by -1 against `x >= 2`: the variable cancels only with
    // the negative coefficient.
    assert!(holds(&["(not (= x 1))", "(not (>= x 2))"], &["(- 1)", "1"]));
    assert!(!holds(&["(not (= x 1))", "(not (>= x 2))"], &["1", "1"]));
    // GMP-style and `(/ ..)` fractions, and a bare negative numeral, are all
    // coefficients the checker reads.
    assert!(holds(&["(not (= x 1))", "(not (>= x 2))"], &["-1", "1"]));
    assert!(holds(
        &["(not (= (* 2 x) 2))", "(not (>= x 2))"],
        &["(- 1/2)", "1"]
    ));
    assert!(holds(
        &["(not (= (* 2 x) 2))", "(not (>= x 2))"],
        &["(- (/ 1 2))", "1"]
    ));
    // An inequality's coefficient is taken in magnitude.
    assert!(holds(&["(not (<= x 1))", "(not (>= x 2))"], &["-1", "1"]));
}

#[test]
fn the_strengthening_follows_the_constant_not_the_sort() {
    // MEASURED on pinned carcara 1.1.0 with `(declare-const x Real)`
    // (`probe_la.py`, 2026-09-13): it strengthens on the integrality of the
    // row's constant with no sort check, so `x < 1.5`, `x >= 1.2` — satisfiable
    // over the reals — is `valid` (`-x > -1.5` becomes `-x >= -1`, `x >= 1.2`
    // becomes `x >= 2`, sum `0 >= 1`), while `x < 1.5`, `x >= 1` is `invalid`
    // (`0 >= 0`) and so is `x > 0.5`, `x < 1.5`. The replay mirrors the
    // checker, not SMT-LIB, on all five probes.
    assert!(holds(&["(not (< x 1.5))", "(not (>= x 1.2))"], &["1", "1"]));
    assert!(!holds(&["(not (< x 1.5))", "(not (>= x 1))"], &["1", "1"]));
    assert!(!holds(&["(not (> x 0.5))", "(not (< x 1.5))"], &["1", "1"]));
    // A strict row over an integral constant: `x > 0`, `x < 1` — the
    // rational sum is `1 > 0`, the strengthened sum is `0 >= 2`; `valid` on
    // the checker for `Int` and `Real` alike.
    assert!(holds(&["(not (> x 0))", "(not (< x 1))"], &["1", "1"]));
    // The gcd form: `-2n > 2` strengthens to `-2n >= 4` (carcara's own
    // example in `strengthen`), which is what closes this step.
    assert!(holds(
        &[
            "(not (<= (- 1) n))",
            "(not (<= (- 1) (+ n m)))",
            "(<= (- 2) (* 2 n))",
            "(not (<= m 1))"
        ],
        &["1", "1", "1", "1"]
    ));
}

#[test]
fn a_satisfiable_row_set_is_refused() {
    assert!(!holds(&["(not (<= x 1))", "(not (>= x 1))"], &["1", "1"]));
    assert!(!holds(&["(not (<= x 1))", "(not (<= y 1))"], &["1", "1"]));
    // A zero-coefficient row drops out; what remains must still contradict.
    assert!(!holds(
        &["(not (<= x 1))", "(not (>= x 2))", "(not (<= y 0))"],
        &["0", "1", "1"]
    ));
}

#[test]
fn nonlinear_products_are_one_opaque_atom_each() {
    // `(* x y)` is one atom; the same product in both rows cancels.
    assert!(holds(
        &["(not (<= (* x y) 1))", "(not (>= (* x y) 2))"],
        &["1", "1"]
    ));
    // A differently spelled product is a different atom.
    assert!(!holds(
        &["(not (<= (* x y) 1))", "(not (>= (* y x) 2))"],
        &["1", "1"]
    ));
    // An n-ary product with a leading numeral is NOT scaled: `(* 2 3 x)` is
    // opaque to the checker, so it does not cancel `(* 6 x)`.
    assert!(!holds(
        &["(not (<= (* 2 3 x) 1))", "(not (>= (* 6 x) 2))"],
        &["1", "1"]
    ));
}

#[test]
fn atom_identity_is_the_parsers() {
    // `|c|` is `c`; whitespace inside an application is nothing; an
    // attribute is dropped.
    assert!(holds(
        &["(>= (g |c|) c)", "(<=  (+ (g c)   1) c)"],
        &["1", "1"]
    ));
    assert!(holds(
        &["(>= (! (g c) :named k) c)", "(<= (+ (g c) 1) c)"],
        &["1", "1"]
    ));
    // A quoted reserved word is not the keyword.
    assert!(!holds(
        &["(>= (g |cl|) c)", "(<= (+ (g cl) 1) c)"],
        &["1", "1"]
    ));
    // Two `choice` spellings differing in the binder are two atoms.
    let other = C.replace("z", "w");
    let ge = format!("(>= (g {C}) {C})");
    let le = format!("(<= (+ (g {other}) 1) {other})");
    assert!(!holds(&[&ge, &le], &["1", "1"]));
}

#[test]
fn a_positive_equality_is_poly_simp_and_never_la_generic() {
    // MEASURED (`probe_eq2.py`): `(cl (= 1.5 (/ 3.0 2.0)))` is `invalid`
    // under `la_generic :args (1)` and `valid` under `poly_simp`.
    assert!(!holds(&["(= 1.5 (/ 3.0 2.0))"], &["1"]));
    assert_eq!(printed_poly_simp_holds("1.5", "(/ 3.0 2.0)"), Some(true));
    assert_eq!(printed_poly_simp_holds("i", "(+ i 0)"), Some(true));
    assert_eq!(printed_poly_simp_holds("(* 2 x)", "(+ x x)"), Some(true));
    assert_eq!(printed_poly_simp_holds("1.5", "(/ 3.0 2.1)"), Some(false));
    assert_eq!(printed_poly_simp_holds("i", "(+ i 1)"), Some(false));
    assert_eq!(printed_poly_simp_holds("(f i)", "(f (+ i 0))"), Some(false));
}

#[test]
fn a_polynomial_identity_is_judged_by_the_pinned_normalizer() {
    // MEASURED on the pinned binary (`probe_ring.py`, 2026-09-13): the ring
    // identity and a commuted product are `valid` under `poly_simp`, the
    // identity with a wrong constant is `invalid` ("terms are not equal
    // after polynomial normalization"). `Polynomial::from_term` at the
    // pinned `9a352ee`, replayed over the text, answers the same.
    assert_eq!(
        printed_poly_simp_holds("(* (+ i 1) (+ i 1))", "(+ (* i i) (+ (* 2 i) 1))"),
        Some(true)
    );
    assert_eq!(
        printed_poly_simp_holds("(* (+ i 1) (+ i 1))", "(+ (* i i) (+ (* 2 i) 2))"),
        Some(false)
    );
    assert_eq!(printed_poly_simp_holds("(* x y)", "(* y x)"), Some(true));
    assert_eq!(
        printed_poly_simp_holds("(* i (+ i 1))", "(+ (* i i) i)"),
        Some(true)
    );
    // A division by a nonzero numeral scales; `to_real` is transparent; a
    // division by zero is one atom.
    assert_eq!(printed_poly_simp_holds("(/ x 2)", "(* 0.5 x)"), Some(true));
    assert_eq!(printed_poly_simp_holds("(to_real x)", "x"), Some(true));
    assert_eq!(printed_poly_simp_holds("(/ x 0)", "(/ x 0)"), Some(true));
    assert_eq!(printed_poly_simp_holds("(/ x 0)", "x"), Some(false));
    // An n-ary product is a product of polynomials, in any order.
    assert_eq!(
        printed_poly_simp_holds("(* x y z)", "(* z y x)"),
        Some(true)
    );
    assert_eq!(
        printed_poly_simp_holds("(* 2 x y)", "(+ (* x y) (* y x))"),
        Some(true)
    );
    assert_eq!(
        printed_poly_simp_holds("(+ (* i i) 1)", "(+ 1 (* i i))"),
        Some(true)
    );
    assert_eq!(
        printed_poly_simp_holds("(+ (* i i) 1)", "(+ 2 (* i i))"),
        Some(false)
    );
    // A bit-vector term is reduced modulo the SORT's width, which the text
    // does not carry: no judgement.
    assert_eq!(printed_poly_simp_holds("(bvadd x y)", "(bvadd y x)"), None);
    assert_eq!(printed_poly_simp_holds("#b0001", "(_ bv1 4)"), None);
}

#[derive(Debug, Eq, PartialEq)]
enum Read {
    La(String, Vec<String>, Vec<String>),
    Poly(String, String, String),
    Unreadable(Option<String>),
}

fn read(rendered: &str) -> Option<Vec<Read>> {
    Some(
        printed_arith_commands(rendered)?
            .into_iter()
            .map(|command| match command {
                PrintedArithCommand::LaGeneric(command) => Read::La(
                    command.name.to_string(),
                    command.literals.iter().map(ToString::to_string).collect(),
                    command.args.iter().map(ToString::to_string).collect(),
                ),
                PrintedArithCommand::PolySimp { name, left, right } => {
                    Read::Poly(name.to_string(), left.to_string(), right.to_string())
                }
                PrintedArithCommand::Unreadable { name } => {
                    Read::Unreadable(name.map(ToString::to_string))
                }
            })
            .collect(),
    )
}

fn names(rendered: &str) -> Vec<String> {
    read(rendered)
        .expect("readable")
        .into_iter()
        .map(|command| match command {
            Read::La(name, ..) | Read::Poly(name, ..) => name,
            Read::Unreadable(name) => name.unwrap_or_else(|| "?".to_string()),
        })
        .collect()
}

#[test]
fn commands_are_read_as_commands_not_as_lines_of_text() {
    let rendered = "(step t3.split (cl (<= (- x y) 1) (<= 2 (- x y))) :rule la_generic :args (1 1))\n\
                    (step t3.lo (cl (not (= x y)) (not (<= (- x y) 1))) :rule la_generic :args (1 1))\n\
                    (step t3 (cl (not (= x y))) :rule resolution :premises (t3.split t3.lo))";
    let commands = read(rendered).expect("two la_generic commands");
    assert_eq!(commands.len(), 2);
    assert_eq!(
        commands[0],
        Read::La(
            "t3.split".to_string(),
            vec!["(<= (- x y) 1)".to_string(), "(<= 2 (- x y))".to_string()],
            vec!["1".to_string(), "1".to_string()]
        )
    );
    assert_eq!(names(rendered), ["t3.split", "t3.lo"]);
    // A comment mentioning the rule is not a command.
    assert!(read("; :rule la_generic")
        .expect("comment skipped")
        .is_empty());
    // A step claiming the rule in a shape this printer never emits is read as
    // unreadable, which the caller refuses — under its own name, so the
    // refusal names the command and not the whole step.
    assert_eq!(
        read("(step t1 (cl) :rule la_generic :premises (t0))").expect("read"),
        [Read::Unreadable(Some("t1".to_string()))]
    );
    assert_eq!(
        read("(step t1 (cl (< x 1)) :rule la_generic)").expect("read"),
        [Read::Unreadable(Some("t1".to_string()))]
    );
    // A command spread over several lines is one command.
    let wrapped =
        "(step t1\n   (cl (<= (- x y) 1) (<= 2 (- x y)))\n   :rule la_generic :args (1 1))";
    assert_eq!(names(wrapped), ["t1"]);
}

#[test]
fn a_quoted_symbol_or_string_literal_spelling_the_rule_is_an_operand() {
    // REFUTED 2026-09-16, on three fixtures whose documents the pinned
    // checker calls `valid`: the reader scanned rendered LINES for the
    // substring `" :rule la_generic"` and refused the whole export of each.
    // None of these three is a rule; all three are legal SMT-LIB operands.
    for rendered in [
        r#"(assume t0 (= (|g :rule la_generic :args (1 1)| x) 1))"#,
        r#"(assume t0 (= s " :rule la_generic :args (1 1)"))"#,
        r#"(assume t0 (= s "x :rule poly_simp)"))"#,
        r#"(step t1 (cl (= s "a :rule la_generic :args (1 1)")) :rule refl)"#,
    ] {
        assert!(
            read(rendered).expect("readable").is_empty(),
            "read a rule out of an operand: {rendered}"
        );
        assert!(
            !rendered_rule_field_names_arith(rendered),
            "token scan read a rule out of an operand: {rendered}"
        );
    }
    // And the same text in the RULE FIELD is still read.
    let real = "(step t1 (cl (<= x 1) (<= 2 x)) :rule la_generic :args (1 1))";
    assert_eq!(names(real), ["t1"]);
    assert!(rendered_rule_field_names_arith(real));
    assert!(rendered_rule_field_names_arith(
        "(step t1 (cl (= x y)) :rule poly_simp)"
    ));
    // A `;` comment is not code to the token scan either.
    assert!(!rendered_rule_field_names_arith("; :rule la_generic"));
}

#[test]
fn poly_simp_commands_are_read_off_a_rendered_step() {
    let rendered = "(step t0.idx (cl (= (select (store a i 1.5) 0) 1.5)) :rule arrays_idx)\n\
                    (step t0.val (cl (= 1.5 (/ 3.0 2.0))) :rule poly_simp)\n\
                    (step t0 (cl (= (select (store a i 1.5) 0) (/ 3.0 2.0))) :rule trans :premises (t0.idx t0.val))";
    assert_eq!(
        read(rendered).expect("one poly_simp command"),
        [Read::Poly(
            "t0.val".to_string(),
            "1.5".to_string(),
            "(/ 3.0 2.0)".to_string()
        )]
    );
    for refused in [
        "(step t1 (cl (= x y) (= y z)) :rule poly_simp)",
        "(step t1 (cl (<= x y)) :rule poly_simp)",
        "(step t1 (cl (= x y)) :rule poly_simp :premises (t0))",
    ] {
        assert_eq!(
            read(refused).expect("read"),
            [Read::Unreadable(Some("t1".to_string()))],
            "{refused}"
        );
    }
}

#[test]
fn poly_simp_reads_the_steps_own_define_funs_as_the_checker_inlines_them() {
    // `complete_blast` names words longer than its inline limit and prints the
    // definitions in the same rendered text; the checker inlines each before
    // judging. Two names for one polynomial are one polynomial.
    let rendered = "(define-fun w1 () Int (+ x 1))\n\
                    (define-fun w2 () Int (+ 1 x))\n\
                    (define-fun w3 () Int (+ x 2))\n\
                    (define-fun w4 () Int (* 2 w1))\n\
                    (step t1.pr (cl (= w1 w2)) :rule poly_simp)\n";
    let definitions = printed_step_definitions(rendered);
    assert_eq!(
        printed_poly_simp_holds_under("w1", "w2", &definitions),
        Some(true)
    );
    assert_eq!(
        printed_poly_simp_holds_under("w4", "(+ w1 w2)", &definitions),
        Some(true)
    );
    // Still refused when the bodies differ, exactly as the checker refuses it.
    assert_eq!(
        printed_poly_simp_holds_under("w1", "w3", &definitions),
        Some(false)
    );
    // Without the definitions the names are two atoms: the old false refusal.
    assert_eq!(printed_poly_simp_holds("w1", "w2"), Some(false));
}

#[test]
fn poly_simp_under_definitions_abstains_on_bit_vectors_and_redefinitions() {
    // A bit-vector word: the judgement reads no sort, so it gives none.
    let rendered =
        "(define-fun a () (_ BitVec 32) (bvmul #b00000000000000000000000010000000 src))\n\
                    (define-fun b () (_ BitVec 32) (bvadd (bvadd src src) src))\n";
    let definitions = printed_step_definitions(rendered);
    assert_eq!(printed_poly_simp_holds_under("a", "b", &definitions), None);
    // A name defined twice is no judgement, never either body.
    let twice = "(define-fun w () Int x)\n(define-fun w () Int y)\n";
    let definitions = printed_step_definitions(twice);
    assert_eq!(printed_poly_simp_holds_under("w", "x", &definitions), None);
    // A self-referential body cannot loop: it runs out of depth or budget.
    let cyclic = "(define-fun w () Int (+ w 1))\n";
    let definitions = printed_step_definitions(cyclic);
    assert_eq!(printed_poly_simp_holds_under("w", "x", &definitions), None);
}
