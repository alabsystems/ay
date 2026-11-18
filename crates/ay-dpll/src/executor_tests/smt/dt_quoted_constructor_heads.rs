// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Constructor heads of printed datatype values. Each prints as the
//! `ay_core::symbol_token` of its output name (`Executor::dt_value_head`),
//! so a name that needs quoting, such as `||`, `|a b|` or `|true|`, reads
//! back as that constructor.

use super::*;

/// The responses to `input`, once in each posture.
fn run_both(input: &str) -> Vec<Vec<String>> {
    [true, false]
        .into_iter()
        .map(|z3_mode| {
            let mut exec = Executor::new();
            exec.set_competition_mode(z3_mode);
            exec.execute_all(&parse(input).expect("parse"))
                .expect("execute")
        })
        .collect()
}

/// `D`'s nullary constructors, as the script quotes them, and the constant
/// that holds each.
const QUOTED_CONSTRUCTORS: [(&str, &str); 8] = [
    ("x0", "||"),
    ("x1", "|a b|"),
    ("x2", "|let|"),
    ("x3", "|true|"),
    ("x4", "|1x|"),
    ("x5", r"|a\|b|"),
    ("x6", r"|\|\||"),
    ("x7", "plain"),
];

/// Each spelling of `QUOTED_CONSTRUCTORS` is the `ay_core::quote_symbol`
/// token of the name paired with it below. Here, in both postures, the
/// get-value response holds each constant with that token, `z` holds `||`
/// and `|\|\||` as two tokens, and the model holds each constant's
/// definition with its token and parses as one s-expression.
#[test]
fn each_constructor_head_prints_as_its_symbol_token() {
    let names = ["", "a b", "let", "true", "1x", "a|b", "||", "plain"];
    for ((_, token), name) in QUOTED_CONSTRUCTORS.iter().zip(names) {
        assert_eq!(ay_core::quote_symbol(name), *token);
    }
    let mut input = String::from("(set-logic ALL)\n(declare-datatypes ((D 0)) ((");
    for (_, token) in QUOTED_CONSTRUCTORS {
        input.push_str(&format!("({token}) "));
    }
    input.push_str(
        "(mk (fld Int)))))\n\
         (declare-datatypes ((W 0)) (((w (w1 D) (w2 D)))))\n\
         (declare-const z W)\n",
    );
    for (constant, token) in QUOTED_CONSTRUCTORS {
        input.push_str(&format!(
            "(declare-const {constant} D) (assert (= {constant} {token}))\n"
        ));
    }
    input.push_str(
        "(assert (= z (w || |\\|\\||)))\n\
         (check-sat)\n\
         (get-value (x0 x1 x2 x3 x4 x5 x6 x7 z))\n\
         (get-model)\n",
    );
    let mut values: Vec<String> = QUOTED_CONSTRUCTORS
        .iter()
        .map(|(constant, token)| format!("({constant} {token})"))
        .collect();
    values.push(r"(z (w || |\|\||))".to_string());
    let values = format!("({})", values.join(" "));
    for out in run_both(&input) {
        assert_eq!(out[0], "sat");
        assert_eq!(out[1], values);
        let model = &out[2];
        for (constant, token) in QUOTED_CONSTRUCTORS {
            let definition = format!("(define-fun {constant} () D {token})");
            assert!(model.contains(&definition), "{definition}:\n{model}");
        }
        assert!(
            model.contains(r"(define-fun z () W (w || |\|\||))"),
            "{model}"
        );
        assert!(
            matches!(ay_frontend::sexp::parse_sexps(model).as_deref(), Ok([_])),
            "{model}"
        );
    }
}

/// `L1` and `L2` both declare the constructor named by the empty symbol
/// `||`. Here, in both postures, get-value prints it as `(as || L1)` and
/// `(as || L2)`, and so does the model.
#[test]
fn an_overloaded_empty_constructor_prints_ascribed() {
    for out in run_both(
        "(set-logic ALL)\n\
         (declare-datatypes ((L1 0)) (((||) (cons (hd Int) (tl L1)))))\n\
         (declare-datatypes ((L2 0)) (((||) (c2 (h2 Int)))))\n\
         (declare-const x L1) (declare-const y L2)\n\
         (assert (= x (cons 1 (as || L1))))\n\
         (assert (= y (as || L2)))\n\
         (check-sat)\n\
         (get-value (x y))\n\
         (get-model)\n",
    ) {
        assert_eq!(out[0], "sat");
        assert_eq!(out[1], "((x (cons 1 (as || L1))) (y (as || L2)))");
        let model = &out[2];
        assert!(
            model.contains("(define-fun x () L1 (cons 1 (as || L1)))"),
            "{model}"
        );
        assert!(model.contains("(define-fun y () L2 (as || L2))"), "{model}");
    }
}

/// For each constructor of `Fruit` below, declared once, `pick`'s function
/// table holds it at `red`. Here, in both postures, the get-value response
/// is `(((pick red) X))` and the model holds the cell
/// `(ite (= x0 red) X apple)`, `X` the constructor as the script quotes it
/// (its `ay_core::quote_symbol` token, checked first), and the model parses
/// as one s-expression.
#[test]
fn a_function_table_cell_prints_its_constructor_token() {
    for (constructor, name) in [
        ("||", ""),
        ("|a b|", "a b"),
        ("|x(y|", "x(y"),
        ("|true|", "true"),
        ("|a#b|", "a#b"),
    ] {
        assert_eq!(ay_core::quote_symbol(name), constructor);
        let input = format!(
            "(set-logic ALL)\n\
             (declare-datatypes ((Color 0)) (((red) (blue))))\n\
             (declare-datatypes ((Fruit 0)) (((orange) ({constructor}) (apple))))\n\
             (declare-fun pick (Color) Fruit)\n\
             (assert (= (pick red) {constructor}))\n\
             (assert (= (pick blue) apple))\n\
             (check-sat)\n\
             (get-value ((pick red)))\n\
             (get-model)\n"
        );
        for out in run_both(&input) {
            assert_eq!(out[0], "sat", "{constructor}");
            assert_eq!(out[1], format!("(((pick red) {constructor}))"));
            let model = &out[2];
            let one_line = model.split_whitespace().collect::<Vec<_>>().join(" ");
            assert!(
                one_line.contains(&format!("Fruit (ite (= x0 red) {constructor} apple))")),
                "{constructor}:\n{model}"
            );
            assert!(
                matches!(ay_frontend::sexp::parse_sexps(model).as_deref(), Ok([_])),
                "{constructor}:\n{model}"
            );
        }
    }
}

/// `B`'s constructor `|a b|`, then `||`, is the value of `(g u)` and of `f`
/// in a script over the uninterpreted sort `U`. Here, in both postures, the
/// get-value response holds each with the constructor as the script quotes
/// it, and so does the model's definition of `f`.
#[test]
fn a_constructor_value_of_a_function_application_prints_its_token() {
    for constructor in ["|a b|", "||"] {
        let input = format!(
            "(set-logic QF_UFDT)\n\
             (declare-datatypes ((A 0)) (((kiwi2) (lime))))\n\
             (declare-datatypes ((B 0)) ((({constructor}) (pear))))\n\
             (declare-sort U 0)\n\
             (declare-fun g (U) B)\n\
             (declare-const u U)\n\
             (declare-const f B)\n\
             (assert (= f (g u)))\n\
             (assert (= (g u) {constructor}))\n\
             (check-sat)\n\
             (get-value (f (g u)))\n\
             (get-model)\n"
        );
        for out in run_both(&input) {
            assert_eq!(out[0], "sat", "{constructor}");
            assert_eq!(out[1], format!("((f {constructor}) ((g u) {constructor}))"));
            let definition = format!("(define-fun f () B {constructor})");
            assert!(out[2].contains(&definition), "{definition}:\n{}", out[2]);
        }
    }
}

/// The `nat`/`list`/`tree` script below, once with `tree`'s constructors
/// named `node` and `leaf` and once named `|nd#|` and `|lf#|`. Here, in both
/// postures, each response to the second script is the response to the
/// first with `node` and `leaf` replaced by `|nd#|` and `|lf#|`.
#[test]
fn a_quoted_constructor_head_reads_as_its_plain_twin() {
    let script = |node: &str, leaf: &str| {
        format!(
            "(set-logic QF_DT)\n\
             (declare-datatypes ((nat 0) (list 0) (tree 0))\n\
             (((succ (pred nat)) (zero))\n\
             ((cons (car tree) (cdr list)) (null))\n\
             (({node} (children list)) ({leaf} (data nat)))))\n\
             (declare-fun x1 () nat)\n\
             (declare-fun x2 () list)\n\
             (declare-fun x3 () tree)\n\
             (assert (and (= (data (car null)) x1)\n\
             (not (= (car (cons x3 (children (car (cdr (cdr null))))))\n\
             ({leaf} (pred (succ (succ (succ zero)))))))))\n\
             (check-sat)\n\
             (get-model)\n\
             (get-value ((car null) (car (cdr (cdr null))) (cdr (cdr null))))\n"
        )
    };
    let plain = run_both(&script("node", "leaf"));
    let quoted = run_both(&script("|nd#|", "|lf#|"));
    for (plain, quoted) in plain.iter().zip(&quoted) {
        assert_eq!(plain.len(), 3, "{plain:?}");
        assert_eq!(plain[0], "sat");
        let expected: Vec<String> = plain
            .iter()
            .map(|response| response.replace("node", "|nd#|").replace("leaf", "|lf#|"))
            .collect();
        assert_eq!(quoted, &expected);
    }
}

/// The array-cell shape of `dt_array_quoted_carrier.rs`, with the one
/// constructor of `T` named `|mk x|` or `|mk\|x|`. Here the answer is `sat`,
/// and the cell and the constant print the same constructor tree, headed by
/// that spelling.
#[test]
fn a_quoted_constructor_head_publishes_its_array_cell() {
    for constructor in ["|mk x|", r"|mk\|x|"] {
        let input = format!(
            "(set-logic ALL)\n\
             (declare-datatypes ((T 0)) ((({constructor} (f0 (_ BitVec 32)) \
             (f1 (_ BitVec 32))))))\n\
             (declare-const seed T)\n\
             (declare-const m (Array (_ BitVec 32) T))\n\
             (declare-const l4 Int)\n\
             (assert (= (select m #x00000000) seed))\n\
             (assert (<= l4 1))\n\
             (assert (= (f0 seed) #x00000005))\n\
             (assert (= (f1 (select m #x00000000)) #x00000009))\n\
             (check-sat)\n\
             (get-value ((select m #x00000000) seed))\n"
        );
        let mut exec = Executor::new();
        let out = exec
            .execute_all(&parse(&input).expect("parse"))
            .expect("execute");
        assert_eq!(out[0], "sat", "{constructor}: {out:?}");
        let tree = format!("({constructor} #x00000005 #x00000009)");
        assert_eq!(out[1].matches(&tree).count(), 2, "{tree}: {}", out[1]);
        assert!(!out[1].contains('@'), "{}", out[1]);
    }
}

/// `T`'s constructor `|mk x|` shares its name with the selector `|mk x|` of
/// `T`'s constructor `other`. Here the answer is `sat`, and the array cell
/// and the constant print the same constructor tree,
/// `(|mk x| #x00000005 #x00000009)`, with no `__ay_`.
#[test]
fn a_constructor_named_like_a_selector_publishes_its_array_cell() {
    let input = "(set-logic ALL)\n\
        (declare-datatypes ((T 0)) (((other (|mk x| Int)) \
        (|mk x| (f0 (_ BitVec 32)) (f1 (_ BitVec 32))))))\n\
        (declare-const seed T)\n\
        (declare-const m (Array (_ BitVec 32) T))\n\
        (declare-const l4 Int)\n\
        (assert ((_ is |mk x|) seed))\n\
        (assert (= (select m #x00000000) seed))\n\
        (assert (<= l4 1))\n\
        (assert (= (f0 seed) #x00000005))\n\
        (assert (= (f1 (select m #x00000000)) #x00000009))\n\
        (check-sat)\n\
        (get-value ((select m #x00000000) seed))\n";
    let mut exec = Executor::new();
    let out = exec
        .execute_all(&parse(input).expect("parse"))
        .expect("execute");
    assert_eq!(out[0], "sat", "{out:?}");
    let tree = "(|mk x| #x00000005 #x00000009)";
    assert_eq!(out[1].matches(tree).count(), 2, "{}", out[1]);
    assert!(!out[1].contains("__ay_"), "{}", out[1]);
}

/// Three array scripts over `L1`, whose nullary constructor is named `emp`
/// or one of `|pop|`, `|\|x|` and `|my nil|`: `L1` values as the elements of
/// `arr`, as the indices of `arr2`, and as the elements of `at`, indexed by
/// another datatype. Here, in both postures, the first two scripts answer
/// `sat` with `emp`, and each script's responses with each quoted name are
/// its responses with `emp`, with `emp` replaced by that name.
#[test]
fn a_quoted_nullary_constructor_reads_as_its_plain_twin_in_arrays() {
    let scripts = [
        "(declare-const arr (Array Int L1))\n\
         (assert (= (select arr 3) C))\n\
         (assert (= (select arr 4) (cons 4 C)))\n\
         (assert (= top C))\n\
         (check-sat)\n\
         (get-value (arr top))\n",
        "(declare-const arr2 (Array L1 Int))\n\
         (assert (= (select arr2 C) (- 9)))\n\
         (assert (= (select arr2 (cons 1 C)) 8))\n\
         (assert (= top C))\n\
         (check-sat)\n\
         (get-value (arr2 top))\n",
        "(declare-datatypes ((Third 0)) (((mk (cx Int)) (tnil))))\n\
         (declare-const at (Array Third L1))\n\
         (assert (= (select at (mk 4)) C))\n\
         (check-sat)\n\
         (get-value (at))\n",
    ];
    for (number, body) in scripts.into_iter().enumerate() {
        let script = |name: &str| {
            format!(
                "(set-logic ALL)\n\
                 (declare-datatypes ((L1 0)) ((({name}) (cons (hd Int) (tl L1)))))\n\
                 (declare-const top L1)\n{}",
                body.replace('C', name)
            )
        };
        let plain = run_both(&script("emp"));
        for name in ["|pop|", r"|\|x|", "|my nil|"] {
            let quoted = run_both(&script(name));
            for (plain, quoted) in plain.iter().zip(&quoted) {
                if number < 2 {
                    assert_eq!(plain[0], "sat", "{body}: {plain:?}");
                }
                let expected: Vec<String> = plain
                    .iter()
                    .map(|response| response.replace("emp", name))
                    .collect();
                assert_eq!(quoted, &expected, "{name} in {body}");
            }
        }
    }
}

/// Scripts that hold an application of a constructor whose fields are
/// constructors named by SMT-LIB command or Alethe words, written bare:
/// `pop`, `reset`, `exit`, `step`, `echo`. Here, in both postures, each
/// answers `sat`, its statistics show no `:model-unconfirmed` entry, and its
/// get-value response is the one given, in which each such word is its
/// quoted token.
#[test]
fn a_constructor_named_by_a_reserved_word_is_sat_inside_an_application() {
    let mut scripts = vec![
        (
            "(declare-datatypes ((Cmd 0)) (((pop) (push (v Int)) (seq (c1 Cmd) (c2 Cmd)))))\n\
             (declare-fun prog (Int) Cmd)\n\
             (assert (= (prog 0) (seq pop pop)))\n"
                .to_string(),
            "((prog 0))",
            "(((prog 0) (seq |pop| |pop|)))".to_string(),
        ),
        (
            "(declare-datatypes ((Cmd 0)) (((reset) (exit) (seq (c1 Cmd) (c2 Cmd)))))\n\
             (declare-fun prog (Int) Cmd)\n\
             (assert (= (prog 0) (seq reset exit)))\n\
             (assert (= (prog 1) exit))\n"
                .to_string(),
            "((prog 0) (prog 1))",
            "(((prog 0) (seq |reset| |exit|)) ((prog 1) |exit|))".to_string(),
        ),
        (
            "(declare-datatypes ((D 0)) (((step) (plain) (mk (fld D)))))\n\
             (declare-const x D)\n\
             (assert (= x (mk step)))\n"
                .to_string(),
            "(x)",
            "((x (mk |step|)))".to_string(),
        ),
    ];
    for word in ["step", "pop", "exit", "echo"] {
        scripts.push((
            format!(
                "(declare-datatypes ((D 0)) ((({word}) (halt) (mk (fld D)))))\n\
                 (declare-fun f (Int) D)\n\
                 (assert (= (f 0) (mk {word})))\n"
            ),
            "((f 0))",
            format!("(((f 0) (mk |{word}|)))"),
        ));
    }
    for (body, terms, values) in scripts {
        let input = format!(
            "(set-logic ALL)\n{body}(check-sat)\n(get-info :all-statistics)\n\
             (get-value {terms})\n"
        );
        for out in run_both(&input) {
            assert_eq!(out[0], "sat", "{body}: {out:?}");
            assert!(!out[1].contains(":model-unconfirmed"), "{body}: {}", out[1]);
            assert_eq!(out[2], values, "{body}");
        }
    }
}

/// The script of `a_quoted_constructor_head_publishes_its_array_cell`, with
/// `m` also asserted equal to a store of `(C #x00000005 #x00000009)` over the
/// constant array of `(C #x00000000 #x00000000)`, `C` each constructor name
/// below. Here, in both postures, the answer is `sat`, and the get-value
/// response holds `(C #x00000005 #x00000009)` twice.
#[test]
fn a_quoted_constructor_head_publishes_a_stored_array_cell() {
    for constructor in ["|C C|", "|C#|", "|pop|", "|mk x|", r"|mk\|x|"] {
        let tree = format!("({constructor} #x00000005 #x00000009)");
        let input = format!(
            "(set-logic ALL)\n\
             (declare-datatypes ((T 0)) ((({constructor} (f0 (_ BitVec 32)) \
             (f1 (_ BitVec 32))))))\n\
             (declare-const seed T)\n\
             (declare-const m (Array (_ BitVec 32) T))\n\
             (declare-const l4 Int)\n\
             (assert (= (select m #x00000000) seed))\n\
             (assert (<= l4 1))\n\
             (assert (= (f0 seed) #x00000005))\n\
             (assert (= (f1 (select m #x00000000)) #x00000009))\n\
             (assert (= m (store ((as const (Array (_ BitVec 32) T)) \
             ({constructor} #x00000000 #x00000000)) #x00000000 {tree})))\n\
             (check-sat)\n\
             (get-value ((select m #x00000000) seed))\n"
        );
        for out in run_both(&input) {
            assert_eq!(out[0], "sat", "{constructor}: {out:?}");
            assert_eq!(out[1].matches(&tree).count(), 2, "{tree}: {}", out[1]);
        }
    }
}

/// `D` declares the constructor `|a b|` and the constructor `|\|a b\||`,
/// whose name is `|a b|`, the first one's token. In each script below, in
/// both postures, the answer is `sat`, the get-value response is the one
/// given, in which each constructor prints as its own token, and the model
/// parses as one s-expression.
#[test]
fn a_constructor_named_like_another_constructors_token_prints_its_own_token() {
    let declarations = "(set-logic ALL)\n\
        (declare-datatypes ((D 0)) (((|a b|) (|\\|a b\\||) (other))))\n";
    let scripts = [
        (
            "(declare-const arr (Array Int D))\n\
             (declare-const x D)\n\
             (assert (= (select arr 0) |a b|))\n\
             (assert (= (select arr 1) |\\|a b\\||))\n\
             (assert (= x |a b|))\n\
             (check-sat)\n\
             (get-value (x (select arr 0) (select arr 1)))\n\
             (get-model)\n",
            r"((x |a b|) ((select arr 0) |a b|) ((select arr 1) |\|a b\||))",
        ),
        (
            "(declare-const arr (Array Int D))\n\
             (declare-const x D)\n\
             (assert (= (select arr 0) |a b|))\n\
             (assert (= x |\\|a b\\||))\n\
             (check-sat)\n\
             (get-value (x (select arr 0)))\n\
             (get-model)\n",
            r"((x |\|a b\||) ((select arr 0) |a b|))",
        ),
        (
            "(declare-const arr (Array D Int))\n\
             (assert (= (select arr |a b|) 1))\n\
             (assert (= (select arr |\\|a b\\||) 2))\n\
             (assert (= (select arr other) 3))\n\
             (check-sat)\n\
             (get-value ((select arr |a b|) (select arr |\\|a b\\||) (select arr other)))\n\
             (get-model)\n",
            r"(((select arr |a b|) 1) ((select arr |\|a b\||) 2) ((select arr other) 3))",
        ),
    ];
    for (body, values) in scripts {
        for out in run_both(&format!("{declarations}{body}")) {
            assert_eq!(out[0], "sat", "{body}: {out:?}");
            assert_eq!(out[1], values, "{body}");
            assert!(
                matches!(ay_frontend::sexp::parse_sexps(&out[2]).as_deref(), Ok([_])),
                "{body}:\n{}",
                out[2]
            );
        }
    }
}

/// `E` wraps a value of `D` in `wrap`, `arr` maps `D` to `E`, and `C` is
/// each constructor name of `D` below, whose identity is not one SMT-LIB
/// token (it holds or is edged by whitespace, or is the word `as`). `arr`
/// maps `C` to `cd` and `other` to `(wrap W)`, `W` first `C` and then
/// `other`, and `x`, which is not `cd`, is `arr` at `y`. Here, in both
/// postures, the answer is `sat` and the get-value response is the one
/// below.
#[test]
fn a_constructor_whose_identity_is_not_one_token_is_read_in_a_stored_field() {
    for constructor in ["|a b|", "| lead|", "|trail |", "| |", "|as|", "|a  b c|"] {
        for wrapped in [constructor, "other"] {
            let input = format!(
                "(set-logic ALL)\n\
                 (declare-datatypes ((D 0)) ((({constructor}) (other))))\n\
                 (declare-datatypes ((E 0)) (((cd) (e2) (wrap (un D)))))\n\
                 (declare-const arr (Array D E))\n\
                 (declare-const x E)\n\
                 (declare-const y D)\n\
                 (assert (= (select arr {constructor}) cd))\n\
                 (assert (= (select arr other) (wrap {wrapped})))\n\
                 (assert (= x (select arr y)))\n\
                 (assert (not (= x cd)))\n\
                 (check-sat)\n\
                 (get-value (x y (select arr other)))\n"
            );
            let values =
                format!("((x (wrap {wrapped})) (y other) ((select arr other) (wrap {wrapped})))");
            for out in run_both(&input) {
                assert_eq!(out[0], "sat", "{constructor} {wrapped}: {out:?}");
                assert_eq!(out[1], values, "{constructor} {wrapped}");
            }
        }
    }
}

/// `C` is each name below of a constructor of `D` with one field, whose
/// identity is not one SMT-LIB token or is the word `as`. `E` wraps a value
/// of `D` in `wrap`, `arr` maps `a2` to `cd` and `b2` to `(wrap (C b2))`, and
/// `x`, which is not `cd`, is `arr` at `y`. Here, in both postures, the
/// answer is `sat` and the get-value response is the one below.
#[test]
fn an_applied_constructor_whose_identity_is_not_one_token_is_read_in_a_stored_field() {
    for constructor in [
        "|a b|", "|a(b|", "|a)b|", "|a\"b|", "|as|", "|(|", "|)|", "|a b)|", "| lead|", "|trail |",
    ] {
        let input = format!(
            "(set-logic ALL)\n\
             (declare-datatypes ((D2 0)) (((a2) (b2))))\n\
             (declare-datatypes ((D 0)) ((({constructor} (p D2)) (other))))\n\
             (declare-datatypes ((E 0)) (((cd) (e2) (wrap (un D)))))\n\
             (declare-const arr (Array D2 E))\n\
             (declare-const x E)\n\
             (declare-const y D2)\n\
             (assert (= (select arr a2) cd))\n\
             (assert (= (select arr b2) (wrap ({constructor} b2))))\n\
             (assert (= x (select arr y)))\n\
             (assert (not (= x cd)))\n\
             (check-sat)\n\
             (get-value (x y (select arr b2)))\n"
        );
        let values = format!(
            "((x (wrap ({constructor} b2))) (y b2) ((select arr b2) (wrap ({constructor} b2))))"
        );
        for out in run_both(&input) {
            assert_eq!(out[0], "sat", "{constructor}: {out:?}");
            assert_eq!(out[1], values, "{constructor}");
        }
    }
}
