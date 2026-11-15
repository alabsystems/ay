// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! #overloaded-nil-surface, API side: the solver's model readers.

use crate::api::model_parse::{decode_typed_value, parse_model_str};
use crate::api::*;
use crate::constructor_ascription::{
    as_application_pair, constructor_ascription_matrix, overload_pairs, AS_APPLICATION_OWN_SORT,
    AS_APPLICATION_UNIT, MATRIX_CONSTRUCTORS, MATRIX_SORTS, OVERLOAD_ASCRIBED_CONSTRUCTORS,
    OVERLOAD_BARE_CONSTRUCTORS, OVERLOAD_PAIR_VARIANTS,
};

fn list_dt(name: &str, head: Sort) -> DatatypeSort {
    DatatypeSort {
        name: name.to_string(),
        constructors: vec![
            DatatypeConstructor {
                name: "cons".to_string(),
                fields: vec![
                    DatatypeField {
                        name: "hd".to_string(),
                        sort: head,
                    },
                    DatatypeField {
                        name: "tl".to_string(),
                        sort: Sort::Datatype(DatatypeSort::new(name, vec![])),
                    },
                ],
            },
            DatatypeConstructor {
                name: "nil".to_string(),
                fields: vec![],
            },
        ],
    }
}

fn nullary(name: &str) -> ModelValue {
    ModelValue::Uninterpreted(name.to_string())
}

fn cons(head: ModelValue, tail: ModelValue) -> ModelValue {
    ModelValue::Datatype {
        constructor: "cons".to_string(),
        args: vec![head, tail],
    }
}

/// Asserts that `model` holds `y` in the uninterpreted map as `nil`, and `x`
/// as `(cons B (cons A nil))` with the nested `nil` as `Uninterpreted("nil")`.
fn assert_bare_representation(model: &Model) {
    assert_eq!(model.uninterpreted_val("y"), Some("nil"));
    assert_eq!(model.datatype_val("y"), None);
    assert_eq!(
        model.datatype_val("x"),
        Some(&cons(nullary("B"), cons(nullary("A"), nullary("nil"))))
    );
}

/// Here the legacy parser reads `u`, the abstract element `(as @S!0 S)`, as
/// `@S!0`, and keeps the ascription in the field of `p`.
#[test]
fn ascribed_abstract_element_is_not_a_constructor() {
    let model = parse_model_str(
        "(model\n  (define-fun u () S (as @S!0 S))\n  (define-fun p () P (mk (as @S!0 S)))\n)",
    );
    assert_eq!(model.uninterpreted_val("u"), Some("@S!0"));
    assert_eq!(model.datatype_val("u"), None);
    let Some(ModelValue::Datatype { constructor, args }) = model.datatype_val("p") else {
        panic!(
            "p is a constructor application: {:?}",
            model.datatype_val("p")
        );
    };
    assert_eq!(constructor, "mk");
    assert!(
        matches!(args.as_slice(), [ModelValue::Uninterpreted(text)]
            if text.contains("@S!0") && text.contains(" S)")),
        "the abstract element keeps its ascription: {args:?}"
    );
}

/// End to end, with `L1` and `L2` both declaring `nil`: here the printed
/// model holds `(as nil L1)` and `(as nil L2)`, and the readers below read
/// `nil`.
#[test]
fn try_get_model_reads_overloaded_nil_as_the_constructor() {
    let mut solver = Solver::new(Logic::All);
    let e = DatatypeSort {
        name: "E".to_string(),
        constructors: ["A", "B"]
            .into_iter()
            .map(|name| DatatypeConstructor {
                name: name.to_string(),
                fields: vec![],
            })
            .collect(),
    };
    let l1 = list_dt("L1", Sort::Datatype(e.clone()));
    let l2 = list_dt("L2", Sort::Int);
    solver.declare_datatype(&e);
    solver.declare_datatype(&l1);
    solver.declare_datatype(&l2);

    let x = solver.declare_const("x", Sort::Datatype(l1.clone()));
    let y = solver.declare_const("y", Sort::Datatype(l2.clone()));
    let a = solver.datatype_constructor(&e, "A", &[]);
    let b = solver.datatype_constructor(&e, "B", &[]);
    let nil1 = solver.datatype_constructor(&l1, "nil", &[]);
    let nil2 = solver.datatype_constructor(&l2, "nil", &[]);
    let inner = solver.datatype_constructor(&l1, "cons", &[a, nil1]);
    let outer = solver.datatype_constructor(&l1, "cons", &[b, inner]);
    let x_eq = solver.eq(x, outer);
    let y_eq = solver.eq(y, nil2);
    solver.assert_term(x_eq);
    solver.assert_term(y_eq);
    assert_eq!(solver.check_sat(), SolveResult::Sat);

    let text = solver.try_get_model_str().expect("model text");
    assert!(
        text.contains("(define-fun y () L2 (as nil L2))"),
        "the printed model ascribes the overloaded constructor: {text}"
    );
    assert!(text.contains("(as nil L1)"), "{text}");

    let model = solver.try_get_model().expect("model");
    assert_bare_representation(model.model());

    // The typed get-value decoder reads `nil` too.
    let nil = ModelValue::Datatype {
        constructor: "nil".to_string(),
        args: vec![],
    };
    assert_eq!(solver.try_get_value(y).expect("value of y"), nil);
    let map = solver.try_get_model_map().expect("model map");
    assert_eq!(map.get("y"), Some(&nil));
    let ctor = |name: &str, args: Vec<ModelValue>| ModelValue::Datatype {
        constructor: name.to_string(),
        args,
    };
    let tail = ctor("cons", vec![ctor("A", vec![]), nil.clone()]);
    assert_eq!(
        map.get("x"),
        Some(&ctor("cons", vec![ctor("B", vec![]), tail]))
    );
}

/// `(w nil nil)` as the legacy reader holds it.
fn w_of_two_nils() -> ModelValue {
    ModelValue::Datatype {
        constructor: "w".to_string(),
        args: vec![nullary("nil"), nullary("nil")],
    }
}

/// End to end: a parametric `List` and a monomorphic `L2` both declare
/// `nil`, and `W` holds one of each. Here the printed `v` ascribes both, the
/// first under `(List Int)`, and [`Solver::try_get_model`] reads both as
/// `nil`.
#[test]
fn try_get_model_reads_nil_ascribed_under_a_parametric_sort() {
    let mut solver = Solver::new(Logic::All);
    solver
        .parse_smtlib2(
            "(declare-datatypes ((List 1)) ((par (T) ((cons (hd T) (tl (List T))) (nil)))))\n\
             (declare-datatypes ((L2 0)) (((cons (hd Int) (tl L2)) (nil))))\n\
             (declare-datatypes ((W 0)) (((w (f1 (List Int)) (f2 L2)))))\n\
             (declare-const v W)\n\
             (assert (= v (w (as nil (List Int)) (as nil L2))))\n",
        )
        .expect("script");
    assert_eq!(solver.check_sat(), SolveResult::Sat);

    let text = solver.try_get_model_str().expect("model text");
    assert!(
        text.contains("(define-fun v () W (w (as nil (List Int)) (as nil L2)))"),
        "the printed model ascribes both constructors: {text}"
    );
    let model = solver.try_get_model().expect("model");
    assert_eq!(model.model().datatype_val("v"), Some(&w_of_two_nils()));
}

/// End to end for an array of an overloaded datatype: here the printed model
/// holds no bare `nil`, and the legacy model reader and the typed get-value
/// decoder read the default and each stored element as `nil`.
#[test]
fn array_of_overloaded_nil_reads_through_both_decoders() {
    let mut solver = Solver::new(Logic::All);
    let l1 = list_dt("L1", Sort::Bool);
    let l2 = list_dt("L2", Sort::Int);
    solver.declare_datatype(&l1);
    solver.declare_datatype(&l2);
    let a = solver.declare_const("a", Sort::array(Sort::Int, Sort::Datatype(l2.clone())));
    let three = solver.int_const(3);
    let nil2 = solver.datatype_constructor(&l2, "nil", &[]);
    let at_three = solver.select(a, three);
    let holds_nil = solver.eq(at_three, nil2);
    solver.assert_term(holds_nil);
    assert_eq!(solver.check_sat(), SolveResult::Sat);

    let text = solver.try_get_model_str().expect("model text");
    assert!(text.contains("(as nil L2)"), "{text}");
    assert!(
        !text
            .replace("(as nil L2)", "")
            .replace("(as nil L1)", "")
            .contains("nil"),
        "no bare nil remains: {text}"
    );

    let is_nil_everywhere_read = |value: &ModelValue, nil: &ModelValue| {
        let ModelValue::Array { default, stores } = value else {
            panic!("a is an array: {value:?}");
        };
        std::iter::once(default.as_ref())
            .chain(stores.iter().map(|(_, value)| value))
            .all(|value| value == nil)
    };
    let model = solver.try_get_model().expect("model");
    let legacy = model.model().array_values.get("a").expect("a is read");
    assert!(
        is_nil_everywhere_read(legacy, &nullary("nil")),
        "{legacy:?}"
    );

    let typed = solver.try_get_value(a).expect("value of a");
    let nil = ModelValue::Datatype {
        constructor: "nil".to_string(),
        args: vec![],
    };
    assert!(is_nil_everywhere_read(&typed, &nil), "{typed:?}");
}

/// What the typed get-value decoder reads from each constant definition of a
/// model text, against the sort the solver holds for the constant.
fn typed_readings(solver: &Solver, model_text: &str) -> Vec<(String, Option<ModelValue>)> {
    let context = solver.executor.context();
    let sorts: std::collections::HashMap<&str, &Sort> = context
        .symbol_iter()
        .map(|(name, info)| (name.as_str(), &info.sort))
        .collect();
    let mut typed = Vec::new();
    let root = ay_frontend::sexp::parse_sexp(model_text).expect("model text parses");
    for definition in root.as_list().expect("a model is a list") {
        let Some([_, name, parameters, _, value]) = definition.as_list() else {
            continue;
        };
        if parameters
            .as_list()
            .is_none_or(|parameters| !parameters.is_empty())
        {
            continue;
        }
        let name = name.as_symbol().expect("a definition names a symbol");
        let sort = sorts
            .get(name)
            .unwrap_or_else(|| panic!("{name} is declared"));
        typed.push((name.to_string(), decode_typed_value(value, sort, context)));
    }
    typed.sort_by(|left, right| left.0.cmp(&right.0));
    typed
}

/// For each case of `constructor_ascription_matrix` (#overloaded-nil-surface),
/// the printed model ascribes the constructor, `Executor::model_for_decoder`
/// is `AscriptionCase::bare` of it, the typed decoder reads the printed
/// model as it reads that text, and [`Solver::try_get_model`] is the legacy
/// parser's reading of that text.
#[test]
fn every_reader_takes_a_printed_ascription_as_the_bare_constructor() {
    let cases = constructor_ascription_matrix();
    assert_eq!(
        cases.len(),
        MATRIX_CONSTRUCTORS.len() * MATRIX_SORTS.len() * 4
    );
    for case in cases {
        let (solver, printed) = case.solve().unwrap_or_else(|error| panic!("{error}"));
        let printed_bare = case.bare(&printed);
        assert_ne!(printed_bare, printed, "{}", case.label);
        for (ascribed, _) in &case.ascriptions {
            assert!(
                !printed_bare.contains(ascribed.as_str()),
                "{}: {printed_bare}",
                case.label
            );
        }
        // The decoder text is `printed_bare`, with the name unquoted (`pop`).
        assert_eq!(
            solver.executor.model_for_decoder(),
            printed_bare,
            "{}:\n{printed}",
            case.label
        );
        let bare = printed_bare;

        assert_eq!(
            typed_readings(&solver, &printed),
            typed_readings(&solver, &bare),
            "{}:\n{printed}",
            case.label
        );

        let read_bare = parse_model_str(&bare);
        let model = solver.try_get_model().expect("model");
        assert_eq!(model.model(), &read_bare, "{}:\n{printed}", case.label);
        // No constructor named `as` is read.
        let read = format!("{read_bare:?}");
        assert!(!read.contains("\"as\""), "{}: {read}", case.label);
        assert!(!read.contains("|as|"), "{}: {read}", case.label);
    }
}

/// For each pair of `overload_pairs` (#overloaded-nil-surface), the readers
/// below read `pair.overloaded` as they read `pair.renamed`, whose decoder
/// text is its model text and whose model does not print the partner's name.
#[test]
fn every_reader_returns_the_same_whether_or_not_a_constructor_is_overloaded() {
    let pairs = overload_pairs();
    assert_eq!(
        pairs.len(),
        (OVERLOAD_ASCRIBED_CONSTRUCTORS.len() + OVERLOAD_BARE_CONSTRUCTORS.len())
            * OVERLOAD_PAIR_VARIANTS
    );
    let responses = |script: &str, queries: &str, z3_mode: bool| {
        let script = format!("{script}(check-sat)\n(get-model)\n(get-value ({queries}))\n");
        let mut executor = Executor::new();
        executor.set_competition_mode(z3_mode);
        executor
            .execute_all(&ay_frontend::parse(&script).expect("parse"))
            .expect("execute")
    };
    // The definitions of a text after `bare_constructor_spelling`, sorted:
    // the two scripts may print the same definitions in another order.
    let definitions = |text: &str| {
        let text = ay_core::bare_constructor_spelling(text);
        // The model's closer, on its own line, belongs to no definition.
        let text = text.strip_suffix("\n)").unwrap_or(&text);
        let mut definitions: Vec<String> =
            text.split("\n  (define-fun ").map(str::to_string).collect();
        definitions.sort();
        definitions
    };
    let mut ascribed_tops = 0;
    let mut parsed = 0;
    let mut failures: Vec<String> = Vec::new();
    for pair in pairs {
        let (overloaded_solver, overloaded) = pair
            .solve(&pair.overloaded)
            .unwrap_or_else(|error| panic!("{error}"));
        let (renamed_solver, renamed) = pair
            .solve(&pair.renamed)
            .unwrap_or_else(|error| panic!("{error}"));
        let mut differs = |reader: &str, same: bool| {
            if !same {
                failures.push(format!(
                    "{}, {reader}:\n{overloaded}\n{renamed}",
                    pair.label
                ));
            }
        };
        differs("the partner is not printed", !renamed.contains("unshared"));

        // A reader of the text alone.
        differs(
            "text only",
            definitions(&overloaded) == definitions(&renamed),
        );
        // The decoder text, which for the renamed script is its model text,
        // and the structured model.
        let decoder_text = |solver: &Solver| solver.try_get_model_str_for_decoder().ok();
        differs(
            "the decoder's text of the renamed script is its model text",
            decoder_text(&renamed_solver).as_deref() == Some(renamed.as_str()),
        );
        let structured = |solver: &Solver| solver.try_get_model().ok().map(|m| m.model().clone());
        differs(
            "try_get_model",
            structured(&overloaded_solver) == structured(&renamed_solver),
        );
        // The typed decoder, on each constant definition of text that parses.
        let parses = |text: &str| ay_frontend::sexp::parse_sexp(text).is_ok();
        differs("parses", parses(&overloaded) == parses(&renamed));
        if parses(&overloaded) && parses(&renamed) {
            parsed += 1;
            differs(
                "typed decoder",
                typed_readings(&overloaded_solver, &overloaded)
                    == typed_readings(&renamed_solver, &renamed),
            );
        }

        // The line of `p`, the application of `as`, is the same in both.
        let line_of = |text: &str, name: &str| {
            let start = format!("(define-fun {name} () ");
            text.lines()
                .find(|line| line.trim_start().starts_with(&start))
                .map(str::to_string)
        };
        differs(
            "p is printed",
            line_of(&renamed, "p").is_some() != pair.tables,
        );
        differs(
            "the application of `as`",
            line_of(&overloaded, "p") == line_of(&renamed, "p"),
        );
        let top = format!("(define-fun top () {} (as ", pair.sort);
        if overloaded.contains(&top) {
            differs(
                "only a name the frontend reads bare is ascribed",
                pair.ascribed(),
            );
            ascribed_tops += 1;
        }

        // `(get-model)` and `(get-value)` as commands, in both postures.
        for z3_mode in [true, false] {
            let overloaded = responses(&pair.overloaded, pair.queries, z3_mode);
            let renamed = responses(&pair.renamed, pair.queries, z3_mode);
            differs(
                "three responses",
                overloaded.len() == 3 && renamed.len() == 3,
            );
            for (overloaded, renamed) in overloaded.iter().zip(&renamed) {
                differs(
                    "a response, text only",
                    definitions(overloaded) == definitions(renamed),
                );
                let forms = |text: &str| ay_frontend::sexp::parse_sexps(text).ok();
                differs(
                    "a response parses",
                    forms(overloaded).is_some() == forms(renamed).is_some(),
                );
            }
        }
    }
    assert!(
        failures.is_empty(),
        "{} of the readings differ:\n{}",
        failures.len(),
        failures.join("\n----\n")
    );
    // Not vacuous: each name of `OVERLOAD_ASCRIBED_CONSTRUCTORS` is ascribed
    // at `top` in all of its scripts, and no name of
    // `OVERLOAD_BARE_CONSTRUCTORS` is.
    assert_eq!(
        ascribed_tops,
        OVERLOAD_ASCRIBED_CONSTRUCTORS.len() * OVERLOAD_PAIR_VARIANTS
    );
    // Not vacuous: the typed decoder read at least 40 pairs whose models
    // parse.
    assert!(parsed >= 40, "{parsed}");
}

/// For each name below, each model and value response holds `(as c Op1)`,
/// `c` quoted as `quote_symbol` quotes the name, and
/// `ay_core::bare_constructor_spelling` of it is the response of the script
/// whose `Op2` declares `unshared` instead, apart from the line of `b`.
#[test]
fn an_ascription_that_quotes_its_constructor_reads_back_as_the_bare_print() {
    let run = |constructor: &str, partner: &str, z3_mode: bool| {
        let script = format!(
            "(declare-datatypes ((Op1 0)) (((|{constructor}|) (halt))))\n\
             (declare-datatypes ((Op2 0)) (((|{partner}|) (stop))))\n\
             (declare-datatypes ((W 0)) (((w (w1 Op1) (w2 Op1)))))\n\
             (declare-const a Op1) (declare-const b Op2) (declare-const c W)\n\
             (assert (= a (as |{constructor}| Op1)))\n\
             (assert (= b (as |{partner}| Op2)))\n\
             (assert (= c (w a a)))\n\
             (check-sat)\n(get-model)\n(get-value (a c))\n"
        );
        let mut executor = Executor::new();
        executor.set_competition_mode(z3_mode);
        executor
            .execute_all(&ay_frontend::parse(&script).expect("parse"))
            .expect("execute")
    };
    for constructor in ["pop", "step", "let", "exit", "nil"] {
        let ascribed = format!("(as {} Op1)", ay_core::quote_symbol(constructor));
        for z3_mode in [true, false] {
            let overloaded = run(constructor, constructor, z3_mode);
            let plain = run(constructor, "unshared", z3_mode);
            assert_eq!(overloaded.len(), plain.len(), "{constructor}");
            assert_eq!(overloaded[0], "sat", "{constructor}");
            for (overloaded, plain) in overloaded.iter().zip(&plain).skip(1) {
                assert!(
                    overloaded.contains(&ascribed),
                    "{constructor}, z3_mode={z3_mode}: {overloaded}"
                );
                assert!(!plain.contains("(as "), "{constructor}: {plain}");
                // `b` is the one value the two scripts name differently.
                let read = ay_core::bare_constructor_spelling(overloaded);
                let lines = |text: &str| -> Vec<String> {
                    text.lines()
                        .filter(|line| !line.contains(" b () Op2 "))
                        .map(str::to_string)
                        .collect()
                };
                assert_eq!(
                    lines(&read),
                    lines(plain),
                    "{constructor}, z3_mode={z3_mode}"
                );
            }
        }
    }
}

/// End to end for names that look like theory names: a constructor named
/// `const`, and a parametric datatype named `Tuple`.
#[test]
fn try_get_model_reads_constructors_named_like_theory_values() {
    let read = |script: &str| {
        let mut solver = Solver::new(Logic::All);
        solver.parse_smtlib2(script).expect("script");
        assert_eq!(solver.check_sat(), SolveResult::Sat);
        let text = solver.try_get_model_str().expect("model text");
        let model = solver.try_get_model().expect("model");
        (text, model.model().clone())
    };
    let w_of = |left: &str, right: &str| ModelValue::Datatype {
        constructor: "w".to_string(),
        args: vec![nullary(left), nullary(right)],
    };

    let (text, model) = read(
        "(declare-datatypes ((L1 0)) (((cons (hd Bool) (tl L1)) (const))))\n\
         (declare-datatypes ((L2 0)) (((cons (hd Int) (tl L2)) (const))))\n\
         (declare-datatypes ((W 0)) (((w (f1 L1) (f2 L2)))))\n\
         (declare-const v W) (declare-const y L2)\n\
         (assert (= v (w (as const L1) (as const L2))))\n\
         (assert (= y (as const L2)))\n",
    );
    assert!(
        text.contains("(define-fun y () L2 (as const L2))"),
        "{text}"
    );
    assert!(
        text.contains("(define-fun v () W (w (as const L1) (as const L2)))"),
        "{text}"
    );
    assert_eq!(model.uninterpreted_val("y"), Some("const"));
    assert_eq!(model.datatype_val("y"), None);
    assert_eq!(model.datatype_val("v"), Some(&w_of("const", "const")));

    let (text, model) = read(
        "(declare-datatypes ((Tuple 2)) ((par (A B) ((mk (fst A) (snd B)) (nil)))))\n\
         (declare-datatypes ((L2 0)) (((cons (hd Int) (tl L2)) (nil))))\n\
         (declare-datatypes ((W 0)) (((w (f1 (Tuple Int Bool)) (f2 L2)))))\n\
         (declare-const v W)\n\
         (assert (= v (w (as nil (Tuple Int Bool)) (as nil L2))))\n",
    );
    assert!(
        text.contains("(define-fun v () W (w (as nil (Tuple Int Bool)) (as nil L2)))"),
        "{text}"
    );
    assert_eq!(model.datatype_val("v"), Some(&w_of("nil", "nil")));
}

/// Here `@a`, a constructor `L1` and `L2` both declare, prints bare, and
/// [`Solver::try_get_model`] reads it as `@a`.
#[test]
fn a_constructor_named_like_an_abstract_element_prints_bare() {
    let mut solver = Solver::new(Logic::All);
    solver
        .parse_smtlib2(
            "(declare-datatypes ((L1 0)) (((cons (hd Bool) (tl L1)) (@a))))\n\
             (declare-datatypes ((L2 0)) (((cons (hd Int) (tl L2)) (@a))))\n\
             (declare-datatypes ((W 0)) (((w (f1 L1) (f2 L2)))))\n\
             (declare-const v W) (declare-const y L2)\n\
             (assert (= v (w (as @a L1) (as @a L2))))\n\
             (assert (= y (as @a L2)))\n",
        )
        .expect("script");
    assert_eq!(solver.check_sat(), SolveResult::Sat);
    let text = solver.try_get_model_str().expect("model text");
    assert!(text.contains("(define-fun y () L2 @a)"), "{text}");
    assert!(text.contains("(define-fun v () W (w @a @a))"), "{text}");
    let model = solver.try_get_model().expect("model");
    assert_eq!(model.model().uninterpreted_val("y"), Some("@a"));
    assert_eq!(
        model.model().datatype_val("v"),
        Some(&ModelValue::Datatype {
            constructor: "w".to_string(),
            args: vec![nullary("@a"), nullary("@a")],
        })
    );
}

/// The nullary constructor `name` as the typed get-value decoder returns it.
fn typed_nullary(name: &str) -> ModelValue {
    ModelValue::Datatype {
        constructor: name.to_string(),
        args: vec![],
    }
}

/// The constant name `k` then `at`, zero-padded to `len - 1` digits.
fn wide_name(at: usize, len: usize) -> String {
    format!("k{at:0width$}", width = len - 1)
}

/// Here 1000 constants of 60 or 63 bytes hold the overloaded `None`: the model
/// text ascribes each, `try_get_named_values` reads each as `None`, and
/// `try_get_named_values_complete` returns a value for each.
#[test]
fn typed_named_values_are_charged_for_the_bare_spelling() {
    for name_len in [60, 63] {
        let names: Vec<String> = (0..1000).map(|at| wide_name(at, name_len)).collect();
        let mut script = String::from(
            "(declare-datatypes ((Oaaa 0)) (((SomeA (va Int)) (None))))\n\
             (declare-datatypes ((Obbb 0)) (((SomeB (vb Bool)) (None))))\n",
        );
        for name in &names {
            script.push_str(&format!(
                "(declare-const {name} Oaaa)\n(assert (= {name} (as None Oaaa)))\n"
            ));
        }
        let mut solver = Solver::new(Logic::All);
        solver.parse_smtlib2(&script).expect("script");
        assert_eq!(solver.check_sat(), SolveResult::Sat);

        // Here the model text ascribes each of them.
        let text = solver.try_get_model_str().expect("model text");
        for name in &names {
            let definition = format!("(define-fun {name} () Oaaa (as None Oaaa))");
            assert!(text.contains(&definition), "{name}");
        }

        let refs: Vec<&str> = names.iter().map(String::as_str).collect();
        let values = solver
            .try_get_named_values(&refs)
            .unwrap_or_else(|error| panic!("name_len {name_len}: {error:?}"));
        assert_eq!(values.len(), names.len());
        assert!(values.iter().all(|value| *value == typed_nullary("None")));
        let complete = solver
            .try_get_named_values_complete(&refs)
            .unwrap_or_else(|error| panic!("name_len {name_len}: {error:?}"));
        assert_eq!(complete.len(), names.len());
    }
}

/// A datatype of one unary and one nullary constructor, `None`.
fn option_dt(name: &str, some: &str, field: &str, sort: Sort) -> DatatypeSort {
    DatatypeSort {
        name: name.to_string(),
        constructors: vec![
            DatatypeConstructor {
                name: some.to_string(),
                fields: vec![DatatypeField {
                    name: field.to_string(),
                    sort,
                }],
            },
            DatatypeConstructor {
                name: "None".to_string(),
                fields: vec![],
            },
        ],
    }
}

/// Here 1000 constants of 62 bytes hold the overloaded `None` of `Oaaa`:
/// [`Solver::values_smtlib`] ascribes each, and [`Solver::try_get_values`]
/// and [`Solver::try_get_model_map`] read each as `None`.
#[test]
fn typed_term_values_are_charged_for_the_bare_spelling() {
    let mut solver = Solver::new(Logic::All);
    let oaaa = option_dt("Oaaa", "SomeA", "va", Sort::Int);
    let obbb = option_dt("Obbb", "SomeB", "vb", Sort::Bool);
    solver.declare_datatype(&oaaa);
    solver.declare_datatype(&obbb);
    let none = solver.datatype_constructor(&oaaa, "None", &[]);
    let terms: Vec<Term> = (0..1000)
        .map(|at| {
            let constant = solver.declare_const(&wide_name(at, 62), Sort::Datatype(oaaa.clone()));
            let is_none = solver.eq(constant, none);
            solver.assert_term(is_none);
            constant
        })
        .collect();
    assert_eq!(solver.check_sat(), SolveResult::Sat);

    let text = solver.values_smtlib(&terms).expect("value text");
    assert_eq!(text.matches(" (as None Oaaa))").count(), terms.len());

    let values = solver.try_get_values(&terms).expect("typed values");
    assert_eq!(values.len(), terms.len());
    assert!(values.iter().all(|value| *value == typed_nullary("None")));
    let map = solver.try_get_model_map().expect("model map");
    assert_eq!(map.len(), terms.len());
    assert!(map.values().all(|value| *value == typed_nullary("None")));
}

/// Here 25 constants hold 200 overloaded `nil`s each under a 40-byte sort:
/// the model text holds at least 5000 of them ascribed,
/// `Executor::model_for_decoder` holds no `(as nil`, and the scalar function
/// reader returns `f`.
#[test]
fn scalar_function_models_are_charged_for_the_bare_spelling() {
    use std::fmt::Write as _;
    let sort = format!("L{}", "a".repeat(39));
    let mut fields = String::new();
    for at in 0..200 {
        write!(fields, " (f{at} {sort})").expect("write to a String");
    }
    let nils = format!(" (as nil {sort})").repeat(200);
    let mut script = format!(
        "(declare-datatypes (({sort} 0)) (((cons (hd Bool) (tl {sort})) (nil))))\n\
         (declare-datatypes ((L2 0)) (((cons (hd Int) (tl L2)) (nil))))\n\
         (declare-datatypes ((W 0)) (((w{fields}))))\n\
         (declare-fun f ((_ BitVec 8)) (_ BitVec 8))\n\
         (assert (= (f #x01) #x07))\n"
    );
    for at in 0..25 {
        script.push_str(&format!(
            "(declare-const v{at} W)\n(assert (= v{at} (w{nils})))\n"
        ));
    }
    let mut solver = Solver::new(Logic::All);
    solver.parse_smtlib2(&script).expect("script");
    assert_eq!(solver.check_sat(), SolveResult::Sat);

    let text = solver.try_get_model_str().expect("model text");
    assert!(text.matches(&format!("(as nil {sort})")).count() >= 25 * 200);

    let models = solver
        .try_get_named_scalar_function_models(&["f"])
        .expect("scalar function model");
    assert_eq!(models.len(), 1);
    assert_eq!(models[0].name(), "f");
    assert!(!solver.executor.model_for_decoder().contains("(as nil"));
}

/// The datatype value of the constant `name` in the structured model of
/// `solver`.
fn structured(solver: &Solver, name: &str) -> ModelValue {
    let model = solver.try_get_model().expect("model");
    model
        .model()
        .datatype_val(name)
        .unwrap_or_else(|| panic!("{name} is a datatype value"))
        .clone()
}

/// The application of the constructor named `as` to `first` and `second`,
/// as the legacy reader holds it.
fn as_application(first: &str, second: &str) -> ModelValue {
    ModelValue::Datatype {
        constructor: "as".to_string(),
        args: vec![nullary(first), nullary(second)],
    }
}

/// Here `p`, the application of a constructor named `as`, prints as
/// `(as Unit Unit)` or `(as nil L1)` with nothing overloaded, and
/// [`Solver::try_get_model`] reads it as that application.
#[test]
fn try_get_model_reads_the_application_of_a_constructor_named_as() {
    for (script, line, first, second) in [
        (
            AS_APPLICATION_UNIT,
            "(define-fun p () P (as Unit Unit))",
            "Unit",
            "Unit",
        ),
        (
            AS_APPLICATION_OWN_SORT,
            "(define-fun p () P (as nil L1))",
            "nil",
            "L1",
        ),
    ] {
        let mut solver = Solver::new(Logic::All);
        solver.parse_smtlib2(script).expect("script");
        assert_eq!(solver.check_sat(), SolveResult::Sat);
        let text = solver.try_get_model_str().expect("model text");
        assert!(text.contains(line), "{text}");
        // Here the decoder text is the model text.
        assert_eq!(
            solver.model_str_for_decoder().as_deref(),
            Some(text.as_str())
        );
        assert_eq!(structured(&solver, "p"), as_application(first, second));
        // Nested in `qq`, the legacy reader holds it as the text
        // `(|as| ...)`.
        let ModelValue::Datatype { constructor, args } = structured(&solver, "qq") else {
            panic!("qq is a constructor application");
        };
        assert_eq!(constructor, "q");
        assert_eq!(
            args.first(),
            Some(&nullary(&format!("(|as| {first} {second})"))),
            "{text}"
        );
    }
}

/// The same application where its text is also the text of an ascription:
/// `(as nil Other)`, `Other` being an enumerator of the second field's sort
/// and a datatype that declares `nil` in one script and `unshared` in the
/// other. Both scripts print that line, and [`Solver::try_get_model`]
/// returns the application for both; the overloaded script ascribes the
/// `nil` of `t`, and the two structured models are equal.
#[test]
fn try_get_model_reads_an_application_of_as_the_same_under_an_overload() {
    let (overloaded, renamed) = as_application_pair();
    let solve = |script: &str| {
        let mut solver = Solver::new(Logic::All);
        solver.parse_smtlib2(script).expect("script");
        assert_eq!(solver.check_sat(), SolveResult::Sat);
        solver
    };
    let (overloaded, renamed) = (solve(&overloaded), solve(&renamed));
    let line = "(define-fun p () P (as nil Other))";
    for solver in [&overloaded, &renamed] {
        let text = solver.try_get_model_str().expect("model text");
        assert!(text.contains(line), "{text}");
        assert_eq!(structured(solver, "p"), as_application("nil", "Other"));
        let ModelValue::Datatype { args, .. } = structured(solver, "qq") else {
            panic!("qq is a constructor application");
        };
        assert_eq!(args.first(), Some(&nullary("(|as| nil Other)")), "{text}");
    }
    // The overloaded script ascribes the `nil` of `t` in the text that
    // leaves the solver, not in the decoder text.
    let surface = overloaded.try_get_model_str().expect("model text");
    assert!(
        surface.contains("(define-fun t () T (cons 1 (as nil T)))"),
        "{surface}"
    );
    let decoded = overloaded
        .try_get_model_str_for_decoder()
        .expect("decoder text");
    assert!(
        decoded.contains("(define-fun t () T (cons 1 nil))"),
        "{decoded}"
    );
    // The two scripts give a decoder the same definitions, compared sorted.
    let definitions = |text: &str| {
        let mut lines: Vec<String> = text.lines().map(str::to_string).collect();
        lines.sort();
        lines
    };
    assert_eq!(
        definitions(&decoded),
        definitions(&renamed.model_str_for_decoder().expect("decoder text"))
    );
    assert_eq!(
        overloaded.try_get_model().expect("model").model(),
        renamed.try_get_model().expect("model").model()
    );
}

/// The enumerations `Color`, which declares `green`, and `Fruit`, which
/// declares `second`, and uninterpreted functions pinned on `fruit_green`
/// (the script's spelling of `Fruit`'s `second`) in argument and result
/// columns.
fn enumeration_tables(second: &str, fruit_green: &str) -> String {
    format!(
        "(declare-datatypes ((Color 0)) (((red) (green) (blue))))\n\
         (declare-datatypes ((Fruit 0)) (((orange) ({second}) (apple))))\n\
         (declare-fun pick (Color) Fruit)\n\
         (declare-fun rev (Fruit) Color)\n\
         (declare-fun two (Fruit Fruit) Fruit)\n\
         (assert (= (pick red) {fruit_green}))\n\
         (assert (= (pick blue) apple))\n\
         (assert (= (rev {fruit_green}) (as green Color)))\n\
         (assert (= (rev apple) blue))\n\
         (assert (= (two {fruit_green} apple) {fruit_green}))\n\
         (assert (= (two apple {fruit_green}) orange))\n"
    )
}

/// Here `Color` and `Fruit` share `green`: the model text holds the cells
/// below, no response holds `__ay_`, and the decoder text, `try_get_model`
/// and `bare_constructor_spelling` of each response equal those of the
/// script whose `Fruit` declares `unshared` instead, `unshared` read as
/// `green`.
#[test]
fn an_enumeration_table_names_the_overloaded_constructor_in_every_cell() {
    let solve = |script: &str| {
        let mut solver = Solver::new(Logic::All);
        solver.parse_smtlib2(script).expect("parse");
        assert_eq!(solver.check_sat(), SolveResult::Sat);
        let model = solver.try_get_model_str().expect("model text");
        (solver, model)
    };
    let (overloaded_solver, overloaded) = solve(&enumeration_tables("green", "(as green Fruit)"));
    let (renamed_solver, renamed) = solve(&enumeration_tables("unshared", "unshared"));

    assert!(!overloaded.contains("__ay_"), "{overloaded}");
    for cell in [
        "(ite (= x0 red) (as green Fruit) apple)",
        "(ite (= x0 (as green Fruit)) (as green Color) blue)",
        "(ite (and (= x0 (as green Fruit)) (= x1 apple)) (as green Fruit) orange)",
    ] {
        assert!(overloaded.contains(cell), "{cell}:\n{overloaded}");
    }
    // The renamed script's text with `unshared` read as `green`.
    let as_overloaded = |text: &str| text.replace("unshared", "green");
    assert_eq!(
        ay_core::bare_constructor_spelling(&overloaded),
        as_overloaded(&renamed)
    );

    let decoder_text = |solver: &Solver| solver.try_get_model_str_for_decoder().expect("text");
    assert_eq!(decoder_text(&renamed_solver), renamed);
    assert_eq!(
        decoder_text(&overloaded_solver),
        as_overloaded(&renamed),
        "{overloaded}"
    );
    let structured = |solver: &Solver| solver.try_get_model().expect("model").model().clone();
    assert_eq!(
        format!("{:?}", structured(&overloaded_solver)),
        as_overloaded(&format!("{:?}", structured(&renamed_solver)))
    );

    // `(get-model)` and `(get-value)` as commands, in both postures.
    for z3_mode in [true, false] {
        let responses = |script: String, queries: &str| {
            let script = format!("{script}(check-sat)\n(get-model)\n(get-value ({queries}))\n");
            let mut executor = Executor::new();
            executor.set_competition_mode(z3_mode);
            executor
                .execute_all(&ay_frontend::parse(&script).expect("parse"))
                .expect("execute")
        };
        let overloaded = responses(
            enumeration_tables("green", "(as green Fruit)"),
            "(pick red) (rev (as green Fruit)) (two (as green Fruit) apple)",
        );
        let renamed = responses(
            enumeration_tables("unshared", "unshared"),
            "(pick red) (rev unshared) (two unshared apple)",
        );
        assert_eq!(overloaded.len(), 3);
        assert_eq!(renamed.len(), 3);
        for (overloaded, renamed) in overloaded.iter().zip(&renamed) {
            assert!(!overloaded.contains("__ay_"), "{overloaded}");
            assert_eq!(
                ay_core::bare_constructor_spelling(overloaded),
                as_overloaded(renamed)
            );
        }
        assert_eq!(
            overloaded[2],
            "(((pick red) (as green Fruit)) ((rev (as green Fruit)) (as green Color)) \
             ((two (as green Fruit) apple) (as green Fruit)))"
        );
    }
}

/// The enumerations `Color`, which declares `shared`, and `Fruit`, which
/// declares `second` (each as the script quotes it), a function table pinned
/// on `fruit_shared`, and constants that have nothing to do with it.
fn odd_enumeration_table(shared: &str, second: &str, fruit_shared: &str) -> String {
    format!(
        "(declare-datatypes ((Color 0)) (((red) ({shared}) (blue))))\n\
         (declare-datatypes ((Fruit 0)) (((orange) ({second}) (apple))))\n\
         (declare-fun pick (Color) Fruit)\n\
         (declare-const b Bool) (declare-const c Color) (declare-const d Fruit)\n\
         (assert (= (pick red) {fruit_shared}))\n\
         (assert (= (pick blue) apple))\n\
         (assert b) (assert (= c blue)) (assert (= d apple))\n"
    )
}

/// For each name below, shared by `Color` and `Fruit`: the model text and
/// the decoder text each parse as one s-expression and do not hold the name
/// unquoted after `(= x0 red)`, and `try_get_model` reads what it reads for
/// the script whose `Fruit` declares `unsharedQ` instead.
#[test]
fn an_enumeration_table_keeps_a_cell_whose_constructor_is_not_one_token() {
    for name in ["x(y", "(", ")", "x)", "a\"b", "\"", "x \"y", "a;b", "a b"] {
        let solve = |script: &str| {
            let mut solver = Solver::new(Logic::All);
            solver.parse_smtlib2(script).expect("parse");
            assert_eq!(solver.check_sat(), SolveResult::Sat, "{name}");
            solver
        };
        let quoted = format!("|{name}|");
        let overloaded = solve(&odd_enumeration_table(
            &quoted,
            &quoted,
            &format!("(as {quoted} Fruit)"),
        ));
        let renamed = solve(&odd_enumeration_table(&quoted, "unsharedQ", "unsharedQ"));

        let unquoted_cell = format!("(= x0 red) {name} ");
        for text in [
            overloaded.try_get_model_str().expect("model text"),
            overloaded
                .try_get_model_str_for_decoder()
                .expect("decoder text"),
        ] {
            let parsed = ay_frontend::sexp::parse_sexps(&text);
            assert!(
                matches!(parsed.as_deref(), Ok([_])),
                "{name}: not one s-expression:\n{text}"
            );
            assert!(!text.contains(&unquoted_cell), "{name}:\n{text}");
            assert!(text.contains("(define-fun pick ("), "{name}:\n{text}");
        }

        let structured = |solver: &Solver| {
            let model = solver.try_get_model().expect("model");
            format!("{:?}", model.model())
        };
        let read = structured(&overloaded);
        assert!(
            read.contains("blue") && read.contains("apple"),
            "{name}: {read}"
        );
        assert_eq!(read, structured(&renamed), "{name}");
    }
}

/// A model text with each run of whitespace as one space.
fn on_one_line(text: &str) -> String {
    text.split_whitespace().collect::<Vec<_>>().join(" ")
}

/// Each name below fails `constructor_ascription::reads_as_one_symbol`. Here,
/// with `Color` and `Fruit` sharing it, the cell keeps `__ay_overload_0` in
/// the model text and in the decoder text; in the decoder text of the twin
/// whose `Color` declares `unsharedQ` instead, the cell holds the name.
#[test]
fn an_enumeration_table_keeps_a_cell_whose_constructor_reads_as_no_symbol() {
    for name in [
        "true", "false", ":k", "5", "-5", "#x0f", "\"a\"", "5.0", "a#b",
    ] {
        assert!(
            !crate::constructor_ascription::reads_as_one_symbol(name),
            "{name}"
        );
        let solve = |script: &str| {
            let mut solver = Solver::new(Logic::All);
            solver.parse_smtlib2(script).expect("parse");
            assert_eq!(solver.check_sat(), SolveResult::Sat, "{name}");
            solver
        };
        let quoted = format!("|{name}|");
        let overloaded = solve(&odd_enumeration_table(
            &quoted,
            &quoted,
            &format!("(as {quoted} Fruit)"),
        ));
        for text in [
            overloaded.try_get_model_str().expect("model text"),
            overloaded
                .try_get_model_str_for_decoder()
                .expect("decoder text"),
        ] {
            assert!(
                on_one_line(&text).contains("Fruit (ite (= x0 red) __ay_overload_0 apple))"),
                "{name}:\n{text}"
            );
            assert!(
                matches!(ay_frontend::sexp::parse_sexps(&text).as_deref(), Ok([_])),
                "{name}: not one s-expression:\n{text}"
            );
        }
        // The twin whose `Color` declares `unsharedQ` instead.
        let twin = solve(&odd_enumeration_table("unsharedQ", &quoted, &quoted));
        let text = twin.try_get_model_str_for_decoder().expect("text");
        assert!(
            on_one_line(&text).contains(&format!("Fruit (ite (= x0 red) {name} apple))")),
            "{name}:\n{text}"
        );
    }
}

/// A parametric enumeration `PE` with the member `member` (as the script
/// quotes it), a table from `(PE Int)` pinned on it, and constants that have
/// nothing to do with it.
fn parametric_enumeration_table(member: &str) -> String {
    format!(
        "(declare-datatypes ((PE 1)) ((par (T) ((pa) ({member}) (pc)))))\n\
         (declare-datatypes ((Fruit 0)) (((orange) (kiwi) (apple))))\n\
         (declare-fun pick ((PE Int)) Fruit)\n\
         (declare-const b Bool) (declare-const c (PE Int)) (declare-const d Fruit)\n\
         (assert (= (pick (as {member} (PE Int))) kiwi))\n\
         (assert (= (pick (as pc (PE Int))) apple))\n\
         (assert b) (assert (= c (as pc (PE Int)))) (assert (= d apple))\n"
    )
}

/// Here the table cell names the member `xy` of `(PE Int)`, and holds the
/// member's identity, for example `x(y@PE!{Int}`, for `x(y`, `a b` and
/// `true`; for those three `try_get_model` reads no `apple`, and with `x(y`
/// neither text is one s-expression.
#[test]
fn a_parametric_enumeration_table_keeps_the_identity_of_a_member_that_is_no_symbol() {
    let solve = |member: &str| {
        let mut solver = Solver::new(Logic::All);
        solver
            .parse_smtlib2(&parametric_enumeration_table(member))
            .expect("parse");
        assert_eq!(solver.check_sat(), SolveResult::Sat, "{member}");
        solver
    };
    let texts = |solver: &Solver| {
        [
            solver.try_get_model_str().expect("model text"),
            solver
                .try_get_model_str_for_decoder()
                .expect("decoder text"),
        ]
    };
    let read = |solver: &Solver| format!("{:?}", solver.try_get_model().expect("model").model());

    let named = solve("xy");
    for text in texts(&named) {
        assert!(
            on_one_line(&text).contains("Fruit (ite (= x0 xy) kiwi apple))"),
            "{text}"
        );
        assert!(
            matches!(ay_frontend::sexp::parse_sexps(&text).as_deref(), Ok([_])),
            "{text}"
        );
    }
    assert!(read(&named).contains("apple"), "{}", read(&named));

    for (member, identity) in [
        ("|x(y|", "x(y@PE!{Int}"),
        ("|a b|", "a b@PE!{Int}"),
        ("|true|", "true@PE!{Int}"),
    ] {
        let odd = solve(member);
        for text in texts(&odd) {
            assert!(
                on_one_line(&text).contains(&format!("Fruit (ite (= x0 {identity}) kiwi apple))")),
                "{member}:\n{text}"
            );
        }
        assert!(!read(&odd).contains("apple"), "{member}: {}", read(&odd));
    }
    let unbalanced = solve("|x(y|");
    for text in texts(&unbalanced) {
        assert!(
            !matches!(ay_frontend::sexp::parse_sexps(&text).as_deref(), Ok([_])),
            "{text}"
        );
    }
}
