// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates
//
//! OMT executor bridge for direct execution (#6702).
//!
//! When a `AYProgram` contains optimization objectives (maximize/minimize),
//! the Solver-based direct path cannot handle them because `ay_dpll::api::Solver`
//! does not expose objective registration. This bridge lowers the program to
//! SMT-LIB text, parses it into `ay_frontend::Command` values, and runs them
//! through `ay_dpll::Executor` which already supports OMT.

use super::context::catch_execute_stage;
use super::types::ExecuteValueMap;
use super::{ExecuteCounterexample, ExecuteError, ExecuteTypedResult, ModelValue};
use crate::program::AYProgram;

/// Execute an OMT-bearing program through the executor bridge.
///
/// Renders the program to SMT-LIB text, parses via `ay_frontend`, and
/// executes through `ay_dpll::Executor`. Returns typed results compatible
/// with the direct execution API.
pub(crate) fn execute_omt(program: &AYProgram) -> Result<ExecuteTypedResult, ExecuteError> {
    // Render to SMT-LIB text
    let smt_text = program.to_string();

    // Parse into commands
    let commands = ay_frontend::parse(&smt_text)
        .map_err(|e| ExecuteError::ConstraintExecution(format!("OMT parse error: {e}")))?;

    // Execute through ay_dpll::Executor with panic handling
    let exec_result: Result<Vec<String>, String> = catch_execute_stage(
        || {
            let mut executor = ay_dpll::Executor::new();
            let outputs = executor
                .execute_all(&commands)
                .map_err(|e| format!("OMT executor error: {e}"))?;
            Ok(outputs)
        },
        |reason| Err(format!("OMT executor panic: {reason}")),
    );

    let outputs = match exec_result {
        Ok(outputs) => outputs,
        Err(reason) => return Ok(ExecuteTypedResult::Unknown(reason)),
    };

    // Interpret the outputs. The executor returns one output per command that
    // produces output: "sat"/"unsat"/"unknown" for check-sat, model text for
    // get-model, objectives text for get-objectives, etc.
    interpret_executor_outputs(&outputs)
}

/// Interpret executor output strings into an `ExecuteTypedResult`.
///
/// Scans outputs for the last check-sat result and any model/objectives data.
fn interpret_executor_outputs(outputs: &[String]) -> Result<ExecuteTypedResult, ExecuteError> {
    let mut last_check_sat: Option<&str> = None;
    let mut model_values = ExecuteValueMap::default();
    let mut objectives_output: Option<&str> = None;

    for output in outputs {
        let trimmed = output.trim();
        match trimmed {
            "sat" | "unsat" | "unknown" => {
                last_check_sat = Some(trimmed);
            }
            s if s.starts_with("(objectives") => {
                objectives_output = Some(s);
            }
            s if s.starts_with("(model") || s.starts_with("(define-fun") => {
                // Model output — parse variable assignments.
                parse_model_into(&mut model_values, s);
            }
            _ => {
                // Other outputs (get-value, echo, etc.) — check for
                // unknown reason strings.
                if last_check_sat.is_none() && trimmed.starts_with("(error") {
                    return Err(ExecuteError::ConstraintExecution(trimmed.to_string()));
                }
            }
        }
    }

    match last_check_sat {
        Some("unsat") => Ok(ExecuteTypedResult::Verified),
        Some("sat") => {
            // If we have objectives output, store it in the values map
            // so callers can access it.
            if let Some(obj_text) = objectives_output {
                model_values.insert(
                    "__objectives".to_string(),
                    ModelValue::String(obj_text.to_string()),
                );
            }
            Ok(ExecuteTypedResult::Counterexample(
                ExecuteCounterexample::new(model_values, ExecuteValueMap::default()),
            ))
        }
        Some(reason) => Ok(ExecuteTypedResult::Unknown(reason.to_string())),
        None => {
            // No check-sat output found — the program may not have had a check-sat
            Ok(ExecuteTypedResult::Unknown(
                "no check-sat result in OMT output".to_string(),
            ))
        }
    }
}

/// Parse simple model output into the values map.
///
/// Handles the common `(define-fun name () Sort value)` pattern from
/// get-model: each line is read by `ay_core::model_constant_definition`.
fn parse_model_into(values: &mut ExecuteValueMap<ModelValue>, model_text: &str) {
    for line in model_text.lines() {
        if let Some((name, value)) = ay_core::model_constant_definition(line) {
            values.insert(name.to_string(), parse_model_value(&value));
        }
    }
}

/// Parse a single model value string into a ModelValue.
fn parse_model_value(s: &str) -> ModelValue {
    if s == "true" {
        ModelValue::Bool(true)
    } else if s == "false" {
        ModelValue::Bool(false)
    } else if let Ok(n) = s.parse::<i64>() {
        ModelValue::Int(n.into())
    } else if s.starts_with("(- ") {
        // Negative integer: (- N)
        let inner = s
            .strip_prefix("(- ")
            .and_then(|s| s.strip_suffix(')'))
            .unwrap_or(s);
        if let Ok(n) = inner.parse::<i64>() {
            ModelValue::Int((-n).into())
        } else {
            ModelValue::String(s.to_string())
        }
    } else {
        ModelValue::String(s.to_string())
    }
}

#[cfg(test)]
mod ascription_tests {
    use super::{parse_model_into, parse_model_value, ExecuteValueMap, ModelValue};

    /// Here `(as nil L2)` reads as `nil` (#overloaded-nil-surface), and the
    /// abstract element `(as @S!0 S)` keeps its spelling.
    #[test]
    fn ascribed_constructor_reads_as_the_bare_constructor() {
        let read = |model: &str| {
            let mut values = ExecuteValueMap::default();
            parse_model_into(&mut values, model);
            values
        };
        let bare = read("(model\n  (define-fun y () L2 nil)\n)");
        let ascribed = read("(model\n  (define-fun y () L2 (as nil L2))\n)");
        assert_eq!(bare.get("y"), Some(&ModelValue::String("nil".to_string())));
        assert_eq!(ascribed.get("y"), bare.get("y"));

        let element = read("(model\n  (define-fun u () S (as @S!0 S))\n)");
        assert_eq!(
            element.get("u"),
            Some(&ModelValue::String("(as @S!0 S)".to_string()))
        );
    }

    /// For each case of `ay_dpll::constructor_ascription_matrix`, this reader
    /// returns for the printed model what it returns for
    /// `AscriptionCase::bare` of it.
    #[test]
    fn a_printed_model_reads_as_its_bare_spelling() {
        let read = |model: &str| {
            let mut values = ExecuteValueMap::default();
            parse_model_into(&mut values, model);
            values
        };
        let mut tops = 0;
        for case in ay_dpll::constructor_ascription_matrix() {
            let (_solver, printed) = case.solve().unwrap_or_else(|error| panic!("{error}"));
            let bare = case.bare(&printed);
            assert_ne!(bare, printed, "{}", case.label);
            let values = read(&printed);
            assert_eq!(values, read(&bare), "{}:\n{printed}", case.label);
            let constructor = case.constructor();
            if let Some(top) = values.get("top") {
                tops += 1;
                assert_eq!(
                    top,
                    &ModelValue::String(constructor.to_string()),
                    "{}:\n{printed}",
                    case.label
                );
                assert_eq!(
                    values.get("nested"),
                    Some(&ModelValue::String(format!(
                        "(w {constructor} {constructor})"
                    ))),
                    "{}:\n{printed}",
                    case.label
                );
            }
        }
        // Not vacuous: `top` was read for each constructor and sort.
        assert_eq!(
            tops,
            ay_dpll::MATRIX_CONSTRUCTORS.len() * ay_dpll::MATRIX_SORTS.len()
        );
    }

    /// For each name `k` below, the models a solver prints for
    /// `Op1 = {k, halt}` beside `Op2 = {k, stop}` and beside
    /// `Op2 = {unshared, stop}` give this reader the same `a` and `c`.
    #[test]
    fn a_constructor_reads_the_same_whether_or_not_its_name_is_overloaded() {
        let read = |constructor: &str, partner: &str| {
            let script = format!(
                "(declare-datatypes ((Op1 0)) (((|{constructor}|) (halt))))\n\
                 (declare-datatypes ((Op2 0)) (((|{partner}|) (stop))))\n\
                 (declare-datatypes ((W 0)) (((w (w1 Op1) (w2 Op1)))))\n\
                 (declare-const a Op1) (declare-const b Op2) (declare-const c W)\n\
                 (assert (= a (as |{constructor}| Op1)))\n\
                 (assert (= b (as |{partner}| Op2)))\n\
                 (assert (= c (w a a)))\n"
            );
            let mut solver = ay_dpll::api::Solver::new(ay_dpll::api::Logic::All);
            solver.parse_smtlib2(&script).expect("script");
            assert_eq!(solver.check_sat(), ay_dpll::api::SolveResult::Sat);
            let printed = solver.try_get_model_str().expect("model text");
            let mut values = ExecuteValueMap::default();
            parse_model_into(&mut values, &printed);
            (printed, values)
        };
        for constructor in [
            "pop", "step", "reset", "exit", "let", "a#b", "a:b", "nil", "true", "false", ":k",
        ] {
            let (overloaded_text, overloaded) = read(constructor, constructor);
            let (plain_text, plain) = read(constructor, "unshared");
            // In the overloaded model `a` prints ascribed for each name but
            // those listed here.
            assert_eq!(
                overloaded_text.contains("(define-fun a () Op1 (as "),
                !matches!(constructor, "a#b" | "a:b" | "true" | "false" | ":k"),
                "{constructor}:\n{overloaded_text}"
            );
            assert!(
                plain_text.contains(&format!("(define-fun a () Op1 {constructor})")),
                "{constructor}: alone, the constructor prints as its name:\n{plain_text}"
            );
            for name in ["a", "c"] {
                assert_eq!(
                    overloaded.get(name),
                    plain.get(name),
                    "{constructor}, {name}:\n{overloaded_text}\n{plain_text}"
                );
            }
            // Here `a` reads as `parse_model_value` reads the name.
            assert_eq!(
                overloaded.get("a"),
                Some(&parse_model_value(constructor)),
                "{constructor}"
            );
            assert_eq!(
                overloaded.get("c"),
                Some(&ModelValue::String(format!(
                    "(w {constructor} {constructor})"
                ))),
                "{constructor}"
            );
        }
    }

    /// For each pair of `ay_dpll::overload_pairs`, this reader returns the
    /// same values for the model of `pair.overloaded` as for that of
    /// `pair.renamed`.
    #[test]
    fn a_model_reads_the_same_whether_or_not_a_constructor_is_overloaded() {
        let read = |model: &str| {
            let mut values = ExecuteValueMap::default();
            parse_model_into(&mut values, model);
            values
        };
        let mut records = 0;
        for pair in ay_dpll::overload_pairs() {
            let (_, overloaded) = pair
                .solve(&pair.overloaded)
                .unwrap_or_else(|error| panic!("{error}"));
            let (_, renamed) = pair
                .solve(&pair.renamed)
                .unwrap_or_else(|error| panic!("{error}"));
            let context = format!("{}:\n{overloaded}\n{renamed}", pair.label);
            let values = read(&overloaded);
            assert_eq!(values, read(&renamed), "{context}");
            for name in ["top", "two", "nested", "n"] {
                assert!(values.contains_key(name), "{name} is read: {context}");
            }
            assert_eq!(values.get("n"), Some(&ModelValue::Int((-5).into())));
            if pair.tables {
                continue;
            }
            assert!(values.contains_key("p"), "p is read: {context}");
            let Some(ModelValue::String(record)) = values.get("r") else {
                panic!("r is a record: {context}");
            };
            // Here the record's fields are separated by single spaces.
            assert!(
                record.starts_with("(rec \"| (as nil L1) )\" ")
                    && (record.ends_with(" -7)") || record.ends_with(" (- 7))"))
                    && !record.contains("  "),
                "{context}"
            );
            records += 1;
        }
        assert_eq!(
            records,
            (ay_dpll::OVERLOAD_ASCRIBED_CONSTRUCTORS.len()
                + ay_dpll::OVERLOAD_BARE_CONSTRUCTORS.len())
                * (ay_dpll::OVERLOAD_PAIR_VARIANTS - 2)
        );
    }

    /// What this reader gives `c` for the model line
    /// `(define-fun c () sort value)`.
    fn value_of(sort: &str, value: &str) -> ModelValue {
        let mut values = ExecuteValueMap::default();
        let model = format!("(model\n  (define-fun c () {sort} {value})\n)");
        parse_model_into(&mut values, &model);
        values.remove("c").expect("c is read")
    }

    /// Here each ascribed value reads as its bare form: `nil`, or the text
    /// paired with it.
    #[test]
    fn ascription_under_a_compound_or_quoted_sort_reads_as_the_bare_constructor() {
        let nil = ModelValue::String("nil".to_string());
        assert_eq!(value_of("(List Int)", "nil"), nil);
        for (sort, value) in [
            ("(List Int)", "(as nil (List Int))"),
            (
                "(List (Pair Int |a b|))",
                "(as nil (List (Pair Int |a b|)))",
            ),
            ("(|My List| Int)", "(as nil (|My List| Int))"),
            ("|L#1|", "(as nil |L#1|)"),
            ("L2", "(as  nil   L2)"),
        ] {
            assert_eq!(value_of(sort, value), nil, "{value}");
        }
        assert_eq!(
            value_of("W", "(w (as nil (List Int)) (as nil L2))"),
            value_of("W", "(w nil nil)")
        );
        // Heads and sort heads named like theory symbols.
        for (sort, value, bare) in [
            ("L1", "(as const L1)", "const"),
            ("L1", "(as bag.empty L1)", "bag.empty"),
            ("L1", "(as set.universe L1)", "set.universe"),
            ("(Tuple Int Bool)", "(as nil (Tuple Int Bool))", "nil"),
            ("(Bag Int)", "(as nil (Bag Int))", "nil"),
            ("(Relation Int Int)", "(as nil (Relation Int Int))", "nil"),
        ] {
            assert_eq!(value_of(sort, value), value_of(sort, bare), "{value}");
            assert_eq!(value_of(sort, value), ModelValue::String(bare.to_string()));
        }
        // Here each quoted name reads unquoted.
        for (value, bare) in [
            ("(as |pop| |L#1|)", "pop"),
            ("(as |a#b| |L#1|)", "a#b"),
            ("(as |my nil| |L#1|)", "my nil"),
        ] {
            assert_eq!(value_of("|L#1|", value), value_of("|L#1|", bare));
            assert_eq!(
                value_of("|L#1|", value),
                ModelValue::String(bare.to_string())
            );
        }
    }

    /// Each value below reads as itself.
    #[test]
    fn theory_values_and_malformed_ascriptions_keep_their_spelling() {
        for (sort, value) in [
            ("(Seq Int)", "(as seq.empty (Seq Int))"),
            ("(Set Int)", "(as set.empty (Set Int))"),
            ("(Array Int Int)", "((as const (Array Int Int)) 0)"),
            ("(_ FiniteField 7)", "(as ff3 (_ FiniteField 7))"),
            ("S", "(as @S!0 S)"),
            ("S", "(as |@S 1!0| S)"),
            ("(S Int)", "(as @S!0 (S Int))"),
            ("(Seq Int)", "(as nil (Seq Int))"),
            ("L", "(as nil L extra)"),
            ("L", "(as nil (List Int) extra)"),
            ("L", "(as nil (List Int) (List Int))"),
            ("L", "(as nil)"),
            ("L", "(as nil ())"),
            ("L", "(as nil ((List) Int))"),
            ("L", "(as (nil) L)"),
            ("L", "(as nil |L)"),
            ("L", "(as nil \"L\")"),
            ("L", "(asnil L)"),
        ] {
            assert_eq!(
                value_of(sort, value),
                ModelValue::String(value.to_string()),
                "{value}"
            );
        }
    }

    /// Each sort of the list below is a quoted symbol holding a space; here
    /// `nil`, `(as nil S)`, `(cons 1 (as nil S))` and `(- 5)` under it read as
    /// `nil`, `nil`, `(cons 1 nil)` and the integer -5.
    #[test]
    fn a_quoted_sort_with_a_space_is_one_token() {
        let string = |text: &str| ModelValue::String(text.to_string());
        for sort in [
            "|My List|",
            "|My  long List|",
            "|L (1|",
            "|L) 1|",
            "|a \"b|",
        ] {
            assert_eq!(value_of(sort, "nil"), string("nil"), "{sort}");
            assert_eq!(
                value_of(sort, &format!("(as nil {sort})")),
                string("nil"),
                "{sort}"
            );
            assert_eq!(
                value_of(sort, &format!("(cons 1 (as nil {sort}))")),
                string("(cons 1 nil)"),
                "{sort}"
            );
            assert_eq!(
                value_of(sort, &format!("(cons 1 (as nil {sort}))")),
                value_of(sort, "(cons 1 nil)"),
                "{sort}"
            );
            assert_eq!(value_of(sort, "(- 5)"), ModelValue::Int((-5).into()));
        }
        // A sort application whose arguments are quoted.
        assert_eq!(
            value_of(
                "(|My Pair| |a b| (|My List| Int))",
                "(as nil (|My Pair| |a b| (|My List| Int)))"
            ),
            string("nil")
        );
        // Here the quoted constant name `|my top|` is read whole.
        let mut values = ExecuteValueMap::default();
        parse_model_into(
            &mut values,
            "(model\n  (define-fun |my top| () |My List| (as nil |My List|))\n)",
        );
        assert_eq!(values.get("|my top|"), Some(&string("nil")));
        assert_eq!(values.len(), 1);
    }

    /// Here each value reads as its text, or the number or Boolean it spells.
    #[test]
    fn the_value_is_the_complete_term() {
        let string = |text: &str| ModelValue::String(text.to_string());
        assert_eq!(value_of("Int", "(- 5)"), ModelValue::Int((-5).into()));
        assert_eq!(value_of("Int", "(-  5 )"), string("(-  5 )"));
        assert_eq!(value_of("Int", "5"), ModelValue::Int(5.into()));
        assert_eq!(value_of("Bool", "true"), ModelValue::Bool(true));
        assert_eq!(value_of("L", "x)"), string("x)"));
        assert_eq!(value_of("Int", "5)"), string("5)"));
        for (sort, value) in [
            ("Real", "(/ 1 2)"),
            ("Real", "(- (/ 1 2))"),
            ("Real", "(- 5.0)"),
            ("Int", "(- 99999999999999999999)"),
            ("(_ BitVec 8)", "#x0f"),
            ("(_ BitVec 8)", "(_ bv5 8)"),
            ("L", "(cons 1 (cons 2 nil))"),
            ("L", "(cons (- 1) (cons (- 2) nil))"),
            ("(Array Int Int)", "((as const (Array Int Int)) 0)"),
            (
                "(Array Int Int)",
                "(store ((as const (Array Int Int)) 0) 1 (- 2))",
            ),
            ("(Seq Int)", "(as seq.empty (Seq Int))"),
            ("Rec", "(rec \"a\" (mk))"),
        ] {
            assert_eq!(value_of(sort, value), string(value), "{value}");
        }
    }

    /// Each string literal below reads as itself, alone and as a field of
    /// `rec`, and here `(as nil S)` beside it reads as `nil`.
    #[test]
    fn a_string_literal_is_one_token() {
        let string = |text: &str| ModelValue::String(text.to_string());
        for literal in [
            "\"|\"",
            "\"a | b\"",
            "\"(as nil L1)\"",
            "\"| (as nil L1) )\"",
            "\")))\"",
            "\"((\"",
            "\"say \"\"(as nil L1)\"\" |\"",
            "\"\"",
        ] {
            assert_eq!(value_of("String", literal), string(literal), "{literal}");
            let bare = format!("(rec {literal} nil {literal})");
            assert_eq!(value_of("Rec", &bare), string(&bare), "{literal}");
            for sort in ["L1", "|My List|", "(List Int)"] {
                let ascribed = format!("(rec {literal} (as nil {sort}) {literal})");
                assert_eq!(value_of("Rec", &ascribed), string(&bare), "{literal}");
            }
        }
    }

    /// For each sort and constructor name below, this reader gives the same
    /// values for the model printed with the name overloaded as for the one
    /// printed with the partner renamed, apart from `o`, the partner itself.
    #[test]
    fn overloading_never_changes_a_value_under_any_sort_spelling() {
        let string = |text: &str| ModelValue::String(text.to_string());
        let read = |sort: &str, constructor: &str, partner: &str| {
            let c = ay_core::quote_symbol(constructor);
            let partner = ay_core::quote_symbol(partner);
            // `Odd`'s constructors `p|q` and `c"d` print unquoted here
            // (checked below).
            let script = format!(
                "(declare-datatypes (({sort} 0)) ((({c}) (cons (hd Int) (tl {sort})))))\n\
                 (declare-datatypes ((Other 0)) ((({partner}) (omk (ofst Int)))))\n\
                 (declare-datatypes ((Odd 0)) (((|p\\|q|) (|c\"d|))))\n\
                 (declare-datatypes ((Rec 0)) (((rec (label String) (o1 Odd) \
                 (tail {sort}) (o2 Odd) (last {sort}) (count Int)))))\n\
                 (declare-const top {sort}) (declare-const two {sort})\n\
                 (declare-const r Rec) (declare-const o Other) (declare-const n Int)\n\
                 (assert (= top (as {c} {sort})))\n\
                 (assert (= two (cons 1 (cons (- 2) (as {c} {sort})))))\n\
                 (assert (= r (rec \"| (as nil L1) )\" |p\\|q| (as {c} {sort}) \
                 |c\"d| (as {c} {sort}) (- 7))))\n\
                 (assert (= o (as {partner} Other)))\n\
                 (assert (= n (- 5)))\n"
            );
            let mut solver = ay_dpll::api::Solver::new(ay_dpll::api::Logic::All);
            solver
                .parse_smtlib2(&script)
                .unwrap_or_else(|error| panic!("{sort} {constructor}: {error}"));
            assert_eq!(solver.check_sat(), ay_dpll::api::SolveResult::Sat);
            let printed = solver.try_get_model_str().expect("model text");
            let mut values = ExecuteValueMap::default();
            parse_model_into(&mut values, &printed);
            (printed, values)
        };
        for sort in ["|My List|", "|My  List (1|", "|L#1|", "L1"] {
            for constructor in ["nil", "pop", "a#b", "my nil", "a|b", "x(y", "as"] {
                let (overloaded_text, mut overloaded) = read(sort, constructor, constructor);
                let (plain_text, mut plain) = read(sort, constructor, "unshared");
                let context = format!("{sort} {constructor}:\n{overloaded_text}\n{plain_text}");
                // Of these names only `nil`, `pop` and `as` print ascribed at
                // `top` in the overloaded model.
                let ascribed = matches!(constructor, "nil" | "pop" | "as");
                assert_eq!(
                    overloaded_text.contains(&format!("(define-fun top () {sort} (as ")),
                    ascribed,
                    "{context}"
                );
                assert!(
                    plain_text.contains(&format!("(define-fun top () {sort} {constructor})")),
                    "alone, the constructor prints as its name: {context}"
                );
                // Both models print the record's constructor fields bare.
                let record = format!(" p|q {constructor} c\"d {constructor} ");
                assert!(
                    overloaded_text.contains(&record) && plain_text.contains(&record),
                    "the record beside the bare `p|q` prints unascribed: {context}"
                );
                // `o` is the partner itself, which the two scripts name
                // differently.
                assert_eq!(overloaded.remove("o"), Some(string(constructor)));
                assert_eq!(plain.remove("o"), Some(string("unshared")));
                assert_eq!(overloaded, plain, "{context}");
                assert_eq!(overloaded.len(), 4, "{context}");
                assert_eq!(overloaded.get("top"), Some(&string(constructor)));
                assert_eq!(
                    overloaded.get("two"),
                    Some(&string(&format!("(cons 1 (cons -2 {constructor}))"))),
                    "{context}"
                );
                assert_eq!(
                    overloaded.get("r"),
                    Some(&string(&format!(
                        "(rec \"| (as nil L1) )\" p|q {constructor} c\"d {constructor} -7)"
                    ))),
                    "{context}"
                );
                assert_eq!(overloaded.get("n"), Some(&ModelValue::Int((-5).into())));
            }
        }
    }
}
