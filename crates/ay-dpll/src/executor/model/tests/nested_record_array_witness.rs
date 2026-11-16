// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Whole nested witnesses, not selected scalar pins or decoder-only fixtures.

use super::*;
use ay_core::{DatatypeConstructor, DatatypeField, DatatypeSort, TermData, TermStore};
use ay_frontend::{parse, sexp::parse_sexp, SExpr};
use ay_model_check::{confirm_completed_model, ArrayValue, GateVerdict, ModelValue, ModelView};

mod native;

const DECLARATIONS: &str = "
    (set-logic ALL) (set-option :produce-models true) (set-option :timeout 5000)
    (declare-datatype Row ((row (len (_ BitVec 64))
      (data (Array (_ BitVec 64) (_ BitVec 8))))))
    (declare-datatype Outer ((outer (rows (Array (_ BitVec 64) Row)))))";

// Keep the original closed equality: no select assertions may repair its model.
const WITNESS: &str = "
    (outer (store ((as const (Array (_ BitVec 64) Row))
      (row (_ bv0 64) ((as const (Array (_ BitVec 64) (_ BitVec 8))) #x00)))
      (_ bv33 64)
      (row (_ bv65 64) (store ((as const (Array (_ BitVec 64) (_ BitVec 8))) #x07)
                            (_ bv64 64) #x09))))";

fn commands(exec: &mut Executor, text: &str) -> Vec<String> {
    exec.execute_all(&parse(text).expect("valid witness source"))
        .expect("public executor commands succeed")
}

fn solve(body: &str) -> Executor {
    let mut exec = Executor::new();
    exec.set_term_memory_limit(Some(64 * 1024 * 1024));
    assert_eq!(
        commands(&mut exec, &format!("{DECLARATIONS}{body}")),
        [] as [String; 0]
    );
    let originals = exec.ctx.assertions.clone();
    assert_ne!(originals, [] as [TermId; 0]);
    assert_eq!(commands(&mut exec, "(check-sat)"), ["sat"]);
    assert_eq!(exec.independent_gate_query_roots().unwrap(), originals);
    assert!(matches!(
        exec.confirm_sat_with_independent_gate(),
        GateVerdict::ConfirmedSat
    ));
    exec
}

fn word(value: u64, width: u32) -> ModelValue {
    ModelValue::BitVec {
        value: value.into(),
        width,
    }
}

fn array(default: ModelValue, store: Vec<(ModelValue, ModelValue)>) -> ModelValue {
    ModelValue::Array(Box::new(ArrayValue { default, store }))
}

fn row(length: u64, default: u64, store: Vec<(ModelValue, ModelValue)>) -> ModelValue {
    ModelValue::Datatype {
        ctor: "row".into(),
        args: vec![word(length, 64), array(word(default, 8), store)],
    }
}

fn outer(default: ModelValue, store: Vec<(ModelValue, ModelValue)>) -> ModelValue {
    ModelValue::Datatype {
        ctor: "outer".into(),
        args: vec![array(default, store)],
    }
}

fn expected() -> ModelValue {
    outer(
        row(0, 0, vec![]),
        vec![(word(33, 64), row(65, 7, vec![(word(64, 64), word(9, 8))]))],
    )
}

// Only constructor identities come from the parsed registry. The complete
// expected payload remains hand-authored, so the parser cannot validate itself
// by dropping the same stores from both source and emitted text.
fn with_source_constructor_names(parsed: &ModelValue, mut value: ModelValue) -> ModelValue {
    let ModelValue::Datatype {
        ctor: outer_ctor,
        args,
    } = parsed
    else {
        panic!("expected parsed Outer")
    };
    let ModelValue::Array(rows) = &args[0] else {
        panic!("expected parsed rows")
    };
    let ModelValue::Datatype { ctor: row_ctor, .. } = &rows.default else {
        panic!("expected parsed default Row")
    };
    let ModelValue::Datatype { ctor, args } = &mut value else {
        unreachable!()
    };
    *ctor = outer_ctor.clone();
    let ModelValue::Array(rows) = &mut args[0] else {
        unreachable!()
    };
    for row in std::iter::once(&mut rows.default).chain(rows.store.iter_mut().map(|(_, row)| row)) {
        let ModelValue::Datatype { ctor, .. } = row else {
            unreachable!()
        };
        *ctor = row_ctor.clone();
    }
    value
}

/// The sole answer is for a genuine Var; never pin a constructor or select App.
struct LeafValue {
    leaf: TermId,
    value: ModelValue,
}

impl ModelView for LeafValue {
    fn leaf_value(&self, term: TermId) -> Option<ModelValue> {
        (term == self.leaf).then(|| self.value.clone())
    }
}

struct ClosedEquality {
    terms: TermStore,
    leaf: TermId,
    assertion: TermId,
}

impl ClosedEquality {
    fn new(value: &ModelValue) -> Self {
        let ModelValue::Datatype { ctor, args } = value else {
            panic!("expected Outer constructor")
        };
        let ModelValue::Array(rows) = &args[0] else {
            panic!("expected rows array")
        };
        let ModelValue::Datatype { ctor: row_ctor, .. } = &rows.default else {
            panic!("expected Row default")
        };
        let row_sort = Sort::Datatype(DatatypeSort::new(
            "WitnessRow",
            vec![DatatypeConstructor::new(
                row_ctor,
                vec![
                    DatatypeField::new("len", Sort::bitvec(64)),
                    DatatypeField::new("data", Sort::array(Sort::bitvec(64), Sort::bitvec(8))),
                ],
            )],
        ));
        let sort = Sort::Datatype(DatatypeSort::new(
            "WitnessOuter",
            vec![DatatypeConstructor::new(
                ctor,
                vec![DatatypeField::new(
                    "rows",
                    Sort::array(Sort::bitvec(64), row_sort),
                )],
            )],
        ));
        let mut terms = TermStore::new();
        let leaf = terms.mk_var("printed_v", sort.clone());
        assert!(matches!(terms.get(leaf), TermData::Var(_, _)));
        let rhs = literal(&mut terms, value, &sort);
        let assertion = terms.mk_app(Symbol::named("="), [leaf, rhs], Sort::Bool);
        Self {
            terms,
            leaf,
            assertion,
        }
    }

    fn check(&self, value: ModelValue) -> GateVerdict {
        confirm_completed_model(
            &self.terms,
            &LeafValue {
                leaf: self.leaf,
                value,
            },
            &[self.assertion],
        )
    }
}

// Build the complete ground RHS, including defaults and every store. The
// checker must evaluate its own constructor/const-array/store/equality rules.
fn literal(terms: &mut TermStore, value: &ModelValue, sort: &Sort) -> TermId {
    match (value, sort) {
        (ModelValue::BitVec { value, width }, Sort::BitVec(bv)) => {
            assert_eq!(*width, bv.width);
            terms.mk_bitvec(value.clone(), *width)
        }
        (ModelValue::Datatype { ctor, args }, Sort::Datatype(dt)) => {
            let declaration = dt
                .constructors
                .iter()
                .find(|item| item.name == *ctor)
                .unwrap();
            assert_eq!(args.len(), declaration.fields.len());
            let children: Vec<_> = args
                .iter()
                .zip(&declaration.fields)
                .map(|(arg, field)| literal(terms, arg, &field.sort))
                .collect();
            terms.mk_app(Symbol::named(ctor), children, sort.clone())
        }
        (ModelValue::Array(value), Sort::Array(array_sort)) => {
            let default = literal(terms, &value.default, &array_sort.element_sort);
            let mut result = terms.mk_const_array(array_sort.index_sort.clone(), default);
            for (key, cell) in &value.store {
                let key = literal(terms, key, &array_sort.index_sort);
                let cell = literal(terms, cell, &array_sort.element_sort);
                result = terms.mk_app(Symbol::named("store"), [result, key, cell], sort.clone());
            }
            result
        }
        _ => panic!("ill-sorted ground RHS {value:?} at {sort:?}"),
    }
}

fn model_binding(output: &str, name: &str) -> String {
    let model = parse_sexp(output).expect("get-model is a complete s-expression");
    let entries = model.as_list().expect("model list");
    assert!(
        entries[0].is_symbol("model"),
        "expected a complete model: {output}"
    );
    let bindings: Vec<_> = entries[1..]
        .iter()
        .filter_map(SExpr::as_list)
        .filter(|parts| {
            parts.len() == 5 && parts[0].is_symbol("define-fun") && parts[1].is_symbol(name)
        })
        .collect();
    assert_eq!(
        bindings.len(),
        1,
        "exactly one public model binding for {name}"
    );
    assert_eq!(bindings[0][2].as_list().unwrap().len(), 0);
    bindings[0][4].to_raw_string()
}

fn value_bindings(output: &str, names: &[&str]) -> Vec<String> {
    let expression = parse_sexp(output).expect("get-value is a complete s-expression");
    let pairs = expression.as_list().expect("get-value pairs");
    assert_eq!(pairs.len(), names.len());
    pairs
        .iter()
        .zip(names)
        .map(|(pair, name)| {
            let fields = pair.as_list().expect("value pair");
            assert_eq!(fields.len(), 2);
            assert!(fields[0].is_symbol(name));
            fields[1].to_raw_string()
        })
        .collect()
}

fn printed_value(exec: &Executor, name: &str, text: &str) -> ModelValue {
    let (_, sort) = exec
        .ctx
        .source_constant_for_value(name)
        .expect("authored source name");
    let guard = rendered_dt_guard::RenderedDatatypeGuard::new(exec);
    assert!(guard.is_bounded());
    exec.parse_rendered_dt_value_cached(text, sort, &guard)
        .expect("complete typed printed witness")
}

#[test]
#[ntest::timeout(20_000)]
fn closed_nested_record_model_and_get_value_are_complete_and_confirmed() {
    for (query, model_index, values_index) in [
        ("(get-value (v v))(get-model)", 1, 0),
        ("(get-model)(get-value (v v))", 0, 1),
    ] {
        let mut exec = solve(&format!("(declare-const v Outer)(assert (= v {WITNESS}))"));
        let (source, _) = exec.ctx.source_constant_for_value("v").unwrap();
        assert!(
            matches!(exec.ctx.terms.get(source), TermData::App(_, _)),
            "exercise eager record elimination"
        );
        let size = exec.ctx.terms.len();
        let output = commands(&mut exec, query);
        assert_eq!(output.len(), 2);
        let parsed_source = printed_value(&exec, "v", WITNESS);
        let correct = with_source_constructor_names(&parsed_source, expected());
        let checker = ClosedEquality::new(&correct);
        assert!(matches!(
            checker.check(parsed_source),
            GateVerdict::ConfirmedSat
        ));
        let whole = model_binding(&output[model_index], "v");
        let mut values = value_bindings(&output[values_index], &["v", "v"]);
        values.push(whole);
        for text in values {
            let verdict = checker.check(printed_value(&exec, "v", &text));
            assert!(
                matches!(verdict, GateVerdict::ConfirmedSat),
                "{query}: {text}: {verdict:?}"
            );
        }
        assert_eq!(
            exec.ctx.terms.len(),
            size,
            "read-only whole witness extraction"
        );
        assert!(matches!(
            exec.confirm_sat_with_independent_gate(),
            GateVerdict::ConfirmedSat
        ));
    }
}

#[test]
fn independent_checker_refutes_each_lost_nested_component() {
    let correct = expected();
    let checker = ClosedEquality::new(&correct);
    assert!(matches!(
        checker.check(correct.clone()),
        GateVerdict::ConfirmedSat
    ));
    let cases = [
        ("outer store33", outer(row(0, 0, vec![]), vec![])),
        (
            "inner store64",
            outer(row(0, 0, vec![]), vec![(word(33, 64), row(65, 7, vec![]))]),
        ),
        (
            "inner default7",
            outer(
                row(0, 0, vec![]),
                vec![(word(33, 64), row(65, 0, vec![(word(64, 64), word(9, 8))]))],
            ),
        ),
        (
            "row length65",
            outer(
                row(0, 0, vec![]),
                vec![(word(33, 64), row(0, 7, vec![(word(64, 64), word(9, 8))]))],
            ),
        ),
        (
            "outer default",
            outer(
                row(1, 0, vec![]),
                vec![(word(33, 64), row(65, 7, vec![(word(64, 64), word(9, 8))]))],
            ),
        ),
    ];
    for (label, value) in cases {
        let verdict = checker.check(value);
        assert!(
            matches!(verdict, GateVerdict::ModelViolates { assertion } if assertion == checker.assertion),
            "{label}: {verdict:?}"
        );
    }
    let wrong_width = outer(
        row(0, 0, vec![]),
        vec![(word(33, 64), row(65, 7, vec![(word(64, 64), word(9, 16))]))],
    );
    assert!(matches!(
        checker.check(wrong_width),
        GateVerdict::CannotConfirm { .. }
    ));
    assert!(matches!(checker.check(correct), GateVerdict::ConfirmedSat));
}

#[test]
#[ntest::timeout(20_000)]
fn asserted_aliases_keep_last_inner_store_and_replace_the_whole_outer_row() {
    let mut exec = solve(
        "(declare-const old Row)(declare-const fresh Row)
        (declare-const cells (Array (_ BitVec 64) (_ BitVec 8)))
        (declare-const table (Array (_ BitVec 64) Row))
        (declare-const v Outer)(declare-const alias Outer)
        (assert (= old (row (_ bv65 64)
          (store ((as const (Array (_ BitVec 64) (_ BitVec 8))) #x07) (_ bv64 64) #x09))))
        (assert (= cells (store (store ((as const (Array (_ BitVec 64) (_ BitVec 8))) #x05)
                           (_ bv64 64) #x09) (_ bv64 64) #x0b)))
        (assert (= fresh (row (_ bv66 64) cells)))
        (assert (= table (store (store (store ((as const (Array (_ BitVec 64) Row))
          (row (_ bv0 64) ((as const (Array (_ BitVec 64) (_ BitVec 8))) #x00)))
          (_ bv33 64) old) (_ bv34 64) old) (_ bv33 64) fresh)))
        (assert (= v (outer table)))(assert (= alias v))",
    );
    let expected_text = "(outer (store (store ((as const (Array (_ BitVec 64) Row))
        (row (_ bv0 64) ((as const (Array (_ BitVec 64) (_ BitVec 8))) #x00)))
        (_ bv34 64) (row (_ bv65 64)
          (store ((as const (Array (_ BitVec 64) (_ BitVec 8))) #x07) (_ bv64 64) #x09)))
        (_ bv33 64) (row (_ bv66 64)
          (store ((as const (Array (_ BitVec 64) (_ BitVec 8))) #x05) (_ bv64 64) #x0b))))";
    let parsed_source = printed_value(&exec, "v", expected_text);
    let correct = with_source_constructor_names(
        &parsed_source,
        outer(
            row(0, 0, vec![]),
            vec![
                (word(34, 64), row(65, 7, vec![(word(64, 64), word(9, 8))])),
                (word(33, 64), row(66, 5, vec![(word(64, 64), word(11, 8))])),
            ],
        ),
    );
    let checker = ClosedEquality::new(&correct);
    assert!(matches!(checker.check(correct), GateVerdict::ConfirmedSat));
    assert!(matches!(
        checker.check(parsed_source),
        GateVerdict::ConfirmedSat
    ));
    let before = commands(&mut exec, "(get-value (v alias v))");
    let reads = commands(
        &mut exec,
        "(get-value (
        (len (select (rows v) (_ bv33 64)))
        (select (data (select (rows v) (_ bv33 64))) (_ bv64 64))
        (select (data (select (rows v) (_ bv33 64))) (_ bv0 64))
        (len (select (rows alias) (_ bv34 64)))
        (select (data (select (rows alias) (_ bv34 64))) (_ bv64 64))))",
    );
    let response = parse_sexp(&reads[0]).unwrap();
    let pairs = response.as_list().unwrap();
    assert_eq!(pairs.len(), 5, "fresh scalar observations: {}", reads[0]);
    let actual: Vec<_> = pairs
        .iter()
        .zip([64, 8, 8, 64, 8])
        .map(|(pair, width)| {
            let parts = pair.as_list().unwrap();
            assert_eq!(parts.len(), 2);
            let value = exec
                .parse_model_value_string(&parts[1].to_raw_string(), &Some(Sort::bitvec(width)));
            match value {
                EvalValue::BitVec { value, .. } => value,
                other => panic!("expected exact bitvector observation, got {other:?}"),
            }
        })
        .collect();
    assert_eq!(actual, [66, 11, 5, 65, 9].map(BigInt::from));
    let after = commands(&mut exec, "(get-value (alias v alias))(get-model)");
    for (output, names) in [
        (&before[0], ["v", "alias", "v"]),
        (&after[0], ["alias", "v", "alias"]),
    ] {
        for text in value_bindings(output, &names) {
            let verdict = checker.check(printed_value(&exec, "v", &text));
            assert!(
                matches!(verdict, GateVerdict::ConfirmedSat),
                "{text}: {verdict:?}"
            );
        }
    }
    for name in ["v", "alias"] {
        let text = model_binding(&after[1], name);
        assert!(matches!(
            checker.check(printed_value(&exec, name, &text)),
            GateVerdict::ConfirmedSat
        ));
    }
    assert!(matches!(
        exec.confirm_sat_with_independent_gate(),
        GateVerdict::ConfirmedSat
    ));
}
