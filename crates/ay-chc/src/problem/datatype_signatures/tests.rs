// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::ground_derivation::{
    validate_ground_derivation, GroundDerivation, GroundDerivationError, GroundDerivationStep,
};
use crate::smt::SmtValue;
use crate::{ChcParser, ClauseBody, HornClause};
use ay_core::kani_compat::DetHashMap;
use std::sync::Arc;

// Exact original drop_inj1 source: the unselected recursive clause must still
// pass source authentication before this concrete two-fact refutation replays.
const DROP_INJ1: &str = r#"
(set-logic HORN)
(declare-datatypes ((list_298 0)) (((nil_331 ) (cons_296  (head_592 Int) (tail_594 list_298)))))
(declare-fun |drop_59| ( list_298 Int list_298 ) Bool)
(assert (forall ( (A list_298) (v_1 Int) (v_2 list_298) )
  (=> (and (and true (= 0 v_1) (= v_2 A))) (drop_59 A v_1 v_2))))
(assert (forall ( (A list_298) (B Int) (C list_298) (D Int) (E list_298) (F Int) )
  (=> (and (drop_59 C F E) (and (= B (+ 1 F)) (= A (cons_296 D E)))) (drop_59 C B A))))
(assert (forall ( (A Int) (B Int) (v_2 list_298) (v_3 list_298) )
  (=> (and (and (= A (+ 1 B)) (= v_2 nil_331) (= v_3 nil_331))) (drop_59 v_2 A v_3))))
(assert (forall ( (A list_298) (B Int) (C Int) (D list_298) )
  (=> (and (drop_59 A C D) (drop_59 A B D) (not (= B C))) false)))
(check-sat)
"#;

fn problem() -> ChcProblem {
    ChcParser::parse(DROP_INJ1).expect("valid recursive source")
}

fn bindings(entries: &[(&str, SmtValue)]) -> DetHashMap<String, SmtValue> {
    entries
        .iter()
        .map(|(name, value)| ((*name).to_owned(), value.clone()))
        .collect()
}

fn concrete_refutation() -> GroundDerivation {
    let nil = SmtValue::Datatype("nil_331".into(), Vec::new());
    GroundDerivation {
        steps: vec![
            GroundDerivationStep {
                clause_index: 0,
                env: bindings(&[
                    ("A", nil.clone()),
                    ("v_1", SmtValue::Int(0)),
                    ("v_2", nil.clone()),
                ]),
                premises: Vec::new(),
            },
            GroundDerivationStep {
                clause_index: 2,
                env: bindings(&[
                    ("A", SmtValue::Int(1)),
                    ("B", SmtValue::Int(0)),
                    ("v_2", nil.clone()),
                    ("v_3", nil.clone()),
                ]),
                premises: Vec::new(),
            },
            GroundDerivationStep {
                clause_index: 3,
                env: bindings(&[
                    ("A", nil.clone()),
                    ("B", SmtValue::Int(1)),
                    ("C", SmtValue::Int(0)),
                    ("D", nil),
                ]),
                premises: vec![0, 1],
            },
        ],
        query_step: 2,
    }
}

#[test]
fn recursive_list_source_and_complete_original_ground_refutation_are_valid() {
    let source = problem();
    source
        .validate()
        .expect("finite recursive snapshots denote one registered List");
    source
        .validate_live_typed_function_applications()
        .expect("standalone typed admission");
    assert_eq!(
        validate_ground_derivation(&source, &concrete_refutation()),
        Ok(())
    );
    let mut changed = concrete_refutation();
    changed.steps[2].env.insert("B".into(), SmtValue::Int(0));
    assert!(
        validate_ground_derivation(&source, &changed).is_err(),
        "nominal source admission must not weaken concrete query/premise replay"
    );
}

#[test]
fn mutual_and_array_wrapped_recursive_constructor_signatures_are_valid() {
    for source in [
        r#"(set-logic HORN)
        (declare-datatypes ((A 0) (B 0))
          (((a0) (mk_a (ab B))) ((b0) (mk_b (ba A)))))
        (declare-fun P (A B) Bool)
        (assert (forall ((a A) (b B))
          (=> (and (= a (mk_a b)) (= b (mk_b a0))) (P a b))))
        (assert (forall ((a A) (b B)) (=> (P a b) false)))"#,
        r#"(set-logic HORN)
        (declare-datatype Tree ((leaf) (node (children (Array Int Tree)))))
        (declare-fun P (Tree (Array Int Tree)) Bool)
        (assert (forall ((t Tree) (xs (Array Int Tree)))
          (=> (= t (node xs)) (P t xs))))
        (assert (forall ((t Tree) (xs (Array Int Tree))) (=> (P t xs) false)))"#,
    ] {
        let source = ChcParser::parse(source).expect("well-typed recursive source");
        source
            .validate()
            .expect("registered nominal constructor signature");
        source
            .validate_live_background_theory_expressions()
            .expect("all original operators typed");
        source
            .validate_live_predicate_applications()
            .expect("all original predicate signatures typed");
        source
            .validate_live_typed_function_applications()
            .expect("standalone registry-authenticated check");
    }
}

fn list_sort(source: &ChcProblem) -> ChcSort {
    source.predicates()[0].arg_sorts[0].clone()
}

/// Edit a datatype's constructors in place. Constructor lists are hash-consed
/// and immutable, so the edit is on a copy that is re-interned into `sort`
/// when the guard drops.
struct ConstructorEdit<'a> {
    sort: &'a mut ChcSort,
    list: Vec<ChcDtConstructor>,
}

impl std::ops::Deref for ConstructorEdit<'_> {
    type Target = Vec<ChcDtConstructor>;

    fn deref(&self) -> &Self::Target {
        &self.list
    }
}

impl std::ops::DerefMut for ConstructorEdit<'_> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.list
    }
}

impl Drop for ConstructorEdit<'_> {
    fn drop(&mut self) {
        let ChcSort::Datatype { constructors, .. } = &mut *self.sort else {
            unreachable!("ConstructorEdit is only built over a datatype")
        };
        *constructors = crate::ChcDtConstructors::new(std::mem::take(&mut self.list));
    }
}

fn constructors(sort: &mut ChcSort) -> ConstructorEdit<'_> {
    let ChcSort::Datatype { constructors, .. } = &*sort else {
        panic!("List sort")
    };
    let list = (**constructors).clone();
    ConstructorEdit { sort, list }
}

fn assert_invalid_source(source: &ChcProblem) {
    let error = source
        .validate_live_typed_function_applications()
        .expect_err("standalone check must authenticate metadata");
    assert!(
        error
            .to_string()
            .contains("conflicting in-memory definitions"),
        "{error}"
    );
    assert_eq!(
        validate_ground_derivation(source, &concrete_refutation()),
        Err(GroundDerivationError::InvalidSourceProblem)
    );
}

#[test]
fn forged_unused_same_name_constructor_and_selector_profiles_are_rejected() {
    for mutation in 0..3 {
        let mut source = problem();
        let mut forged = list_sort(&source);
        match mutation {
            0 => constructors(&mut forged)[0].name = "different_nil".into(),
            1 => constructors(&mut forged)[1].selectors[0].name = "different_head".into(),
            _ => constructors(&mut forged)[1].selectors[0].sort = ChcSort::Bool,
        }
        source.declare_predicate("unused_forged_profile", vec![forged]);
        assert_invalid_source(&source);
    }
}

#[test]
fn forged_full_descriptors_with_changed_arity_or_recursive_tail_are_rejected() {
    // Structural forgeries of a same-named full descriptor: an appended
    // constructor, a dropped selector, and a renamed constructor inside the
    // finite recursive tail snapshot. Each reaches replay only through an
    // unused predicate profile, and each is still refused: nominal
    // identification of the recursive tail never excuses a definition that
    // differs from the registered one.
    for mutation in 0..3 {
        let mut source = problem();
        let mut forged = list_sort(&source);
        match mutation {
            0 => constructors(&mut forged).push(ChcDtConstructor {
                name: "extra_331".into(),
                selectors: Vec::new(),
            }),
            1 => {
                constructors(&mut forged)[1].selectors.pop();
            }
            _ => {
                let mut outer = constructors(&mut forged);
                let tail = &mut outer[1].selectors[1].sort;
                constructors(tail)[1].name = "different_cons".into();
            }
        }
        source.declare_predicate("unused_forged_profile", vec![forged]);
        assert_invalid_source(&source);
    }

    // Control: a shallower snapshot of the same definition (the recursive
    // tail cut to its bare name) is the same definition, so admission and
    // the concrete replay both still succeed.
    let mut nominal = problem();
    let mut shallow = list_sort(&nominal);
    constructors(&mut shallow)[1].selectors[1].sort = ChcSort::Uninterpreted("list_298".into());
    nominal.declare_predicate("unused_shallow_profile", vec![shallow]);
    nominal
        .validate_live_typed_function_applications()
        .expect("a shallower snapshot of one definition is that definition");
    assert_eq!(
        validate_ground_derivation(&nominal, &concrete_refutation()),
        Ok(())
    );
}

#[test]
fn conflicting_nested_snapshot_and_explicit_registry_cannot_be_hidden() {
    let mut nested = problem();
    let mut forged = list_sort(&nested);
    {
        let mut outer = constructors(&mut forged);
        let tail = &mut outer[1].selectors[1].sort;
        constructors(tail)[1].selectors[0].sort = ChcSort::Bool;
    }
    nested.declare_predicate("unused_nested_profile", vec![forged]);
    assert_invalid_source(&nested);

    let mut registry = problem();
    let mut definition = registry.datatype_defs()["list_298"].clone();
    definition[1].1[0].1 = ChcSort::Bool;
    registry.add_datatype_def("list_298".into(), definition);
    assert_invalid_source(&registry);
}

fn add_application(source: &mut ChcProblem, name: &str, result: ChcSort, args: Vec<ChcExpr>) {
    let application = ChcExpr::FuncApp(
        name.into(),
        result,
        args.into_iter().map(Arc::new).collect(),
    );
    source.add_clause(HornClause::query(ClauseBody::constraint(ChcExpr::eq(
        application,
        ChcExpr::Int(0),
    ))));
}

#[test]
fn constructor_predicate_builtin_and_ordinary_uf_collisions_still_refuse() {
    for name in ["cons_296", "tail_594", "drop_59", "to_real"] {
        let mut source = problem();
        add_application(&mut source, name, ChcSort::Int, vec![ChcExpr::Int(0)]);
        assert!(
            source.validate_live_typed_function_applications().is_err(),
            "{name}"
        );
        assert!(source.validate().is_err());
    }
    let mut ordinary = problem();
    add_application(
        &mut ordinary,
        "ordinary",
        ChcSort::Int,
        vec![ChcExpr::Int(0)],
    );
    ordinary
        .validate()
        .expect("ordinary scalar UF remains supported");
    add_application(
        &mut ordinary,
        "ordinary",
        ChcSort::Int,
        vec![ChcExpr::Bool(false)],
    );
    assert!(
        ordinary.validate().is_err(),
        "ordinary UFs remain non-overloadable"
    );
    assert_eq!(
        validate_ground_derivation(&ordinary, &concrete_refutation()),
        Err(GroundDerivationError::InvalidSourceProblem)
    );
}

#[test]
fn metadata_copy_and_comparison_allowances_fail_closed() {
    let mut remaining = 2;
    assert!(copy_sort(
        &ChcSort::Uninterpreted("too_long".into()),
        0,
        &mut remaining
    )
    .is_err());
    assert_eq!(remaining, 0);
    let mut deep = ChcSort::Int;
    for _ in 0..MAX_ARRAY_DEPTH {
        deep = ChcSort::Array(Box::new(ChcSort::Int), Box::new(deep));
    }
    let mut remaining = MAX_COPY_WORK;
    assert!(copy_sort(&deep, 0, &mut remaining).is_err());
    let source = problem();
    let mut guard = AuthenticatedDatatypes::new(&source, &[]).expect("registered definitions");
    guard.comparison_remaining = 0;
    assert!(guard.matches("nil_331", &list_sort(&source), &[]).is_err());
}

#[test]
fn scalar_only_nodes_and_unused_predicate_sorts_do_not_consume_datatype_admission() {
    // The standalone typed-function checker did not impose the executor's
    // 131072-expression-root/node cap. Its new metadata authentication must
    // not impose that ceiling on ordinary scalar nodes or unused scalar sorts.
    let mut source = problem();
    source.declare_predicate("unused_scalar", vec![ChcSort::Int; 131_073]);
    let expression = ChcExpr::Op(ChcOp::And, vec![Arc::new(ChcExpr::Bool(true)); 131_073]);
    let guard = AuthenticatedDatatypes::new(&source, &[&expression])
        .expect("scalar work remains outside datatype admission accounting");
    assert!(guard.contains("cons_296"));
    source
        .validate_live_typed_function_applications()
        .expect("unused scalar predicate metadata must not consume DT root cap");
}

#[test]
fn forgeries_inside_the_nested_tail_snapshot_are_rejected() {
    // Forgeries the by-name (nominal) tail comparison could in principle
    // hide: everything about the OUTER signature matches the registry; only
    // the nested snapshot differs (an appended constructor, a retyped head, a
    // tail cut to a different bare name, a forgery three levels deep, a
    // nested snapshot under a different name).
    for mutation in 0..5 {
        let mut source = problem();
        let mut forged = list_sort(&source);
        {
            let mut outer = constructors(&mut forged);
            let tail = &mut outer[1].selectors[1].sort;
            match mutation {
                0 => constructors(tail).push(ChcDtConstructor {
                    name: "extra".into(),
                    selectors: Vec::new(),
                }),
                1 => constructors(tail)[1].selectors[0].sort = ChcSort::Bool,
                2 => {
                    constructors(tail)[1].selectors[1].sort =
                        ChcSort::Uninterpreted("other_list".into())
                }
                3 => {
                    let deeper = ChcSort::Datatype {
                        name: "list_298".into(),
                        constructors: constructors(tail).clone().into(),
                    };
                    let mut deepest = deeper.clone();
                    constructors(&mut deepest)[1].selectors[0].name = "forged_head".into();
                    let mut middle = deeper;
                    constructors(&mut middle)[1].selectors[1].sort = deepest;
                    *tail = middle;
                }
                _ => {
                    let ChcSort::Datatype { name, .. } = tail else {
                        panic!()
                    };
                    *name = "list_299".into();
                }
            }
        }
        source.declare_predicate("unused_forged_profile", vec![forged]);
        source
            .validate_live_typed_function_applications()
            .expect_err(&format!("mutation {mutation} must be refused"));
        assert_eq!(
            validate_ground_derivation(&source, &concrete_refutation()),
            Err(GroundDerivationError::InvalidSourceProblem),
            "mutation {mutation}"
        );
    }
}

#[test]
fn a_deeper_honest_unfolding_of_the_tail_still_replays() {
    // Control for the forgeries above: an honest snapshot unfolded two
    // levels deep is the same definition, admitted and replayed.
    let mut source = problem();
    let mut honest = list_sort(&source);
    let tail = constructors(&mut honest)[1].selectors[1].sort.clone();
    let mut deep = honest.clone();
    constructors(&mut deep)[1].selectors[1].sort = ChcSort::Datatype {
        name: "list_298".into(),
        constructors: {
            let mut c = constructors(&mut honest.clone()).clone();
            c[1].selectors[1].sort = tail;
            c.into()
        },
    };
    source.declare_predicate("unused_deep_profile", vec![deep]);
    source
        .validate_live_typed_function_applications()
        .expect("an honest deeper unfolding is the same definition");
    assert_eq!(
        validate_ground_derivation(&source, &concrete_refutation()),
        Ok(())
    );
}
