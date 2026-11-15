// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use ay_core::{Sort, TermId, TermStore};
use ay_frontend::parse;

use crate::features::StaticFeatures;
use crate::Executor;

fn nested(terms: &TermStore, roots: &[TermId]) -> bool {
    StaticFeatures::collect(terms, roots).has_nested_arrays
}

fn carrier(name: &str) -> Sort {
    Sort::Uninterpreted(name.to_string())
}

fn int_array(element: Sort) -> Sort {
    Sort::array(Sort::Int, element)
}

/// A declared carrier with an array field, stored in an outer array, is
/// nested; the same outer array over a carrier of scalars is not.
#[test]
fn a_declared_carrier_with_an_array_field_nests_inside_an_outer_array() {
    let mut terms = TermStore::new();
    terms.register_datatype_field_sorts("Row", &[int_array(Sort::Int), Sort::Int]);
    terms.register_datatype_field_sorts("Pair", &[Sort::Int, Sort::Bool]);

    let rows = terms.mk_var("rows", int_array(carrier("Row")));
    assert!(nested(&terms, &[rows]));

    let pairs = terms.mk_var("pairs", int_array(carrier("Pair")));
    assert!(!nested(&terms, &[pairs]), "a carrier of scalars is flat");

    // An undeclared uninterpreted element sort is an ordinary flat array.
    let opaque = terms.mk_var("opaque", int_array(carrier("U")));
    assert!(!nested(&terms, &[opaque]));
}

/// The nesting may sit several carriers deep: `PbTerm{lits: Vec{data: Array}}`
/// is the MODEL_CHECKER_CONSUMER record shape.
#[test]
fn nesting_is_found_through_a_chain_of_declared_carriers() {
    let mut terms = TermStore::new();
    let data = Sort::array(Sort::bitvec(64), Sort::bitvec(40));
    terms.register_datatype_field_sorts("Vec", &[Sort::bitvec(64), data]);
    terms.register_datatype_field_sorts("PbTerm", &[Sort::bitvec(128), carrier("Vec")]);

    let table = terms.mk_var("table", Sort::array(Sort::bitvec(64), carrier("PbTerm")));
    assert!(nested(&terms, &[table]));

    // One record holding one flat array, with no outer array, stays flat.
    let lone = terms.mk_var("lone", carrier("PbTerm"));
    assert!(!nested(&terms, &[lone]));
}

/// A record whose FIELD is itself a nested array carries nested state even
/// with no outer array: injectivity moves `(not (= r1 r2))` onto that field.
#[test]
fn a_lone_carrier_whose_field_is_a_nested_array_is_nested() {
    let mut terms = TermStore::new();
    terms.register_datatype_field_sorts("Grid", &[int_array(int_array(Sort::Int))]);
    let grid = terms.mk_var("grid", carrier("Grid"));
    assert!(nested(&terms, &[grid]));
}

/// Recursive carriers terminate; recursion through an array field nests.
#[test]
fn recursive_carriers_terminate_and_recursion_through_an_array_nests() {
    let mut terms = TermStore::new();
    terms.register_datatype_field_sorts("List", &[]);
    terms.register_datatype_field_sorts("List", &[Sort::Int, carrier("List")]);
    let lists = terms.mk_var("lists", int_array(carrier("List")));
    assert!(!nested(&terms, &[lists]));

    terms.register_datatype_field_sorts("Tree", &[int_array(carrier("Tree"))]);
    let tree = terms.mk_var("tree", carrier("Tree"));
    assert!(nested(&terms, &[tree]));
}

/// A quantifier-bound variable counts, and an inline schema that shares its
/// name with a registered carrier cannot hide the registered array field.
#[test]
fn bound_variables_and_same_named_inline_schemas_are_resolved() {
    let mut terms = TermStore::new();
    terms.register_datatype_field_sorts("Row", &[int_array(Sort::Int)]);
    let body = terms.mk_var("p", Sort::Bool);
    let quantified = terms.mk_forall(vec![("x".to_string(), int_array(carrier("Row")))], body);
    assert!(nested(&terms, &[quantified]));

    let inline_row = Sort::struct_type("Row", [("tag", Sort::Int)]);
    let shadowed = terms.mk_var("shadowed", int_array(inline_row));
    assert!(nested(&terms, &[shadowed]));
}

/// End to end through the SMT-LIB frontend, which is what registers the
/// carrier: the record-boxed memory of the ABV quarantine repro is nested, and
/// a record holding a flat array beside scalars is not.
#[test]
fn parsed_declare_datatype_carriers_are_resolved() {
    let script = "(set-logic ALL)
        (declare-datatype Row ((mk_row (cells (Array (_ BitVec 32) (_ BitVec 32))))))
        (declare-datatype Vec ((mk_vec (len Int) (data (Array Int Int)))))
        (declare-const mem (Array (_ BitVec 32) Row))
        (declare-const v Vec)
        (assert (= (select (cells (select mem #x00000000)) #x00000000) #x00000001))
        (assert (= (select (data v) 0) (len v)))";
    let mut exec = Executor::new();
    exec.execute_all(&parse(script).expect("invariant: valid SMT-LIB"))
        .expect("invariant: declarations and assertions execute");
    let [boxed, flat] = exec.ctx.assertions[..] else {
        panic!("expected exactly two assertions");
    };
    assert!(nested(&exec.ctx.terms, &[boxed]));
    assert!(!nested(&exec.ctx.terms, &[flat]));
}

/// Parametric instances and mutually recursive blocks register their carriers
/// through the same path: `(Box (Array Int Int))` stored in an outer array is
/// nested, `(Box Int)` is not, and a `declare-datatypes` block whose `Node`
/// reaches an array only through its sibling `Leaf` still nests inside an
/// outer array.
#[test]
fn parametric_instances_and_mutual_blocks_are_resolved() {
    let script = "(set-logic ALL)
        (declare-datatype Box (par (T) ((mk_box (unbox T)))))
        (declare-datatypes ((Node 0) (Leaf 0))
          (((mk_node (kid Leaf)) (nil_node))
           ((mk_leaf (cells (Array Int Int))))))
        (declare-const boxed_rows (Array Int (Box (Array Int Int))))
        (declare-const boxed_ints (Array Int (Box Int)))
        (declare-const nodes (Array Int Node))
        (assert (= (select (unbox (select boxed_rows 0)) 0) 1))
        (assert (= (unbox (select boxed_ints 0)) 1))
        (assert (is-mk_node (select nodes 0)))";
    let mut exec = Executor::new();
    exec.execute_all(&parse(script).expect("invariant: valid SMT-LIB"))
        .expect("invariant: declarations and assertions execute");
    let [rows, ints, nodes] = exec.ctx.assertions[..] else {
        panic!("expected exactly three assertions");
    };
    assert!(
        nested(&exec.ctx.terms, &[rows]),
        "parametric array instance"
    );
    assert!(
        !nested(&exec.ctx.terms, &[ints]),
        "parametric scalar instance"
    );
    assert!(nested(&exec.ctx.terms, &[nodes]), "mutual block");
}
