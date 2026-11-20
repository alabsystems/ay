// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `(get-value)` answers a term that mentions an application of an ordinary
//! declared function from the model `(get-model)` prints, or with an error
//! (#get-value-published-model). A test either replays a run's printed values
//! with `common::coherence::assert_published_values_coherent` or compares the
//! run's outputs with fixed texts.

#![allow(clippy::panic)]

mod common;

use common::coherence::{assert_published_values_coherent, Expect, PublishedRun};
use ntest::timeout;

// ---- 1.1: answers exact against the printed model of the same run ----

#[test]
#[timeout(60000)]
fn n1_nested_int_applications_read_the_printed_tables() {
    let run = assert_published_values_coherent(
        "(set-logic QF_UFLIA)
         (set-option :produce-models true)
         (declare-fun f (Int) Int)
         (declare-fun g (Int) Int)
         (declare-fun x () Int)
         (assert (= x 1))
         (assert (= (f 1) 5))
         (assert (= (g 5) 7))
         (assert (= (g 6) 8))
         (check-sat)
         (get-model)
         (get-value (x (f x) (g 5) (g (f x)) (g (f 1)) (= (g (f x)) 7)))",
        Expect::Literal,
    );
    assert_eq!(run.expect_value("(g (f x))"), "7");
    assert_eq!(run.expect_value("(= (g (f x)) 7)"), "true");
}

#[test]
#[timeout(60000)]
fn t8_bitvector_keyed_enum_table() {
    assert_published_values_coherent(
        "(set-logic ALL)
         (set-option :produce-models true)
         (declare-datatypes ((E 0)) (((e) (b) (c))))
         (declare-fun f ((_ BitVec 4)) E)
         (declare-fun g (E) (_ BitVec 4))
         (declare-fun x () (_ BitVec 4))
         (declare-fun y () E)
         (assert (= (f x) b))
         (assert (not (= (f (bvadd x #x1)) b)))
         (assert (= (g (f #x3)) #x7))
         (assert (= (g y) #x2))
         (check-sat)
         (get-model)
         (get-value ((f x) (f #x3) y (g y) (f #x0)))",
        Expect::Literal,
    );
}

#[test]
#[timeout(60000)]
fn t8b_bitvector_keyed_enum_table_one_query_per_batch() {
    assert_published_values_coherent(
        "(set-logic ALL)
         (set-option :produce-models true)
         (declare-datatypes ((E 0)) (((e) (b) (c))))
         (declare-fun f ((_ BitVec 4)) E)
         (declare-fun g (E) (_ BitVec 4))
         (declare-fun x () (_ BitVec 4))
         (declare-fun y () E)
         (assert (= (f x) b))
         (assert (not (= (f (bvadd x #x1)) b)))
         (assert (= (g (f #x3)) #x7))
         (assert (= (g y) #x2))
         (check-sat)
         (get-model)
         (get-value (x))
         (get-value ((f x)))
         (get-value ((f #x0)))
         (get-value ((= (f x) (f #x0))))
         (get-value ((f #x1)))
         (get-value ((f #x5)))
         (get-value ((f (bvadd x #x1))))
         (get-value ((g (f #x0))))
         (get-value ((g b)))
         (get-value ((g e)))
         (get-value ((g c)))
         (get-value ((= (f #x0) b)))
         (get-value ((f #x3)))
         (get-value ((g (f #x3))))
         (get-value (y))
         (get-value ((g y)))",
        Expect::Literal,
    );
}

const LANE1_PREFIX: &str = "(set-logic QF_DT)
     (set-option :produce-models true)
     (declare-datatype Unit ((u0) (u1) (u2)))
     (declare-fun f (Unit) Unit)
     (declare-fun x () Unit)
     (assert (= (f u0) u1))
     (assert (not (= (f u1) u1)))
     (assert (not (= x (f u1))))
     (assert (not (= x u0)))
     (check-sat)
     (get-model)";

#[test]
#[timeout(60000)]
fn lane1_enum_table_at_an_unlisted_constructor() {
    assert_published_values_coherent(
        &format!("{LANE1_PREFIX}\n(get-value ((f u2)))"),
        Expect::Literal,
    );
}

#[test]
#[timeout(60000)]
fn lane1b_enum_table_at_variable_and_nested_points() {
    assert_published_values_coherent(
        &format!("{LANE1_PREFIX}\n(get-value (x (f u1) (f x) (= (f x) (f u1)) (f u2) (f (f u0))))"),
        Expect::Literal,
    );
}

#[test]
#[timeout(60000)]
fn lane1c_entailed_enum_application() {
    let run = assert_published_values_coherent(
        "(set-logic QF_DT)
         (set-option :produce-models true)
         (declare-datatype Unit ((u0) (u1) (u2)))
         (declare-fun f (Unit) Unit)
         (declare-fun x () Unit)
         (assert (= (f u1) u2))
         (assert (= x u1))
         (check-sat)
         (get-model)
         (get-value (x (f u1) (f x) (= (f x) u2)))",
        Expect::Literal,
    );
    assert_eq!(run.expect_value("(f x)"), "u2");
    assert_eq!(run.expect_value("(= (f x) u2)"), "true");
}

#[test]
#[timeout(60000)]
fn lane_clash_user_constructor_spelled_like_an_abstract_value() {
    assert_published_values_coherent(
        "(set-logic QF_DT)
         (set-option :produce-models true)
         (declare-datatype Unit ((|@Unit!1|) (u1) (u2)))
         (declare-fun f (Unit) Unit)
         (declare-fun x () Unit)
         (assert (= (f |@Unit!1|) u1))
         (assert (not (= (f u1) u1)))
         (assert (not (= x (f u1))))
         (assert (not (= x |@Unit!1|)))
         (check-sat)
         (get-model)
         (get-value ((f u2) x (f x)))",
        Expect::Literal,
    );
}

#[test]
#[timeout(60000)]
fn gv4b_selector_bearing_result_reads_the_printed_cell() {
    let run = assert_published_values_coherent(
        "(set-logic ALL)
         (set-option :produce-models true)
         (declare-datatypes ((L 0)) (((nil) (cons (hd Int) (tl L)))))
         (declare-fun f (Int) L)
         (declare-fun x () Int)
         (assert (= x 1))
         (assert (= (f 1) (cons 3 nil)))
         (assert (= (f 2) nil))
         (check-sat)
         (get-model)
         (get-value ((f x) (= (f x) (cons 3 nil)) ((_ is cons) (f x)) (hd (f x))))",
        Expect::Literal,
    );
    assert_eq!(run.expect_value("(f x)"), "(cons 3 nil)");
    assert_eq!(run.expect_value("(= (f x) (cons 3 nil))"), "true");
    assert_eq!(run.expect_value("((_ is cons) (f x))"), "true");
    assert_eq!(run.expect_value("(hd (f x))"), "3");
}

#[test]
#[timeout(60000)]
fn us_const_gv_fresh_declare_sort_application_has_a_value() {
    assert_published_values_coherent(
        "(set-logic QF_UF)
         (set-option :produce-models true)
         (declare-sort U 0)
         (declare-const a U)
         (declare-const b U)
         (declare-fun f (U) U)
         (assert (distinct a b))
         (assert (= (f a) b))
         (check-sat)
         (get-model)
         (get-value (a b (f a) (f b) (f (f a))))",
        Expect::Literal,
    );
}

#[test]
#[timeout(60000)]
fn n2_declare_sort_chain_and_predicate() {
    assert_published_values_coherent(
        "(set-logic QF_UF)
         (set-option :produce-models true)
         (declare-sort U 0)
         (declare-fun f (U) U)
         (declare-fun g (U) U)
         (declare-fun p (U) Bool)
         (declare-fun x () U)
         (declare-fun a () U)
         (declare-fun b () U)
         (declare-fun c () U)
         (assert (distinct a b c))
         (assert (= x a))
         (assert (= (f a) b))
         (assert (= (g b) c))
         (assert (= (g c) a))
         (assert (p b))
         (assert (not (p c)))
         (check-sat)
         (get-model)
         (get-value (x (f x) (g (f x)) (= (g (f x)) c) (p (f x)) (p (g (f x)))))",
        Expect::Literal,
    );
}

#[test]
#[timeout(60000)]
fn n01_declare_sort_unlisted_point() {
    assert_published_values_coherent(
        "(set-logic QF_UF)
         (set-option :produce-models true)
         (declare-sort U 0)
         (declare-fun f (U) U)
         (declare-fun x () U)
         (declare-fun y () U)
         (assert (not (= x y)))
         (assert (= (f x) y))
         (check-sat)
         (get-model)
         (get-value (x y (f x) (f y)))",
        Expect::Literal,
    );
}

// ---- 1.2: coherent, or an honest error ----

/// lane1d's batch is coherent with the printed model, or an error.
#[test]
#[timeout(60000)]
fn lane1d_predicate_over_an_enum_application() {
    assert_published_values_coherent(
        "(set-logic QF_DT)
         (set-option :produce-models true)
         (declare-datatype Unit ((u0) (u1) (u2)))
         (declare-fun f (Unit) Unit)
         (declare-fun p (Unit) Bool)
         (declare-fun x () Unit)
         (assert (= (f u0) u1))
         (assert (not (= (f u1) u1)))
         (assert (not (= x (f u1))))
         (assert (not (= x u0)))
         (assert (p u2))
         (assert (not (p u0)))
         (assert (not (p u1)))
         (check-sat)
         (get-model)
         (get-value ((f u2) (p (f u2)) (p u0) (p u2)))",
        Expect::AllowBatchError,
    );
}

#[test]
#[timeout(60000)]
fn t12_unmentioned_constructor_points() {
    assert_published_values_coherent(
        "(set-logic QF_UFDTLIA)
         (set-option :produce-models true)
         (declare-datatypes ((E 0)) (((e) (b) (c))))
         (declare-fun f (E) Int)
         (declare-fun h (E) E)
         (declare-fun x () E)
         (assert (= (f e) 1))
         (assert (= (f b) 2))
         (assert (= (h x) b))
         (assert (= x e))
         (check-sat)
         (get-model)
         (get-value ((f c) (h c) (h e) (h b)))",
        Expect::AllowBatchError,
    );
}

#[test]
#[timeout(60000)]
fn t12a_in_graph_applications_without_get_model() {
    assert_published_values_coherent(
        "(set-logic QF_UFDTLIA)
         (set-option :produce-models true)
         (declare-datatypes ((E 0)) (((e) (b) (c))))
         (declare-fun f (E) Int)
         (declare-fun h (E) E)
         (declare-fun x () E)
         (assert (= (f e) 1))
         (assert (= (f b) 2))
         (assert (= (h x) b))
         (assert (= x e))
         (check-sat)
         (get-value (x (h x) (h e) (= (h x) (h e)) (= (h e) b) (f e) (f x) (f b) (f c) (f (h x)) (h (h x))))",
        Expect::AllowBatchError,
    );
}

#[test]
#[timeout(60000)]
fn t12e_integer_table_over_an_enum_application() {
    assert_published_values_coherent(
        "(set-logic QF_UFDTLIA)
         (set-option :produce-models true)
         (declare-datatypes ((E 0)) (((e) (b) (c))))
         (declare-fun g (E) Int)
         (declare-fun h (E) E)
         (declare-fun x () E)
         (assert (= (g e) 10))
         (assert (= (g b) 20))
         (assert (= (g c) 30))
         (assert (= (h x) b))
         (assert (= x e))
         (check-sat)
         (get-model)
         (get-value ((h e) (g (h e)) (g e) (g b) (+ (g (h e)) 0)))",
        Expect::AllowBatchError,
    );
}

#[test]
#[timeout(60000)]
fn t12d_reordered_constructors() {
    assert_published_values_coherent(
        "(set-logic QF_UFDT)
         (set-option :produce-models true)
         (declare-datatypes ((E 0)) (((c) (b) (e))))
         (declare-fun h (E) E)
         (declare-fun x () E)
         (assert (= (h x) b))
         (assert (= x e))
         (check-sat)
         (get-model)
         (get-value (x (h x) (h e) (= (h e) b) (h b) (h c)))",
        Expect::AllowBatchError,
    );
}

/// `f`'s printed cells at `1` and at the else branch are abstract values of
/// `(Ph Int)` whose EUF classes hold `pa` and `pb`. Here (f 1) is `pa` and
/// (f 3), which selects the else branch, is `pb`.
#[test]
#[timeout(60000)]
fn t7b_parametric_enum_table_answers_its_backed_else_cell() {
    let run = assert_published_values_coherent(
        "(set-logic ALL)
         (set-option :produce-models true)
         (declare-datatypes ((Ph 1)) ((par (T) ((pa) (pb)))))
         (declare-fun f (Int) (Ph Int))
         (declare-fun g ((Ph Int)) Int)
         (declare-fun x () (Ph Int))
         (assert (= (f 1) (as pa (Ph Int))))
         (assert (= (f 2) (as pb (Ph Int))))
         (assert (= (g x) 3))
         (assert (= (g (f 1)) 4))
         (check-sat)
         (get-model)
         (get-value (x (f 1) (f 3)))",
        Expect::AllowBatchError,
    );
    assert_eq!(run.expect_value("(f 1)"), "pa");
    assert_eq!(run.expect_value("(f 3)"), "pb");
}

/// `h`'s printed body is one abstract value of `E`, whose EUF class holds
/// (h k) and `j`. Here (h k), (h j) and (h e) each answer the value printed
/// for `j`, which the assertion (= (h k) j) requires of (h k).
#[test]
#[timeout(60000)]
fn cert_enum_uf_constant_table_answers_its_backed_body() {
    let run = assert_published_values_coherent(
        "(set-logic ALL)
         (set-option :produce-models true)
         (declare-datatypes ((E 0)) (((e) (b) (c))))
         (declare-const k E)
         (declare-const j E)
         (declare-fun h (E) E)
         (declare-fun g (Int) Int)
         (assert (> (g 3) 3))
         (assert (not (= k j)))
         (assert (= (h k) j))
         (assert (forall ((x Int)) (=> (> x 1000) (> (g x) 0))))
         (check-sat)
         (get-model)
         (get-value (k j (h k) (h j) (h e)))",
        Expect::AllowBatchError,
    );
    let j = run.expect_value("j");
    assert!(!j.contains('@'), "{j}");
    for term in ["(h k)", "(h j)", "(h e)"] {
        assert_eq!(run.expect_value(term), j, "{term}");
    }
}

#[test]
#[timeout(60000)]
fn n07_application_at_an_array_element() {
    assert_published_values_coherent(
        "(set-logic ALL)
         (set-option :produce-models true)
         (declare-datatypes ((E 0)) (((e) (b) (c))))
         (declare-fun a () (Array Int E))
         (declare-fun f (E) Int)
         (assert (not (= (select a 1) (select a 2))))
         (assert (= (f (select a 1)) 3))
         (assert (= (f (select a 2)) 4))
         (check-sat)
         (get-model)
         (get-value ((select a 1) (select a 2) (f e) (f b) (f c)))",
        Expect::AllowBatchError,
    );
}

/// A printed body with no keyed row answers its one cell at every point, here
/// at an argument the printed model values only by completion. The cell is
/// an abstract value of `Unit` whose EUF class holds (f x) and `u1`, so each
/// answer is `u1`.
#[test]
#[timeout(60000)]
fn gv6_constant_body_at_an_unconstrained_argument() {
    let run = assert_published_values_coherent(
        "(set-logic QF_UFDT)
         (set-option :produce-models true)
         (declare-datatype Unit ((u0) (u1)))
         (declare-fun f (Unit) Unit)
         (declare-fun x () Unit)
         (declare-fun y () Unit)
         (assert (= (f x) u1))
         (assert (= x u0))
         (check-sat)
         (get-model)
         (get-value (x y (f x) (f y) (f u0)))",
        Expect::Coherent,
    );
    for term in ["(f x)", "(f y)", "(f u0)"] {
        assert_eq!(run.expect_value(term), "u1", "{term}");
    }
}

// ---- Abstract values of a datatype sort in printed cells ----

/// The answers of `run` to `terms`, in order, each also checked to hold no
/// abstract value (no `@`).
fn answers<'r>(run: &'r PublishedRun, terms: &[&str]) -> Vec<&'r str> {
    terms
        .iter()
        .map(|term| {
            let value = run.expect_value(term);
            assert!(!value.contains('@'), "{term} answers {value}");
            value
        })
        .collect()
}

/// `B`'s first constructor is `plain`, `|a b|` or `||`, and `g`'s printed
/// table gives (g u) an abstract value of `B` whose EUF class holds that
/// constructor and `f`. Here, for each spelling, (g u) and `f` answer the
/// constructor, the equalities and the tester over (g u) answer `true`, and
/// the batch is coherent with the printed model.
#[test]
#[timeout(60000)]
fn a_backed_datatype_abstract_cell_answers_its_constructor() {
    for constructor in ["plain", "|a b|", "||"] {
        let run = assert_published_values_coherent(
            &format!(
                "(set-logic QF_UFDT)
                 (set-option :produce-models true)
                 (declare-datatypes ((A 0)) (((kiwi2) (lime))))
                 (declare-datatypes ((B 0)) ((({constructor}) (pear))))
                 (declare-sort U 0)
                 (declare-fun g (U) B)
                 (declare-const u U)
                 (declare-const f B)
                 (assert (= f (g u)))
                 (assert (= (g u) {constructor}))
                 (check-sat)
                 (get-model)
                 (get-value (f (g u) (= (g u) {constructor}) ((_ is {constructor}) (g u)) (= f (g u))))"
            ),
            Expect::Coherent,
        );
        let tester = format!("((_ is {constructor}) (g u))");
        let equality = format!("(= (g u) {constructor})");
        assert_eq!(
            answers(&run, &["f", "(g u)", &equality, &tester, "(= f (g u))"]),
            [constructor, constructor, "true", "true", "true"],
            "{constructor}"
        );
    }
}

/// `g`'s cells are abstract values of `B` whose EUF classes hold `|a b|`
/// and `pear`. Here (g u) is `|a b|`, (g v) is `pear`, and `k` reads them as
/// its printed table does.
#[test]
#[timeout(60000)]
fn backed_datatype_abstract_cells_answer_distinct_constructors() {
    let run = assert_published_values_coherent(
        "(set-logic ALL)
         (set-option :produce-models true)
         (declare-sort U 0)
         (declare-const u U)
         (declare-const v U)
         (declare-datatypes ((B 0)) (((|a b|) (pear))))
         (declare-fun g (U) B)
         (declare-fun k (B) Int)
         (assert (= (g u) |a b|))
         (assert (= (g v) pear))
         (assert (= (k (g u)) 5))
         (check-sat)
         (get-model)
         (get-value ((g u) (g v) (k (g u)) (k |a b|)))",
        Expect::Coherent,
    );
    assert_eq!(
        answers(&run, &["(g u)", "(g v)", "(k (g u))", "(k |a b|)"]),
        ["|a b|", "pear", "5", "5"]
    );
}

/// `h`'s cell is an abstract value of `B`, the field type of the record `P`
/// that `g` returns. Here (h u) and the field (p1 (g u)) are `||`, and (g u)
/// is `(mk || 3)`.
#[test]
#[timeout(60000)]
fn a_backed_datatype_abstract_cell_beside_a_record_field() {
    let run = assert_published_values_coherent(
        "(set-logic ALL)
         (set-option :produce-models true)
         (declare-sort U 0)
         (declare-const u U)
         (declare-datatypes ((B 0)) (((||) (pear))))
         (declare-datatypes ((P 0)) (((mk (p1 B) (p2 Int)))))
         (declare-fun g (U) P)
         (declare-fun h (U) B)
         (assert (= (p1 (g u)) ||))
         (assert (= (p2 (g u)) 3))
         (assert (= (h u) (p1 (g u))))
         (check-sat)
         (get-model)
         (get-value ((g u) (p1 (g u)) (h u) (= (h u) ||)))",
        Expect::Coherent,
    );
    assert_eq!(
        answers(&run, &["(g u)", "(p1 (g u))", "(h u)", "(= (h u) ||)"]),
        ["(mk || 3)", "||", "||", "true"]
    );
}

/// `h`'s cell is an abstract value of `B`, stored as the cell of the array
/// `a` at 1 and of the array `(g u)` at 0. Here (h u) and both cells are
/// `plain`, and no answer holds an abstract value.
#[test]
#[timeout(60000)]
fn a_backed_datatype_abstract_cell_beside_arrays_of_the_datatype() {
    let run = assert_published_values_coherent(
        "(set-logic ALL)
         (set-option :produce-models true)
         (declare-sort U 0)
         (declare-const u U)
         (declare-datatypes ((B 0)) (((plain) (pear))))
         (declare-fun g (U) (Array Int B))
         (declare-fun h (U) B)
         (declare-const a (Array Int B))
         (assert (= (select (g u) 0) plain))
         (assert (= (select a 1) (h u)))
         (assert (= (h u) plain))
         (check-sat)
         (get-model)
         (get-value ((g u) (select (g u) 0) (h u) a (select a 1)))",
        Expect::Coherent,
    );
    let values = answers(
        &run,
        &["(g u)", "(select (g u) 0)", "(h u)", "a", "(select a 1)"],
    );
    assert_eq!([values[1], values[2], values[4]], ["plain"; 3]);
}

/// `g`'s cell is an abstract value of the instance `(Ph Int)` whose EUF class
/// holds `pb` and `y`. Here (g u) and `y` are `pb`.
#[test]
#[timeout(60000)]
fn a_backed_parametric_datatype_abstract_cell_answers_its_constructor() {
    let run = assert_published_values_coherent(
        "(set-logic ALL)
         (set-option :produce-models true)
         (declare-datatypes ((Ph 1)) ((par (T) ((pa) (pb)))))
         (declare-sort U 0)
         (declare-const u U)
         (declare-fun g (U) (Ph Int))
         (declare-const y (Ph Int))
         (assert (= y (g u)))
         (assert (= (g u) (as pb (Ph Int))))
         (check-sat)
         (get-model)
         (get-value (y (g u)))",
        Expect::Coherent,
    );
    assert_eq!(answers(&run, &["y", "(g u)"]), ["pb", "pb"]);
}

/// `g`'s cells are abstract values of `B` whose EUF classes hold no
/// constructor term. Here the batch is coherent with the printed model or an
/// error, no answer holds an abstract value, and every error says the
/// printed cell is not a value of its datatype sort.
#[test]
#[timeout(60000)]
fn an_unbacked_datatype_abstract_cell_is_not_answered() {
    let run = assert_published_values_coherent(
        "(set-logic ALL)
         (set-option :produce-models true)
         (declare-datatypes ((B 0)) (((b1) (b2) (b3) (b4))))
         (declare-fun g (Int) B)
         (declare-fun x () Int)
         (assert (distinct (g 1) (g 2) (g 3)))
         (assert (> x 5))
         (check-sat)
         (get-model)
         (get-value ((g 1) (g 2) (g 3) (g x)))",
        Expect::AllowBatchError,
    );
    for (term, value) in &run.pairs {
        assert!(!value.contains('@'), "{term} answers {value}");
    }
    for error in &run.errors {
        assert!(
            error.contains("is not a value of its datatype sort"),
            "{error}"
        );
    }
}

/// `E`'s constructor `|@E!0|` is spelled as the abstract value `@E!0` of
/// `E`, and `f`'s printed table gives (f 1), which is asserted equal to `b`,
/// a cell spelled `(as @E!0 E)`. The printed model itself is not checked
/// here: replayed, its `(as @E!0 E)` names the constructor, which contradicts
/// `(= (f 1) b)`. Here the get-value answer is `b` for (f 1) or an error that
/// says the printed cell is not a value of its datatype sort.
#[test]
#[timeout(60000)]
fn a_cell_spelled_as_a_constructor_named_like_an_abstract_value_is_not_repeated() {
    let lines = solve_lines(
        "(set-logic ALL)
         (set-option :produce-models true)
         (declare-datatypes ((E 0)) (((b) (|@E!0|))))
         (declare-fun f (Int) E)
         (assert (= (f 1) b))
         (assert (= (f 2) |@E!0|))
         (check-sat)
         (get-model)
         (get-value ((f 1) (f 2)))",
    );
    let answer = lines.last().expect("the get-value answer");
    assert!(
        answer.starts_with("(((f 1) b) ")
            || (answer.starts_with("(error")
                && answer.contains("is not a value of its datatype sort")),
        "{lines:?}"
    );
}

// ---- 1.3: batches that mention no declared function, unchanged ----

fn solve_lines(script: &str) -> Vec<String> {
    common::solve_vec(script)
}

#[test]
#[timeout(120000)]
fn p3_depth_200_record_select_and_deep_ite() {
    let mut chain = "0".to_owned();
    for i in (1..=200).rev() {
        chain = format!("(ite (= x {i}) {i} {chain})");
    }
    let script = format!(
        "(set-logic ALL)
         (set-option :produce-models true)
         (declare-datatypes ((R 0)) (((mk (arr (Array Int Int)) (k Int)))))
         (declare-const r R)
         (declare-const x Int)
         (declare-const y Int)
         (assert (= (select (arr r) 0) 7))
         (assert (= x 3))
         (assert (= y {chain}))
         (check-sat)
         (get-value ((select (arr r) 0) y))"
    );
    assert_eq!(
        solve_lines(&script),
        ["sat", "(((select (arr r) 0) 7) (y 3))"]
    );
}

#[test]
#[timeout(120000)]
fn agg_deep_record_select_beside_a_deep_predicate_chain() {
    let mut chain = "(ite (p 0) y (+ y 0))".to_owned();
    for i in 1..300 {
        chain = format!("(ite (p {i}) {chain} (+ y {i}))");
    }
    let script = format!(
        "(set-logic ALL)
         (set-option :produce-models true)
         (declare-datatypes ((R 0)) (((mk (arr (Array Int Int)) (tag Int)))))
         (declare-const r R)
         (declare-fun p (Int) Bool)
         (declare-const y Int)
         (assert (= (select (arr r) 0) 5))
         (assert (> {chain} 0))
         (check-sat)
         (get-value ((select (arr r) 0)))
         (get-value ((tag r)))"
    );
    assert_eq!(
        solve_lines(&script),
        ["sat", "(((select (arr r) 0) 5))", "(((tag r) 0))"]
    );
}

#[test]
#[timeout(300000)]
fn agg_big_record_select_beside_a_wide_sum() {
    const WIDTH: usize = 30_000;
    let mut script = String::from(
        "(set-logic ALL)
         (set-option :produce-models true)
         (declare-datatypes ((R 0)) (((mk (arr (Array Int Int)) (tag Int)))))
         (declare-const r R)
         (assert (= (select (arr r) 0) 5))\n",
    );
    for i in 0..WIDTH {
        script.push_str(&format!("(declare-const x{i} Int)\n"));
    }
    script.push_str("(assert (> (+");
    for i in 0..WIDTH {
        script.push_str(&format!(" x{i}"));
    }
    script.push_str(") 0))\n(check-sat)\n(get-value ((select (arr r) 0)))");
    assert_eq!(solve_lines(&script), ["sat", "(((select (arr r) 0) 5))"]);
}

// ---- 1.4: key decidability ----

/// A predicate over floating-point arguments at the two terms the script
/// asserts it at: `(g a)` answers true and `(g b)` false, coherently with the
/// printed model.
#[test]
#[timeout(60000)]
fn fp_keyed_ground_applications_answer_their_listed_rows() {
    let run = assert_published_values_coherent(
        "(set-logic QF_UFFP)
         (set-option :produce-models true)
         (declare-fun g ((_ FloatingPoint 5 11)) Bool)
         (declare-const a (_ FloatingPoint 5 11))
         (declare-const b (_ FloatingPoint 5 11))
         (assert (g a))
         (assert (not (g b)))
         (check-sat)
         (get-model)
         (get-value ((g a) (g b)))",
        Expect::Literal,
    );
    assert_eq!(run.expect_value("(g a)"), "true");
    assert_eq!(run.expect_value("(g b)"), "false");
}

const SEQ_KEYED: &str = "(set-logic ALL)
     (set-option :produce-models true)
     (declare-fun f ((Seq Int)) Int)
     (declare-const s (Seq Int))
     (declare-const t (Seq Int))
     (assert (= (f s) 1))
     (assert (= (f t) 2))
     (assert (= (seq.len s) 1))
     (assert (= (seq.len t) 2))
     (check-sat)";

/// A function over sequences at the two terms the script asserts it at:
/// `(f s)` answers 1 and `(f t)` 2, coherently with the printed model.
#[test]
#[timeout(60000)]
fn seq_keyed_in_graph_application_answers_its_listed_row() {
    let run = assert_published_values_coherent(
        &format!("{SEQ_KEYED}\n(get-model)\n(get-value ((f s) (f t)))"),
        Expect::Literal,
    );
    assert_eq!(run.expect_value("(f s)"), "1");
    assert_eq!(run.expect_value("(f t)"), "2");
}

/// An application at a point no listed row's source term names, of a function
/// whose printed keys are sequences, is a batch error that names the term.
#[test]
#[timeout(60000)]
fn seq_keyed_fresh_application_is_a_batch_error_naming_it() {
    let outputs = common::solve_vec(&format!(
        "{SEQ_KEYED}\n(get-value ((f s) (f (seq.unit (seq.nth s 0)))))"
    ));
    assert_eq!(outputs[0], "sat", "{outputs:?}");
    assert!(
        outputs[1].starts_with("(error \"value of (f (seq.unit (seq.nth s 0))) is not available:"),
        "{outputs:?}"
    );
}

/// Applications of floating-point-keyed tables at points that no authored
/// application names answer coherently with the printed tables.
#[test]
#[timeout(60000)]
fn fp_keyed_tables_answer_fresh_points_and_composite_terms() {
    assert_published_values_coherent(
        "(set-logic QF_UFFP)
         (set-option :produce-models true)
         (declare-fun g ((_ FloatingPoint 5 11)) Bool)
         (declare-fun h ((_ FloatingPoint 5 11)) (_ FloatingPoint 5 11))
         (declare-const a (_ FloatingPoint 5 11))
         (declare-const b (_ FloatingPoint 5 11))
         (assert (g a))
         (assert (not (g b)))
         (assert (fp.eq (h a) b))
         (assert (fp.eq (h b) a))
         (check-sat)
         (get-model)
         (get-value ((g (fp.mul RNE a b)) (g (fp.sub RNE b b)) (g (fp.add RNE a b))))
         (get-value ((g (_ +zero 5 11)) (g (_ NaN 5 11)) (g (_ -oo 5 11))))
         (get-value ((ite (g a) a b) (fp.add RNE (h a) (h b)) (h (h a))))",
        Expect::Literal,
    );
}

/// An array-keyed table answers a concrete array argument whose default
/// differs from every key's over an `Int` index, coherently with the printed
/// table.
#[test]
#[timeout(60000)]
fn array_keyed_table_answers_arrays_with_another_default() {
    assert_published_values_coherent(
        "(set-logic ALL)
         (set-option :produce-models true)
         (declare-datatypes ((R 0)) (((mk (arr (Array Int (Array Int Int))) (k Int)))))
         (declare-const r R)
         (declare-fun f (Int) Int)
         (declare-fun g ((Array Int Int)) Int)
         (assert (= (f (select (select (arr r) 1) 2)) 3))
         (assert (> (select (select (arr r) 1) 2) 10))
         (assert (= (g (select (arr r) 1)) 7))
         (assert (= (g (select (arr r) 2)) 8))
         (check-sat)
         (get-model)
         (get-value ((g (select (arr r) 1)) (g (select (arr r) 2)) (g (select (arr r) 3))))
         (get-value ((g ((as const (Array Int Int)) 5))))",
        Expect::Literal,
    );
}

/// The text of the else cell of the one-line body `(get-model)` printed for
/// `name` in `model`: the last token of the line after its `define-fun` line.
/// For tables whose keys do not parse as SMT-LIB terms.
fn else_cell_of_one_line_body(model: &str, name: &str) -> String {
    let mut lines = model.lines();
    lines
        .find(|line| {
            line.trim_start()
                .starts_with(&format!("(define-fun {name} "))
        })
        .unwrap_or_else(|| panic!("{name} is not printed:\n{model}"));
    let body = lines.next().expect("a body line").trim_end_matches(')');
    body.rsplit(' ').next().expect("a last token").to_owned()
}

/// A String-keyed function with the keys `""`, `" "`, `"(x"`, `"k"`,
/// `" lead"` and `"a""b"`: each asserted application answers its asserted
/// value, alone and inside `+`; an application whose argument evaluates to a
/// key answers that key's value; and applications at `"zzzz"` and `"lead"`,
/// which equal no key, answer the else cell of the printed body.
#[test]
#[timeout(60000)]
fn string_keyed_table_answers_listed_computed_and_fresh_points() {
    let outputs = common::solve_vec(
        r#"(set-logic ALL)
         (set-option :produce-models true)
         (declare-fun f (String) Int)
         (declare-fun s () String)
         (assert (= (f "") 1))
         (assert (= (f " ") 2))
         (assert (= (f "(x") 3))
         (assert (= (f "k") 4))
         (assert (= (f " lead") 5))
         (assert (= (f "a""b") 6))
         (assert (= (f s) 10))
         (assert (= (str.len s) 7))
         (check-sat)
         (get-model)
         (get-value ((f "") (f " ") (f "(x") (f "k") (f " lead") (f "a""b") (f s)))
         (get-value ((+ 1 (f "k"))))
         (get-value ((+ (f "") (f " ") (f "(x"))))
         (get-value ((f (str.++ "a" """" "b"))))
         (get-value ((f (str.substr " leading" 0 5))))
         (get-value ((f "zzzz")))
         (get-value ((f "lead")))"#,
    );
    assert_eq!(outputs[0], "sat", "{outputs:?}");
    let otherwise = else_cell_of_one_line_body(&outputs[1], "f");
    assert_eq!(
        outputs[2..],
        [
            r#"(((f "") 1) ((f " ") 2) ((f "(x") 3) ((f "k") 4) ((f " lead") 5) ((f "a""b") 6) ((f s) 10))"#
                .to_owned(),
            r#"(((+ 1 (f "k")) 5))"#.to_owned(),
            r#"(((+ (f "") (f " ") (f "(x")) 6))"#.to_owned(),
            r#"(((f (str.++ "a" """" "b")) 6))"#.to_owned(),
            r#"(((f (str.substr " leading" 0 5)) 5))"#.to_owned(),
            format!(r#"(((f "zzzz") {otherwise}))"#),
            format!(r#"(((f "lead") {otherwise}))"#),
        ],
        "{outputs:?}"
    );
}

/// String-valued applications as arguments and inside String operations:
/// with `(g t)` asserted `"qq"` and `(g "")` asserted `"h""i"`, `(f (g t))` and
/// `(f "qq")` answer the 12 asserted for `(f (g t))`, `(str.len (g t))` answers
/// 2, `(str.len (g ""))` 3 and `(str.++ (g "") "!")` `"h""i!"`.
#[test]
#[timeout(60000)]
fn string_valued_cells_are_read_as_the_strings_they_denote() {
    let outputs = common::solve_vec(
        r#"(set-logic ALL)
         (set-option :produce-models true)
         (declare-fun f (String) Int)
         (declare-fun g (String) String)
         (declare-fun s () String)
         (declare-fun t () String)
         (assert (= (f s) 10))
         (assert (= (f (str.++ s "x")) 11))
         (assert (= (f (g t)) 12))
         (assert (= (f "") 1))
         (assert (= (f "hello") 2))
         (assert (= (g "") "h""i"))
         (assert (= (g "r") "hello"))
         (assert (= (g s) "end"))
         (assert (= (g t) "qq"))
         (assert (= (str.len s) 3))
         (assert (= (str.len t) 2))
         (check-sat)
         (get-value ((f (g t))))
         (get-value ((f "qq")))
         (get-value ((str.len (g t))))
         (get-value ((str.len (g ""))))
         (get-value ((str.++ (g "") "!")))"#,
    );
    assert_eq!(
        outputs,
        [
            "sat",
            "(((f (g t)) 12))",
            r#"(((f "qq") 12))"#,
            "(((str.len (g t)) 2))",
            r#"(((str.len (g "")) 3))"#,
            r#"(((str.++ (g "") "!") "h""i!"))"#,
        ]
    );
}

/// A String key whose characters start and end with `"`, beside the key
/// `"x"`: each asserted application answers its asserted value, and an
/// application at another point is a batch error that names it.
#[test]
#[timeout(60000)]
fn string_key_spelled_like_a_literal_leaves_fresh_points_an_error() {
    let outputs = common::solve_vec(
        r#"(set-logic ALL)
         (set-option :produce-models true)
         (declare-fun f (String) Int)
         (declare-fun s () String)
         (assert (= (f "") 1))
         (assert (= (f """x""") 2))
         (assert (= (f "x") 3))
         (assert (= (f s) 10))
         (assert (= (str.len s) 5))
         (check-sat)
         (get-value ((f "") (f """x""") (f "x")))
         (get-value ((f "zz")))"#,
    );
    assert_eq!(outputs[0], "sat", "{outputs:?}");
    assert_eq!(
        outputs[1], r#"(((f "") 1) ((f """x""") 2) ((f "x") 3))"#,
        "{outputs:?}"
    );
    assert!(
        outputs[2].starts_with(r#"(error "value of (f "zz") is not available:"#),
        "{outputs:?}"
    );
}

/// A String-keyed function whose values hold strings spelled with `""` and
/// `\u{e9}`: `str.len` of the field answers 3 for `"a""b"`, 5 for `"plain"`
/// and 1 for `"\u{e9}"`, and the field of `(f "")` answers `"a""b"`.
#[test]
#[timeout(60000)]
fn strings_inside_datatype_cells_are_read_as_the_strings_they_denote() {
    let outputs = common::solve_vec(
        r#"(set-logic ALL)
         (set-option :produce-models true)
         (declare-datatype P ((mk (name String))))
         (declare-fun f (String) P)
         (declare-fun s () String)
         (assert (= (f "") (mk "a""b")))
         (assert (= (f "k") (mk "plain")))
         (assert (= (f s) (mk "\u{e9}")))
         (assert (= (str.len s) 3))
         (check-sat)
         (get-value ((str.len (name (f "")))))
         (get-value ((str.len (name (f "k")))))
         (get-value ((str.len (name (f s)))))
         (get-value ((name (f ""))))"#,
    );
    assert_eq!(
        outputs,
        [
            "sat",
            r#"(((str.len (name (f ""))) 3))"#,
            r#"(((str.len (name (f "k"))) 5))"#,
            "(((str.len (name (f s))) 1))",
            r#"(((name (f "")) "a""b"))"#,
        ]
    );
}

// ---- Reads the published model defines beside the function tables ----

/// A selector applied to a function application whose printed value is built
/// by another constructor answers what the printed selector definition gives
/// there, alone and inside larger terms.
#[test]
#[timeout(60000)]
fn wrong_constructor_selector_of_an_application_reads_the_printed_selector() {
    let run = assert_published_values_coherent(
        "(set-logic ALL)
         (set-option :produce-models true)
         (declare-datatypes ((L 0)) (((nil) (cons (hd Int) (tl L)))))
         (declare-fun f (Int) L)
         (assert (= (f 1) (cons 3 nil)))
         (assert (= (f 2) nil))
         (assert (= (hd (f 2)) 5))
         (check-sat)
         (get-model)
         (get-value ((f 1) (hd (f 2)) (= (hd (f 2)) 5) (+ 1 (hd (f 2))) (hd (f 1))))",
        Expect::Literal,
    );
    assert_eq!(run.expect_value("(hd (f 2))"), "5");
    assert_eq!(run.expect_value("(= (hd (f 2)) 5)"), "true");
    assert_eq!(run.expect_value("(+ 1 (hd (f 2)))"), "6");
    assert_eq!(run.expect_value("(hd (f 1))"), "3");
}

/// Integer division and remainder by zero over a function application answer
/// the value the asserted equality on that term gives.
#[test]
#[timeout(60000)]
fn division_by_zero_of_an_application_answers_its_asserted_value() {
    let run = assert_published_values_coherent(
        "(set-logic ALL)
         (set-option :produce-models true)
         (declare-fun f (Int) Int)
         (declare-fun z () Int)
         (assert (= (f 1) 4))
         (assert (= z 0))
         (assert (= (div (f 1) z) 7))
         (assert (= (mod (f 1) z) 2))
         (check-sat)
         (get-model)
         (get-value ((div (f 1) z) (mod (f 1) z) (= (div (f 1) z) 7)))",
        Expect::Literal,
    );
    assert_eq!(run.expect_value("(div (f 1) z)"), "7");
    assert_eq!(run.expect_value("(mod (f 1) z)"), "2");
    assert_eq!(run.expect_value("(= (div (f 1) z) 7)"), "true");
}

// ---- Functions the model defines without a function table ----

const C2: &str = "(set-logic UFLIA)
     (set-option :produce-models true)
     (declare-fun f (Int) Int)
     (declare-fun g (Int) Int)
     (declare-fun x () Int)
     (assert (forall ((y Int)) (>= (g y) 0)))
     (assert (= x 1))
     (assert (= (f 1) 5))
     (assert (= (g 5) 7))
     (assert (= (g 6) 8))
     (check-sat)";

/// n1 with a quantified assertion on `g`: applications of `g` at applications
/// of `f` answer 7 at `(f x)` and `(f 1)` and 8 at `(+ (f x) 1)`, coherently
/// with the printed model.
#[test]
#[timeout(60000)]
fn quantified_function_at_a_table_application_has_its_printed_value() {
    let run = assert_published_values_coherent(
        &format!(
            "{C2}
             (get-model)
             (get-value (x (f x) (g 5) (g (f x)) (g (f 1)) (= (g (f x)) 7)))
             (get-value ((g (f 2))))
             (get-value ((g (+ (f x) 1))))"
        ),
        Expect::Literal,
    );
    assert_eq!(run.expect_value("(g (f x))"), "7");
    assert_eq!(run.expect_value("(g (f 1))"), "7");
    assert_eq!(run.expect_value("(= (g (f x)) 7)"), "true");
    assert_eq!(run.expect_value("(g (+ (f x) 1))"), "8");
}

/// `(eval)` answers 7 for the same `(g (f x))`.
#[test]
#[timeout(60000)]
fn eval_of_a_quantified_function_at_a_table_application() {
    let outputs = common::solve_vec(&format!("{C2}\n(eval (g (f x)))"));
    assert_eq!(outputs, ["sat", "7"]);
}

/// A predicate under a quantified assertion at applications of a function
/// with asserted points: `(p (f x))` answers false and `(p (- (f x) 2))` true,
/// and `f` at an `ite` over `(p (f x))` answers 5, coherently with the printed
/// model.
#[test]
#[timeout(60000)]
fn quantified_predicate_at_a_table_application_has_its_printed_value() {
    let run = assert_published_values_coherent(
        "(set-logic UFLIA)
         (set-option :produce-models true)
         (declare-fun f (Int) Int)
         (declare-fun p (Int) Bool)
         (declare-fun x () Int)
         (assert (forall ((y Int)) (=> (p y) (> y 0))))
         (assert (p 3))
         (assert (= (f 1) 5))
         (assert (= (f 4) 9))
         (assert (= x 1))
         (check-sat)
         (get-model)
         (get-value ((p 3) (p (f x)) (p (- (f x) 2))))
         (get-value ((f (ite (p (f x)) 4 1))))
         (get-value ((and (p (- (f x) 2)) (= (f 4) 9))))",
        Expect::Literal,
    );
    assert_eq!(run.expect_value("(p (f x))"), "false");
    assert_eq!(run.expect_value("(p (- (f x) 2))"), "true");
    assert_eq!(run.expect_value("(f (ite (p (f x)) 4 1))"), "5");
    assert_eq!(
        run.expect_value("(and (p (- (f x) 2)) (= (f 4) 9))"),
        "true"
    );
}

/// A function under a quantified assertion at applications of a function
/// with asserted points: `(f (g 3))` answers 0, alone and inside `+` and `=`,
/// coherently with the printed model.
#[test]
#[timeout(60000)]
fn quantified_function_at_a_table_application_inside_larger_terms() {
    let run = assert_published_values_coherent(
        "(set-logic ALL)
         (set-option :produce-models true)
         (declare-fun f (Int) Int)
         (declare-fun g (Int) Int)
         (declare-fun x () Int)
         (assert (forall ((y Int)) (>= (f y) 0)))
         (assert (= (g (f x)) 5))
         (assert (= (g 3) 9))
         (assert (= (f 1) 3))
         (assert (> x 10))
         (check-sat)
         (get-model)
         (get-value ((f (g 3)) (f (g x)) (f (+ (g 3) 0))))
         (get-value ((+ 0 (f (g 3))) (= (f (g 3)) 0)))",
        Expect::Literal,
    );
    assert_eq!(run.expect_value("(f (g 3))"), "0");
    assert_eq!(run.expect_value("(+ 0 (f (g 3)))"), "0");
    assert_eq!(run.expect_value("(= (f (g 3)) 0)"), "true");
}

/// A function no assertion mentions, beside a quantified assertion and a
/// function with asserted points: `(h (f 1))` answers 0, `(f (h (f 1)))` 6 and
/// `(P (h (f 1)))` true, coherently with the printed model.
#[test]
#[timeout(60000)]
fn unmentioned_function_at_a_table_application_has_its_printed_value() {
    let run = assert_published_values_coherent(
        "(set-logic UFLIA)
         (set-option :produce-models true)
         (declare-fun P (Int) Bool)
         (declare-fun f (Int) Int)
         (declare-fun h (Int) Int)
         (assert (forall ((x Int)) (P x)))
         (assert (= (f 1) 5))
         (assert (= (f 2) 6))
         (check-sat)
         (get-model)
         (get-value ((h 1) (h (f 1)) (f (h (f 1))) (P (h (f 1))) (P (f 1))))",
        Expect::Literal,
    );
    assert_eq!(run.expect_value("(h (f 1))"), "0");
    assert_eq!(run.expect_value("(f (h (f 1)))"), "6");
    assert_eq!(run.expect_value("(P (h (f 1)))"), "true");
    assert_eq!(run.expect_value("(P (f 1))"), "true");
}

// ---- The other answer routes ----

const N1: &str = "(set-logic QF_UFLIA)
     (set-option :produce-models true)
     (declare-fun f (Int) Int)
     (declare-fun g (Int) Int)
     (declare-fun x () Int)
     (assert (= x 1))
     (assert (= (f 1) 5))
     (assert (= (g 5) 7))
     (assert (= (g 6) 8))
     (check-sat)";

/// `(eval)` answers n1's (g (f x)) and (= (g (f x)) 7) from the printed
/// tables.
#[test]
#[timeout(60000)]
fn eval_answers_from_the_printed_tables() {
    let outputs = common::solve_vec(&format!("{N1}\n(eval (g (f x)))\n(eval (= (g (f x)) 7))"));
    assert_eq!(outputs, ["sat", "7", "true"]);
}

/// The Rust `values()` answers n1's (g (f x)), built through the API, from the
/// printed tables.
#[test]
#[timeout(60000)]
fn rust_values_answer_from_the_printed_tables() {
    use ay_dpll::api::{Logic, ModelValue, Solver, Sort};
    let mut solver = Solver::new(Logic::QfUflia);
    let f = solver.declare_fun("f", &[Sort::Int], Sort::Int);
    let g = solver.declare_fun("g", &[Sort::Int], Sort::Int);
    let x = solver.declare_const("x", Sort::Int);
    let [one, five, six, seven, eight] = [1, 5, 6, 7, 8].map(|n| solver.int_const(n));
    let f_one = solver.apply(&f, &[one]);
    let g_five = solver.apply(&g, &[five]);
    let g_six = solver.apply(&g, &[six]);
    for (left, right) in [(x, one), (f_one, five), (g_five, seven), (g_six, eight)] {
        let equal = solver.eq(left, right);
        solver.assert_term(equal);
    }
    assert!(solver.check_sat_with_details().result.is_sat());
    let f_x = solver.apply(&f, &[x]);
    let g_f_x = solver.apply(&g, &[f_x]);
    let values = solver
        .try_get_values(&[g_f_x])
        .expect("values of (g (f x))");
    assert!(
        matches!(&values[0], ModelValue::Int(value) if value.to_string() == "7"),
        "{values:?}"
    );
}
