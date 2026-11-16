// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![allow(clippy::unwrap_used, clippy::panic)]

use super::*;
use crate::ChcParser;
use std::fmt::Write as _;

mod fixtures;
mod reference;
use fixtures::*;

#[test]
fn acyclic_nested_arrays_and_signatures_share_existing_datatype_definitions() {
    let parser = parsed(ACYCLIC);
    parser.problem.validate().unwrap();
    let leaf = &parser.declared_datatype_sorts["Leaf"];
    let pair = &parser.declared_datatype_sorts["Pair"];
    let outer = &parser.declared_datatype_sorts["Outer"];
    same_metadata(leaf, field(pair, 0));
    same_metadata(leaf, field(pair, 1));
    same_metadata(pair, field(outer, 0));
    same_metadata(leaf, array_value(array_value(field(outer, 1))));

    let predicate = parser.problem.get_predicate_by_name("Inv").unwrap();
    for (index, source) in [leaf, pair, outer].into_iter().enumerate() {
        same_metadata(source, &predicate.arg_sorts[index]);
    }
    same_metadata(leaf, &parser.variables["l"]);
    same_metadata(pair, &parser.functions["pair"].0);
    same_metadata(leaf, &parser.functions["pair"].1[0]);
    same_metadata(leaf, &parser.functions["first"].0);
    same_metadata(pair, &parser.functions["first"].1[0]);
    same_metadata(pair, &parser.functions["pair-field"].0);
    same_metadata(leaf, &parser.problem.datatype_defs()["Pair"][0].1[0].1);
    same_metadata(
        leaf,
        array_value(array_value(
            &parser.problem.datatype_defs()["Outer"][0].1[1].1,
        )),
    );
}

#[test]
fn unrelated_plural_declaration_preserves_prior_acyclic_identity() {
    let mut parser = parsed(ACYCLIC);
    let before: Vec<_> = ["Leaf", "Pair", "Outer"]
        .into_iter()
        .map(|name| parser.declared_datatype_sorts[name].clone())
        .collect();
    feed(
        &mut parser,
        "(declare-datatypes ((Flag 0)) (((flag-off) (flag-on))))",
    );
    for (name, old) in ["Leaf", "Pair", "Outer"].into_iter().zip(&before) {
        same_metadata(old, &parser.declared_datatype_sorts[name]);
    }
    same_metadata(
        &before[0],
        array_value(array_value(field(
            &parser.declared_datatype_sorts["Outer"],
            1,
        ))),
    );
    parser.problem.validate().unwrap();
}

#[test]
fn unchanged_resolution_is_borrowed_without_structural_equality() {
    let parser = parsed(ACYCLIC);
    let leaf = parser.declared_datatype_sorts["Leaf"].clone();
    let array = ChcSort::Array(Box::new(ChcSort::Int), Box::new(leaf.clone()));
    for sort in [
        ChcSort::Bool,
        ChcSort::Uninterpreted("Missing".into()),
        leaf,
        array,
    ] {
        let mut memo = ResolutionMemo::default();
        let mut resolver = Resolver::new(&parser.declared_datatype_sorts, &mut memo);
        let result = resolver.resolve(&sort);
        assert!(matches!(result, Cow::Borrowed(value) if std::ptr::eq(value, &raw const sort)));
        assert!(resolver.seen.is_empty());
    }
}

#[test]
fn placeholder_resolution_copies_only_changed_ancestors() {
    let mut parser = ChcParser::new();
    let leaf = datatype("Leaf", "leaf", vec![ChcSort::Int]);
    parser
        .declared_datatype_sorts
        .insert("Leaf".into(), leaf.clone());
    let source = datatype(
        "Outer",
        "outer",
        vec![
            leaf.clone(),
            ChcSort::Array(
                Box::new(ChcSort::Bool),
                Box::new(ChcSort::Uninterpreted("Leaf".into())),
            ),
        ],
    );
    let mut memo = ResolutionMemo::default();
    let mut resolver = Resolver::new(&parser.declared_datatype_sorts, &mut memo);
    let result = resolver.resolve(&source);
    assert!(matches!(&result, Cow::Owned(_)));
    assert!(!crate::ChcDtConstructors::ptr_eq(
        metadata(&source),
        metadata(&result)
    ));
    same_metadata(&leaf, field(&result, 0));
    same_metadata(&leaf, array_value(field(&result, 1)));
    assert!(
        matches!(array_value(field(&source, 1)), ChcSort::Uninterpreted(name) if name == "Leaf")
    );
    assert!(resolver.seen.is_empty());
}

#[test]
fn self_mutual_and_forward_references_keep_finite_snapshot_shape() {
    let self_recursive = parsed(
        "(declare-datatype List ((nil) (cons (head Int) (tail List)))) \
         (declare-rel Inv (List)) (declare-var xs List) (rule (Inv xs)) (query Inv)",
    );
    self_recursive.problem.validate().unwrap();
    let list = &self_recursive.declared_datatype_sorts["List"];
    let tail_snapshot = &metadata(list)[1].selectors[1].sort;
    assert!(matches!(tail_snapshot, ChcSort::Datatype { name, .. } if name == "List"));
    assert!(matches!(&metadata(tail_snapshot)[1].selectors[1].sort,
        ChcSort::Uninterpreted(name) if name == "List"));
    same_metadata(list, &self_recursive.functions["tail"].0);

    let mutual = parsed(
        "(declare-datatypes ((A 0) (B 0)) (((mk-a (a-b B)) (a-zero)) ((mk-b (b-a A)) (b-zero)))) \
         (declare-rel Inv (A)) (declare-var x A) (rule (Inv x)) (query Inv)",
    );
    mutual.problem.validate().unwrap();
    for (name, other) in [("A", "B"), ("B", "A")] {
        let nested = field(&mutual.declared_datatype_sorts[name], 0);
        assert!(matches!(nested, ChcSort::Datatype { name, .. } if name == other));
        assert!(matches!(field(nested, 0), ChcSort::Uninterpreted(back) if back == name));
    }

    let forward = parsed(
        "(declare-datatypes ((A 0) (B 0) (C 0)) \
          (((mk-a (a-b B))) ((mk-b (b-c C))) ((mk-c (c-value Int))))) \
         (declare-rel Inv (A C)) (declare-var a A) (declare-var c C) \
         (rule (Inv a c)) (query Inv)",
    );
    forward.problem.validate().unwrap();
    let nested_b = field(&forward.declared_datatype_sorts["A"], 0);
    assert!(matches!(field(nested_b, 0), ChcSort::Uninterpreted(name) if name == "C"));
    same_metadata(
        &forward.declared_datatype_sorts["C"],
        &forward.functions["b-c"].0,
    );
}

#[test]
fn seen_name_cut_keeps_embedded_definition_and_registry_placeholder_distinct() {
    let mut parser = ChcParser::new();
    let registry = datatype("T", "registered", vec![ChcSort::Bool]);
    let embedded = datatype("T", "embedded", vec![ChcSort::Int]);
    parser
        .declared_datatype_sorts
        .insert("T".into(), registry.clone());
    let mut memo = ResolutionMemo::default();
    let mut resolver = Resolver::on_path(&parser.declared_datatype_sorts, &mut memo, &["T"]);
    let result = resolver.resolve(&embedded);
    assert!(matches!(&result, Cow::Borrowed(_)));
    same_metadata(&embedded, &result);
    let placeholder = ChcSort::Uninterpreted("T".into());
    let resolved_placeholder = resolver.resolve(&placeholder);
    same_metadata(&registry, &resolved_placeholder);
    assert_eq!(resolver.seen.len(), 1);
    assert!(resolver.seen.contains("T"));
}

#[test]
fn registry_replacement_never_canonicalizes_complete_conflicting_metadata() {
    let mut parser = ChcParser::new();
    let old = datatype("T", "old", vec![ChcSort::Int]);
    parser
        .declared_datatype_sorts
        .insert("T".into(), old.clone());
    let new = datatype("T", "new", vec![ChcSort::Bool]);
    parser
        .declared_datatype_sorts
        .insert("T".into(), new.clone());
    let source = datatype(
        "Outer",
        "outer",
        vec![old.clone(), ChcSort::Uninterpreted("T".into())],
    );
    let mut memo = ResolutionMemo::default();
    let mut resolver = Resolver::new(&parser.declared_datatype_sorts, &mut memo);
    let resolved = resolver.resolve(&source);
    same_metadata(&old, field(&resolved, 0));
    same_metadata(&new, field(&resolved, 1));
    assert!(!crate::ChcDtConstructors::ptr_eq(
        metadata(field(&resolved, 0)),
        metadata(field(&resolved, 1))
    ));
    assert_eq!(metadata(field(&resolved, 0))[0].name, "old");
    assert_eq!(metadata(field(&resolved, 1))[0].name, "new");
    assert!(resolver.seen.is_empty());
}

#[test]
fn parsed_conflicting_redefinition_remains_visible_to_problem_validation() {
    let source = "(set-logic HORN) \
        (declare-datatype T ((old (old-field Int)))) \
        (declare-var before T) \
        (declare-datatype T ((new (new-field Bool)))) \
        (declare-var after T) \
        (assert (= before after)) (check-sat)";
    let problem = ChcParser::parse(source).unwrap();
    let error = problem
        .validate()
        .expect_err("conflicting definitions must remain visible");
    assert!(
        error
            .to_string()
            .contains("conflicting in-memory definitions"),
        "{error}"
    );
    assert!(ChcParser::parse("(declare-var s (Seq Int))").is_err());
}

/// `D1 = mk(a: leaf, b: leaf)`, `Dk = mk(a: D(k-1), b: D(k-1))`, one
/// `declare-datatype` per level: `O(k)` text, `2^k` paths.
fn struct_dag(leaf: &str, k: usize) -> String {
    let mut text = String::new();
    for level in 1..=k {
        let inner = if level == 1 {
            leaf.to_owned()
        } else {
            format!("D{}", level - 1)
        };
        write!(
            &mut text,
            "(declare-datatype D{level} ((mk{level} (a{level} {inner}) (b{level} {inner})))) "
        )
        .unwrap();
    }
    text
}

#[test]
fn nested_datatype_dag_resolves_in_type_text_time() {
    // 2^64 paths: a walk of the tree expansion would not return.
    let parser = parsed(&struct_dag("(_ BitVec 32)", 64));
    let top = &parser.declared_datatype_sorts["D64"];
    same_metadata(&parser.declared_datatype_sorts["D63"], field(top, 0));
    same_metadata(&parser.declared_datatype_sorts["D63"], field(top, 1));
    same_metadata(
        &parser.declared_datatype_sorts["D63"],
        &parser.functions["a64"].0,
    );
}

#[test]
fn dag_over_a_recursive_snapshot_resolves_in_type_text_time() {
    // Every level reaches the `List` snapshot's cut placeholder, so the
    // closedness shortcut alone cannot skip it; the path-independent memo does.
    let source = format!(
        "(declare-datatype List ((nil) (cons (head Int) (tail List)))) {}",
        struct_dag("List", 64)
    );
    let parser = parsed(&source);
    let list = &parser.declared_datatype_sorts["List"];
    let mut level = &parser.declared_datatype_sorts["D64"];
    for depth in (1..64).rev() {
        level = field(level, depth % 2);
        same_metadata(&parser.declared_datatype_sorts[&format!("D{depth}")], level);
    }
    same_metadata(list, field(level, 0));
    same_metadata(list, field(level, 1));
    let tail = &metadata(field(level, 0))[1].selectors[1].sort;
    assert!(matches!(&metadata(tail)[1].selectors[1].sort,
        ChcSort::Uninterpreted(name) if name == "List"));
}

const LIST: &str = "(declare-datatype List ((nil) (cons (head Int) (tail List)))) ";

/// One `declare-datatypes` command holding every level of [`struct_dag`].
fn struct_dag_one_block(leaf: &str, k: usize) -> String {
    let mut names = String::new();
    for level in 1..=k {
        write!(&mut names, "(D{level} 0)").unwrap();
    }
    let mut bodies = String::new();
    for level in 1..=k {
        let inner = if level == 1 {
            leaf.to_owned()
        } else {
            format!("D{}", level - 1)
        };
        write!(
            &mut bodies,
            "((mk{level} (a{level} {inner}) (b{level} {inner})))"
        )
        .unwrap();
    }
    format!("(declare-datatypes ({names}) ({bodies}))")
}

/// [`struct_dag`] with one `declare-datatypes` command per level.
fn struct_dag_plural_per_level(leaf: &str, k: usize) -> String {
    let mut text = String::new();
    for level in 1..=k {
        let inner = if level == 1 {
            leaf.to_owned()
        } else {
            format!("D{}", level - 1)
        };
        write!(
            &mut text,
            "(declare-datatypes ((D{level} 0)) (((mk{level} (a{level} {inner}) (b{level} {inner}))))) "
        )
        .unwrap();
    }
    text
}

/// One block of `k` datatypes, each with a field of the next one's sort.
fn chained_block(k: usize) -> String {
    let mut names = String::new();
    for level in 1..=k {
        write!(&mut names, "(T{level} 0)").unwrap();
    }
    let mut bodies = String::new();
    for level in 1..=k {
        let next = if level == k {
            "Int".to_owned()
        } else {
            format!("T{}", level + 1)
        };
        write!(&mut bodies, "((mk{level} (f{level} {next})))").unwrap();
    }
    format!("(declare-datatypes ({names}) ({bodies}))")
}

/// `k` unrelated self-recursive lists, one `declare-datatype` each.
fn recursive_lists(k: usize) -> String {
    let mut text = String::new();
    for level in 1..=k {
        write!(&mut text, "(declare-datatype L{level} ((nil{level}) (cons{level} (h{level} Int) (t{level} L{level})))) ").unwrap();
    }
    text
}

#[test]
fn resolution_work_is_linear_in_the_declarations_for_every_encoding() {
    let encodings: [(&str, fn(usize) -> String); 7] = [
        ("declare-datatype per level", |k| {
            struct_dag("(_ BitVec 32)", k)
        }),
        ("declare-datatype per level over List", |k| {
            format!("{LIST}{}", struct_dag("List", k))
        }),
        ("one declare-datatypes block", |k| {
            struct_dag_one_block("(_ BitVec 32)", k)
        }),
        ("declare-datatypes per level", |k| {
            struct_dag_plural_per_level("(_ BitVec 32)", k)
        }),
        ("declare-datatypes per level over List", |k| {
            format!("{LIST}{}", struct_dag_plural_per_level("List", k))
        }),
        (
            "one block chaining through forward references",
            chained_block,
        ),
        (
            "self-recursive lists, one declaration each",
            recursive_lists,
        ),
    ];
    for (encoding, source) in encodings {
        let work: Vec<usize> = [16, 32, 64]
            .into_iter()
            .map(|k| parsed(&source(k)).dt_resolution.work())
            .collect();
        // Linear work at most doubles with k (a fixed part only lowers the
        // ratio); quadratic work would quadruple, a tree walk would square.
        // The count includes the memo's bookkeeping (roots re-resolved per
        // block, entries unsettled per generation); a BitVec-only DAG does no
        // resolution work at all.
        for pair in work.windows(2) {
            assert!(
                pair[1] * 2 <= pair[0] * 5,
                "{encoding}: resolution work {work:?} for k = 16, 32, 64"
            );
        }
    }
}
