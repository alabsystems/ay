// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Hash-consing, identity and cost of datatype constructor lists.

use super::*;
use crate::{ChcDtSelector, ChcVar};
use std::collections::hash_map::DefaultHasher;
use std::collections::HashSet;

fn selector(name: &str, sort: ChcSort) -> ChcDtSelector {
    ChcDtSelector {
        name: name.to_string(),
        sort,
    }
}

fn constructor(name: &str, selectors: Vec<ChcDtSelector>) -> ChcDtConstructor {
    ChcDtConstructor {
        name: name.to_string(),
        selectors,
    }
}

fn datatype(name: &str, constructors: Vec<ChcDtConstructor>) -> ChcSort {
    ChcSort::Datatype {
        name: name.to_string(),
        constructors: ChcDtConstructors::new(constructors),
    }
}

/// `D0 = (_ BitVec 32)`, `Dk = { ak: D(k-1), bk: D(k-1) }`: `O(k)` type text,
/// `2^k` leaves as a tree.
pub(crate) fn struct_dag(k: usize) -> ChcSort {
    let mut sort = ChcSort::BitVec(32);
    for level in 1..=k {
        sort = datatype(
            &format!("D{level}"),
            vec![constructor(
                &format!("mk{level}"),
                vec![
                    selector(&format!("a{level}"), sort.clone()),
                    selector(&format!("b{level}"), sort),
                ],
            )],
        );
    }
    sort
}

fn constructors_of(sort: &ChcSort) -> &ChcDtConstructors {
    let ChcSort::Datatype { constructors, .. } = sort else {
        panic!("expected a datatype, got {sort:?}")
    };
    constructors
}

fn std_hash<T: Hash>(value: &T) -> u64 {
    let mut hasher = DefaultHasher::new();
    value.hash(&mut hasher);
    hasher.finish()
}

/// Counts the bytes a `Hash` implementation feeds: the hashing work.
#[derive(Default)]
struct CountingHasher(usize);

impl Hasher for CountingHasher {
    fn finish(&self) -> u64 {
        0
    }

    fn write(&mut self, bytes: &[u8]) {
        self.0 += bytes.len();
    }
}

fn hash_work<T: Hash>(value: &T) -> usize {
    let mut hasher = CountingHasher::default();
    value.hash(&mut hasher);
    hasher.0
}

#[test]
fn equal_lists_built_independently_are_one_allocation() {
    for k in [1, 2, 8, 32] {
        let first = struct_dag(k);
        let second = struct_dag(k);
        let (left, right) = (constructors_of(&first), constructors_of(&second));
        assert!(ChcDtConstructors::ptr_eq(left, right), "k={k}");
        assert_eq!(left.id(), right.id());
        assert_eq!(first, second);
        assert_eq!(first.cmp(&second), Ordering::Equal);
        assert_eq!(std_hash(&first), std_hash(&second));
        let x = ChcVar::new("x", first.clone());
        assert_eq!(x, ChcVar::new("x", second.clone()));
        assert_eq!(std_hash(&x), std_hash(&ChcVar::new("x", second)));
    }
}

#[test]
fn interning_is_shared_across_threads() {
    let sorts: Vec<ChcSort> = std::thread::scope(|scope| {
        let workers: Vec<_> = (0..4).map(|_| scope.spawn(|| struct_dag(24))).collect();
        workers
            .into_iter()
            .map(|worker| worker.join().expect("worker"))
            .collect()
    });
    for sort in &sorts[1..] {
        assert!(ChcDtConstructors::ptr_eq(
            constructors_of(&sorts[0]),
            constructors_of(sort)
        ));
    }
}

type Labelled = (&'static str, Vec<ChcDtConstructor>);

/// Lists that differ in exactly one place, including ones a naive spelling
/// (concatenated names, untagged sorts, no counts) would confuse.
fn distinct_lists() -> Vec<Labelled> {
    let mut lists = distinct_constructor_shapes();
    lists.extend(distinct_scalar_selectors());
    lists.extend(distinct_nested_selectors());
    lists
}

/// Constructor counts, names and order.
fn distinct_constructor_shapes() -> Vec<Labelled> {
    vec![
        ("empty", vec![]),
        ("one nullary", vec![constructor("c", vec![])]),
        ("renamed nullary", vec![constructor("d", vec![])]),
        ("empty-named nullary", vec![constructor("", vec![])]),
        (
            "two nullary",
            vec![constructor("c", vec![]), constructor("d", vec![])],
        ),
        (
            "two nullary swapped",
            vec![constructor("d", vec![]), constructor("c", vec![])],
        ),
        (
            "ctor a, selector bc",
            vec![constructor("a", vec![selector("bc", ChcSort::Int)])],
        ),
        (
            "ctor ab, selector c",
            vec![constructor("ab", vec![selector("c", ChcSort::Int)])],
        ),
        (
            "selectors split across constructors",
            vec![
                constructor("c", vec![selector("s", ChcSort::Int)]),
                constructor("t", vec![]),
            ],
        ),
    ]
}

/// Scalar selector sorts, their widths, count and order.
fn distinct_scalar_selectors() -> Vec<Labelled> {
    let one = |sort: ChcSort| vec![constructor("c", vec![selector("s", sort)])];
    vec![
        ("selector Int", one(ChcSort::Int)),
        ("selector Real", one(ChcSort::Real)),
        ("selector Bool", one(ChcSort::Bool)),
        ("selector BV8", one(ChcSort::BitVec(8))),
        ("selector BV16", one(ChcSort::BitVec(16))),
        (
            "two selectors",
            vec![constructor(
                "c",
                vec![selector("s", ChcSort::Int), selector("t", ChcSort::Bool)],
            )],
        ),
        (
            "two selectors swapped",
            vec![constructor(
                "c",
                vec![selector("t", ChcSort::Bool), selector("s", ChcSort::Int)],
            )],
        ),
    ]
}

/// Arrays, uninterpreted sorts and nested datatypes, shallow and deep.
fn distinct_nested_selectors() -> Vec<Labelled> {
    let one = |sort: ChcSort| vec![constructor("c", vec![selector("s", sort)])];
    let leaf = |name: &str| datatype(name, vec![constructor("leaf", vec![])]);
    let array = |key: ChcSort, value: ChcSort| ChcSort::Array(Box::new(key), Box::new(value));
    let mut deep = ChcSort::BitVec(31);
    for level in 1..=6 {
        deep = datatype(
            &format!("D{level}"),
            vec![constructor(
                &format!("mk{level}"),
                vec![
                    selector(&format!("a{level}"), deep.clone()),
                    selector(&format!("b{level}"), deep),
                ],
            )],
        );
    }
    vec![
        ("array Int->Bool", one(array(ChcSort::Int, ChcSort::Bool))),
        ("array Bool->Int", one(array(ChcSort::Bool, ChcSort::Int))),
        ("uninterpreted L", one(ChcSort::Uninterpreted("L".into()))),
        ("datatype L", one(leaf("L"))),
        ("datatype M, same constructors", one(leaf("M"))),
        (
            "datatype L, different constructors",
            one(datatype("L", vec![constructor("other-leaf", vec![])])),
        ),
        ("deep difference", one(deep)),
        ("deep original", one(struct_dag(6))),
    ]
}

#[test]
fn distinct_lists_have_distinct_identities() {
    let lists: Vec<_> = distinct_lists()
        .into_iter()
        .map(|(label, list)| (label, ChcDtConstructors::new(list)))
        .collect();
    let mut ids = HashSet::new();
    for (label, list) in &lists {
        assert!(ids.insert(list.id()), "{label}: id collides");
    }
    for (i, (left_label, left)) in lists.iter().enumerate() {
        for (j, (right_label, right)) in lists.iter().enumerate() {
            let same = i == j;
            assert_eq!(left == right, same, "{left_label} vs {right_label}");
            assert_eq!(
                left.cmp(right) == Ordering::Equal,
                same,
                "{left_label} vs {right_label}"
            );
            assert_eq!(left.cmp(right), right.cmp(left).reverse());
        }
    }
    // Rebuilding every list from scratch reproduces every identity.
    for ((label, rebuilt), (_, original)) in distinct_lists().into_iter().zip(&lists) {
        let rebuilt = ChcDtConstructors::new(rebuilt);
        assert!(ChcDtConstructors::ptr_eq(&rebuilt, original), "{label}");
        assert_eq!(rebuilt.id(), original.id(), "{label}");
    }
}

#[test]
fn datatype_sort_equality_is_name_and_definition() {
    let list = vec![constructor("c", vec![selector("s", ChcSort::Int)])];
    let a = datatype("A", list.clone());
    let b = datatype("B", list.clone());
    assert!(ChcDtConstructors::ptr_eq(
        constructors_of(&a),
        constructors_of(&b)
    ));
    assert_ne!(a, b);
    assert_ne!(a, ChcSort::Uninterpreted("A".into()));
    assert_ne!(a, datatype("A", vec![constructor("c", vec![])]));
    assert_eq!(a, datatype("A", list));
}

#[test]
fn identity_encoding_is_pinned() {
    // The id is part of the v2 normalized CHC identity. A change to the
    // encoding must bump `DATATYPE_IDENTITY_DOMAIN` and the normalized-input
    // schema together; this golden value catches an unversioned change.
    let sort = datatype(
        "Pair",
        vec![
            constructor("nil", vec![]),
            constructor(
                "mk",
                vec![
                    selector("fst", ChcSort::BitVec(32)),
                    selector(
                        "snd",
                        ChcSort::Array(
                            Box::new(ChcSort::Int),
                            Box::new(datatype("Leaf", vec![constructor("leaf", vec![])])),
                        ),
                    ),
                    selector("opaque", ChcSort::Uninterpreted("U".into())),
                ],
            ),
        ],
    );
    assert_eq!(constructors_of(&sort).id().to_string(), GOLDEN_PAIR_ID);
}

/// Recomputed independently of this crate from the documented encoding:
/// SHA-256 over the domain, then `u64` little-endian counts and lengths,
/// one tag byte per sort (`BitVec` 3 + `u32` width, `Array` 4, `Int` 1,
/// `Datatype` 6 + name + child id, `Uninterpreted` 5 + name).
const GOLDEN_PAIR_ID: &str = "a58391ba5597a9ad15936778f255beb71398d0552cfda45f376b64d6848bbbba";

#[test]
fn hash_eq_and_debug_cost_do_not_grow_with_nesting() {
    // At k = 64 the tree expansion has 2^64 leaves: anything that walked it
    // would not return. Hash work is the name plus a fixed-size id.
    let mut works = Vec::new();
    for k in 1..=64 {
        let sort = struct_dag(k);
        let var = ChcVar::new("x", sort.clone());
        let work = hash_work(&var);
        assert!(work <= 96, "k={k}: ChcVar hash fed {work} bytes");
        works.push(work);
        assert_eq!(var, ChcVar::new("x", struct_dag(k)));
        let debug = format!("{sort:?}");
        assert!(debug.len() <= 160, "k={k}: Debug is {} bytes", debug.len());
    }
    // Only the decimal digits of `Dk` vary.
    assert_eq!(works[9], works[63]);
}

#[test]
fn dead_lists_leave_the_intern_table() {
    let list = || {
        vec![constructor(
            "dead_lists_leave_the_intern_table",
            vec![selector("only-here", ChcSort::Int)],
        )]
    };
    let id = {
        let live = ChcDtConstructors::new(list());
        let again = ChcDtConstructors::new(list());
        assert!(ChcDtConstructors::ptr_eq(&live, &again));
        assert_eq!(table_entries_for(live.id()), 1);
        live.id()
    };
    assert_eq!(table_entries_for(id), 0);
    // A nested list dies with its last parent.
    let child_id = {
        let parent = datatype(
            "Parent",
            vec![constructor(
                "p",
                vec![selector("child", datatype("Child", list()))],
            )],
        );
        constructors_of(&constructors_of(&parent)[0].selectors[0].sort).id()
    };
    assert_eq!(child_id, id);
    assert_eq!(table_entries_for(child_id), 0);
}

/// [`struct_dag`] over any leaf sort.
fn struct_dag_over(leaf: ChcSort, k: usize) -> ChcSort {
    let mut sort = leaf;
    for level in 1..=k {
        sort = datatype(
            &format!("D{level}"),
            vec![constructor(
                &format!("mk{level}"),
                vec![
                    selector(&format!("a{level}"), sort.clone()),
                    selector(&format!("b{level}"), sort),
                ],
            )],
        );
    }
    sort
}

#[test]
fn content_summary_reaches_through_nesting_without_a_walk() {
    // k = 64: 2^64 paths, so a walk that found nothing would not return.
    let array_of = |value: ChcSort| ChcSort::Array(Box::new(ChcSort::Int), Box::new(value));
    for (leaf, bitvec, uninterpreted) in [
        (ChcSort::Int, false, false),
        (ChcSort::BitVec(8), true, false),
        (ChcSort::Uninterpreted("U".into()), false, true),
        (array_of(ChcSort::BitVec(1)), true, false),
        (array_of(ChcSort::Uninterpreted("U".into())), false, true),
    ] {
        let top = struct_dag_over(leaf.clone(), 64);
        let list = constructors_of(&top);
        assert_eq!(list.contains_bitvec(), bitvec, "{leaf:?}");
        assert_eq!(list.mentions_uninterpreted(), uninterpreted, "{leaf:?}");
    }
    let nullary = datatype("Unit", vec![constructor("unit", vec![])]);
    assert!(!constructors_of(&nullary).contains_bitvec());
    assert!(!constructors_of(&nullary).mentions_uninterpreted());
}
