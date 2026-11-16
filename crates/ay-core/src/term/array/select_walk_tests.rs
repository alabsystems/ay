// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The concrete store-tail walk is iterative. These tests do not claim that
//! array-map expansion, lambda substitution, or store construction is so.

use super::*;

#[derive(Clone, Copy)]
enum Indices {
    Int,
    Bv64,
}

impl Indices {
    fn sort(self) -> Sort {
        match self {
            Self::Int => Sort::Int,
            Self::Bv64 => Sort::bitvec(64),
        }
    }

    fn value_sort(self) -> Sort {
        match self {
            Self::Int => Sort::Int,
            Self::Bv64 => Sort::bitvec(32),
        }
    }

    fn index(self, store: &mut TermStore, value: u32) -> TermId {
        match self {
            Self::Int => store.mk_int(BigInt::from(value)),
            Self::Bv64 => store.mk_bitvec(BigInt::from(value), 64),
        }
    }

    fn value(self, store: &mut TermStore, value: u32) -> TermId {
        match self {
            Self::Int => store.mk_int(BigInt::from(value)),
            Self::Bv64 => store.mk_bitvec(BigInt::from(value), 32),
        }
    }
}

fn raw_store(store: &mut TermStore, array: TermId, index: TermId, value: TermId) -> TermId {
    let sort = store.sort(array).clone();
    store.intern(
        TermData::App(Symbol::named("store"), vec![array, index, value]),
        sort,
    )
}

fn prefix(store: &mut TermStore, kind: Indices, mut array: TermId) -> TermId {
    let value = store.mk_var(
        "prefix_value",
        store.sort(array).array_element().unwrap().clone(),
    );
    for number in 10..34 {
        let index = kind.index(store, number);
        array = raw_store(store, array, index, value);
    }
    array
}

// Frozen pre-loop algorithm, used ONLY with shallow inputs. It keeps every
// original rewrite's order, including per-recursion sort checks and fallbacks.
fn recursive_reference(store: &mut TermStore, array: TermId, index: TermId) -> TermId {
    let elem_sort = match store.sort(array).array_element() {
        Some(elem_sort) => {
            debug_assert_eq!(store.sort(array).array_index(), Some(store.sort(index)));
            elem_sort.clone()
        }
        None => {
            return store.intern(
                TermData::App(Symbol::named("select"), vec![array, index]),
                Sort::Bool,
            );
        }
    };
    if let Some(value) = store.get_const_array(array) {
        return value;
    }
    if let Some((var, body)) = store.get_lambda_array(array) {
        return store.substitute_var(body, var, index);
    }
    if let Some(name) = store.get_as_array_func(array) {
        let name = name.to_string();
        return store.intern(TermData::App(Symbol::named(&name), vec![index]), elem_sort);
    }
    if let Some((name, args)) = store.get_array_map(array) {
        let name = name.to_string();
        let args = args.to_vec();
        let selects = args
            .iter()
            .map(|&array| recursive_reference(store, array, index))
            .collect();
        return store.intern(TermData::App(Symbol::named(&name), selects), elem_sort);
    }
    if let TermData::App(Symbol::Named(name), args) = store.get(array) {
        if name == "store" {
            if let &[inner, key, value] = args.as_slice() {
                if key == index {
                    return value;
                }
                if let (Some(a), Some(b)) = (store.get_int(index), store.get_int(key)) {
                    if a != b {
                        return recursive_reference(store, inner, index);
                    }
                }
                if let (Some((a, _)), Some((b, _))) =
                    (store.get_bitvec(index), store.get_bitvec(key))
                {
                    if a != b {
                        return recursive_reference(store, inner, index);
                    }
                }
            }
        }
    }
    store.intern(
        TermData::App(Symbol::named("select"), vec![array, index]),
        elem_sort,
    )
}

fn check_reference(store: &TermStore, array: TermId, index: TermId) -> TermId {
    let mut actual = store.clone();
    let mut expected = store.clone();
    let result = actual.mk_select(array, index);
    assert_eq!(result, recursive_reference(&mut expected, array, index));
    assert_eq!(actual.entries_snapshot(), expected.entries_snapshot());
    result
}

#[test]
fn long_raw_int_and_bv_store_tails_fit_a_two_mib_stack() {
    std::thread::Builder::new()
        .name("select-store-tail-2mib".into())
        .stack_size(2 * 1024 * 1024)
        .spawn(|| {
            for kind in [Indices::Int, Indices::Bv64] {
                let mut store = TermStore::new();
                let base = store.mk_var("a", Sort::array(kind.sort(), kind.value_sort()));
                let mut array = base;
                // Raw interned applications guarantee that construction has
                // not squashed or reordered the chain this test must traverse.
                let count = 16_384 + 37;
                for number in 0..count {
                    let index = kind.index(&mut store, number);
                    let value = kind.value(&mut store, number);
                    array = raw_store(&mut store, array, index, value);
                }
                let index = kind.index(&mut store, 5);
                let expected = kind.value(&mut store, 5);
                assert_eq!(store.mk_select(array, index), expected);
                let missing = kind.index(&mut store, count + 5);
                let expected = store.mk_select(base, missing);
                assert_eq!(store.mk_select(array, missing), expected);
                // Do not leak or return the store to a larger-stack thread.
                drop(store);
            }
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn shallow_concrete_walks_match_the_frozen_recursive_reference() {
    for kind in [Indices::Int, Indices::Bv64] {
        let mut store = TermStore::new();
        let base = store.mk_var("a", Sort::array(kind.sort(), kind.value_sort()));
        for count in 0..=12 {
            let mut array = base;
            for number in 0..count {
                let key = kind.index(&mut store, number % 7);
                let value = kind.value(&mut store, number + 100);
                array = raw_store(&mut store, array, key, value);
            }
            for number in 0..=8 {
                let index = kind.index(&mut store, number);
                // check_reference asserts the match itself; the id is unused.
                let _ = check_reference(&store, array, index);
            }
        }
    }
}

#[test]
fn symbolic_barrier_and_nearest_shadowed_write_remain_observable() {
    for kind in [Indices::Int, Indices::Bv64] {
        let mut store = TermStore::new();
        let base = store.mk_var("a", Sort::array(kind.sort(), kind.value_sort()));
        let index = kind.index(&mut store, 5);
        let old = kind.value(&mut store, 100);
        let new = kind.value(&mut store, 200);
        let first = raw_store(&mut store, base, index, old);
        let shadow = raw_store(&mut store, first, index, new);
        let outer = prefix(&mut store, kind, shadow);
        assert_eq!(check_reference(&store, outer, index), new);
        let symbolic = store.mk_var("symbolic", kind.sort());
        let barrier = raw_store(&mut store, shadow, symbolic, old);
        let outer = prefix(&mut store, kind, barrier);
        let expected = store.intern(
            TermData::App(Symbol::named("select"), vec![barrier, index]),
            kind.value_sort(),
        );
        assert_eq!(check_reference(&store, outer, index), expected);
        assert_eq!(check_reference(&store, barrier, symbolic), old);
        let unknown = store.intern(
            TermData::App(Symbol::named("select"), vec![outer, symbolic]),
            kind.value_sort(),
        );
        assert_eq!(check_reference(&store, outer, symbolic), unknown);
    }
}

#[test]
fn constant_and_lambda_terminals_are_rewritten_after_a_concrete_prefix() {
    for kind in [Indices::Int, Indices::Bv64] {
        let mut store = TermStore::new();
        let index = kind.index(&mut store, 5);
        let default = kind.value(&mut store, 99);
        let constant = store.mk_const_array(kind.sort(), default);
        let array = prefix(&mut store, kind, constant);
        assert_eq!(check_reference(&store, array, index), default);
        let var = store.mk_var("bound", kind.sort());
        let lambda = store.mk_lambda_array(var, var);
        let array = prefix(&mut store, kind, lambda);
        assert_eq!(check_reference(&store, array, index), index);
    }
}

#[test]
fn as_array_and_map_terminals_keep_their_rewrite_order() {
    for kind in [Indices::Int, Indices::Bv64] {
        let mut store = TermStore::new();
        let sort = Sort::array(kind.sort(), kind.value_sort());
        let index = kind.index(&mut store, 5);
        let as_array = store.mk_as_array("f", sort.clone());
        let array = prefix(&mut store, kind, as_array);
        let expected = store.intern(
            TermData::App(Symbol::named("f"), vec![index]),
            kind.value_sort(),
        );
        assert_eq!(check_reference(&store, array, index), expected);
        let a = kind.value(&mut store, 123);
        let b = kind.value(&mut store, 456);
        let left = store.mk_const_array(kind.sort(), a);
        let right = store.mk_const_array(kind.sort(), b);
        let left = prefix(&mut store, kind, left);
        let right = prefix(&mut store, kind, right);
        let map = store.mk_array_map("combine", vec![left, right], sort);
        let array = prefix(&mut store, kind, map);
        let expected = store.intern(
            TermData::App(Symbol::named("combine"), vec![a, b]),
            kind.value_sort(),
        );
        assert_eq!(check_reference(&store, array, index), expected);
    }
}

#[test]
fn malformed_store_arities_are_not_walked_through() {
    let mut store = TermStore::new();
    let sort = Sort::array(Sort::Int, Sort::Int);
    let base = store.mk_var("a", sort.clone());
    let index = store.mk_int(5.into());
    let key = store.mk_int(1.into());
    let value = store.mk_int(2.into());
    for args in [
        vec![],
        vec![base],
        vec![base, key],
        vec![base, key, value, value],
    ] {
        let malformed = store.intern(TermData::App(Symbol::named("store"), args), sort.clone());
        let array = prefix(&mut store, Indices::Int, malformed);
        let expected = store.intern(
            TermData::App(Symbol::named("select"), vec![malformed, index]),
            Sort::Int,
        );
        assert_eq!(check_reference(&store, array, index), expected);
    }
}

#[test]
fn inner_non_array_and_changed_element_sorts_keep_the_original_fallback() {
    let mut store = TermStore::new();
    let outer_sort = Sort::array(Sort::Int, Sort::Int);
    let index = store.mk_int(5.into());
    let key = store.mk_int(1.into());
    let value = store.mk_int(2.into());
    let non_array = store.mk_var("not_array", Sort::Bool);
    let different = store.mk_var("different_element", Sort::array(Sort::Int, Sort::Bool));
    for base in [non_array, different] {
        let array = store.intern(
            TermData::App(Symbol::named("store"), vec![base, key, value]),
            outer_sort.clone(),
        );
        let expected = store.intern(
            TermData::App(Symbol::named("select"), vec![base, index]),
            Sort::Bool,
        );
        assert_eq!(check_reference(&store, array, index), expected);
    }
    // Existing raw-term semantics return a matching write before inspecting
    // the inner array or stored value sort. This patch does not strengthen it.
    let array = store.intern(
        TermData::App(Symbol::named("store"), vec![non_array, index, non_array]),
        outer_sort,
    );
    assert_eq!(check_reference(&store, array, index), non_array);
}

#[test]
fn inner_index_sort_is_rechecked_instead_of_inherited_from_the_outer_store() {
    let mut store = TermStore::new();
    let base = store.mk_var("inner", Sort::array(Sort::bitvec(64), Sort::Int));
    let index = store.mk_int(5.into());
    let key = store.mk_int(1.into());
    let value = store.mk_int(2.into());
    let array = store.intern(
        TermData::App(Symbol::named("store"), vec![base, key, value]),
        Sort::array(Sort::Int, Sort::Int),
    );
    let mut reference = store.clone();
    let actual = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        store.mk_select(array, index)
    }));
    let expected = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        recursive_reference(&mut reference, array, index)
    }));
    if cfg!(debug_assertions) {
        assert!(actual.is_err());
        assert!(expected.is_err());
    } else {
        assert_eq!(actual.unwrap(), expected.unwrap());
        assert_eq!(store.entries_snapshot(), reference.entries_snapshot());
    }
}
