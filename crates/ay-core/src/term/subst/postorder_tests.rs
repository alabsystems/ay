// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Controls for the core postorder walk, not the complete deep consumer route.

use super::*;

mod deep;
mod oracle;

fn raw(store: &mut TermStore, name: &str, args: Vec<TermId>, sort: Sort) -> TermId {
    store.intern(TermData::App(Symbol::named(name), args), sort)
}

fn assert_same_store(actual: &TermStore, expected: &TermStore) {
    assert_eq!(actual.entries_snapshot(), expected.entries_snapshot());
    for index in 0..actual.len() {
        let term = TermId(u32::try_from(index).unwrap());
        assert_eq!(actual.is_no_mbqi(term), expected.is_no_mbqi(term));
        assert_eq!(actual.quantifier_id(term), expected.quantifier_id(term));
        assert_eq!(actual.skolem_id(term), expected.skolem_id(term));
        assert_eq!(
            actual.explicit_quantifier_weight(term),
            expected.explicit_quantifier_weight(term)
        );
        assert_eq!(
            actual.quantifier_no_patterns(term),
            expected.quantifier_no_patterns(term)
        );
    }
}

fn parity(store: &TermStore, root: TermId, from: &[TermId], to: &[TermId]) {
    let mut actual = store.clone();
    let mut expected = store.clone();
    assert_eq!(actual.simplify(root), oracle::simplify(&mut expected, root));
    assert_same_store(&actual, &expected);
    let mut actual = store.clone();
    let mut expected = store.clone();
    assert_eq!(
        actual.substitute(root, from, to),
        oracle::substitute(&mut expected, root, from, to)
    );
    assert_same_store(&actual, &expected);
}

fn quantified_roots(store: &mut TermStore, body: TermId, pattern: TermId) -> Vec<TermId> {
    let vars = vec![("bound".to_owned(), Sort::Int)];
    let triggers = vec![vec![pattern, TermId::SENTINEL]];
    let forall = store.mk_forall_with_triggers(vars.clone(), body, triggers.clone());
    let exists = store.mk_exists_with_triggers(vars, body, triggers);
    for quantifier in [forall, exists] {
        store.set_quantifier_id(quantifier, "postorder-qid".to_owned());
        store.set_skolem_id(quantifier, "postorder-skid".to_owned());
        store.set_quantifier_weight(quantifier, 17);
        store.set_quantifier_no_patterns(quantifier, vec![pattern, TermId::SENTINEL]);
    }
    store.mark_no_mbqi(forall);
    vec![forall, exists]
}

fn shallow_fixture(store: &mut TermStore) -> (Vec<TermId>, Vec<TermId>, Vec<TermId>) {
    let x = store.mk_var("x", Sort::Int);
    let y = store.mk_var("y", Sort::Int);
    let p = store.mk_var("p", Sort::Bool);
    let q = store.mk_var("q", Sort::Bool);
    let zero = store.mk_int(0.into());
    let one = store.mk_int(1.into());
    let two = store.mk_int(2.into());
    let three = store.mk_int(3.into());
    let t = store.mk_bool(true);
    let f = store.mk_bool(false);
    let sum = raw(store, "+", vec![two, three], Sort::Int);
    let left = raw(store, "+", vec![x, sum, zero], Sort::Int);
    let right = raw(store, "*", vec![y, one], Sort::Int);
    let disjunction = raw(store, "or", vec![f, q], Sort::Bool);
    let body = raw(store, "and", vec![t, p, disjunction], Sort::Bool);
    let not = store.intern(TermData::Not(body), Sort::Bool);
    let ite = store.intern(TermData::Ite(body, left, right), Sort::Int);
    let binding = store.mk_let(
        vec![("first".to_owned(), left), ("second".to_owned(), right)],
        ite,
    );
    // A shared child appears both before and after a parent that references it.
    // Whole ordered snapshots expose any changed DFS constructor order.
    let shared = raw(store, "opaque", vec![left, right], Sort::Int);
    let outer = raw(
        store,
        "opaque",
        vec![shared, left, shared, binding],
        Sort::Int,
    );
    let mut roots = vec![x, two, sum, left, right, body, not, ite, binding, outer];
    roots.extend(quantified_roots(store, body, left));
    let a = store.mk_bitvec(1.into(), 8);
    let b = store.mk_bitvec(2.into(), 8);
    roots.push(raw(store, "bvadd", vec![a, b], Sort::bitvec(8)));
    let array = store.mk_var("array", Sort::array(Sort::Int, Sort::Int));
    let array_sort = store.sort(array).clone();
    let written = raw(store, "store", vec![array, x, sum], array_sort);
    roots.push(written);
    roots.push(raw(store, "select", vec![written, x], Sort::Int));
    (roots, vec![x, y, p, q, a], vec![two, three, t, f, b])
}

#[test]
fn shallow_postorder_matches_recursive_ids_interner_order_and_metadata() {
    let mut store = TermStore::new();
    let (roots, from, to) = shallow_fixture(&mut store);
    for root in roots {
        parity(&store, root, &from, &to);
        parity(&store, root, &[], &to);
        parity(&store, root, &from, &[]);
    }
}

#[test]
fn simultaneous_swaps_duplicate_matches_and_self_containing_replacements_match_oracle() {
    let mut store = TermStore::new();
    let x = store.mk_var("x", Sort::Int);
    let y = store.mk_var("y", Sort::Int);
    let z = store.mk_var("z", Sort::Int);
    let one = store.mk_int(1.into());
    let self_containing = raw(&mut store, "+", vec![x, one], Sort::Int);
    let root = raw(
        &mut store,
        "opaque",
        vec![x, y, x, self_containing],
        Sort::Int,
    );
    for (from, to) in [
        (vec![x, y], vec![y, x]),
        (vec![x, x], vec![y, z]),
        (vec![x, y], vec![y]),
        (vec![x], vec![y, z]),
        (vec![x], vec![self_containing]),
        (vec![x], vec![x]),
    ] {
        parity(&store, root, &from, &to);
    }
    assert_eq!(
        store.substitute(x, &[x], &[self_containing]),
        self_containing
    );
    assert_eq!(store.substitute(x, &[x, x], &[y, z]), y);
    let mut cache = crate::kani_compat::det_hash_map_new();
    cache.insert(x, one);
    assert_eq!(store.substitute_inner(x, &[x], &[y], &mut cache), y);
}

#[test]
fn quantifier_triggers_and_no_patterns_remain_unvisited_and_metadata_is_copied() {
    let mut store = TermStore::new();
    let p = store.mk_var("p", Sort::Bool);
    let q = store.mk_var("q", Sort::Bool);
    let t = store.mk_bool(true);
    let body = raw(&mut store, "and", vec![t, p], Sort::Bool);
    for root in quantified_roots(&mut store, body, p) {
        parity(&store, root, &[p], &[q]);
        let simplified = store.simplify(root);
        let rewritten = store.substitute(root, &[p], &[q]);
        for result in [simplified, rewritten] {
            let triggers = match store.get(result) {
                TermData::Forall(_, _, triggers) | TermData::Exists(_, _, triggers) => triggers,
                _ => unreachable!("the old worker preserves quantifier nodes"),
            };
            assert_eq!(triggers, &vec![vec![p, TermId::SENTINEL]]);
            assert_eq!(store.quantifier_no_patterns(result), &[p, TermId::SENTINEL]);
            assert_eq!(store.quantifier_id(result), Some("postorder-qid"));
            assert_eq!(store.skolem_id(result), Some("postorder-skid"));
            assert_eq!(store.explicit_quantifier_weight(result), Some(17));
            assert_eq!(store.is_no_mbqi(result), store.is_no_mbqi(root));
        }
    }
}

#[test]
fn malformed_application_arities_keep_the_old_sort_preserving_fallback() {
    let mut store = TermStore::new();
    let x = store.mk_var("x", Sort::Int);
    let y = store.mk_var("y", Sort::Int);
    for (name, expected_arity, sort) in [
        ("store", 3, Sort::array(Sort::Int, Sort::Int)),
        ("select", 2, Sort::Int),
        ("div", 2, Sort::Int),
        ("=", 2, Sort::Bool),
        ("bvnot", 1, Sort::bitvec(8)),
    ] {
        for arity in 0..5 {
            if arity != expected_arity {
                let root = raw(&mut store, name, vec![x; arity], sort.clone());
                parity(&store, root, &[x], &[y]);
                let rewritten = store.substitute(root, &[x], &[y]);
                assert_eq!(store.sort(rewritten), &sort);
            }
        }
    }
}

#[test]
fn invalid_term_ids_preserve_direct_hit_and_unmatched_refusal_behavior() {
    let mut store = TermStore::new();
    let x = store.mk_var("x", Sort::Int);
    assert_eq!(
        store.substitute(TermId::SENTINEL, &[], &[x]),
        TermId::SENTINEL
    );
    assert_eq!(
        store.substitute(TermId::SENTINEL, &[TermId::SENTINEL], &[x]),
        x
    );
    assert_eq!(
        store.substitute(x, &[x], &[TermId::SENTINEL]),
        TermId::SENTINEL
    );
    let invalid_child = raw(&mut store, "opaque", vec![TermId::SENTINEL], Sort::Int);
    let mut expected = store.clone();
    assert_eq!(
        store.substitute(invalid_child, &[TermId::SENTINEL], &[x]),
        oracle::substitute(&mut expected, invalid_child, &[TermId::SENTINEL], &[x])
    );
    assert_same_store(&store, &expected);
    for substitute in [false, true] {
        let mut actual = store.clone();
        let mut expected = store.clone();
        let actual = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            if substitute {
                actual.substitute(TermId::SENTINEL, &[x], &[x])
            } else {
                actual.simplify(TermId::SENTINEL)
            }
        }));
        let expected = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            if substitute {
                oracle::substitute(&mut expected, TermId::SENTINEL, &[x], &[x])
            } else {
                oracle::simplify(&mut expected, TermId::SENTINEL)
            }
        }));
        assert!(actual.is_err());
        assert!(expected.is_err());
    }
}
