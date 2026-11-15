// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

fn evaluate(terms: &TermStore, term: TermId, vars: &[TermId; 3], values: [u8; 3]) -> u8 {
    if let Some(index) = vars.iter().position(|id| *id == term) {
        return values[index];
    }
    let TermData::App(op, args) = terms.get(term) else {
        panic!("unexpected fixture term")
    };
    match op.name() {
        "bvadd" => args
            .iter()
            .fold(0, |a, b| (a + evaluate(terms, *b, vars, values)) & 3),
        "bvmul" => args
            .iter()
            .fold(1, |a, b| (a * evaluate(terms, *b, vars, values)) & 3),
        "bvand" => args
            .iter()
            .fold(3, |a, b| a & evaluate(terms, *b, vars, values)),
        "bvor" => args
            .iter()
            .fold(0, |a, b| a | evaluate(terms, *b, vars, values)),
        _ => panic!("unexpected fixture operator"),
    }
}

fn circuit_nodes(terms: &TermStore, roots: &[TermId]) -> usize {
    let mut pending = roots.to_vec();
    let mut seen = HashSet::default();
    let mut count = 0;
    while let Some(term) = pending.pop() {
        if seen.insert(term) {
            count += usize::from(operation(terms, term).is_some());
            pending.extend(terms.children(term));
        }
    }
    count
}

#[test]
fn bv_sharing_exposes_common_circuits_and_preserves_every_two_bit_assignment() {
    for name in ["bvadd", "bvmul", "bvand", "bvor"] {
        let mut terms = TermStore::new();
        let vars = ["x", "y", "z"].map(|name| terms.mk_var(name, Sort::bitvec(2)));
        let xy = terms.mk_app(Symbol::named(name), [vars[0], vars[1]], Sort::bitvec(2));
        let yz = terms.mk_app(Symbol::named(name), [vars[1], vars[2]], Sort::bitvec(2));
        let xyz = terms.mk_app(Symbol::named(name), [vars[0], yz], Sort::bitvec(2));
        let before = [xy, xyz];
        let mut after = before;
        assert_eq!(circuit_nodes(&terms, &before), 3);
        assert!(terms.maximize_bv_sharing(&mut after));
        assert_eq!(circuit_nodes(&terms, &after), 2);
        for x in 0..4 {
            for y in 0..4 {
                for z in 0..4 {
                    for (old, new) in before.into_iter().zip(after) {
                        assert_eq!(
                            evaluate(&terms, old, &vars, [x, y, z]),
                            evaluate(&terms, new, &vars, [x, y, z])
                        );
                    }
                }
            }
        }
        assert!(!terms.maximize_bv_sharing(&mut after));
    }
}

#[test]
fn bv_sharing_does_not_reassociate_user_owned_names_or_mixed_widths() {
    let mut terms = TermStore::new();
    terms.register_declared_function("bvadd");
    let a = terms.mk_var("a", Sort::bitvec(2));
    let b = terms.mk_var("b", Sort::bitvec(2));
    let ab = terms.mk_app(Symbol::named("bvadd"), [a, b], Sort::bitvec(2));
    let nested = terms.mk_app(Symbol::named("bvadd"), [a, ab], Sort::bitvec(2));
    let mut roots = [nested];
    assert!(!terms.maximize_bv_sharing(&mut roots));
    assert_eq!(roots, [nested]);

    let wide = terms.mk_var("wide", Sort::bitvec(4));
    let malformed = terms.mk_app(Symbol::named("bvmul"), [a, wide], Sort::bitvec(2));
    assert!(!terms.maximize_bv_sharing(&mut [malformed]));
}

#[test]
fn bv_sharing_keeps_shared_prefixes_atomic_on_a_deep_dag() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::bitvec(8));
    let mut prefix = x;
    let mut roots = Vec::new();
    for _ in 0..4096 {
        prefix = terms.mk_app(Symbol::named("bvadd"), [prefix, x], Sort::bitvec(8));
        roots.push(prefix);
    }
    let original = roots.clone();
    assert!(!terms.maximize_bv_sharing(&mut roots));
    assert_eq!(roots, original);
}
