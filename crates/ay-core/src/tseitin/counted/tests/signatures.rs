// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
#![cfg(test)]
use super::*;

#[test]
fn bool_array_reads_and_bv_comparisons_remain_unresolved_atoms() {
    let source = ample();
    let mut terms = TermStore::new();
    let mut builder = CountedTermBuilder::new(&mut terms, &source).unwrap();
    let array = builder
        .variable("array", &Sort::array(Sort::bitvec(8), Sort::Bool))
        .unwrap();
    let i = builder.variable("i", &Sort::bitvec(8)).unwrap();
    let j = builder.variable("j", &Sort::bitvec(8)).unwrap();
    let read = builder.apply(CountedBuiltin::Select, &[array, i]).unwrap();
    let less = builder.apply(CountedBuiltin::BvULt, &[i, j]).unwrap();
    let root = builder.apply(CountedBuiltin::Iff, &[read, less]).unwrap();
    builder.finish().unwrap();
    let cnf = CountedCnf::encode(&mut terms, &[root], &ample()).unwrap();
    assert_eq!(cnf.data.theory_atoms, [read, less]);
    assert_eq!(cnf.data.num_vars, 3);
}

#[test]
fn non_boolean_distinct_bridges_retain_typed_equality_obligation() {
    for sort in [Sort::bitvec(8), Sort::array(Sort::bitvec(2), Sort::Bool)] {
        let source = ample();
        let mut terms = TermStore::new();
        let mut builder = CountedTermBuilder::new(&mut terms, &source).unwrap();
        let a = builder.variable("a", &sort).unwrap();
        let b = builder.variable("b", &sort).unwrap();
        let root = builder.apply(CountedBuiltin::Distinct, &[a, b]).unwrap();
        builder.finish().unwrap();
        let cnf = CountedCnf::encode(&mut terms, &[root], &ample()).unwrap();
        assert_eq!(cnf.data.theory_atoms, [cnf.data.bridges[0].equality]);
        assert_eq!(cnf.data.steps.len(), 5);
    }
}

#[test]
fn all_dead_arms_are_typed_before_constant_or_root_publication() {
    let mut terms = TermStore::new();
    let yes = terms.mk_bool(true);
    let bits = terms.mk_var("bits", Sort::bitvec(8));
    let bad = terms.mk_app(Symbol::named("=>"), [yes, bits], Sort::Bool);
    let root = terms.mk_app(Symbol::named("or"), [yes, bad], Sort::Bool);
    assert!(matches!(
        CountedCnf::encode(&mut terms, &[root], &ample()),
        Err(Error::Invalid)
    ));
    // Well-typed ITE shell, malformed expression in its unreachable arm;
    // the native raw ITE constructor itself rejects mismatched branch sorts.
    let dead = terms.mk_ite_raw(yes, yes, bad);
    assert!(CountedCnf::encode(&mut terms, &[dead], &ample()).is_err());
}

#[test]
fn indexed_lookalikes_unknown_functions_and_invalid_roots_never_become_gates() {
    for symbol in [
        Symbol::indexed("=>", vec![]),
        Symbol::indexed("=", vec![0]),
        Symbol::named("user_predicate"),
    ] {
        let mut terms = TermStore::new();
        let a = terms.mk_var("a", Sort::Bool);
        let b = terms.mk_var("b", Sort::Bool);
        let root = terms.mk_app(symbol, [a, b], Sort::Bool);
        assert!(matches!(
            CountedCnf::encode(&mut terms, &[root], &ample()),
            Err(Error::Unsupported)
        ));
    }
    let mut terms = TermStore::new();
    let bits = terms.mk_var("bits", Sort::bitvec(8));
    assert!(matches!(
        CountedCnf::encode(&mut terms, &[bits], &ample()),
        Err(Error::Invalid)
    ));
    assert!(matches!(
        CountedCnf::encode(&mut terms, &[TermId(u32::MAX)], &ample()),
        Err(Error::Invalid)
    ));
}

#[test]
fn malformed_arity_width_and_array_signature_are_not_opaque_atoms() {
    for case in 0..4 {
        let mut terms = TermStore::new();
        let a = terms.mk_var("a", Sort::bitvec(8));
        let b = terms.mk_var("b", Sort::bitvec(9));
        let yes = terms.mk_bool(true);
        let root = match case {
            0 => terms.mk_app(Symbol::named("="), [a, b], Sort::Bool),
            1 => terms.mk_app(Symbol::named("distinct"), [yes, yes, yes], Sort::Bool),
            2 => terms.mk_app(Symbol::named("select"), [a, b], Sort::Bool),
            _ => terms.mk_app(Symbol::named("bvult"), [a, b], Sort::Bool),
        };
        assert!(CountedCnf::encode(&mut terms, &[root], &ample()).is_err());
    }
}

#[test]
fn source_name_collisions_keep_distinct_typed_terms() {
    let source = ample();
    let mut terms = TermStore::new();
    let mut builder = CountedTermBuilder::new(&mut terms, &source).unwrap();
    let boolean = builder.variable("same", &Sort::Bool).unwrap();
    let bits = builder.variable("same", &Sort::bitvec(8)).unwrap();
    let eq = builder.apply(CountedBuiltin::Eq, &[bits, bits]).unwrap();
    let root = builder.apply(CountedBuiltin::And, &[boolean, eq]).unwrap();
    builder.finish().unwrap();
    let cnf = CountedCnf::encode(&mut terms, &[root], &ample()).unwrap();
    assert!(cnf.data.term_literals[boolean.index()].is_some());
    assert!(cnf.data.term_literals[bits.index()].is_none());
    assert_eq!(cnf.data.theory_atoms, [eq]);
}
