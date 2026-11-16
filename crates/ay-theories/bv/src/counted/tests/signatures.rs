// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
#![cfg(test)]

use super::*;

#[test]
fn ill_typed_dead_arms_refuse_before_creating_any_gate() {
    let mut terms = TermStore::new();
    let yes = terms.mk_bool(true);
    let bits = terms.mk_var("bits", Sort::bitvec(8));
    let bad = terms.mk_app(Symbol::named("=>"), [yes, bits], Sort::Bool);
    let root = terms.mk_app(Symbol::named("or"), [yes, bad], Sort::Bool);
    let original = ample();
    let mut encoder = CountedBvEncoder::new(&terms, &original).unwrap();
    assert!(encoder.encode_terms(&[root]).is_err());
    assert_eq!(encoder.solver.next_var, 1);
    assert_eq!(encoder.solver.clauses.as_slice(), &[] as &[CnfClause]);
    assert!(original.check().is_err());
}

#[test]
fn arrays_ufs_and_indexed_builtin_lookalikes_refuse_instead_of_opaque_bits() {
    for kind in 0..3 {
        let mut terms = TermStore::new();
        let index = terms.mk_var("index", Sort::bitvec(8));
        let root = match kind {
            0 => {
                let array = terms.mk_var("array", Sort::array(Sort::bitvec(8), Sort::bitvec(8)));
                terms.mk_app(Symbol::named("select"), [array, index], Sort::bitvec(8))
            }
            1 => {
                terms.register_declared_function("bvadd");
                operation(&mut terms, "bvadd", index, index, 8)
            }
            _ => terms.mk_app(
                Symbol::indexed("bvadd", vec![]),
                [index, index],
                Sort::bitvec(8),
            ),
        };
        let original = ample();
        let mut encoder = CountedBvEncoder::new(&terms, &original).unwrap();
        assert!(encoder.encode_terms(&[root]).is_err());
        assert_eq!(encoder.solver.next_var, 1);
        assert!(encoder.clauses().is_err());
    }
}

#[test]
fn invalid_literal_imports_are_terminal_and_do_not_publish_partial_clauses() {
    for literal in [0, i32::MIN, 2] {
        let terms = TermStore::new();
        let original = ample();
        let mut encoder = CountedBvEncoder::new(&terms, &original).unwrap();
        let _ = encoder.fresh_bits(1).unwrap();
        assert_eq!(encoder.add_clause(&[literal]), Err(CountedBvError::Invalid));
        assert!(encoder.clauses().is_err());
        assert!(encoder.fresh_bits(1).is_err());
        assert!(original.check().is_err());
    }
}

#[test]
fn unknown_source_lookup_cannot_bypass_terminal_refusal() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::bitvec(8));
    let original = ample();
    let mut encoder = CountedBvEncoder::new(&terms, &original).unwrap();
    assert_eq!(encoder.bits(x), Err(CountedBvError::Invalid));
    assert!(encoder.encode_terms(&[x]).is_err());
}

#[test]
fn typed_variable_source_ids_remain_distinct_even_with_shared_spelling() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("shared", Sort::bitvec(8));
    let y = terms.mk_var("shared", Sort::Bool);
    let original = ample();
    let mut encoder = CountedBvEncoder::new(&terms, &original).unwrap();
    encoder.encode_terms(&[x, y]).unwrap();
    assert_eq!(encoder.bits(x).unwrap().len(), 8);
    let literal = encoder.literal(y).unwrap();
    assert!(!encoder.bits(x).unwrap().contains(&literal));
    encoder.finish().unwrap();
}

#[test]
fn malformed_snapshot_constants_and_forward_cycles_are_not_opaque_sources() {
    let constant = TermData::Const(Constant::BitVec {
        value: BigInt::from(1u32) << 4096,
        width: 8,
    });
    let malformed = TermStore::from_entries(vec![(constant, Sort::bitvec(8))], None, None, 0);
    let cyclic = TermStore::from_entries(
        vec![(TermData::Not(TermId::new(0)), Sort::Bool)],
        None,
        None,
        0,
    );
    for terms in [malformed, cyclic] {
        let original = ample();
        let mut encoder = CountedBvEncoder::new(&terms, &original).unwrap();
        assert!(encoder.encode_terms(&[TermId::new(0)]).is_err());
        assert_eq!(encoder.solver.next_var, 1);
        assert_eq!(encoder.solver.clauses.as_slice(), &[] as &[CnfClause]);
        assert!(original.check().is_err());
    }
}
