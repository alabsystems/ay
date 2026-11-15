// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_core::TermStore;

fn app(terms: &mut TermStore, op: &str, args: &[TermId], sort: Sort) -> TermId {
    terms.mk_app(Symbol::named(op), args, sort)
}

#[test]
fn packed_sparse_reads_export_checked_address_guards_and_last_write() {
    for width in [9, 64, 128] {
        let mut terms = TermStore::new();
        let base = terms.mk_var("base", Sort::bitvec(width));
        let x = terms.mk_var("x", Sort::bitvec(8));
        let y = terms.mk_var("y", Sort::bitvec(8));
        let sort = Sort::array(Sort::bitvec(width), Sort::bitvec(8));
        let mut array = app(&mut terms, "const-array", &[y], sort.clone());
        array = app(&mut terms, "store", &[array, base, y], sort.clone());
        array = app(&mut terms, "store", &[array, base, x], sort.clone());
        for offset in [1, 3] {
            let offset = terms.mk_bitvec(offset.into(), width);
            let index = app(&mut terms, "bvadd", &[offset, base], Sort::bitvec(width));
            array = app(&mut terms, "store", &[array, index, y], sort.clone());
        }
        let read = app(&mut terms, "select", &[array, base], Sort::bitvec(8));
        let equality = app(&mut terms, "=", &[read, x], Sort::Bool);
        addition_tests::certificate(&format!("sparse-{width}"), &terms, equality,
            &format!("(declare-const base (_ BitVec {width}))\n(declare-const x (_ BitVec 8))\n(declare-const y (_ BitVec 8))"));
        let wrong = app(&mut terms, "=", &[read, y], Sort::Bool);
        assert!(AlethePrinter::new(&terms)
            .format_bv_packed_identity(ProofId(7), &[wrong])
            .is_none());
    }
}

#[test]
fn packed_sparse_reads_refuse_open_arrays_defaults_and_discarded_bad_values() {
    let mut terms = TermStore::new();
    let base = terms.mk_var("base", Sort::bitvec(64));
    let value = terms.mk_var("x", Sort::bitvec(8));
    let bad = terms.mk_var("bad", Sort::Bool);
    let sort = Sort::array(Sort::bitvec(64), Sort::bitvec(8));
    let open = terms.mk_var("open", sort.clone());
    let constant = app(&mut terms, "const-array", &[value], sort.clone());
    let malformed = app(&mut terms, "store", &[constant, base, bad], sort.clone());
    let malformed = app(&mut terms, "store", &[malformed, base, value], sort.clone());
    for array in [open, constant, malformed] {
        let read = app(&mut terms, "select", &[array, base], Sort::bitvec(8));
        let equality = app(&mut terms, "=", &[read, value], Sort::Bool);
        assert!(AlethePrinter::new(&terms)
            .format_bv_packed_identity(ProofId(7), &[equality])
            .is_none());
    }
    let mut array = constant;
    for _ in 0..33 {
        array = app(&mut terms, "store", &[array, base, value], sort.clone());
    }
    let read = app(&mut terms, "select", &[array, base], Sort::bitvec(8));
    let equality = app(&mut terms, "=", &[read, value], Sort::Bool);
    assert!(AlethePrinter::new(&terms)
        .format_bv_packed_identity(ProofId(7), &[equality])
        .is_none());
}
