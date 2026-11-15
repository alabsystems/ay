// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::tests::{certificate, original, TestResult};
use super::*;

fn problem(width: usize, count: usize, expected: &str) -> String {
    let mut array = "memory".to_string();
    for offset in 0..count {
        let key = format!("(bvadd (bvsub base (_ bv32 {width})) (_ bv{offset} {width}))");
        let value = if offset == count / 2 {
            "saved"
        } else {
            "other"
        };
        array = format!("(store {array} {key} {value})");
    }
    let middle = count / 2;
    let key = format!("(bvsub (bvadd base (_ bv{middle} {width})) (_ bv32 {width}))");
    format!(
        "(set-logic QF_ABV)
        (declare-const base (_ BitVec {width}))
        (declare-const memory (Array (_ BitVec {width}) (_ BitVec 8)))
        (declare-const saved (_ BitVec 8))
        (declare-const other (_ BitVec 8))
        (assert (not (= (select {array} {key}) {expected})))
        (check-sat)"
    )
}

#[test]
fn affine_store_reads_export_checked_address_derivations() -> TestResult {
    for width in [9, 64, 128] {
        for count in [2, 40, 48, 64] {
            certificate(
                &format!("affine-address-{width}-{count}"),
                &problem(width, count, "saved"),
            )?;
            let (context, _, negative) = original(&problem(width, count, "other"))?;
            assert!(AlethePrinter::new(&context.terms)
                .format_bv_circuit_refutation(ProofId(7), &[negative])
                .is_none());
        }
    }
    Ok(())
}

#[test]
fn affine_store_capacity_and_formatting_budget_remain_bounded() -> TestResult {
    let (context, _, negative) = original(&problem(64, 65, "saved"))?;
    assert!(AlethePrinter::new(&context.terms)
        .format_bv_circuit_refutation(ProofId(7), &[negative])
        .is_none());
    let (context, _, negative) = original(&problem(64, 40, "saved"))?;
    let printer = AlethePrinter::new_with_overrides_and_budget(&context.terms, None, Some(64));
    assert!(printer
        .format_bv_circuit_refutation(ProofId(7), &[negative])
        .is_none());
    assert!(printer.work_budget_exhausted());
    Ok(())
}

#[test]
fn affine_address_refuses_changed_descendants_even_under_canonical_ancestor() {
    let mut terms = ay_core::TermStore::new();
    let base = terms.mk_var("base", Sort::bitvec(64));
    let offset = terms.mk_bitvec(32.into(), 64);
    let address = terms.mk_app(Symbol::named("bvsub"), [base, offset], Sort::bitvec(64));
    let canonical = AlethePrinter::new(&terms).format_term(address);
    for (term, changed) in [
        (base, "different"),
        (offset, "(_ bv31 64)"),
        (address, "base"),
    ] {
        let mut overrides = DetHashMap::default();
        overrides.insert(address, canonical.clone());
        overrides.insert(term, changed.to_string());
        let printer = AlethePrinter::new_with_overrides(&terms, Some(&overrides));
        let mut proof = PackedProof::new(&printer, ProofId(7)).unwrap();
        assert!(Circuit::new(&mut proof).address(address, 0).is_none());
    }
}
