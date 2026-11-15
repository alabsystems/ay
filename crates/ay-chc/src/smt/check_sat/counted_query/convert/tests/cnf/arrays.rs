// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
#![cfg(test)]

use super::*;
use ay_arrays::counted_reads::{Derivation, Unresolved};

fn source() -> ChcExpr {
    let index = Arc::new(var("i", ChcSort::BitVec(8)));
    let value = Arc::new(var("v", ChcSort::BitVec(8)));
    let array = Arc::new(ChcExpr::ConstArray(
        ChcSort::BitVec(8),
        Arc::new(ChcExpr::BitVec(2, 8)),
    ));
    let stored = Arc::new(ChcExpr::Op(
        ChcOp::Store,
        vec![array, index.clone(), value.clone()],
    ));
    let read = Arc::new(ChcExpr::Op(ChcOp::Select, vec![stored, index]));
    ChcExpr::Op(ChcOp::Eq, vec![read, value])
}

#[test]
fn actual_array_read_derivations_precede_cnf_sealing_without_new_authored_roots() {
    let source = source();
    let original = ample();
    let mut built = convert(&source, &original).unwrap();
    let before = built.terms().len();
    built
        .with_cnf(|context, cnf| {
            let closure = context
                .array_reads()
                .expect("array source must use the real closure");
            closure.validate_source(cnf.terms())?;
            assert!(cnf.terms().len() > before);
            assert_eq!(closure.roots(), &[context.root()]);
            assert_eq!(cnf.roots(), closure.roots());
            assert_eq!(closure.reads().len(), 2);
            assert_eq!(closure.steps().len(), 3);
            assert!(closure.unresolved().is_empty());
            assert!(closure
                .steps()
                .iter()
                .any(|step| matches!(step.derivation(), Derivation::Row1 { .. })));
            assert!(closure
                .steps()
                .iter()
                .any(|step| matches!(step.derivation(), Derivation::Row2 { .. })));
            assert!(closure
                .steps()
                .iter()
                .any(|step| matches!(step.derivation(), Derivation::ConstFill { .. })));
            let roots: Vec<_> = cnf
                .rows()
                .iter()
                .filter_map(|row| match row.justification() {
                    CountedCnfJustification::Root(root) => Some(root),
                    _ => None,
                })
                .collect();
            assert_eq!(roots, vec![context.root()]);
            let used = original.usage()?.work_admitted;
            closure.admission().admit(3, 0)?;
            assert_eq!(original.usage()?.work_admitted, used + 3);
            assert_eq!(context.admission().usage(), closure.admission().usage());
            Ok(())
        })
        .unwrap();
    built.finish().unwrap();
}

#[test]
fn scalar_cnf_has_no_array_stage_and_array_equality_keeps_its_unresolved_authority() {
    let source = ChcExpr::Bool(true);
    let mut built = convert(&source, &ample()).unwrap();
    built
        .with_cnf(|context, _| {
            assert!(context.array_reads().is_none());
            Ok(())
        })
        .unwrap();
    built.finish().unwrap();
    let sort = ChcSort::Array(Box::new(ChcSort::BitVec(8)), Box::new(ChcSort::BitVec(64)));
    let source = op(ChcOp::Eq, vec![var("a", sort.clone()), var("b", sort)]);
    let mut built = convert(&source, &ample()).unwrap();
    built.with_cnf(|context,cnf| {
        let closure=context.array_reads().unwrap();
        assert!(closure.reads().is_empty());
        assert!(closure.steps().is_empty());
        assert!(matches!(closure.unresolved(),[Unresolved::ArrayRelation { source,.. }] if *source==context.root()));
        assert_eq!(cnf.theory_atoms(),&[context.root()]);
        assert_eq!(cnf.roots(),&[context.root()]);
        Ok(())
    }).unwrap();
    built.finish().unwrap();
}

fn sequence(source: &ChcExpr, original: &CountedAdmission) -> Result<()> {
    let mut built = convert(source, original)?;
    let result = built.with_cnf(|context, cnf| {
        let closure = context.array_reads().unwrap();
        closure.validate_source(cnf.terms())?;
        assert_eq!(closure.steps().len(), 3);
        Ok(())
    });
    built.finish()?;
    result
}

#[test]
fn exact_and_one_short_grants_cover_actual_array_closure_cnf_and_disposal() {
    let source = source();
    let original = ample();
    sequence(&source, &original).unwrap();
    let receipt = original.usage().unwrap();
    for (work, bytes, error) in [
        (receipt.work_admitted, receipt.storage_admitted, None),
        (
            receipt.work_admitted - 1,
            receipt.storage_admitted,
            Some(CountedAdmissionError::WorkExhausted),
        ),
        (
            receipt.work_admitted,
            receipt.storage_admitted - 1,
            Some(CountedAdmissionError::StorageExhausted),
        ),
    ] {
        let original = owner(work, bytes);
        let result = sequence(&source, &original);
        if let Some(error) = error {
            assert_eq!(result, Err(Error::Stopped(error)));
            assert_eq!(original.check(), Err(error));
        } else {
            result.unwrap();
            let receipt = original.usage().unwrap();
            assert_eq!((receipt.work_remaining, receipt.storage_remaining), (0, 0));
        }
    }
}

#[test]
fn nested_array_representation_declines_before_any_counted_cnf_callback() {
    let element = ChcSort::Array(Box::new(ChcSort::BitVec(8)), Box::new(ChcSort::BitVec(8)));
    let sort = ChcSort::Array(Box::new(ChcSort::BitVec(8)), Box::new(element));
    let source = op(ChcOp::Eq, vec![var("a", sort.clone()), var("b", sort)]);
    let mut built = convert(&source, &ample()).unwrap();
    let mut reached = false;
    assert_eq!(
        built.with_cnf(|_, _| {
            reached = true;
            Ok(())
        }),
        Err(Error::Unsupported)
    );
    assert!(!reached);
    built.finish().unwrap();
}
