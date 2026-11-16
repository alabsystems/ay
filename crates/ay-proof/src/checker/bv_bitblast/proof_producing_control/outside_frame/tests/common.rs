// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

type TestResult<T> = Result<T, Box<dyn std::error::Error>>;

fn common_writes(malformed: bool, wrong_value: bool) -> TestResult<Fixture> {
    let mut f = fixture(9, 2, 1, false);
    let TermData::App(_, property) = f.terms.get(f.property).clone() else {
        return Err("fixture property is not an application".into());
    };
    if property.len() != 2 {
        return Err("fixture property is not a binary disjunction".into());
    }
    let not_outside = *property.first().ok_or("fixture property has no guard")?;
    let equality = *property.get(1).ok_or("fixture property has no equality")?;
    let TermData::App(_, reads) = f.terms.get(equality).clone() else {
        return Err("fixture equality is not an application".into());
    };
    let mut arrays = Vec::new();
    let mut observe = None;
    for read in reads {
        let TermData::App(_, args) = f.terms.get(read).clone() else {
            return Err("fixture read is not an application".into());
        };
        arrays.push(*args.first().ok_or("fixture read has no array")?);
        observe = Some(*args.get(1).ok_or("fixture read has no index")?);
    }
    let observe = observe.ok_or("fixture equality has no reads")?;
    let word = Sort::bitvec(9);
    let first_array = *arrays.first().ok_or("fixture equality has no reads")?;
    let array = f.terms.sort(first_array).clone();
    let output = f.terms.mk_var("output", word.clone());
    let value = f.terms.mk_var("shared_value", Sort::bitvec(8));
    let bad = if malformed {
        app(&mut f.terms, "bvadd", &[value], Sort::bitvec(8))
    } else {
        value
    };
    let wrong = f.terms.mk_var("wrong", Sort::bitvec(8));
    let mut new_reads = Vec::new();
    for (i, base) in arrays.into_iter().enumerate() {
        // The second store overwrites the first, but must not hide its
        // malformed value in either native conditional validation or export.
        let first = app(&mut f.terms, "store", &[base, output, bad], array.clone());
        let last = if wrong_value && i == 1 { wrong } else { value };
        let written = app(&mut f.terms, "store", &[first, output, last], array.clone());
        new_reads.push(app(
            &mut f.terms,
            "select",
            &[written, observe],
            Sort::bitvec(8),
        ));
    }
    let equal = app(&mut f.terms, "=", &new_reads, Sort::Bool);
    f.property = app(&mut f.terms, "or", &[not_outside, equal], Sort::Bool);
    let TermData::App(_, guard) = f.terms.get(f.guard).clone() else {
        return Err("fixture guard is not an application".into());
    };
    let stack = *guard.first().ok_or("fixture guard has no stack pointer")?;
    let size = *guard.get(1).ok_or("fixture guard has no frame size")?;
    let start = app(&mut f.terms, "bvsub", &[stack, size], word.clone());
    let extent = f.terms.mk_bitvec(40.into(), 9);
    let end = app(&mut f.terms, "bvadd", &[output, extent], word.clone());
    let before = app(&mut f.terms, "bvule", &[end, start], Sort::Bool);
    let after = app(&mut f.terms, "bvuge", &[output, stack], Sort::Bool);
    let separated = app(&mut f.terms, "or", &[before, after], Sort::Bool);
    let limit = f.terms.mk_bitvec(471.into(), 9);
    let nowrap = app(&mut f.terms, "bvule", &[output, limit], Sort::Bool);
    let negative = f.terms.mk_not_raw(f.property);
    let tail = app(&mut f.terms, "and", &[f.guard, negative], Sort::Bool);
    let tail = app(&mut f.terms, "and", &[nowrap, tail], Sort::Bool);
    f.root = app(&mut f.terms, "and", &[separated, tail], Sort::Bool);
    f.clause = f.terms.mk_not_raw(f.root);
    Ok(f)
}

#[test]
fn combined_memory_validation_checks_even_overwritten_common_values() -> TestResult<()> {
    let valid = common_writes(false, false)?;
    validate(&valid.terms, &[valid.clause], &mut || Ok(())).unwrap();
    for (malformed, wrong) in [(true, false), (false, true)] {
        let f = common_writes(malformed, wrong)?;
        assert!(validate(&f.terms, &[f.clause], &mut || Ok(())).is_err());
    }
    Ok(())
}

#[test]
fn combined_memory_validation_honors_cancellation() -> TestResult<()> {
    let f = common_writes(false, false)?;
    let result = validate(&f.terms, &[f.clause], &mut || {
        Err(ProofCheckError::ResourceLimit)
    });
    assert_eq!(result, Err(Failure::Cancelled));
    Ok(())
}
