// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Independently computed numeric guards and false twins, including every5bit nonpower input.
use std::error::Error;
fn main() -> Result<(), Box<dyn Error>> {
    let mut good = 0;
    let mut rejected = 0;
    for line in include_str!("signed_nonpower_numeric/cases.tsv").lines() {
        let f: Vec<_> = line.split('\t').collect();
        if f.len() != 6 {
            return Err("badnumericrow".into());
        }
        let w: u32 = f[0].parse()?;
        if ![5, 64, 128].contains(&w) {
            return Err("badnumericwidth".into());
        }
        let op = f[1];
        let a: u128 = f[2].parse()?;
        let d: u128 = f[3].parse()?;
        let expected: u128 = f[4].parse()?;
        let name = f[5];
        let mask = if w == 128 {
            u128::MAX
        } else {
            (1u128 << w) - 1
        };
        for valid in [true, false] {
            let v = if valid {
                expected
            } else {
                expected.wrapping_add(1) & mask
            };
            let input = format!(
                "(set-logic QF_BV)\n(declare-const x (_ BitVec {w}))\n(assert (or (not (= x (_ bv{a} {w}))) (= ({op} x (_ bv{d} {w})) (_ bv{v} {w}))))\n"
            );
            let mut e = ay_dpll::Executor::new();
            e.execute_all(&ay_frontend::parse(&input)?)?;
            let roots = e
                .context()
                .concrete_authored_assertion_terms_aligned_bounded(1)
                .ok_or("missingnumericroot")?;
            if roots.len() != 1 {
                return Err("expectedonenumericroot".into());
            }
            let actual = ay_proof::recognize_bv_bitblast(e.terms(), &roots);
            println!("numeric={name} truth={valid} recognized={actual}");
            if actual != valid {
                return Err(
                    format!("numericguardmismatch {name} truth={valid} actual={actual}").into(),
                );
            }
            if valid {
                good += 1;
            } else {
                rejected += 1;
            }
        }
    }
    if good != 2304 || rejected != 2304 {
        return Err("missingnumericcases".into());
    }
    println!(
        "numeric_true_admitted={good} numeric_false_rejected={rejected} independent_numeric_reference=true"
    );
    Ok(())
}
