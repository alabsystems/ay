// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Preserve old scalar and array-clause admissions without changing retry eligibility.
use std::error::Error;
fn input(depth: usize, negative: bool, unit: bool, array: bool, valid: bool) -> String {
    let divisor = if unit {
        "#xff"
    } else if negative {
        "#xfe"
    } else {
        "#x02"
    };
    let mut term = String::from("(let ((s0 x)) ");
    for i in 1..=depth {
        let previous = format!("s{}", i - 1);
        let numerator = if unit {
            previous
        } else {
            format!("(bvmul {previous} {divisor})")
        };
        term.push_str(&format!("(let ((s{i} (bvsdiv {numerator} {divisor}))) "));
    }
    let multiplier = if valid { "#x03" } else { "#x04" };
    term.push_str(&format!(
        "(= (bvadd (bvmul (bvudiv s{depth} #x03) {multiplier}) (bvurem s{depth} #x03)) s{depth})"
    ));
    term.push_str(&")".repeat(depth + 1));
    let logic = if array { "QF_ABV" } else { "QF_BV" };
    let mut declarations = format!("(set-logic {logic})\n(declare-const x (_ BitVec 8))\n");
    if array {
        declarations.push_str("(declare-const a (Array (_ BitVec 1) (_ BitVec 1)))\n(declare-const b (Array (_ BitVec 1) (_ BitVec 1)))\n");
        term = format!("(or {term} (= a b))");
    }
    format!("{declarations}(assert {term})\n")
}
fn main() -> Result<(), Box<dyn Error>> {
    let mut cases = Vec::new();
    for depth in [8, 16, 64, 128] {
        for negative in [false, true] {
            for array in [false, true] {
                for valid in [false, true] {
                    cases.push((depth, negative, false, array, valid));
                }
            }
        }
    }
    for depth in [16, 128, 384] {
        for valid in [false, true] {
            cases.push((depth, true, true, true, valid));
        }
    }
    let mut admitted = 0;
    for (depth, negative, unit, array, valid) in cases {
        let mut e = ay_dpll::Executor::new();
        e.execute_all(&ay_frontend::parse(&input(
            depth, negative, unit, array, valid,
        ))?)?;
        let roots = e
            .context()
            .concrete_authored_assertion_terms_aligned_bounded(1)
            .ok_or("missing root")?;
        if roots.len() != 1 {
            return Err("expected exactly one root".into());
        }
        let actual = ay_proof::recognize_bv_bitblast(e.terms(), &roots);
        // Two depth128 negative-power clauses already exceeded the old bounded fragment.
        let required = valid && (unit || !negative || depth != 128);
        if (!valid && actual) || (required && !actual) {
            return Err(format!("preservation: depth={depth} negative={negative} unit={unit} array={array} valid={valid} recognized={actual}").into());
        }
        if actual {
            admitted += 1;
        }
    }
    println!(
        "preservation_cases=38 required_old_admissions=17 recognized={admitted} false_accepts=0"
    );
    Ok(())
}
