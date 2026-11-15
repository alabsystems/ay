// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Preserve all47 old admissions and reject all51 false clauses.
use std::error::Error;
fn input(depth: usize, divisor: &str, unit: bool, array: bool, valid: bool) -> String {
    let mut term = String::from("(let ((s0 x)) ");
    for i in 1..=depth {
        let prev = format!("s{}", i - 1);
        let numerator = if unit {
            prev
        } else {
            format!("(bvmul {prev} {divisor})")
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
    let mut checked_required = 0;
    let mut cases = Vec::new();
    for depth in [8, 16, 64, 128] {
        for divisor in ["#x02", "#xfe", "#x03", "#xfd", "#x05", "#xfb"] {
            for array in [false, true] {
                for valid in [false, true] {
                    cases.push((depth, divisor, false, array, valid));
                }
            }
        }
    }
    for depth in [16, 128, 384] {
        for valid in [false, true] {
            cases.push((depth, "#xff", true, true, valid));
        }
    }
    let mut admitted = 0;
    for (depth, divisor, unit, array, valid) in cases {
        let name = format!("{divisor}-depth{depth}-unit{unit}-array{array}-valid{valid}");
        let mut e = ay_dpll::Executor::new();
        e.execute_all(&ay_frontend::parse(&input(
            depth, divisor, unit, array, valid,
        ))?)?;
        let roots = e
            .context()
            .concrete_authored_assertion_terms_aligned_bounded(1)
            .ok_or("missingroot")?;
        if roots.len() != 1 {
            return Err("expected exactlyoneroot".into());
        }
        let actual = ay_proof::recognize_bv_bitblast(e.terms(), &roots);
        println!(
            "name={name} truth={valid} recognized={actual} terms={}",
            e.terms().len()
        );
        let required = valid && !(depth == 128 && !unit && matches!(divisor, "#xfe" | "#x03"));
        if required {
            checked_required += 1;
            if !actual {
                return Err(format!("oldadmissionlost: {name}").into());
            }
        }
        if !valid && actual {
            return Err(format!("false clause accepted: {name}").into());
        }
        if valid && actual {
            admitted += 1;
        }
    }
    if checked_required != 47 {
        return Err("missingoldadmissioncase".into());
    }
    println!(
        "cases=102 true_admissions={admitted} required_preserved={checked_required} false_accepts=0"
    );
    Ok(())
}
