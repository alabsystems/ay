// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Ordinary native consumer: strict signed power-of-two proofs and SAT twins.
//! Inputs omit set-logic so the constructor's QF_BV/All modes are effective.
use ay_dpll::api::{Logic, Solver};
use std::{error::Error, time::Duration};
fn literal(value: u128, width: u32) -> String {
    format!("(_ bv{value} {width})")
}
fn goal(width: u32, shift: u32, negative: bool, op: &str, valid: bool) -> String {
    let magnitude = 1u128 << shift;
    let mask = if width == 128 {
        u128::MAX
    } else {
        (1u128 << width) - 1
    };
    let divisor = if negative {
        mask - magnitude + 1
    } else {
        magnitude
    };
    let zero = literal(0, width);
    let sign = format!("(bvslt x {zero})");
    let absolute = format!("(ite {sign} (bvneg x) x)");
    let low = literal(magnitude - 1, width);
    // Independent sign/magnitude identity rather than the checker's biased shift.
    let expected = match op {
        "bvsdiv" => {
            let q = format!("(bvlshr {absolute} {})", literal(u128::from(shift), width));
            let q = format!("(ite {sign} (bvneg {q}) {q})");
            if negative {
                format!("(bvneg {q})")
            } else {
                q
            }
        }
        "bvsrem" => {
            let r = format!("(bvand {absolute} {low})");
            format!("(ite {sign} (bvneg {r}) {r})")
        }
        _ if negative => format!("(bvneg (bvand (bvneg x) {low}))"),
        _ => format!("(bvand x {low})"),
    };
    let expected = if valid {
        expected
    } else {
        format!("(bvadd {expected} {})", literal(1, width))
    };
    format!(
        "(declare-const x (_ BitVec {width}))\n(assert (not (= ({op} x {}) {expected})))\n",
        literal(divisor, width)
    )
}
fn main() -> Result<(), Box<dyn Error>> {
    let mut calls = 0;
    for width in [2, 3, 5, 32, 64, 128] {
        let mut shifts = vec![1, 2, width - 1];
        if width == 128 {
            shifts.extend([63, 64]);
        }
        shifts.sort_unstable();
        shifts.dedup();
        for shift in shifts.into_iter().filter(|k| *k < width) {
            for negative in [false, true] {
                if !negative && shift == width - 1 {
                    continue;
                }
                for op in ["bvsdiv", "bvsrem", "bvsmod"] {
                    for valid in [true, false] {
                        let input = goal(width, shift, negative, op, valid);
                        for logic in [Logic::QfBv, Logic::All] {
                            let mut s = Solver::try_new(logic)?;
                            s.set_produce_proofs(true);
                            s.set_produce_unsat_cores(true);
                            s.set_timeout(Some(Duration::from_secs(120)));
                            s.set_quantifier_deadline_backstop(false);
                            s.try_set_option("rlimit", "400000")?;
                            s.parse_smtlib2(&input)?;
                            let d = s.check_sat_with_details();
                            let r = d.accept_for_consumer()?;
                            let accepted = if valid {
                                r.is_unsat()
                                    && d.result.was_unsat_strictly_verified()
                                    && s.last_proof().is_some()
                            } else {
                                r.is_sat()
                                    && d.result.was_model_validated()
                                    && d.verification.sat_delegated_checks == 0
                            };
                            if !accepted {
                                return Err(format!("w={width} k={shift} negative={negative} op={op} valid={valid} logic={logic:?}: {}", d.result).into());
                            }
                            calls += 1;
                        }
                    }
                }
            }
        }
    }
    println!("signed_power_solver_calls={calls} all_strict_proofs_or_validated_SAT=true");
    Ok(())
}
