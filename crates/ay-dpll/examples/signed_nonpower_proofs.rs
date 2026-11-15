// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Ordinary consumer regression for demonstrated nonpower signed-literal proofs.
//! SMT inputs omit set-logic so both constructor modes remain effective.
use ay_dpll::api::{Logic, Solver};
use std::{error::Error, time::Duration};
fn lit(v: u128, w: u32) -> String {
    format!("(_ bv{v} {w})")
}
fn main() -> Result<(), Box<dyn Error>> {
    let mut withheld = 0;
    let mut proved = 0;
    let mut controls = 0;
    for w in [5, 32, 64, 128] {
        for m in [3u128, 5] {
            for negative in [false, true] {
                for op in ["bvsdiv", "bvsrem", "bvsmod"] {
                    for valid in [true, false] {
                        if w != 5
                            && !(w == 64 && m == 5 && !negative && op == "bvsrem")
                            && !(w == 128 && m == 5 && negative && op == "bvsmod")
                        {
                            continue;
                        }

                        let mask = if w == 128 {
                            u128::MAX
                        } else {
                            (1u128 << w) - 1
                        };
                        let divisor = if negative { mask - m + 1 } else { m };
                        let zero = lit(0, w);
                        let mag = lit(m, w);
                        let sign = format!("(bvslt x {zero})");
                        let absolute = format!("(ite {sign} (bvneg x) x)");
                        let q = format!("(bvudiv {absolute} {mag})");
                        let r = format!("(bvurem {absolute} {mag})");
                        let signed_r = format!("(ite {sign} (bvneg {r}) {r})");
                        let expected = match op {
                            "bvsdiv" => {
                                let q = format!("(ite {sign} (bvneg {q}) {q})");
                                if negative {
                                    format!("(bvneg {q})")
                                } else {
                                    q
                                }
                            }
                            "bvsrem" => signed_r,
                            _ => {
                                let adjusted = if negative {
                                    format!("(ite {sign} (bvneg {r}) (bvsub {r} {mag}))")
                                } else {
                                    format!("(ite {sign} (bvsub {mag} {r}) {r})")
                                };
                                format!("(ite (= {r} {zero}) {zero} {adjusted})")
                            }
                        };
                        let expected = if valid {
                            expected
                        } else {
                            format!("(bvadd {expected} {})", lit(1, w))
                        };
                        let input = format!(
                            "(declare-const x (_ BitVec {w}))\n(assert (not (= ({op} x {}) {expected})))\n",
                            lit(divisor, w)
                        );
                        for logic in [Logic::QfBv, Logic::All] {
                            let mut s = Solver::try_new(logic)?;
                            s.set_produce_proofs(true);
                            s.set_produce_unsat_cores(true);
                            s.set_timeout(Some(Duration::from_secs(120)));
                            s.set_quantifier_deadline_backstop(false);
                            s.try_set_option("rlimit", "400000")?;
                            s.parse_smtlib2(&input)?;
                            let d = s.check_sat_with_details();
                            println!(
                                "width={w} magnitude={m} negative={negative} op={op} valid={valid} logic={logic:?} result={} strict={} model={} delegated={} diagnostic={:?}",
                                d.result,
                                d.result.was_unsat_strictly_verified(),
                                d.result.was_model_validated(),
                                d.verification.sat_delegated_checks,
                                d.unknown_diagnostic
                            );
                            if valid && d.result.is_unknown() {
                                println!(
                                    "decline={:?} step1={:?}",
                                    s.last_proof_decline(),
                                    s.describe_last_proof_step(1)
                                );
                            }
                            if valid {
                                if d.result.is_unsat() {
                                    d.accept_for_consumer()?;
                                    if !d.result.was_unsat_strictly_verified()
                                        || s.last_proof().is_none()
                                    {
                                        return Err("unverified UNSAT".into());
                                    }
                                    proved += 1;
                                } else if d.result.is_sat() {
                                    return Err("true identity returned SAT".into());
                                } else {
                                    withheld += 1;
                                }
                            } else {
                                if !d.accept_for_consumer()?.is_sat()
                                    || !d.result.was_model_validated()
                                    || d.verification.sat_delegated_checks != 0
                                {
                                    return Err("false twin lost validated SAT".into());
                                }
                                controls += 1;
                            }
                        }
                    }
                }
            }
        }
    }
    println!("proved={proved} withheld={withheld} validated_false_twins={controls}");
    if proved != 28 || controls != 28 || withheld != 0 {
        return Err("signed literal goals still withheld".into());
    }
    Ok(())
}
