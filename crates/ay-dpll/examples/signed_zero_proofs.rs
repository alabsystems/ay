//! Native strict-proof regression for signed literal-zero division.
//! Inputs are headerless so the constructor's requested logic remains effective.
use ay_dpll::api::{Logic, Solver};
use std::{error::Error, time::Duration};

fn check(input: &str, logic: Logic, unsat: bool) -> Result<(), Box<dyn Error>> {
    let mut solver = Solver::try_new(logic)?;
    solver.set_produce_proofs(true);
    solver.set_produce_unsat_cores(true);
    solver.set_timeout(Some(Duration::from_secs(120)));
    solver.set_quantifier_deadline_backstop(false);
    solver.try_set_option("rlimit", "400000")?;
    solver.parse_smtlib2(input)?;
    let details = solver.check_sat_with_details();
    let result = details.accept_for_consumer()?;
    let okay = if unsat {
        result.is_unsat()
            && details.result.was_unsat_strictly_verified()
            && solver.last_proof().is_some()
    } else {
        result.is_sat()
            && details.result.was_model_validated()
            && details.verification.sat_delegated_checks == 0
    };
    if !okay {
        return Err(format!(
            "logic={logic:?} expected strict UNSAT={unsat}, actual={} diagnostic={:?} input={input}",
            details.result, details.unknown_diagnostic
        )
        .into());
    }
    Ok(())
}

fn main() -> Result<(), Box<dyn Error>> {
    let mut calls = 0;
    for width in [1, 5, 128] {
        let mask = if width == 128 {
            u128::MAX
        } else {
            (1u128 << width) - 1
        };
        for op in ["bvsdiv", "bvsrem", "bvsmod"] {
            let expected = if op == "bvsdiv" {
                format!("(ite (bvslt x (_ bv0 {width})) (_ bv1 {width}) (_ bv{mask} {width}))")
            } else {
                "x".to_string()
            };
            for identity in [true, false] {
                let rhs = if identity {
                    expected.clone()
                } else {
                    format!("(bvadd {expected} (_ bv1 {width}))")
                };
                let input = format!("(declare-const x (_ BitVec {width}))(assert (not (= ({op} x (_ bv0 {width})) {rhs})))");
                for logic in [Logic::QfBv, Logic::All] {
                    check(&input, logic, identity)?;
                    calls += 1;
                }
            }
        }
    }
    println!("native_solver_calls={calls} requested_logics=QF_BV,ALL headerless_inputs=true; signed-zero strict proofs and validated SAT twins passed");
    Ok(())
}
