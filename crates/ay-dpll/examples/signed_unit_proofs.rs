//! Native strict-proof regression for signed literal-unit identities.
use ay_dpll::api::{Logic, Solver, Sort};
use std::{error::Error, time::Duration};

fn solver(logic: Logic) -> Result<Solver, Box<dyn Error>> {
    let mut solver = Solver::try_new(logic)?;
    solver.set_produce_proofs(true);
    solver.set_produce_unsat_cores(true);
    solver.set_timeout(Some(Duration::from_secs(120)));
    solver.set_quantifier_deadline_backstop(false);
    solver.try_set_option("rlimit", "400000")?;
    Ok(solver)
}
fn check_logic(input: &str, unsat: bool, logic: Logic) -> Result<(), Box<dyn Error>> {
    let mut solver = solver(logic)?;
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
            "expected strict UNSAT={unsat}, actual={} diagnostic={:?} input={input}",
            details.result, details.unknown_diagnostic
        )
        .into());
    }
    Ok(())
}
fn check(input: &str, unsat: bool) -> Result<(), Box<dyn Error>> {
    for logic in [Logic::QfBv, Logic::All] {
        check_logic(input, unsat, logic)?;
    }
    Ok(())
}
fn main() -> Result<(), Box<dyn Error>> {
    let mut calls = 0;
    for width in [1, 4, 5, 128] {
        let mask = if width == 128 {
            u128::MAX
        } else {
            (1u128 << width) - 1
        };
        let divisors = if mask == 1 { vec![mask] } else { vec![1, mask] };
        for divisor in divisors {
            for op in ["bvsdiv", "bvsrem", "bvsmod"] {
                let expected = if op != "bvsdiv" {
                    format!("(_ bv0 {width})")
                } else if divisor == mask {
                    "(bvneg x)".to_string()
                } else {
                    "x".to_string()
                };
                for identity in [true, false] {
                    let rhs = if identity {
                        expected.clone()
                    } else {
                        format!("(bvadd {expected} (_ bv1 {width}))")
                    };
                    let input = format!("(declare-const x (_ BitVec {width}))(assert (not (= ({op} x (_ bv{divisor} {width})) {rhs})))");
                    check(&input, identity)?;
                    calls += 2;
                    if width == 5 || width == 128 {
                        let minimum = 1u128 << (width - 1);
                        let forced = format!("{input}(assert (= x (_ bv{minimum} {width})))");
                        check(&forced, identity)?;
                        calls += 2;
                    }
                }
            }
        }
        if width == 5 || width == 128 {
            for divisor in [2, mask - 1] {
                for op in ["bvsdiv", "bvsrem", "bvsmod"] {
                    let wrong = if op == "bvsdiv" {
                        "x".to_string()
                    } else {
                        format!("(_ bv0 {width})")
                    };
                    let input = format!("(declare-const x (_ BitVec {width}))(assert (= x (_ bv1 {width})))(assert (not (= ({op} x (_ bv{divisor} {width})) {wrong})))");
                    check(&input, false)?;
                    calls += 2;
                }
            }
        }
    }
    let mut declarations_refused = 0;
    for name in [
        "bvsdiv", "bvsrem", "bvsmod", "my_sdiv", "my_srem", "my_smod",
    ] {
        let mut solver = solver(Logic::All)?;
        let sort = Sort::bitvec(5);
        match solver.try_declare_fun(name, &[sort.clone(), sort.clone()], sort.clone()) {
            Err(error) if name.starts_with("bvs") => {
                println!("typed_declaration_refused name={name} error={error}");
                declarations_refused += 1;
            }
            Err(error) => return Err(error.into()),
            Ok(function) => {
                let x = solver.try_declare_const("x", sort)?;
                let one = solver.try_bv_const_u64(1, 5)?;
                let value = solver.try_apply(&function, &[x, one])?;
                let equality = solver.try_eq(value, x)?;
                let different = solver.try_not(equality)?;
                solver.try_assert_term(different)?;
                let details = solver.check_sat_with_details();
                if !details.accept_for_consumer()?.is_sat()
                    || !details.result.was_model_validated()
                    || details.verification.sat_delegated_checks != 0
                {
                    return Err(format!(
                        "UF {name} was treated as builtin: {} {:?}",
                        details.result, details.unknown_diagnostic
                    )
                    .into());
                }
                calls += 1;
            }
        }
    }
    println!("native_solver_calls={calls} typed_declaration_refusals={declarations_refused}; strict identities, false twins, MIN overflow, nonunits and UF isolation passed");
    Ok(())
}
