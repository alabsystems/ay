// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Reserved signed heads must not become opaque query-authentication leaves.
//! Each atomic control has no unsigned operator on its expected side.
use ay_dpll::api::{Logic, Solver, Sort};
use std::{error::Error, time::Duration};
fn main() -> Result<(), Box<dyn Error>> {
    let mut declines = 0;
    for width in [5_u32, 128] {
        let mask = if width == 128 {
            u128::MAX
        } else {
            (1_u128 << width) - 1
        };
        for magnitude in [3_u128, 5] {
            for negative in [false, true] {
                for op in ["bvsdiv", "bvsrem", "bvsmod"] {
                    let divisor = if negative {
                        mask - magnitude + 1
                    } else {
                        magnitude
                    };
                    let input = format!(
                        "(set-logic QF_BV)\n(declare-const x (_ BitVec {width}))\n(assert (not (= ({op} x (_ bv{divisor} {width})) x)))\n"
                    );
                    let mut executor = ay_dpll::Executor::new();
                    executor.execute_all(&ay_frontend::parse(&input)?)?;
                    let roots = executor
                        .context()
                        .concrete_authored_assertion_terms_aligned_bounded(1)
                        .ok_or("missingauthroot")?;
                    if roots.len() != 1 {
                        return Err("expectedoneauthroot".into());
                    }
                    match ay_proof::authenticate_bool_bv_unsat_query(executor.terms(), &roots, None)
                    {
                        Err(ay_proof::BoolBvUnsatAuthenticationError::UnsupportedFragment {
                            ..
                        }) => declines += 1,
                        Err(other) => {
                            return Err(format!("unexpectedauthenticationoutcome:{other}").into());
                        }
                        Ok(_) => {
                            return Err(format!(
                                "reservedheadwasqueryauthenticated:{op} {divisor} {width}"
                            )
                            .into());
                        }
                    }
                }
            }
        }
    }
    if declines != 24 {
        return Err("expected24reserveddeclines".into());
    }
    let mut uf = 0;
    for name in ["my_sdiv", "my_srem", "my_smod"] {
        for value in [3, 29] {
            let mut s = Solver::try_new(Logic::All)?;
            s.set_produce_proofs(true);
            s.set_produce_unsat_cores(true);
            s.set_timeout(Some(Duration::from_secs(120)));
            s.set_quantifier_deadline_backstop(false);
            s.try_set_option("rlimit", "400000")?;
            let sort = Sort::bitvec(5);
            let f = s.try_declare_fun(name, &[sort.clone(), sort.clone()], sort.clone())?;
            let x = s.try_declare_const("x", sort)?;
            let d = s.try_bv_const_u64(value, 5)?;
            let v = s.try_apply(&f, &[x, d])?;
            let eq = s.try_eq(v, x)?;
            let neq = s.try_not(eq)?;
            s.try_assert_term(neq)?;
            let d = s.check_sat_with_details();
            if !d.accept_for_consumer()?.is_sat()
                || !d.result.was_model_validated()
                || d.verification.sat_delegated_checks != 0
            {
                return Err(format!("UFidentitylost: {name} {value}").into());
            }
            uf += 1;
        }
    }
    println!("nonpower_reserved_authentication_declines=24 ordinary_UF_validated_SAT={uf}");
    Ok(())
}
