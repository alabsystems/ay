// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Nonpower rejection, query-authentication refusal and ordinary UF controls.
use ay_dpll::api::{Logic, Solver, Sort};
use std::{error::Error, time::Duration};
fn main() -> Result<(), Box<dyn Error>> {
    let cases: Vec<_> = include_str!("fixtures/signed_power_authority.smt2")
        .split("\n; CASE\n")
        .collect();
    if cases.len() != 30 {
        return Err("expected 30 authority cases".into());
    }
    for (name, input) in cases[..24].iter().enumerate() {
        let mut e = ay_dpll::Executor::new();
        e.execute_all(&ay_frontend::parse(input)?)?;
        let roots = e
            .context()
            .concrete_authored_assertion_terms_aligned_bounded(1)
            .ok_or("missing nonpower root")?;
        if ay_proof::recognize_bv_bitblast(e.terms(), &roots) {
            return Err(format!("false nonpower clause accepted: {name}").into());
        }
    }
    for (name, input) in cases[24..].iter().enumerate() {
        let mut e = ay_dpll::Executor::new();
        e.execute_all(&ay_frontend::parse(input)?)?;
        let roots = e
            .context()
            .concrete_authored_assertion_terms_aligned_bounded(1)
            .ok_or("missing auth root")?;
        match ay_proof::authenticate_bool_bv_unsat_query(e.terms(), &roots, None) {
            Err(ay_proof::BoolBvUnsatAuthenticationError::UnsupportedFragment { .. }) => {}
            Err(other) => {
                return Err(format!("unexpected authentication outcome {name}: {other}").into());
            }
            Ok(_) => {
                return Err(format!("reserved operator unexpectedly authenticated: {name}").into());
            }
        }
    }
    for name in ["my_sdiv", "my_srem", "my_smod"] {
        let mut s = Solver::try_new(Logic::All)?;
        s.set_produce_proofs(true);
        s.set_produce_unsat_cores(true);
        s.set_timeout(Some(Duration::from_secs(120)));
        s.set_quantifier_deadline_backstop(false);
        s.try_set_option("rlimit", "400000")?;
        let sort = Sort::bitvec(5);
        let f = s.try_declare_fun(name, &[sort.clone(), sort.clone()], sort.clone())?;
        let x = s.try_declare_const("x", sort)?;
        let two = s.try_bv_const_u64(2, 5)?;
        let v = s.try_apply(&f, &[x, two])?;
        let eq = s.try_eq(v, x)?;
        let neq = s.try_not(eq)?;
        s.try_assert_term(neq)?;
        let d = s.check_sat_with_details();
        if !d.accept_for_consumer()?.is_sat()
            || !d.result.was_model_validated()
            || d.verification.sat_delegated_checks != 0
        {
            return Err(format!("UF identity lost: {name}").into());
        }
    }
    println!(
        "nonpower_false_rejections=24 reserved_authentication_declines=6 typed_UF_validated_SAT=3"
    );
    Ok(())
}
