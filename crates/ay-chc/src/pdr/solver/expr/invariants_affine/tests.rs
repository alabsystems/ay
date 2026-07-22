// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::pdr::config::PdrConfig;
use crate::ChcParser;
use std::collections::BTreeMap;
use std::time::Duration;

fn add_coeff(coeffs: &mut BTreeMap<String, i128>, name: &str, coeff: i128) {
    *coeffs.entry(name.to_string()).or_default() += coeff;
}

fn collect_linear(
    expr: &ChcExpr,
    scale: i128,
    coeffs: &mut BTreeMap<String, i128>,
    constant: &mut i128,
) -> bool {
    match expr {
        ChcExpr::Int(value) => {
            *constant += scale * value;
            true
        }
        ChcExpr::Var(var) => {
            add_coeff(coeffs, &var.name, scale);
            true
        }
        ChcExpr::Op(ChcOp::Add, args) => args
            .iter()
            .all(|arg| collect_linear(arg.as_ref(), scale, coeffs, constant)),
        ChcExpr::Op(ChcOp::Sub, args) if args.len() == 2 => {
            collect_linear(args[0].as_ref(), scale, coeffs, constant)
                && collect_linear(args[1].as_ref(), -scale, coeffs, constant)
        }
        ChcExpr::Op(ChcOp::Neg, args) if args.len() == 1 => {
            collect_linear(args[0].as_ref(), -scale, coeffs, constant)
        }
        ChcExpr::Op(ChcOp::Mul, args) if args.len() == 2 => {
            match (args[0].as_ref(), args[1].as_ref()) {
                (ChcExpr::Int(k), rhs) | (rhs, ChcExpr::Int(k)) => {
                    collect_linear(rhs, scale * k, coeffs, constant)
                }
                _ => false,
            }
        }
        _ => false,
    }
}

fn proves_double_relation(expr: &ChcExpr, doubled: &str, base: &str) -> bool {
    let Some((coeffs, constant)) = equality_linear_form(expr) else {
        return false;
    };

    let base_coeff = coeffs.get(base).copied();
    let doubled_coeff = coeffs.get(doubled).copied();
    constant == 0
        && coeffs.len() == 2
        && ((base_coeff == Some(2) && doubled_coeff == Some(-1))
            || (base_coeff == Some(-2) && doubled_coeff == Some(1)))
}

fn equality_linear_form(expr: &ChcExpr) -> Option<(BTreeMap<String, i128>, i128)> {
    let ChcExpr::Op(ChcOp::Eq, args) = expr else {
        return None;
    };
    if args.len() != 2 {
        return None;
    }

    let mut coeffs = BTreeMap::new();
    let mut constant = 0;
    if !collect_linear(args[0].as_ref(), 1, &mut coeffs, &mut constant)
        || !collect_linear(args[1].as_ref(), -1, &mut coeffs, &mut constant)
    {
        return None;
    }
    coeffs.retain(|_, coeff| *coeff != 0);
    Some((coeffs, constant))
}

fn proves_var_equality(expr: &ChcExpr, left: &str, right: &str) -> bool {
    let Some((coeffs, constant)) = equality_linear_form(expr) else {
        return false;
    };

    let left_coeff = coeffs.get(left).copied();
    let right_coeff = coeffs.get(right).copied();
    constant == 0
        && coeffs.len() == 2
        && ((left_coeff == Some(1) && right_coeff == Some(-1))
            || (left_coeff == Some(-1) && right_coeff == Some(1)))
}

fn double_relation_base(expr: &ChcExpr, doubled: &str) -> Option<String> {
    let (coeffs, constant) = equality_linear_form(expr)?;
    if constant != 0 || coeffs.len() != 2 {
        return None;
    }
    let doubled_coeff = coeffs.get(doubled).copied()?;
    for (name, coeff) in coeffs {
        if name == doubled {
            continue;
        }
        if (doubled_coeff == -1 && coeff == 2) || (doubled_coeff == 1 && coeff == -2) {
            return Some(name);
        }
    }
    None
}

fn frame_proves_double_relation(
    solver: &PdrSolver,
    pred: PredicateId,
    doubled: &str,
    base: &str,
) -> bool {
    let lemmas: Vec<_> = solver.frames[1]
        .lemmas
        .iter()
        .filter(|lemma| lemma.predicate == pred)
        .collect();

    lemmas
        .iter()
        .any(|lemma| proves_double_relation(&lemma.formula, doubled, base))
        || lemmas.iter().any(|lemma| {
            let Some(intermediate) = double_relation_base(&lemma.formula, doubled) else {
                return false;
            };
            intermediate == base
                || lemmas
                    .iter()
                    .any(|eq_lemma| proves_var_equality(&eq_lemma.formula, &intermediate, base))
        })
}

#[test]
fn budgeted_affine_kernel_prefers_fact_predicates_on_dillig12_shape() {
    let input = r#"
(set-logic HORN)

(declare-fun SAD (Int Int) Bool)
(declare-fun FUN (Int Int Int Int Int) Bool)

(assert
  (forall ((A Int) (B Int) (C Int) (D Int) (E Int))
    (=>
      (and (= A 0) (= B 0) (= C 0) (= D 0) (= E 1))
      (FUN A B C D E)
    )
  )
)

(assert
  (forall ((A Int) (B Int) (C Int) (D Int) (E Int)
           (F Int) (G Int) (I Int) (H Int))
    (=>
      (and
        (FUN A B C D E)
        (= F (+ A 1))
        (= G (+ B 1))
        (= I (+ C 1))
        (= H (+ D 2))
      )
      (FUN F G I H E)
    )
  )
)

(assert
  (forall ((A Int) (B Int) (C Int) (D Int) (E Int) (X Int))
    (=>
      (and
        (FUN A B C D E)
        (= X (* 2 C))
      )
      (SAD X C)
    )
  )
)

(check-sat)
(exit)
"#;

    let problem = ChcParser::parse(input).expect("parse affine kernel fixture");
    let config = PdrConfig {
        solve_timeout: Some(Duration::from_secs(2)),
        ..Default::default()
    };
    let mut solver = PdrSolver::new(problem, config);

    solver.discover_affine_invariants_via_kernel(None);

    let fun = solver
        .problem
        .predicates()
        .iter()
        .find(|p| p.name == "FUN")
        .expect("missing FUN")
        .id;
    let fun_vars = solver
        .canonical_vars(fun)
        .expect("canonical vars for FUN")
        .to_vec();
    let found_fun_relation =
        frame_proves_double_relation(&solver, fun, &fun_vars[3].name, &fun_vars[2].name);
    assert!(
        found_fun_relation,
        "expected budgeted kernel to learn FUN arg3 = 2*arg2 before derived sampling"
    );

    let sad = solver
        .problem
        .predicates()
        .iter()
        .find(|p| p.name == "SAD")
        .expect("missing SAD")
        .id;
    let sad_vars = solver
        .canonical_vars(sad)
        .expect("canonical vars for SAD")
        .to_vec();
    let found_sad_relation = solver.frames[1].lemmas.iter().any(|lemma| {
        lemma.predicate == sad
            && proves_double_relation(&lemma.formula, &sad_vars[0].name, &sad_vars[1].name)
    });
    assert!(
        !found_sad_relation,
        "tiny-budget kernel should return after fact-predicate progress instead of sampling derived predicates"
    );
}
