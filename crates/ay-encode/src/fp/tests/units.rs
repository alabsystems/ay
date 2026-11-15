// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Private unit-check of constant DATA, not a public SAT/Unsafe credential.

use super::*;

fn literal(expr: &ChcExpr, budget: &mut WorkBudget<'_>) -> i32 {
    budget.charge(512).unwrap();
    match expr {
        ChcExpr::Var(v) => {
            assert_eq!(v.sort, ChcSort::Bool);
            let suffix = v.name.strip_prefix("__ay_fp_bits_").unwrap();
            let id: i32 = suffix.parse().unwrap();
            assert!(id > 0);
            id
        }
        ChcExpr::Op(ChcOp::Not, args) if args.len() == 1 => -literal(&args[0], budget),
        _ => panic!("constant DATA must contain only Boolean CNF literals"),
    }
}

fn collect(expr: &ChcExpr, rows: &mut Vec<Vec<i32>>, budget: &mut WorkBudget<'_>) {
    budget.admit(1024, 1024).unwrap();
    match expr {
        ChcExpr::Op(ChcOp::And, args) => {
            for child in args {
                collect(child, rows, budget);
            }
        }
        ChcExpr::Op(ChcOp::Or, args) => {
            assert!(args.len() <= 4);
            assert!(rows.len() < 4096);
            let mut row = Vec::new();
            row.try_reserve_exact(args.len()).unwrap();
            for arg in args {
                row.push(literal(arg, budget));
            }
            rows.push(row);
        }
        ChcExpr::Bool(true) => {}
        ChcExpr::Bool(false) => {
            assert!(rows.len() < 4096);
            rows.push(Vec::new());
        }
        _ => {
            assert!(rows.len() < 4096);
            rows.push(vec![literal(expr, budget)]);
        }
    }
}

pub(super) fn consistent(body: &ClauseBody, budget: &mut WorkBudget<'_>) -> bool {
    budget.admit(65_536, 1_048_576).unwrap();
    let mut rows = Vec::new();
    rows.try_reserve_exact(4096).unwrap();
    collect(body.constraint.as_ref().unwrap(), &mut rows, budget);
    let mut maximum = 0usize;
    for row in &rows {
        for lit in row {
            budget.charge(256).unwrap();
            maximum = maximum.max(lit.unsigned_abs() as usize);
        }
    }
    assert!(
        maximum <= 4096,
        "fixed constant fixture exceeded its scratch envelope"
    );
    budget.admit(4096, 8192).unwrap();
    let mut values = vec![0i8; maximum + 1];
    let mut result = true;
    for _ in 0..=maximum {
        budget.charge(256).unwrap();
        let mut progress = false;
        for row in &rows {
            budget.charge(256).unwrap();
            let mut satisfied = false;
            let mut unset = None;
            let mut count = 0usize;
            for &lit in row {
                budget.charge(256).unwrap();
                let value = values[lit.unsigned_abs() as usize];
                if value == if lit > 0 { 1 } else { -1 } {
                    satisfied = true;
                    break;
                }
                if value == 0 {
                    unset = Some(lit);
                    count += 1;
                }
            }
            if satisfied {
                continue;
            }
            if count == 0 {
                result = false;
                break;
            }
            if count == 1 {
                let lit = unset.unwrap();
                values[lit.unsigned_abs() as usize] = if lit > 0 { 1 } else { -1 };
                progress = true;
            }
        }
        if !result || !progress {
            break;
        }
    }
    if result {
        // No partial assignment is accepted as a constant-case success.
        for row in &rows {
            budget.charge(256).unwrap();
            assert!(row.iter().any(|&lit| {
                budget.charge(256).unwrap();
                values[lit.unsigned_abs() as usize] == if lit > 0 { 1 } else { -1 }
            }));
        }
    }
    drop(values);
    drop(rows);
    budget.charge(0).unwrap();
    result
}
