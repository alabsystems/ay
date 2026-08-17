// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#[path = "generator/expressions.rs"]
mod expressions;

use super::super::recognize_fp_ground_eval;
use ay_core::{BitVecSort, Sort, Symbol, TermId, TermStore};
use expressions::{random_fp_expr, random_literal};
use num_bigint::BigInt;

pub(super) struct AcceptedClause {
    pub(super) declarations: Vec<String>,
    pub(super) literals: Vec<String>,
}

pub(super) struct Prng(u64);

impl Prng {
    pub(super) fn next(&mut self) -> u64 {
        self.0 ^= self.0 >> 12;
        self.0 ^= self.0 << 25;
        self.0 ^= self.0 >> 27;
        self.0.wrapping_mul(0x2545_F491_4F6C_DD1D)
    }

    pub(super) fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }

    pub(super) fn chance(&mut self, percent: u64) -> bool {
        self.below(100) < percent
    }
}

#[derive(Clone)]
pub(super) struct T {
    pub(super) id: TermId,
    pub(super) text: String,
}

pub(super) fn bv_text(value: u64, width: u32) -> String {
    let mut text = String::from("#b");
    for bit in (0..width).rev() {
        text.push(if (value >> bit) & 1 == 1 { '1' } else { '0' });
    }
    text
}

pub(super) fn fp_sort(format: (u32, u32)) -> Sort {
    Sort::FloatingPoint(format.0, format.1)
}

pub(super) fn accepted_clauses(seed: u64, rounds: u32, with_vars: bool) -> Vec<AcceptedClause> {
    let mut rng = Prng(seed);
    let mut accepted = Vec::new();
    for _ in 0..rounds {
        let (terms, clause_ids, clause) = random_clause(&mut rng, with_vars);
        if recognize_fp_ground_eval(&terms, &clause_ids) {
            accepted.push(clause);
        }
    }
    accepted
}

fn random_clause(rng: &mut Prng, with_vars: bool) -> (TermStore, Vec<TermId>, AcceptedClause) {
    let mut terms = TermStore::new();
    let format = match rng.below(3) {
        0 => (5u32, 11u32),
        1 => (8, 24),
        _ => (11, 53),
    };
    let mut declarations = Vec::new();
    let mut vars = Vec::new();
    let mut clause_ids = Vec::new();
    let mut literals = Vec::new();
    if with_vars {
        add_variables(
            &mut terms,
            rng,
            format,
            &mut declarations,
            &mut vars,
            &mut clause_ids,
            &mut literals,
        );
    }
    let extra = 1 + rng.below(2);
    for _ in 0..extra {
        let literal = random_literal(&mut terms, rng, format, 2, &vars);
        clause_ids.push(literal.id);
        literals.push(literal.text);
    }
    (
        terms,
        clause_ids,
        AcceptedClause {
            declarations,
            literals,
        },
    )
}

#[allow(clippy::too_many_arguments)]
fn add_variables(
    terms: &mut TermStore,
    rng: &mut Prng,
    format: (u32, u32),
    declarations: &mut Vec<String>,
    vars: &mut Vec<T>,
    clause_ids: &mut Vec<TermId>,
    literals: &mut Vec<String>,
) {
    add_fp_variables(terms, rng, format, declarations, vars, clause_ids, literals);
    if rng.chance(30) {
        declarations.push("(declare-const b0 Bool)".to_string());
        clause_ids.push(terms.mk_var("b0".to_string(), Sort::Bool));
        literals.push("b0".to_string());
    }
    if rng.chance(25) {
        add_sign_variable(terms, rng, format, declarations, clause_ids, literals);
    }
}

#[allow(clippy::too_many_arguments)]
fn add_fp_variables(
    terms: &mut TermStore,
    rng: &mut Prng,
    format: (u32, u32),
    declarations: &mut Vec<String>,
    vars: &mut Vec<T>,
    clause_ids: &mut Vec<TermId>,
    literals: &mut Vec<String>,
) {
    let count = 1 + rng.below(2);
    for index in 0..count {
        let name = format!("v{index}");
        let variable_format = if rng.chance(50) { (5, 11) } else { format };
        declarations.push(format!(
            "(declare-const {name} (_ FloatingPoint {} {}))",
            variable_format.0, variable_format.1
        ));
        let variable = T {
            id: terms.mk_var(name.clone(), fp_sort(variable_format)),
            text: name,
        };
        if rng.chance(65) {
            let ground = random_fp_expr(terms, rng, variable_format, 1, &[]);
            let equality =
                terms.mk_app(Symbol::named("="), vec![variable.id, ground.id], Sort::Bool);
            clause_ids.push(terms.mk_not(equality));
            literals.push(format!("(not (= {} {}))", variable.text, ground.text));
        }
        if variable_format == format {
            vars.push(variable);
        }
    }
}

fn add_sign_variable(
    terms: &mut TermStore,
    rng: &mut Prng,
    format: (u32, u32),
    declarations: &mut Vec<String>,
    clause_ids: &mut Vec<TermId>,
    literals: &mut Vec<String>,
) {
    declarations.push("(declare-const s0 (_ BitVec 1))".to_string());
    let sign = terms.mk_var("s0".to_string(), Sort::BitVec(BitVecSort::new(1)));
    let exponent = terms.mk_bitvec(BigInt::from(0u64), format.0);
    let significand = terms.mk_bitvec(BigInt::from(1u64), format.1 - 1);
    let value = terms.mk_app(
        Symbol::named("fp"),
        vec![sign, exponent, significand],
        fp_sort(format),
    );
    let name = ["fp.isZero", "fp.isSubnormal", "fp.isNegative"][rng.below(3) as usize];
    let predicate = terms.mk_app(Symbol::named(name), vec![value], Sort::Bool);
    let text = format!(
        "({name} (fp s0 {} {}))",
        bv_text(0, format.0),
        bv_text(1, format.1 - 1)
    );
    if rng.chance(50) {
        clause_ids.push(terms.mk_not(predicate));
        literals.push(format!("(not {text})"));
    } else {
        clause_ids.push(predicate);
        literals.push(text);
    }
}
