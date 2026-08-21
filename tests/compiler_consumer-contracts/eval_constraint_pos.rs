#![feature(contracts)]
// SURROGATE: models the pre-BigInt eval_constraint (2026-06 shape). Main's live
// eval_constraint has since gained assignment_covers_constraint and an
// eval_constraint_bigint fallback; the recorded call-node verdict is unaffected.
extern crate core;
use core::contracts::ensures;

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct PbLit {
    pub var: u32,
    pub negated: bool,
}

pub struct PbTerm {
    pub coeff: i128,
    pub lits: Vec<PbLit>,
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum PbRel {
    Ge,
    Eq,
}

pub struct PbConstraint {
    pub terms: Vec<PbTerm>,
    pub rel: PbRel,
    pub rhs: i128,
}

fn eval_lit(lit: PbLit, assignment: &[bool]) -> bool {
    let value = lit
        .var
        .checked_sub(1)
        .and_then(|index| usize::try_from(index).ok())
        .and_then(|index| assignment.get(index))
        .copied()
        .unwrap_or(false);
    if lit.negated {
        !value
    } else {
        value
    }
}

fn eval_term(term: &PbTerm, assignment: &[bool]) -> bool {
    term.lits
        .iter()
        .copied()
        .all(|lit| eval_lit(lit, assignment))
}

fn eval_terms(terms: &[PbTerm], assignment: &[bool]) -> i128 {
    terms
        .iter()
        .filter(|term| eval_term(term, assignment))
        .map(|term| term.coeff)
        .sum()
}

#[ensures(result == match constraint.rel {
    PbRel::Ge => eval_terms(&constraint.terms, assignment) >= constraint.rhs,
    PbRel::Eq => eval_terms(&constraint.terms, assignment) == constraint.rhs,
})]
pub fn eval_constraint(constraint: &PbConstraint, assignment: &[bool]) -> bool {
    let lhs = eval_terms(&constraint.terms, assignment);
    let rhs = constraint.rhs;
    match constraint.rel {
        PbRel::Ge => lhs >= rhs,
        PbRel::Eq => lhs == rhs,
    }
}
