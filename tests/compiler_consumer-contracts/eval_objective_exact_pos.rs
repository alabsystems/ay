// W8 POSITIVE — real ay-pb eval_objective_exact: result == the checked fold it IS.
#![feature(contracts)]
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
pub struct PbObjective {
    pub terms: Vec<PbTerm>,
}
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ObjectiveEvalError {
    Overflow,
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
fn eval_terms_checked(terms: &[PbTerm], assignment: &[bool]) -> Result<i128, ObjectiveEvalError> {
    terms
        .iter()
        .filter(|term| eval_term(term, assignment))
        .try_fold(0i128, |sum, term| {
            sum.checked_add(term.coeff)
                .ok_or(ObjectiveEvalError::Overflow)
        })
}

#[ensures(result == eval_terms_checked(&objective.terms, assignment))]
pub fn eval_objective_exact(
    objective: &PbObjective,
    assignment: &[bool],
) -> Result<i128, ObjectiveEvalError> {
    eval_terms_checked(&objective.terms, assignment)
}
