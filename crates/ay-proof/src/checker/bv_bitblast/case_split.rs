// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A lemma validated by cases on an `ite` condition `(= v K)`.
//!
//! A clause is valid exactly when it holds under every assignment with
//! `v = K` and under every assignment with `v != K`. Under the first, every
//! occurrence of the variable `v` may be read as the literal `K`; under the
//! second, every occurrence of the condition term `(= v K)` may be read as
//! `false`. Each case is therefore checked as the clause lowered with that
//! reading — valid for EVERY assignment, which is more than the case needs —
//! and the lemma is admitted only when both are.
//!
//! This is for circuits that agree only because of the case. external-codegen's IDIV
//! lowerings guard `bvsdiv`'s overflow: `(ite (= b #xff..ff) (bvneg a)
//! (bvsdiv a b))` against `(bvsdiv a b)`, spelled by `bvsdiv`'s definition.
//! With `b` free the two sides share every divider and differ only when
//! `b = -1`, where a full symbolic divider must be shown to compute `-a`: the
//! exact attempt exceeded every proof-size cap (measured 2026-09-30: 32 MB of
//! resolution at 32 bits, the construction clause cap at 64). Split, the
//! `b != -1` case is the same term on both sides, and the `b = -1` case
//! divides by the closed `(bvneg #xff..ff)` — a shift by zero.

use super::*;

/// Case-split candidates tried at most per lemma.
const MAX_CANDIDATES: usize = 2;
/// Source nodes walked looking for candidates.
const MAX_VISITS: usize = 1 << 16;

/// One case of a split on `condition`, `(= variable value)`.
#[derive(Clone, Copy, Debug)]
pub(super) struct Case {
    condition: TermId,
    variable: TermId,
    value: TermId,
    holds: bool,
}

impl Case {
    /// Both cases of every candidate condition below `clause`: `ite`
    /// conditions `(= v K)`, `v` a bit-vector variable and `K` a literal.
    pub(super) fn candidates(terms: &TermStore, clause: &[TermId]) -> Vec<[Self; 2]> {
        let mut found: Vec<[Self; 2]> = Vec::new();
        let mut seen = HashSet::new();
        let mut stack = clause.to_vec();
        while let Some(term) = stack.pop() {
            if seen.len() > MAX_VISITS || found.len() >= MAX_CANDIDATES {
                break;
            }
            if !seen.insert(term) {
                continue;
            }
            if let TermData::Ite(condition, ..) = terms.get(term) {
                if let Some((variable, value)) = variable_literal(terms, *condition) {
                    if !found.iter().any(|[case, _]| case.condition == *condition) {
                        let case = |holds| Self {
                            condition: *condition,
                            variable,
                            value,
                            holds,
                        };
                        found.push([case(true), case(false)]);
                    }
                }
            }
            stack.extend(terms.children(term));
        }
        found
    }
}

/// `(v, K)` for `(= v K)` or `(= K v)`, `v` a bit-vector variable and `K` a
/// bit-vector literal.
fn variable_literal(terms: &TermStore, condition: TermId) -> Option<(TermId, TermId)> {
    let TermData::App(Symbol::Named(name), args) = terms.get(condition) else {
        return None;
    };
    let [left, right] = args.as_slice() else {
        return None;
    };
    if name.as_str() != "=" || !matches!(terms.sort(*left), Sort::BitVec(_)) {
        return None;
    }
    let is_var = |term: TermId| matches!(terms.get(term), TermData::Var(..));
    let is_literal =
        |term: TermId| matches!(terms.get(term), TermData::Const(Constant::BitVec { .. }));
    if is_var(*left) && is_literal(*right) {
        Some((*left, *right))
    } else if is_literal(*left) && is_var(*right) {
        Some((*right, *left))
    } else {
        None
    }
}

impl Case {
    /// How the clause is read under this case (`hypotheses.rs`): the
    /// variable as the literal when the condition holds, or else the
    /// condition itself as `false`.
    pub(super) fn binding(&self) -> Result<(TermId, TermId), TermId> {
        if self.holds {
            Ok((self.variable, self.value))
        } else {
            Err(self.condition)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn an_ite_on_a_variable_literal_equality_is_a_candidate_in_both_cases() {
        let mut terms = TermStore::new();
        let a = terms.mk_var("a".to_string(), Sort::bitvec(8));
        let b = terms.mk_var("b".to_string(), Sort::bitvec(8));
        let minus_one = terms.mk_bitvec(num_bigint::BigInt::from(255), 8);
        let condition = terms.mk_app(Symbol::named("="), &[minus_one, b], Sort::Bool);
        let negated = terms.mk_app(Symbol::named("bvneg"), &[a], Sort::bitvec(8));
        let ite = terms.mk_ite_raw(condition, negated, a);
        let equality = terms.mk_app(Symbol::named("="), &[a, ite], Sort::Bool);
        let cases = Case::candidates(&terms, &[equality]);
        assert_eq!(cases.len(), 1);
        let [holds, fails] = cases[0];
        assert!(holds.holds && !fails.holds);
        assert_eq!(
            (holds.variable, holds.value, holds.condition),
            (b, minus_one, condition)
        );
        // An `ite` on anything else is not.
        let other = terms.mk_app(Symbol::named("="), &[a, b], Sort::Bool);
        let ite = terms.mk_ite_raw(other, negated, a);
        let equality = terms.mk_app(Symbol::named("="), &[a, ite], Sort::Bool);
        assert!(Case::candidates(&terms, &[equality]).is_empty());
    }
}
