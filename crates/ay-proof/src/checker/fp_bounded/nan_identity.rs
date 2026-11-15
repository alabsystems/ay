// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The single abstract NaN theorem, not IEEE fp.eq or an FP evaluator.
//!
//! Only three literals are admitted: !isNaN(x), !isNaN(y), and structural
//! =(x,y), in any order/orientation, over one valid FP sort. Subjects are
//! opaque values: no recursive traversal, allocation, or evaluation is needed.
//! Global term/signature validation is still required at the bundle boundary.
//! SMT-LIB FloatingPoint defines one NaN value per format, with isNaN true
//! exactly for that value: <https://smt-lib.org/theories-FloatingPoint.shtml>.

use ay_core::{ProofId, Sort, Symbol, TermData, TermId, TermStore};

use super::ProofCheckError;

#[cfg(test)]
#[path = "nan_identity/tests.rs"]
mod tests;

/// A borrowed, fallible view. Each term lookup pays for its own read; charge
/// covers the additional constant-size inspection/comparison and control polls.
pub(crate) trait NanIdentityView<'a> {
    fn term(&mut self, id: TermId) -> Result<(&'a TermData, &'a Sort), ProofCheckError>;
    fn charge(&mut self, work: usize) -> Result<(), ProofCheckError>;
}

/// Errors, including transient cancellation, are terminal: do not fall back to
/// enumeration after a refused read/debit. Ordinary nonmatches still final-poll.
pub(crate) fn is_exact_nan_identity<'a>(
    view: &mut impl NanIdentityView<'a>,
    clause: &[TermId],
) -> Result<bool, ProofCheckError> {
    view.charge(0)?;
    let accepted = match_clause(view, clause)?;
    view.charge(0)?;
    Ok(accepted)
}

fn named<'a>(
    view: &mut impl NanIdentityView<'a>,
    symbol: &'a Symbol,
    expected: &str,
) -> Result<bool, ProofCheckError> {
    view.charge(2)?; // Symbol discriminant and constant-time byte length.
    let Symbol::Named(name) = symbol else {
        return Ok(false);
    };
    if name.len() != expected.len() {
        return Ok(false);
    }
    // Length first: an oversized/unrelated identity is never string-compared.
    view.charge(expected.len())?;
    Ok(name.as_str() == expected)
}

fn match_clause<'a>(
    view: &mut impl NanIdentityView<'a>,
    clause: &[TermId],
) -> Result<bool, ProofCheckError> {
    view.charge(1)?;
    if clause.len() != 3 {
        return Ok(false);
    }
    let mut subjects = [None; 2];
    let mut count = 0;
    let mut endpoints = None;
    for &literal in clause {
        let (data, sort) = view.term(literal)?;
        view.charge(2)?; // Boolean sort and term discriminant.
        if !matches!(sort, Sort::Bool) {
            return Ok(false);
        }
        match data {
            TermData::Not(atom) => {
                view.charge(1)?;
                if count == subjects.len() {
                    return Ok(false);
                }
                let (inner, inner_sort) = view.term(*atom)?;
                view.charge(3)?; // Boolean sort, app discriminant, arity.
                let TermData::App(symbol, args) = inner else {
                    return Ok(false);
                };
                if !matches!(inner_sort, Sort::Bool)
                    || args.len() != 1
                    || !named(view, symbol, "fp.isNaN")?
                {
                    return Ok(false);
                }
                view.charge(1)?;
                subjects[count] = Some(args[0]);
                count += 1;
            }
            TermData::App(symbol, args) => {
                view.charge(2)?; // Existing equality and arity.
                if endpoints.is_some() || args.len() != 2 || !named(view, symbol, "=")? {
                    return Ok(false);
                }
                view.charge(2)?;
                endpoints = Some([args[0], args[1]]);
            }
            _ => return Ok(false),
        }
    }
    view.charge(3)?;
    let ([Some(x), Some(y)], Some([left, right])) = (subjects, endpoints) else {
        return Ok(false);
    };
    view.charge(4)?;
    if !((x == left && y == right) || (x == right && y == left)) {
        return Ok(false);
    }
    // These are also both classification subjects, by the exact ID check.
    let (_, left_sort) = view.term(left)?;
    let (_, right_sort) = view.term(right)?;
    view.charge(6)?;
    Ok(matches!(
        (left_sort, right_sort),
        (Sort::FloatingPoint(eb, sb), Sort::FloatingPoint(other_eb, other_sb))
            if *eb >= 2 && *sb >= 2 && eb == other_eb && sb == other_sb
    ))
}

/// The in-memory checker retains its surrounding control envelope. This schema
/// is constant-size; only the raw snapshot adapter needs individual debit/polls.
pub(super) fn in_store(
    terms: &TermStore,
    step: ProofId,
    clause: &[TermId],
) -> Result<bool, ProofCheckError> {
    // Every match necessarily interprets these two heads. Opaque subjects
    // remain unrestricted; user declarations of the interpreted heads do not.
    if terms.is_declared_function("=") || terms.is_declared_function("fp.isNaN") {
        return Ok(false);
    }
    is_exact_nan_identity(&mut StoreView { terms, step }, clause)
}

struct StoreView<'a> {
    terms: &'a TermStore,
    step: ProofId,
}

impl<'a> NanIdentityView<'a> for StoreView<'a> {
    fn term(&mut self, id: TermId) -> Result<(&'a TermData, &'a Sort), ProofCheckError> {
        if id.index() >= self.terms.len() {
            return Err(ProofCheckError::InvalidTheoryLemma {
                step: self.step,
                reason: "NaN identity references a missing term".into(),
            });
        }
        Ok((self.terms.get(id), self.terms.sort(id)))
    }

    fn charge(&mut self, _: usize) -> Result<(), ProofCheckError> {
        Ok(())
    }
}
