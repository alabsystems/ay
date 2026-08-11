// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Equiv/ITE/XOR tautology rules and eq_reflexive Alethe rule.
//!
//! Negation-decomposition rules (`not_and`, `not_or`, etc.) and `contraction`
//! are in [`boolean_negation`]. Uses shared utilities from the `boolean` module.

use ay_core::{ProofId, TermId, TermStore};

use super::boolean::{
    apps, check_any_candidate, clause_matches_expected, clause_matches_unordered, decode_app, err,
    ites, make_err, negated_apps, negated_ites, ExpectedLit,
};
use super::ProofCheckError;

// ---- Equiv tautology rules ----

pub(crate) fn validate_equiv_pos1(
    terms: &TermStore,
    step: ProofId,
    clause: &[TermId],
) -> Result<(), ProofCheckError> {
    check_any_candidate(
        step,
        "equiv_pos1",
        "clause must contain (not (= ...))",
        negated_apps(terms, clause, "="),
        |(not_eq, args)| {
            if args.len() != 2 {
                return Err("equality must be binary");
            }
            let expected = [
                ExpectedLit::Lit(not_eq),
                ExpectedLit::Lit(args[0]),
                ExpectedLit::Not(args[1]),
            ];
            if clause_matches_expected(terms, clause, &expected) {
                Ok(())
            } else {
                Err("clause shape does not match equality")
            }
        },
    )
}

pub(crate) fn validate_equiv_pos2(
    terms: &TermStore,
    step: ProofId,
    clause: &[TermId],
) -> Result<(), ProofCheckError> {
    check_any_candidate(
        step,
        "equiv_pos2",
        "clause must contain (not (= ...))",
        negated_apps(terms, clause, "="),
        |(not_eq, args)| {
            if args.len() != 2 {
                return Err("equality must be binary");
            }
            let expected = [
                ExpectedLit::Lit(not_eq),
                ExpectedLit::Not(args[0]),
                ExpectedLit::Lit(args[1]),
            ];
            if clause_matches_expected(terms, clause, &expected) {
                Ok(())
            } else {
                Err("clause shape does not match equality")
            }
        },
    )
}

pub(crate) fn validate_equiv_neg1(
    terms: &TermStore,
    step: ProofId,
    clause: &[TermId],
) -> Result<(), ProofCheckError> {
    check_any_candidate(
        step,
        "equiv_neg1",
        "clause must contain an equality",
        apps(terms, clause, "="),
        |(eq_term, args)| {
            if args.len() != 2 {
                return Err("equality must be binary");
            }
            let expected = [
                ExpectedLit::Lit(eq_term),
                ExpectedLit::Not(args[0]),
                ExpectedLit::Not(args[1]),
            ];
            if clause_matches_expected(terms, clause, &expected) {
                Ok(())
            } else {
                Err("clause shape does not match equality")
            }
        },
    )
}

pub(crate) fn validate_equiv_neg2(
    terms: &TermStore,
    step: ProofId,
    clause: &[TermId],
) -> Result<(), ProofCheckError> {
    check_any_candidate(
        step,
        "equiv_neg2",
        "clause must contain an equality",
        apps(terms, clause, "="),
        |(eq_term, args)| {
            if args.len() != 2 {
                return Err("equality must be binary");
            }
            let expected = [eq_term, args[0], args[1]];
            if clause_matches_unordered(clause, &expected) {
                Ok(())
            } else {
                Err("clause shape does not match equality")
            }
        },
    )
}

// ---- ITE tautology rules ----

pub(crate) fn validate_ite_pos1(
    terms: &TermStore,
    step: ProofId,
    clause: &[TermId],
) -> Result<(), ProofCheckError> {
    check_any_candidate(
        step,
        "ite_pos1",
        "clause must contain (not (ite ...))",
        negated_ites(terms, clause),
        |(not_ite, (c, _t, e))| {
            let expected = [not_ite, c, e];
            if clause_matches_unordered(clause, &expected) {
                Ok(())
            } else {
                Err("clause shape does not match ite")
            }
        },
    )
}

pub(crate) fn validate_ite_pos2(
    terms: &TermStore,
    step: ProofId,
    clause: &[TermId],
) -> Result<(), ProofCheckError> {
    check_any_candidate(
        step,
        "ite_pos2",
        "clause must contain (not (ite ...))",
        negated_ites(terms, clause),
        |(not_ite, (c, t, _e))| {
            let expected = [
                ExpectedLit::Lit(not_ite),
                ExpectedLit::Not(c),
                ExpectedLit::Lit(t),
            ];
            if clause_matches_expected(terms, clause, &expected) {
                Ok(())
            } else {
                Err("clause shape does not match ite")
            }
        },
    )
}

pub(crate) fn validate_ite_neg1(
    terms: &TermStore,
    step: ProofId,
    clause: &[TermId],
) -> Result<(), ProofCheckError> {
    check_any_candidate(
        step,
        "ite_neg1",
        "clause must contain an ite term",
        ites(terms, clause),
        |(ite, (c, _t, e))| {
            let expected = [
                ExpectedLit::Lit(ite),
                ExpectedLit::Lit(c),
                ExpectedLit::Not(e),
            ];
            if clause_matches_expected(terms, clause, &expected) {
                Ok(())
            } else {
                Err("clause shape does not match ite")
            }
        },
    )
}

pub(crate) fn validate_ite_neg2(
    terms: &TermStore,
    step: ProofId,
    clause: &[TermId],
) -> Result<(), ProofCheckError> {
    check_any_candidate(
        step,
        "ite_neg2",
        "clause must contain an ite term",
        ites(terms, clause),
        |(ite, (c, t, _e))| {
            let expected = [
                ExpectedLit::Lit(ite),
                ExpectedLit::Not(c),
                ExpectedLit::Not(t),
            ];
            if clause_matches_expected(terms, clause, &expected) {
                Ok(())
            } else {
                Err("clause shape does not match ite")
            }
        },
    )
}

// ---- XOR tautology rules ----

pub(crate) fn validate_xor_pos1(
    terms: &TermStore,
    step: ProofId,
    clause: &[TermId],
) -> Result<(), ProofCheckError> {
    check_any_candidate(
        step,
        "xor_pos1",
        "clause must contain (not (xor ...))",
        negated_apps(terms, clause, "xor"),
        |(not_xor, args)| {
            if args.len() != 2 {
                return Err("xor must be binary");
            }
            let expected = [not_xor, args[0], args[1]];
            if clause_matches_unordered(clause, &expected) {
                Ok(())
            } else {
                Err("clause shape does not match xor")
            }
        },
    )
}

pub(crate) fn validate_xor_pos2(
    terms: &TermStore,
    step: ProofId,
    clause: &[TermId],
) -> Result<(), ProofCheckError> {
    check_any_candidate(
        step,
        "xor_pos2",
        "clause must contain (not (xor ...))",
        negated_apps(terms, clause, "xor"),
        |(not_xor, args)| {
            if args.len() != 2 {
                return Err("xor must be binary");
            }
            let expected = [
                ExpectedLit::Lit(not_xor),
                ExpectedLit::Not(args[0]),
                ExpectedLit::Not(args[1]),
            ];
            if clause_matches_expected(terms, clause, &expected) {
                Ok(())
            } else {
                Err("clause shape does not match xor")
            }
        },
    )
}

pub(crate) fn validate_xor_neg1(
    terms: &TermStore,
    step: ProofId,
    clause: &[TermId],
) -> Result<(), ProofCheckError> {
    check_any_candidate(
        step,
        "xor_neg1",
        "clause must contain a xor term",
        apps(terms, clause, "xor"),
        |(xor_term, args)| {
            if args.len() != 2 {
                return Err("xor must be binary");
            }
            let expected = [
                ExpectedLit::Lit(xor_term),
                ExpectedLit::Lit(args[0]),
                ExpectedLit::Not(args[1]),
            ];
            if clause_matches_expected(terms, clause, &expected) {
                Ok(())
            } else {
                Err("clause shape does not match xor")
            }
        },
    )
}

pub(crate) fn validate_xor_neg2(
    terms: &TermStore,
    step: ProofId,
    clause: &[TermId],
) -> Result<(), ProofCheckError> {
    check_any_candidate(
        step,
        "xor_neg2",
        "clause must contain a xor term",
        apps(terms, clause, "xor"),
        |(xor_term, args)| {
            if args.len() != 2 {
                return Err("xor must be binary");
            }
            let expected = [
                ExpectedLit::Lit(xor_term),
                ExpectedLit::Not(args[0]),
                ExpectedLit::Lit(args[1]),
            ];
            if clause_matches_expected(terms, clause, &expected) {
                Ok(())
            } else {
                Err("clause shape does not match xor")
            }
        },
    )
}

// ---- Derived (premise-based) rules ----

pub(crate) fn validate_eq_reflexive(
    terms: &TermStore,
    step: ProofId,
    clause: &[TermId],
) -> Result<(), ProofCheckError> {
    if clause.len() != 1 {
        return err(step, "eq_reflexive", "clause must have exactly 1 literal");
    }
    let args = decode_app(terms, clause[0], "=")
        .ok_or_else(|| make_err(step, "eq_reflexive", "literal must be an equality"))?;
    if args.len() != 2 {
        return err(step, "eq_reflexive", "equality must be binary");
    }
    if args[0] != args[1] {
        return err(step, "eq_reflexive", "equality must be reflexive");
    }
    Ok(())
}

/// `eq_symmetric`: `(cl (= (= a b) (= b a)))` — an equivalence between a
/// binary equality and its argument-swapped orientation.
pub(crate) fn validate_eq_symmetric(
    terms: &TermStore,
    step: ProofId,
    clause: &[TermId],
) -> Result<(), ProofCheckError> {
    if clause.len() != 1 {
        return err(step, "eq_symmetric", "clause must have exactly 1 literal");
    }
    let outer = decode_app(terms, clause[0], "=")
        .ok_or_else(|| make_err(step, "eq_symmetric", "literal must be an equivalence"))?;
    if outer.len() != 2 {
        return err(step, "eq_symmetric", "equivalence must be binary");
    }
    let lhs = decode_app(terms, outer[0], "=")
        .ok_or_else(|| make_err(step, "eq_symmetric", "lhs must be an equality"))?;
    let rhs = decode_app(terms, outer[1], "=")
        .ok_or_else(|| make_err(step, "eq_symmetric", "rhs must be an equality"))?;
    if lhs.len() != 2 || rhs.len() != 2 {
        return err(step, "eq_symmetric", "equalities must be binary");
    }
    if lhs[0] != rhs[1] || lhs[1] != rhs[0] {
        return err(step, "eq_symmetric", "rhs must be the argument-swapped lhs");
    }
    Ok(())
}
