// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Shared predicate classification; interruption is never unsupported syntax.

use ay_core::{Sort, TermData, TermId, TermStore};
use ay_fp::{FpBuildError, FpConstruction};

use super::backend::{Encoder, Predicate};
use super::FpPredicateResult;

enum Dispatch {
    Encode(Predicate),
    /// The negation of a predicate: `distinct` over two rounding modes.
    EncodeNegated(Predicate),
    NotFp,
    Unsupported,
}

pub(in crate::executor::theories::fp) fn bitblast_fp_predicate_controlled(
    terms: &TermStore,
    fp: &mut FpConstruction<'_, '_>,
    term: TermId,
) -> Result<FpPredicateResult, FpBuildError> {
    dispatch(terms, fp, term)
}

pub(super) fn dispatch<E: Encoder>(
    terms: &TermStore,
    fp: &mut E,
    term: TermId,
) -> Result<FpPredicateResult, E::Error> {
    fp.checkpoint()?;
    let result = match classify(terms, fp, term)? {
        Dispatch::Encode(predicate) => match fp.predicate(predicate)? {
            Some(lit) => FpPredicateResult::Bitblasted(lit),
            None => FpPredicateResult::Unsupported,
        },
        Dispatch::EncodeNegated(predicate) => match fp.predicate(predicate)? {
            Some(lit) => FpPredicateResult::Bitblasted(-lit),
            None => FpPredicateResult::Unsupported,
        },
        Dispatch::NotFp => FpPredicateResult::NotFpPredicate,
        Dispatch::Unsupported => FpPredicateResult::Unsupported,
    };
    fp.checkpoint()?;
    Ok(result)
}

fn classify<E: Encoder>(terms: &TermStore, fp: &mut E, term: TermId) -> Result<Dispatch, E::Error> {
    let TermData::App(sym, args) = terms.get(term) else {
        return Ok(Dispatch::NotFp);
    };
    // The existing adapter matches both named and indexed operator spellings.
    let mut distinct_bv = false;
    if sym.name() == "distinct" {
        for &arg in args {
            fp.checkpoint()?;
            if matches!(terms.sort(arg), Sort::BitVec(..)) {
                distinct_bv = true;
                break;
            }
        }
    }
    if sym.name() == "distinct"
        && args
            .first()
            .is_some_and(|&a| ay_fp::rewriter::is_rounding_mode_sort(terms.sort(a)))
    {
        return Ok(if args.len() == 2 {
            Dispatch::EncodeNegated(Predicate::RmEq(args[0], args[1]))
        } else {
            Dispatch::Unsupported
        });
    }
    let predicate = match sym.name() {
        "fp.eq" if args.len() == 2 => Predicate::Eq(args[0], args[1]),
        "fp.lt" if args.len() == 2 => Predicate::Lt(args[0], args[1]),
        "fp.leq" if args.len() == 2 => Predicate::Le(args[0], args[1]),
        "fp.gt" if args.len() == 2 => Predicate::Gt(args[0], args[1]),
        "fp.geq" if args.len() == 2 => Predicate::Ge(args[0], args[1]),
        "fp.isNaN" if args.len() == 1 => Predicate::IsNan(args[0]),
        "fp.isInfinite" if args.len() == 1 => Predicate::IsInfinite(args[0]),
        "fp.isZero" if args.len() == 1 => Predicate::IsZero(args[0]),
        "fp.isNormal" if args.len() == 1 => Predicate::IsNormal(args[0]),
        "fp.isSubnormal" if args.len() == 1 => Predicate::IsSubnormal(args[0]),
        "fp.isPositive" if args.len() == 1 => Predicate::IsPositive(args[0]),
        "fp.isNegative" if args.len() == 1 => Predicate::IsNegative(args[0]),
        "=" if args.len() == 2 && matches!(terms.sort(args[0]), Sort::FloatingPoint(..)) => {
            // SMT identity differs from IEEE equality on NaN and signed zero.
            Predicate::StructuralEq(args[0], args[1])
        }
        "=" if args.len() == 2 && matches!(terms.sort(args[0]), Sort::BitVec(..)) => {
            Predicate::Bv(term)
        }
        // Rounding modes are three bits each; their equality is an encoded
        // predicate, never a free Tseitin atom (false-SAT #6189).
        "=" if args.len() == 2 && ay_fp::rewriter::is_rounding_mode_sort(terms.sort(args[0])) => {
            Predicate::RmEq(args[0], args[1])
        }
        "distinct" if distinct_bv => {
            if args.len() != 2 {
                return Ok(Dispatch::Unsupported);
            }
            Predicate::Bv(term)
        }
        "bvult" | "bvule" | "bvugt" | "bvuge" | "bvslt" | "bvsle" | "bvsgt" | "bvsge"
            if args.len() == 2 && matches!(terms.sort(args[0]), Sort::BitVec(..)) =>
        {
            Predicate::Bv(term)
        }
        // Value producers receive semantics from their consuming predicates.
        "fp.add" | "fp.sub" | "fp.mul" | "fp.div" | "fp.sqrt" | "fp.fma" | "fp.roundToIntegral"
        | "fp.rem" | "fp.abs" | "fp.neg" | "fp.min" | "fp.max" | "fp.to_ubv" | "fp.to_sbv"
        | "fp.to_ieee_bv" | "to_fp" | "to_fp_unsigned" => {
            return Ok(Dispatch::NotFp);
        }
        name if name.starts_with("fp.") => return Ok(Dispatch::Unsupported),
        _ => return Ok(Dispatch::NotFp),
    };
    Ok(Dispatch::Encode(predicate))
}
