// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Structural commutativity of correctly rounded IEEE addition/multiplication.
//! SMT-LIB FloatingPoint defines both from the exact real operation followed
//! by the same rounding mode; NaN is one abstract value and zero-sign rules
//! are symmetric. This is structural `=`, never IEEE `fp.eq` (NaN != NaN).
//! Subjects remain opaque, and no encoding enumeration or arithmetic is used.
//! Definition: <https://smt-lib.org/theories-FloatingPoint.shtml>.

use super::*;

fn read<'a>(
    terms: &'a TermStore,
    term: TermId,
    meter: &mut Meter<'_>,
) -> Option<(&'a TermData, &'a Sort)> {
    meter.node()?;
    meter.inspect(1)?;
    if term.index() >= terms.len() {
        return meter.refuse();
    }
    Some((terms.get(term), terms.sort(term)))
}

fn literal_is_theorem(terms: &TermStore, literal: TermId, meter: &mut Meter<'_>) -> Option<bool> {
    let mut term = literal;
    let mut negative = false;
    let mut negations = 0;
    let pair = loop {
        let (data, sort) = read(terms, term, meter)?;
        if sort != &Sort::Bool {
            return Some(false);
        }
        meter.inspect(16)?;
        match data {
            TermData::Not(inner) if negations < 2 => {
                term = *inner;
                negative = !negative;
                negations += 1;
            }
            TermData::App(Symbol::Named(name), args)
                if args.len() == 2
                    && ((!negative && name == "=") || (negative && name == "distinct"))
                    && !terms.is_declared_function(name) =>
            {
                break [args[0], args[1]];
            }
            _ => return Some(false),
        }
    };
    let (left, left_sort) = read(terms, pair[0], meter)?;
    let (right, right_sort) = read(terms, pair[1], meter)?;
    if !matches!(left_sort, Sort::FloatingPoint(eb, sb) if *eb >= 2 && *sb >= 2)
        || left_sort != right_sort
    {
        return Some(false);
    }
    let (
        TermData::App(Symbol::Named(left_op), left_args),
        TermData::App(Symbol::Named(right_op), right_args),
    ) = (left, right)
    else {
        return Some(false);
    };
    meter.inspect(32)?;
    if !matches!(left_op.as_str(), "fp.add" | "fp.mul")
        || left_op != right_op
        || terms.is_declared_function(left_op)
        || left_args.len() != 3
        || right_args.len() != 3
        || left_args[0] != right_args[0]
        || left_args[1] != right_args[2]
        || left_args[2] != right_args[1]
    {
        return Some(false);
    }
    let (_, mode_sort) = read(terms, left_args[0], meter)?;
    let (_, a_sort) = read(terms, left_args[1], meter)?;
    let (_, b_sort) = read(terms, left_args[2], meter)?;
    Some(
        matches!(mode_sort, Sort::Uninterpreted(name) if name == "RoundingMode")
            && a_sort == left_sort
            && b_sort == left_sort,
    )
}

pub(super) fn clause_is_theorem(
    terms: &TermStore,
    clause: &[TermId],
    meter: &mut Meter<'_>,
) -> Option<bool> {
    meter.inspect(0)?;
    for &literal in clause {
        if literal_is_theorem(terms, literal, meter)? {
            meter.inspect(0)?;
            return Some(true);
        }
    }
    meter.inspect(0)?;
    Some(false)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn wide_commutativity_is_checked_with_the_original_budget_and_refuses_forgery() {
        for (operation, relation, wrong_mode, wrong_sort, valid) in [
            (Symbol::named("fp.mul"), "=", false, false, true),
            (Symbol::named("fp.add"), "=", false, false, true),
            (Symbol::named("fp.mul"), "fp.eq", false, false, false),
            (Symbol::named("fp.sub"), "=", false, false, false),
            (Symbol::named("fp.mul"), "=", true, false, false),
            (Symbol::named("fp.mul"), "=", false, true, false),
            (Symbol::indexed("fp.mul", vec![0]), "=", false, false, false),
        ] {
            let mut terms = TermStore::new();
            let sort = Sort::FloatingPoint(15, 113);
            let mode_sort = Sort::Uninterpreted("RoundingMode".into());
            let mode = terms.mk_var("mode", mode_sort.clone());
            let other_mode = terms.mk_var("other_mode", mode_sort);
            let a = terms.mk_var("a", sort.clone());
            let b = terms.mk_var(
                "b",
                if wrong_sort {
                    Sort::FloatingPoint(8, 24)
                } else {
                    sort.clone()
                },
            );
            let left = terms.mk_app(operation.clone(), [mode, a, b], sort.clone());
            let right = terms.mk_app(
                operation,
                [if wrong_mode { other_mode } else { mode }, b, a],
                sort,
            );
            let equality = terms.mk_app(Symbol::named(relation), [left, right], Sort::Bool);
            let distinct = terms.mk_app(Symbol::named("distinct"), [left, right], Sort::Bool);
            let not_distinct = terms.mk_not_raw(distinct);
            let mut work = 0usize;
            let mut bytes = 0usize;
            let result = validate_fp_ground_eval_with_progress(
                &terms,
                ProofId(0),
                &[equality],
                &mut |w, b| {
                    work = work.saturating_add(w);
                    bytes = bytes.saturating_add(b);
                    work <= 10_000 && bytes <= 64 * 1024
                },
            );
            assert_eq!(
                result.is_ok(),
                valid,
                "{result:?}; work={work}, bytes={bytes}"
            );
            if valid {
                assert!(validate_fp_ground_eval(&terms, ProofId(0), &[not_distinct]).is_ok());
            }
            assert!(matches!(
                validate_fp_ground_eval_with_progress(
                    &terms,
                    ProofId(0),
                    &[equality],
                    &mut |_, _| false
                ),
                Err(ProofCheckError::ResourceLimit)
            ));
        }
    }
}
