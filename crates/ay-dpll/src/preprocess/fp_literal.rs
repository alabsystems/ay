// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Borrowed IEEE literal recognition shared by native propagation and models.
//! This inspects representation only; it neither evaluates nor copies fields.

use ay_core::term::{CountedTermError, TermConstructionAdmission};
use ay_core::{Constant, Sort, Symbol, TermData, TermId, TermStore};

fn bits(
    terms: &TermStore,
    term: TermId,
    width: u32,
    owner: &dyn TermConstructionAdmission,
) -> Result<bool, CountedTermError> {
    owner.admit(1, 0)?;
    if term.index() >= terms.len() {
        return Err(CountedTermError::InvalidInput);
    }
    Ok(
        matches!(terms.get(term), TermData::Const(Constant::BitVec { value, width: actual })
        if *actual == width && terms.sort(term) == &Sort::bitvec(width)
            && value.sign() != num_bigint::Sign::Minus && value.bits() <= u64::from(width)),
    )
}

pub(crate) fn is_value(
    terms: &TermStore,
    term: TermId,
    owner: &dyn TermConstructionAdmission,
) -> Result<bool, CountedTermError> {
    owner.admit(1, 0)?;
    if term.index() >= terms.len() {
        return Err(CountedTermError::InvalidInput);
    }
    if matches!(terms.sort(term), Sort::Uninterpreted(name) if name == "RoundingMode") {
        let TermData::App(Symbol::Named(name), args) = terms.get(term) else {
            return Ok(false);
        };
        owner.admit(name.len(), 0)?;
        owner.admit(args.len(), 0)?;
        let literal = args.is_empty()
            && matches!(
                name.as_str(),
                "RNE"
                    | "RNA"
                    | "RTP"
                    | "RTN"
                    | "RTZ"
                    | "roundNearestTiesToEven"
                    | "roundNearestTiesToAway"
                    | "roundTowardPositive"
                    | "roundTowardNegative"
                    | "roundTowardZero"
            )
            && !terms.is_declared_function(name);
        owner.check()?;
        return Ok(literal);
    }
    let Sort::FloatingPoint(eb, sb) = terms.sort(term) else {
        return Ok(false);
    };
    if *eb < 2 || *sb < 2 {
        return Ok(false);
    }
    let TermData::App(head, children) = terms.get(term) else {
        return Ok(false);
    };
    owner.admit(children.len(), 0)?;
    let result = match head {
        Symbol::Named(name) => {
            owner.admit(name.len(), 0)?;
            name == "fp"
                && !terms.is_declared_function(name)
                && children.len() == 3
                && bits(terms, children[0], 1, owner)?
                && bits(terms, children[1], *eb, owner)?
                && bits(terms, children[2], *sb - 1, owner)?
        }
        Symbol::Indexed(name, indices) => {
            owner.admit(name.len(), 0)?;
            owner.admit(indices.len(), 0)?;
            if indices.as_slice() != [*eb, *sb] || terms.is_declared_function(name) {
                false
            } else {
                match (name.as_str(), children.as_slice()) {
                    ("to_fp", [source]) => match eb.checked_add(*sb) {
                        Some(width) => bits(terms, *source, width, owner)?,
                        None => false,
                    },
                    ("+zero" | "-zero" | "+oo" | "-oo" | "NaN", []) => true,
                    _ => false,
                }
            }
        }
        _ => false,
    };
    owner.check()?;
    Ok(result)
}

#[cfg(test)]
mod tests {
    use super::*;
    use ay_core::original_query::{CountedAdmission, FiniteAdmissionGrant};
    use std::sync::Arc;

    #[test]
    fn rounding_literals_do_not_infer_meaning_from_free_or_declared_names() {
        let owner = CountedAdmission::new(
            FiniteAdmissionGrant::new(10_000, 32_768),
            None,
            Arc::new(|| false),
        )
        .unwrap();
        let mut terms = TermStore::new();
        let sort = Sort::Uninterpreted("RoundingMode".into());
        for name in [
            "RNE",
            "RNA",
            "RTP",
            "RTN",
            "RTZ",
            "roundNearestTiesToEven",
            "roundNearestTiesToAway",
            "roundTowardPositive",
            "roundTowardNegative",
            "roundTowardZero",
        ] {
            let value = terms.mk_app(Symbol::named(name), [], sort.clone());
            assert!(is_value(&terms, value, &owner).unwrap());
        }
        let free = terms.mk_var("RNE", sort.clone());
        assert!(!is_value(&terms, free, &owner).unwrap());
        let indexed = terms.mk_app(Symbol::indexed("RNE", vec![0]), [], sort.clone());
        assert!(!is_value(&terms, indexed, &owner).unwrap());
        let malformed = terms.mk_app(Symbol::named("RTP"), [], Sort::Bool);
        assert!(!is_value(&terms, malformed, &owner).unwrap());
        let rne = terms.mk_app(Symbol::named("RNE"), [], sort);
        terms.register_declared_function("RNE");
        assert!(!is_value(&terms, rne, &owner).unwrap());
    }
}
