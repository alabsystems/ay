// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Rabinowitsch's inverse-coordinate construction: f != 0 iff ∃ y. yf=1.
//! The native proof checker introduces its own formal coordinates; none of
//! these generated source-foreign TermIds supplies theorem/model authority.
use super::*;
use ay_core::term::CountedFieldBuiltin as Field;
pub(super) struct Encoded {
    pub roots: Vec<TermId>,
    pub auxiliaries: Vec<TermId>,
}
pub(super) fn encode(
    terms: &mut TermStore,
    signed: &[Lit],
    converter: &TacticModelConverter,
    owner: Owner<'_>,
) -> Result<Encoded, TacticFailure> {
    let mut result = Encoded {
        roots: Vec::new(),
        auxiliaries: Vec::new(),
    };
    reserve_counted(&mut result.roots, signed.len(), owner).map_err(|_| failed())?;
    let borrowed = super::super::field_to_bv::Borrowed(owner);
    let mut builder = CountedTermBuilder::with_admission(terms, &borrowed).map_err(|_| failed())?;
    for &lit in signed {
        pay(owner, 1)?;
        let TermData::App(Symbol::Named(name), args) = builder.terms().get(lit.atom) else {
            return Err(failed());
        };
        if args.len() < 2 || !matches!(name.as_str(), "=" | "distinct") {
            return Err(failed());
        }
        let equal = (name.as_str() == "=") == (lit.polarity == Polarity::Positive);
        if !equal && args.len() != 2
            || name.as_str() == "distinct" && lit.polarity == Polarity::Negative && args.len() != 2
        {
            return Err(failed());
        }
        if equal && name.as_str() == "=" {
            result.roots.push(lit.atom);
            continue;
        }
        let (a, b) = (args[0], args[1]);
        let Sort::FiniteField(field) = *builder.terms().sort(a) else {
            return Err(failed());
        };
        if builder.terms().sort(b) != &Sort::FiniteField(field) {
            return Err(failed());
        }
        if equal {
            result.roots.push(
                builder
                    .apply(CountedBuiltin::Eq, &[a, b])
                    .map_err(|_| failed())?,
            );
            continue;
        }
        let name = super::super::field_to_bv::fresh_scalar_name(
            builder.terms(),
            converter.namespace(),
            "@ay.ffsat.inverse",
            lit.atom.index(),
            owner,
        )?;
        reserve_counted(&mut result.auxiliaries, 1, owner).map_err(|_| failed())?;
        let auxiliary = builder
            .variable(&name, &Sort::FiniteField(field))
            .map_err(|_| failed())?;
        result.auxiliaries.push(auxiliary);
        let negative = builder
            .field_apply(Field::Neg, &[b])
            .map_err(|_| failed())?;
        let difference = builder
            .field_apply(Field::Add, &[a, negative])
            .map_err(|_| failed())?;
        let product = builder
            .field_apply(Field::Mul, &[auxiliary, difference])
            .map_err(|_| failed())?;
        let one = builder.finite_field(1, field).map_err(|_| failed())?;
        result.roots.push(
            builder
                .apply(CountedBuiltin::Eq, &[product, one])
                .map_err(|_| failed())?,
        );
    }
    owner.check().map_err(|_| failed())?;
    Ok(result)
}
