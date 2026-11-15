// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
use super::*;

pub(super) fn build(
    terms: &mut TermStore,
    source: &Source,
    owner: &CountedAdmission,
) -> Result<Vec<DistinctBridge>> {
    let mut requests = Vec::new();
    for &id in &source.order {
        owner.admit(1, 0)?;
        if source.kinds[id.index()] == Kind::Distinct {
            let TermData::App(_, args) = terms.get(id) else {
                return Err(Error::Invalid);
            };
            let [a, b] = args.as_slice() else {
                return Err(Error::Invalid);
            };
            memory::push(&mut requests, (id, *a, *b), owner)?;
        }
    }
    let mut bridges = Vec::new();
    if !requests.is_empty() {
        let mut builder = CountedTermBuilder::new(terms, owner)?;
        for &(source, a, b) in &requests {
            owner.admit(1, 0)?;
            let equality = builder.apply(CountedBuiltin::Eq, &[a, b])?;
            let negation = builder.apply(CountedBuiltin::Not, &[equality])?;
            let equivalence = builder.apply(CountedBuiltin::Eq, &[source, negation])?;
            memory::push(
                &mut bridges,
                DistinctBridge {
                    source,
                    equality,
                    negation,
                    equivalence,
                },
                owner,
            )?;
        }
        builder.finish()?;
    }
    drop(requests);
    owner.check()?;
    Ok(bridges)
}
