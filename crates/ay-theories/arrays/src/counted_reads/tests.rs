// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_core::original_query::FiniteAdmissionGrant;
use num_bigint::BigInt;
use std::sync::Arc;

mod congruence;
mod model;
mod oracle;
mod provenance;
mod resources;
mod seal;
mod shape;

fn owner(work: u64, bytes: usize) -> CountedAdmission {
    CountedAdmission::new(
        FiniteAdmissionGrant::new(work, bytes),
        None,
        Arc::new(|| false),
    )
    .expect("original counted owner")
}

fn ample() -> CountedAdmission {
    owner(100_000_000, 256 * 1024 * 1024)
}

fn array_sort() -> Sort {
    Sort::array(Sort::bitvec(2), Sort::bitvec(8))
}

struct Fixture {
    terms: TermStore,
    base: TermId,
    write_index: TermId,
    read_index: TermId,
    value: TermId,
    stored: TermId,
    read: TermId,
    root: TermId,
}

enum IndexRelation {
    Same,
    Symbolic,
}

fn fixture(original: &CountedAdmission, relation: IndexRelation) -> Result<Fixture> {
    let mut terms = TermStore::try_new_with_admission(original)?;
    let mut builder = CountedTermBuilder::new(&mut terms, original)?;
    let base = builder.variable("a", &array_sort())?;
    let write_index = builder.variable("i", &Sort::bitvec(2))?;
    let read_index = match relation {
        IndexRelation::Same => write_index,
        IndexRelation::Symbolic => builder.variable("j", &Sort::bitvec(2))?,
    };
    let value = builder.variable("v", &Sort::bitvec(8))?;
    let stored = builder.apply(CountedBuiltin::Store, &[base, write_index, value])?;
    let read = builder.apply(CountedBuiltin::Select, &[stored, read_index])?;
    let root = builder.apply(CountedBuiltin::Eq, &[read, value])?;
    builder.finish()?;
    Ok(Fixture {
        terms,
        base,
        write_index,
        read_index,
        value,
        stored,
        read,
        root,
    })
}

fn application<'a>(terms: &'a TermStore, term: TermId, name: &str) -> &'a [TermId] {
    let TermData::App(symbol, args) = terms.get(term) else {
        panic!("expected raw {name} application, got {:?}", terms.get(term));
    };
    assert_eq!(symbol.name(), name);
    args
}

fn row_steps(closure: &CountedArrayReadClosure) -> (&Step, &Step) {
    let hit = closure
        .steps()
        .iter()
        .find(|step| matches!(step.derivation(), Derivation::Row1 { .. }))
        .expect("actual ROW1 step");
    let miss = closure
        .steps()
        .iter()
        .find(|step| matches!(step.derivation(), Derivation::Row2 { .. }))
        .expect("actual ROW2 step");
    (hit, miss)
}

fn derive_fixture(fixture: &mut Fixture, original: &CountedAdmission) -> CountedArrayReadClosure {
    CountedArrayReadClosure::derive(&mut fixture.terms, &[fixture.root], original)
        .expect("actual paid read closure")
}
