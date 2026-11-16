// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::super::{Executor, Model};
use ay_bv::BvModel;
use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::{Sort, TermId};
use num_bigint::BigInt;

struct Fixture {
    exec: Executor,
    model: Model,
    read_i: TermId,
    read_j: TermId,
    read_k: TermId,
}

/// Three reads `(select A i)`, `(select A j)`, `(select A k)` of an array with
/// an uninterpreted element sort, reachable only through uncommitted
/// disequality atoms, so no equality atom links any two of them. `index_bits`
/// assigns `i`, `j`, `k`; `None` leaves an index out of the model.
fn fixture(index_bits: [Option<u8>; 3]) -> Fixture {
    let mut exec = Executor::new();
    let element = Sort::Uninterpreted("E".to_string());
    let array = exec
        .ctx
        .terms
        .mk_var("A", Sort::array(Sort::bitvec(8), element));
    let indices: Vec<TermId> = ["i", "j", "k"]
        .into_iter()
        .map(|name| exec.ctx.terms.mk_var(name, Sort::bitvec(8)))
        .collect();
    let reads: Vec<TermId> = indices
        .iter()
        .map(|&index| exec.ctx.terms.mk_select(array, index))
        .collect();
    for pair in [(reads[0], reads[2]), (reads[1], reads[2])] {
        let equal = exec.ctx.terms.mk_eq(pair.0, pair.1);
        let assertion = exec.ctx.terms.mk_not(equal);
        exec.ctx.assertions.push(assertion);
    }
    let mut values = HashMap::default();
    for (&index, bits) in indices.iter().zip(index_bits) {
        if let Some(bits) = bits {
            values.insert(index, BigInt::from(bits));
        }
    }
    let mut model = Model::empty();
    model.bv_model = Some(BvModel {
        values,
        term_to_bits: HashMap::default(),
        bool_overrides: HashMap::default(),
    });
    Fixture {
        exec,
        model,
        read_i: reads[0],
        read_j: reads[1],
        read_k: reads[2],
    }
}

fn carrier(fixture: &Fixture, read: TermId) -> String {
    fixture
        .model
        .euf_model
        .as_ref()
        .and_then(|euf| euf.term_values.get(&read))
        .cloned()
        .expect("every read receives a carrier")
}

fn complete(index_bits: [Option<u8>; 3]) -> Fixture {
    let mut fixture = fixture(index_bits);
    let mut model = std::mem::replace(&mut fixture.model, Model::empty());
    fixture
        .exec
        .complete_uninterpreted_sort_model(&mut model, &[], None);
    fixture.model = model;
    fixture
}

/// RED before #carrier-select-congruence: `(select A i)` and `(select A j)`
/// under `i = j = #x00` received two different elements for one cell.
#[test]
fn reads_of_one_cell_share_one_carrier() {
    let fixture = complete([Some(0), Some(0), Some(1)]);
    assert_eq!(
        carrier(&fixture, fixture.read_i),
        carrier(&fixture, fixture.read_j)
    );
    assert_ne!(
        carrier(&fixture, fixture.read_i),
        carrier(&fixture, fixture.read_k)
    );
}

/// Different model indices are different cells: nothing is merged.
#[test]
fn reads_of_distinct_cells_keep_distinct_carriers() {
    let fixture = complete([Some(0), Some(1), Some(2)]);
    assert_ne!(
        carrier(&fixture, fixture.read_i),
        carrier(&fixture, fixture.read_j)
    );
    assert_ne!(
        carrier(&fixture, fixture.read_j),
        carrier(&fixture, fixture.read_k)
    );
}

/// An index the model does not determine proves no congruence: two reads at
/// undetermined indices stay apart, and neither joins the determined read.
#[test]
fn undetermined_index_merges_nothing() {
    let fixture = fixture([None, None, Some(0)]);
    let carriers = [fixture.read_i, fixture.read_j, fixture.read_k];
    assert_eq!(
        fixture
            .exec
            .select_congruent_carrier_pairs(&fixture.model, &carriers),
        [] as [(usize, usize); 0]
    );
}
