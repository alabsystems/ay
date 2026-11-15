// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Authored producer-shaped PbTerm / Vec records, not a compiler export.

use super::*;
use ay_core::{DatatypeConstructor, DatatypeField, Symbol};

#[derive(Default)]
pub(super) struct Model {
    pub(super) leaves: HashMap<TermId, Arc<ModelValue>>,
    pub(super) applications: HashMap<TermId, ModelValue>,
}

impl ModelView for Model {
    fn leaf_value(&self, term: TermId) -> Option<ModelValue> {
        self.leaves.get(&term).map(|value| value.as_ref().clone())
    }

    fn uf_app_value(&self, term: TermId) -> Option<ModelValue> {
        self.applications.get(&term).cloned()
    }
}

impl Model {
    pub(super) fn install(&mut self, terms: &TermStore, values: Vec<CompletedArrayAssignment>) {
        for assignment in values {
            let (term, stamp, value) = assignment.into_parts();
            assert_eq!(Some(stamp), terms.entry_stamp(term));
            assert!(self.leaves.insert(term, value).is_none());
        }
    }
}

fn record(name: &str, constructor: &str, fields: Vec<DatatypeField>) -> Sort {
    Sort::Datatype(DatatypeSort::new(
        name,
        vec![DatatypeConstructor::new(constructor, fields)],
    ))
}

pub(super) fn app(terms: &mut TermStore, name: &str, args: &[TermId], sort: Sort) -> TermId {
    terms.mk_app(Symbol::named(name), args, sort)
}

pub(super) fn eq_bv(terms: &mut TermStore, left: TermId, value: u64, width: u32) -> TermId {
    let right = terms.mk_bitvec(BigInt::from(value), width);
    app(terms, "=", &[left, right], Sort::Bool)
}

pub(super) struct Fixture {
    pub(super) a: TermId,
    pub(super) b: TermId,
    pub(super) length: TermId,
    pub(super) capacity: TermId,
    pub(super) coefficient: TermId,
    pub(super) b_length: TermId,
    pub(super) roots: Vec<TermId>,
}

impl Fixture {
    pub(super) fn new(terms: &mut TermStore) -> Self {
        let vector = record(
            "Vec_bv8",
            "mkVec_bv8",
            vec![
                DatatypeField::new("fld_ptr", Sort::bitvec(64)),
                DatatypeField::new("fld_len", Sort::bitvec(64)),
                DatatypeField::new("fld_cap", Sort::bitvec(64)),
                DatatypeField::new("fld_data", Sort::array(Sort::bitvec(64), Sort::bitvec(8))),
            ],
        );
        let element = record(
            "PbTerm",
            "mkPbTerm",
            vec![
                DatatypeField::new("fld_coeff", Sort::bitvec(128)),
                DatatypeField::new("fld_lits", vector.clone()),
            ],
        );
        let array = Sort::array(Sort::bitvec(64), element.clone());
        let a = terms.mk_var("a", array.clone());
        let b = terms.mk_var("b", array);
        let index = terms.mk_bitvec(BigInt::from(0x8000_0000_0000_0001u64), 64);
        let a_cell = app(terms, "select", &[a, index], element.clone());
        let b_cell = app(terms, "select", &[b, index], element);
        let a_vec = app(terms, "fld_lits", &[a_cell], vector.clone());
        let b_vec = app(terms, "fld_lits", &[b_cell], vector);
        let length = app(terms, "fld_len", &[a_vec], Sort::bitvec(64));
        let capacity = app(terms, "fld_cap", &[b_vec], Sort::bitvec(64));
        let b_length = app(terms, "fld_len", &[b_vec], Sort::bitvec(64));
        let coefficient = app(terms, "fld_coeff", &[a_cell], Sort::bitvec(128));
        let roots = vec![
            app(terms, "=", &[a, b], Sort::Bool),
            eq_bv(terms, length, 65, 64),
            eq_bv(terms, capacity, 66, 64),
            eq_bv(terms, coefficient, 7, 128),
        ];
        Self {
            a,
            b,
            length,
            capacity,
            coefficient,
            b_length,
            roots,
        }
    }
}

pub(super) fn completion<'a>(
    terms: &'a TermStore,
    model: &'a Model,
    roots: &'a [TermId],
) -> ArrayCompletion<'a> {
    let result = crate::confirm_model_with_array_completion(terms, model, roots);
    assert!(matches!(result.verdict(), GateVerdict::ConfirmedSat));
    result.into_parts().1.unwrap()
}

pub(super) fn assert_value(terms: &TermStore, model: &Model, term: TermId, n: u64, width: u32) {
    let actual = Evaluator::new(terms, model).evaluate(term);
    let crate::EvalOutcome::Value(actual) = actual else {
        panic!("expected concrete recovered value");
    };
    assert!(value_eq(&actual, &ModelValue::bitvec(BigInt::from(n), width)).unwrap());
}
