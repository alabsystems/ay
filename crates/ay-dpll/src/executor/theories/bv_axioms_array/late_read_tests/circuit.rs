// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::*;
use ay_core::{CnfClause, TermStore};

pub(super) fn raw_select(terms: &mut TermStore, array: TermId, index: TermId) -> TermId {
    let sort = terms.sort(array).array_element().unwrap().clone();
    terms.mk_app(Symbol::named("select"), [array, index], sort)
}

pub(super) fn materialize<'a>(
    executor: &'a Executor,
    roots: &[TermId],
    reads: Option<&LateArrayReads>,
    booleans: &[TermId],
) -> BvSolver<'a> {
    let mut bv = BvSolver::new(&executor.ctx.terms);
    // These are the already-live Boolean atoms normally provided by the
    // skeleton/linking path, not asserted truth values or fake bit mappings.
    for &term in booleans {
        assert!(bv.ensure_bool_literal(term).is_some());
    }
    executor.materialize_array_bv_terms(&mut bv, roots, reads);
    bv
}

pub(super) fn condition_map(bv: &BvSolver<'_>, condition: TermId) -> BTreeMap<TermId, u32> {
    let literal = bv.bool_to_var()[&condition];
    assert!(literal > 0, "fixture uses a positive Boolean variable");
    BTreeMap::from([(condition, literal as u32)])
}

pub(super) struct Circuit {
    pub(super) clauses: Vec<CnfClause>,
    pub(super) axioms: Vec<CnfClause>,
    pub(super) num_vars: u32,
    observed: Vec<Vec<i32>>,
}

impl Circuit {
    pub(super) fn new(
        executor: &Executor,
        bv: &BvSolver<'_>,
        roots: &[TermId],
        reads: Option<&LateArrayReads>,
        observed: &[TermId],
        conditions: &BTreeMap<TermId, u32>,
    ) -> Self {
        Self::with_offset(executor, bv, roots, reads, observed, conditions, 0)
    }

    pub(super) fn with_offset(
        executor: &Executor,
        bv: &BvSolver<'_>,
        roots: &[TermId],
        reads: Option<&LateArrayReads>,
        observed: &[TermId],
        conditions: &BTreeMap<TermId, u32>,
        offset: u32,
    ) -> Self {
        let generated = executor.generate_array_bv_axioms(
            bv,
            offset,
            offset + bv.num_vars(),
            roots,
            conditions,
            reads,
        );
        let observed = observed
            .iter()
            .map(|&term| {
                let bits = if let Some(bits) = bv.get_term_bits(term) {
                    bits.to_vec()
                } else {
                    vec![*bv
                        .bool_to_var()
                        .get(&term)
                        .expect("observed term is encoded")]
                };
                bits.into_iter()
                    .map(|bit| offset_bv_bit(bit, offset))
                    .collect()
            })
            .collect();
        let mut clauses: Vec<_> = bv
            .clauses()
            .iter()
            .map(|clause| {
                CnfClause::new(
                    clause
                        .0
                        .iter()
                        .map(|&bit| offset_bv_bit(bit, offset))
                        .collect(),
                )
            })
            .collect();
        clauses.extend_from_slice(&generated.clauses);
        Self {
            num_vars: offset + bv.num_vars() + generated.num_vars,
            clauses,
            axioms: generated.clauses,
            observed,
        }
    }

    /// Enumerate complete assignments, not just clauses reachable from an
    /// expected model. Projection records existential auxiliary-bit choices;
    /// exact table equality proves both rejection and valid-model coverage.
    pub(super) fn check_relation(&self, expected: impl Fn(&[u64]) -> bool) {
        assert!(self.num_vars <= 18, "tiny exhaustive fixture only");
        let width: usize = self.observed.iter().map(Vec::len).sum();
        assert!(width <= 12);
        for literal in self.clauses.iter().flat_map(|clause| &clause.0) {
            assert!(literal.unsigned_abs() > 0 && literal.unsigned_abs() <= self.num_vars);
        }
        let mut admitted = vec![false; 1usize << width];
        for assignment in 0..(1u64 << self.num_vars) {
            if self.clauses.iter().all(|clause| {
                clause
                    .0
                    .iter()
                    .any(|&literal| literal_value(assignment, literal))
            }) {
                let mut key = 0;
                let mut shift = 0;
                for bits in &self.observed {
                    for &bit in bits {
                        key |= usize::from(literal_value(assignment, bit)) << shift;
                        shift += 1;
                    }
                }
                admitted[key] = true;
            }
        }
        for (key, actual) in admitted.into_iter().enumerate() {
            let mut remaining = key as u64;
            let values: Vec<_> = self
                .observed
                .iter()
                .map(|bits| {
                    let value = remaining & ((1u64 << bits.len()) - 1);
                    remaining >>= bits.len();
                    value
                })
                .collect();
            assert_eq!(actual, expected(&values), "semantic tuple {values:?}");
        }
    }
}

fn literal_value(assignment: u64, literal: i32) -> bool {
    let variable = (assignment >> (literal.unsigned_abs() - 1)) & 1 != 0;
    if literal > 0 {
        variable
    } else {
        !variable
    }
}
