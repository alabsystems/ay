// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Admission of the ordinary unit-chain graph, not an alternate proof search.
//! Root ordering, visible-unit fast path, fallback BFS and reverse trail scan
//! are shared with every ordinary caller.

use super::*;
use crate::counted_storage::{try_reserve, Result as AdmissionResult};
use crate::decision_trace::counted_decision::invalid;
use crate::solver::conflict_analysis_minimize_lrat::root;
use ay_core::original_query::CountedAdmissionError;
use std::convert::Infallible;

mod counted;
mod filter;
#[cfg(test)]
mod tests;

pub(in crate::solver) trait Policy: root::Policy {
    fn enter_chain(&self, s: &Solver, roots: &[usize]) -> Result<(), Self::Error>;
    fn mark(&self, s: &mut Solver) -> Result<(), Self::Error>;
    fn chain(&self, s: &mut Solver, id: u64) -> Result<(), Self::Error>;
    fn sort(&self, values: &mut [(usize, Literal, u64)]) -> Result<(), Self::Error>;
    fn new_filter(&self, len: usize) -> Result<DetHashSet<Literal>, Self::Error>;
    fn filter(&self, values: &DetHashSet<Literal>) -> Result<(), Self::Error>;
}

impl Policy for root::Ordinary {
    fn enter_chain(&self, _: &Solver, _: &[usize]) -> Result<(), Infallible> {
        Ok(())
    }
    fn mark(&self, _: &mut Solver) -> Result<(), Infallible> {
        Ok(())
    }
    fn chain(&self, s: &mut Solver, id: u64) -> Result<(), Infallible> {
        s.conflict.add_to_chain(id);
        Ok(())
    }
    fn sort(&self, values: &mut [(usize, Literal, u64)]) -> Result<(), Infallible> {
        values.sort_unstable_by_key(|b| std::cmp::Reverse(b.0));
        Ok(())
    }
    fn new_filter(&self, len: usize) -> Result<DetHashSet<Literal>, Infallible> {
        Ok(crate::kani_compat::det_hash_set_with_capacity(len))
    }
    fn filter(&self, _: &DetHashSet<Literal>) -> Result<(), Infallible> {
        Ok(())
    }
}

pub(in crate::solver) fn finalize_roots<P: Policy>(
    s: &mut Solver,
    uip: Literal,
    roots: &[usize],
    p: &P,
) -> Result<(), P::Error> {
    s.materialize_level0_unit_proofs_impl(false, p)?;
    let mut filter = p.new_filter(1 + s.conflict.learned_count())?;
    p.filter(&filter)?;
    filter.insert(uip.negated());
    for i in 0..s.conflict.learned_count() {
        p.work(2)?;
        p.filter(&filter)?;
        filter.insert(s.conflict.learned_at(i).negated());
    }
    s.append_lrat_unit_chain_admitted(roots, &filter, p)?;
    p.work(0)
}
