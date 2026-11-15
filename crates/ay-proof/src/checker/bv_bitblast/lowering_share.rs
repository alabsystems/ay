// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! What the proof-producing lowering keeps, and what it is charged for.
//!
//! `BvExpr` is a tree of boxes, so every lowered term is materialized once
//! per occurrence. Until 2026-09-29 the lowering ALSO kept a clone of every
//! term's full result in its memo and charged that full result to the
//! construction budget, level by level. A right-nested chain therefore cost
//! the SUM of its subtree sizes: the raw `ule`/`uge` lemmas of external-codegen's
//! per-lane `<16 x i8>` unsigned compares (a 16-lane `concat` chain on each
//! side of an equality) were charged 103,994 nodes against the 100,000 budget
//! (measured 2026-09-29), for an expression an order of magnitude smaller
//! (`lowering_share_tests.rs` holds the charge below twice the tree).
//!
//! Now the memo holds a clone only of a term that is REQUESTED more than
//! once, and the budget is charged for the nodes that are materialized, once
//! each: a term's NEW nodes (its result minus the results of the operands it
//! was handed), each memo copy, and each clone a memo hit returns. Counting a
//! result still walks it, and that walk is charged separately, as work, so no
//! cap is left to the wall clock.
//!
//! Which terms are requested more than once is counted BEFORE any is lowered,
//! by a census: one count per request an entry point declares
//! ([`ProofProducingLowerer::census_requests`]; a top-level request nobody
//! declared is counted when it is made) and one per operand a lowering
//! requests ([`ProofProducingLowerer::requested_operands`], which states what
//! each lowering arm asks for). A term the census did not count, and every
//! term once the census caps stopped it, is memoized. The census decides only
//! what is copied: with every term lowered once, the lowered expressions are
//! the ones memoizing every term builds (`lowering_share_tests.rs`).
//!
//! A term whose lowering FAILED is remembered with its reason
//! ([`ProofProducingLowerer::remember_failure`]), so no request lowers it
//! again either. That mattered while lemma validation caught a failure and
//! went on: a division whose operand failed became a free leaf, and until
//! 2026-09-30 that operand was lowered again on every request, twice per level
//! of a nest of divisions. No lowering catches a failure now: a reserved
//! operator is abstracted only after its whole application, operands
//! included, validates (`BvApplicationLowering::Abstractable`), so a failure
//! refuses the whole lowering, and a nest of them is refused once.
//!
//! Test builds hold each finished lowering of an entry point to its census
//! (`audit_census`): no term was lowered twice, and every term was requested
//! exactly as often as it was counted.

use super::*;

/// Census walks and result-count walks of one lowering, in nodes visited: the
/// same per-lemma work figure the expansion and replay phases are held to.
const MAX_PROOF_PRODUCING_LOWERING_WALK: u64 = MAX_PROOF_PRODUCING_BV_WORK_PER_LEMMA;

/// A request an entry point makes at the top level, declared before it
/// lowers anything ([`ProofProducingLowerer::census_requests`]).
#[derive(Clone, Copy)]
pub(super) enum Request {
    /// `lower(term)`.
    Lower(TermId),
    /// The requests the lowering of `term` makes, without `term` itself: the
    /// trace of a sparse read that is validated but not lowered
    /// (`validate_sparse_read`).
    OperandsOf(TermId),
}

impl ProofProducingLowerer<'_, '_> {
    /// Count every top-level request of an entry point, and every request the
    /// lowerings they start will make, before any is lowered: a term two
    /// requests share is then memoized the FIRST time it is lowered, rather
    /// than lowered again when a later root turns out to reach it.
    pub(super) fn census_requests(
        &mut self,
        requests: impl IntoIterator<Item = Request>,
    ) -> Result<(), String> {
        let requests: Vec<Request> = requests.into_iter().collect();
        self.count_offset_equalities(requests.iter().map(|request| match *request {
            Request::Lower(term) | Request::OperandsOf(term) => term,
        }));
        let mut stack = Vec::new();
        let mut operands = Vec::new();
        for request in requests {
            match request {
                Request::Lower(term) => self.declare(term, &mut stack)?,
                Request::OperandsOf(term) => {
                    operands.clear();
                    self.requested_operands(term, &mut operands)?;
                    for &operand in &operands {
                        self.declare(operand, &mut stack)?;
                    }
                }
            }
        }
        self.census_walk(stack)
    }

    fn declare(&mut self, term: TermId, stack: &mut Vec<TermId>) -> Result<(), String> {
        *self.declared.entry(term).or_insert(0) += 1;
        self.census_edge(term, stack)
    }

    /// A top-level `lower(term)`: consume its declaration, or count the
    /// request now. An undeclared request that reaches terms an earlier root
    /// already lowered makes them be lowered again: entry points declare.
    pub(super) fn census_top_level(&mut self, term: TermId) -> Result<(), String> {
        if let Some(pending) = self.declared.get_mut(&term) {
            if *pending > 0 {
                *pending -= 1;
                return Ok(());
            }
        }
        self.count_offset_equalities([term]);
        let mut stack = Vec::new();
        self.census_edge(term, &mut stack)?;
        self.census_walk(stack)
    }

    fn census_walk(&mut self, mut stack: Vec<TermId>) -> Result<(), String> {
        let mut operands = Vec::new();
        while let Some(term) = stack.pop() {
            self.poll_lowering()?;
            operands.clear();
            self.requested_operands(term, &mut operands)?;
            for &operand in &operands {
                self.census_edge(operand, &mut stack)?;
            }
        }
        Ok(())
    }

    /// Count one request for `child`, and queue it the first time. A census
    /// that would exceed the term caps stops counting; from then on every
    /// term is memoized (`memoizes`).
    fn census_edge(&mut self, child: TermId, stack: &mut Vec<TermId>) -> Result<(), String> {
        self.charge_lowering_walk(1)?;
        if self.census_seen.len() >= MAX_PROOF_PRODUCING_TERM_NODES
            || self.census_edges >= MAX_PROOF_PRODUCING_TERM_EDGES
        {
            self.census_incomplete = true;
            return Ok(());
        }
        self.census_edges += 1;
        *self.parents.entry(child).or_insert(0) += 1;
        if self.census_seen.insert(child) {
            stack.push(child);
        }
        Ok(())
    }

    /// The operands the lowering of `term` requests, with multiplicity: what
    /// the arms under `lower_inner` call `lower` on.
    ///
    /// * A sparse read requests its index, then the index and the value of
    ///   every store its trace reads through, and the fill of a constant base
    ///   (`sparse_array_trace`); never the store chain itself.
    /// * An application answered by one free leaf requests nothing
    ///   (`uninterpreted_leaf_symbol`, `non_finite_atom`), nor does an indexed
    ///   BitVec operator the lowering refuses before lowering its operand
    ///   (`indexed_bv_operator_lowers_operand`). A reserved operator that
    ///   lemma validation abstracts still requests its operands first.
    /// * `extract` requests its operand once; the operands of a `concat` it
    ///   looks through are taken out of the lowered `concat`
    ///   (`slice_concat.rs`), not requested again.
    /// * A binary `=`/`distinct` wider than the producer's words requests
    ///   each narrow piece of its slices once (`wide_equality.rs`); one
    ///   between two offset words requests the two words
    ///   (`offset_equality.rs`).
    /// * A term an entry point will answer from a memo entry it installs
    ///   (`census_opaque`) requests nothing.
    ///
    /// Every other application requests each argument once, `not` its
    /// operand, and `ite` its three. An arm that fails refuses the whole
    /// lowering, so what it would have requested is never audited. An
    /// UNDER-count, which makes a term be lowered twice, is what
    /// `audit_census` exists to catch.
    pub(super) fn requested_operands(
        &mut self,
        term: TermId,
        out: &mut Vec<TermId>,
    ) -> Result<(), String> {
        let terms = self.terms;
        if terms.entry_stamp(term).is_none() || self.census_opaque.contains(&term) {
            return Ok(());
        }
        match terms.get(term) {
            TermData::Not(inner) => out.push(*inner),
            TermData::Ite(condition, then_term, else_term) => {
                out.extend([*condition, *then_term, *else_term]);
            }
            TermData::App(Symbol::Named(name), args)
                if name == "select"
                    && args.len() == 2
                    && terms.entry_stamp(args[0]).is_some()
                    && self.sparse_read(args[0]).is_some() =>
            {
                out.push(args[1]);
                self.sparse_chain_operands(args[0], out)?;
            }
            // Any other read: the finite-array lanes lower the array, then
            // the index. The select arm precedes every leaf abstraction.
            TermData::App(Symbol::Named(name), args) if name == "select" => {
                out.extend_from_slice(args);
            }
            // Wide equalities and order predicates request narrow pieces.
            // Equality can align fields; order uses canonical limbs so its
            // borrow chain stays bounded independently of concat arity.
            TermData::App(Symbol::Named(name), args)
                if matches!(
                    name.as_str(),
                    "=" | "distinct"
                        | "bvult"
                        | "bvule"
                        | "bvugt"
                        | "bvuge"
                        | "bvslt"
                        | "bvsle"
                        | "bvsgt"
                        | "bvsge"
                ) && args.len() == 2
                    && terms.entry_stamp(args[0]).is_some()
                    && self.is_wide(args[0]) =>
            {
                let partition = if matches!(name.as_str(), "=" | "distinct") {
                    wide_equality::Partition::Fields
                } else {
                    wide_equality::Partition::Limbs
                };
                self.wide_word_requests(args[0], args[1], partition, out)?;
            }
            TermData::App(symbol, args) => {
                // An equality between two offset words requests the two
                // words (`offset_equality.rs`).
                if let (Symbol::Named(name), [lhs, rhs]) = (symbol, args.as_slice()) {
                    if matches!(name.as_str(), "=" | "distinct") {
                        if let Some(reading) = self.offset_equality(*lhs, *rhs) {
                            out.extend([reading.minuend, reading.subtrahend]);
                            return Ok(());
                        }
                    }
                }
                let answered_by_leaf = match terms.sort(term) {
                    Sort::Bool => {
                        self.uninterpreted_leaf_symbol(symbol) || self.non_finite_atom(args)
                    }
                    Sort::BitVec(_) => {
                        self.uninterpreted_leaf_symbol(symbol)
                            || matches!(symbol, Symbol::Indexed(name, _)
                                if !self.indexed_bv_operator_lowers_operand(name))
                    }
                    _ => false,
                };
                if !answered_by_leaf {
                    match self.padded_product_operands(symbol, args) {
                        Some(operands) => out.extend(operands),
                        None => out.extend_from_slice(args),
                    }
                }
            }
            _ => {}
        }
        Ok(())
    }

    /// Whether a later request for `term` can come: it was counted more than
    /// once, it was not counted, or the census stopped before counting every
    /// request (a count it did make may then be short).
    pub(super) fn memoizes(&self, term: TermId) -> bool {
        self.census_incomplete || self.parents.get(&term).is_none_or(|&edges| edges > 1)
    }

    /// Remember that `term` failed to lower, with `reason`, unless the
    /// failure may depend on more than the term and the lowerer's
    /// configuration: a budget or the deadline ran out (`resource_exhausted`,
    /// sticky), the caller cancelled, or a cycle was refused
    /// (`cycle_refused`). Otherwise a later request would fail the same way,
    /// so [`Self::lower_inner`] refuses it with the same reason and lowers
    /// nothing. Refusing can only decline a lemma, never accept one. At most
    /// one entry per lowered term, and those are capped at
    /// `MAX_PROOF_PRODUCING_TERM_NODES`.
    pub(super) fn remember_failure(&mut self, term: TermId, reason: &str) {
        if self.resource_exhausted || self.cancelled || self.cycle_refused {
            return;
        }
        self.failed.insert(term, reason.to_owned());
    }

    /// Install (or clear) the disjointness facts. A term that failed without
    /// them may lower with them, so every remembered failure is forgotten;
    /// the memo, whose entries are exact without facts, stays.
    pub(super) fn install_disjoint_facts(&mut self, facts: Option<disjoint::Shape>) {
        self.disjoint_spans = facts;
        self.failed.clear();
    }

    /// Charge one result-count or census walk.
    pub(super) fn charge_lowering_walk(&mut self, nodes: usize) -> Result<(), String> {
        let walked = self
            .lowering_walk
            .saturating_add(u64::try_from(nodes).unwrap_or(u64::MAX));
        if walked > MAX_PROOF_PRODUCING_LOWERING_WALK {
            self.resource_exhausted = true;
            return Err(format!(
                "proof-producing lowering walks exceed {MAX_PROOF_PRODUCING_LOWERING_WALK} nodes"
            ));
        }
        self.lowering_walk = walked;
        Ok(())
    }

    /// Account one freshly lowered `result` of `term`, `nodes` occurrences in
    /// all, of which `operands` were handed to it by the lowerings it made:
    /// the rest were materialized here. A shared term keeps one more copy.
    pub(super) fn keep_lowered(
        &mut self,
        term: TermId,
        result: &ProofProducingExpr,
        nodes: usize,
        operands: usize,
    ) -> Result<(), String> {
        self.charge_constructed_expr_nodes(nodes.saturating_sub(operands))?;
        if self.memoizes(term) {
            self.charge_constructed_expr_nodes(nodes)?;
            self.memo_node_counts.insert(term, nodes);
            self.memo.insert(term, result.clone());
        }
        Ok(())
    }
}

#[cfg(test)]
impl ProofProducingLowerer<'_, '_> {
    /// A finished lowering matched its census: no term was lowered twice,
    /// and, the census complete, every term was requested exactly as often as
    /// it was counted (term index, counted, requested).
    pub(super) fn audit_census(&self) {
        assert_eq!(self.relowerings, 0, "a term was lowered twice");
        if self.census_incomplete {
            return;
        }
        let requested = |term: &TermId| self.requests.get(term).copied().unwrap_or(0);
        let mut mismatches: Vec<(usize, u32, u32)> = self
            .parents
            .iter()
            .filter(|&(term, &counted)| requested(term) != counted)
            .map(|(term, &counted)| (term.index(), counted, requested(term)))
            .chain(
                self.requests
                    .iter()
                    .filter(|(term, _)| !self.parents.contains_key(term))
                    .map(|(term, &made)| (term.index(), 0, made)),
            )
            .collect();
        mismatches.sort_unstable();
        assert!(
            mismatches.is_empty(),
            "census (term, counted, requested): {mismatches:?}"
        );
    }
}

#[cfg(test)]
#[path = "lowering_share_tests.rs"]
mod tests;

#[cfg(test)]
#[path = "lowering_census_tests.rs"]
mod census_tests;
