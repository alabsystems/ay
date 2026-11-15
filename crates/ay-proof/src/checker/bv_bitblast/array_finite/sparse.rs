// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Scalar reads through bounded store chains without address-domain enumeration.
//! Constant-array defaults are exact. Reads of an arbitrary base array become
//! independent scalar leaves keyed by the actual array and read-index terms.
//! This weakens array congruence, so only a refutation can authorize a result;
//! a satisfiable abstraction is never a source model. Every store is validated.
//!
//! Index sorts wider than the complete-domain bound always read this way. A
//! narrower index reads this way only under
//! [`super::SmallIndexReads::StoreChain`].

use super::super::*;

// Includes four saved registers and both writes of an eight-byte local cell.
// Source-node, edge, expression, work and cancellation limits also apply.
const MAX_STORES: usize = 64;
const MAX_ADDRESS_DEPTH: usize = 16;

#[derive(Clone, Copy)]
struct Address {
    base: Option<TermId>,
    offset: u128,
}

/// Exact address readings owned by ONE lowerer borrowing one immutable term
/// arena. The mask is part of the interpretation; height preserves the opened
/// arithmetic depth check when a result is requested from a deeper position.
#[derive(Default)]
pub(in crate::checker::bv_bitblast) struct SparseAddressMemo {
    entries: HashMap<(TermId, u128), (Address, usize)>,
}

/// One source-bound read of an arbitrary array, before store muxes.
/// Retained only until the complete source query has been lowered.
pub(in crate::checker::bv_bitblast) struct SparseBaseRead {
    array: TermId,
    key: TermId,
    index: BvExpr,
    value: BvExpr,
}

struct ReadTrace {
    stores: Vec<Store>,
    index: BvExpr,
    value: BvExpr,
    boolean: bool,
}

struct Store {
    key: TermId,
    index: BvExpr,
    value: BvExpr,
}

impl ProofProducingLowerer<'_, '_> {
    pub(super) fn lower_sparse_array_select(
        &mut self,
        result: TermId,
        array: TermId,
        key: TermId,
    ) -> Option<Result<ProofProducingExpr, String>> {
        if self.terms.entry_stamp(array).is_none() {
            return Some(Err(
                "sparse read array is outside the live term store".into()
            ));
        }
        let Some((index_width, width)) = self.sparse_read(array) else {
            // The original full-domain lane and its resource bounds are
            // unchanged; record that a store-chain retry would lower this read
            // differently.
            if self.sparse_read_shape(array).is_some() {
                self.scalarized_small_index_reads = true;
            }
            return None;
        };
        Some(self.sparse_array_read(result, array, key, index_width, width))
    }

    /// The index and value widths of a read of `array` this lane owns, or
    /// `None` when the full-domain lane (or no lane) does. A small-index read
    /// is owned here only under [`super::SmallIndexReads::StoreChain`].
    pub(in crate::checker::bv_bitblast) fn sparse_read(&self, array: TermId) -> Option<(u32, u32)> {
        let (index_width, width) = self.sparse_read_shape(array)?;
        (index_width > array_finite::MAX_EXACT_FINITE_ARRAY_INDEX_WIDTH
            || self.small_index_reads == array_finite::SmallIndexReads::StoreChain)
            .then_some((index_width, width))
    }

    /// The index and value widths of a read of `array` this lane can lower
    /// under some [`super::SmallIndexReads`] mode.
    fn sparse_read_shape(&self, array: TermId) -> Option<(u32, u32)> {
        let Sort::Array(sort) = self.terms.sort(array) else {
            return None;
        };
        let Sort::BitVec(index) = &sort.index_sort else {
            return None;
        };
        if index.width == 0 || index.width > MAX_PROOF_PRODUCING_INTERNAL_BV_WIDTH {
            return None;
        }
        let width = match &sort.element_sort {
            Sort::Bool => 1,
            Sort::BitVec(value)
                if value.width > 0 && value.width <= MAX_PROOF_PRODUCING_INTERNAL_BV_WIDTH =>
            {
                value.width
            }
            _ => return None,
        };
        Some((index.width, width))
    }

    /// What a read's trace requests after its index (`sparse_array_trace`):
    /// the index and the value of every store it reads through, then the
    /// fill of a constant base. A trace that would fail refuses the read, so
    /// the census may stop wherever the trace would.
    pub(in crate::checker::bv_bitblast) fn sparse_chain_operands(
        &mut self,
        array: TermId,
        out: &mut Vec<TermId>,
    ) -> Result<(), String> {
        let terms = self.terms;
        let mut cursor = array;
        for _ in 0..=MAX_STORES {
            self.charge_lowering_walk(1)?;
            if terms.entry_stamp(cursor).is_none() {
                break;
            }
            let TermData::App(Symbol::Named(name), args) = terms.get(cursor) else {
                break;
            };
            match (name.as_str(), args.as_slice()) {
                ("const-array", [fill]) => {
                    out.push(*fill);
                    break;
                }
                ("store", [base, at, stored]) => {
                    out.extend([*at, *stored]);
                    cursor = *base;
                }
                _ => break,
            }
        }
        Ok(())
    }

    fn sparse_array_read(
        &mut self,
        result: TermId,
        array: TermId,
        key: TermId,
        index_width: u32,
        value_width: u32,
    ) -> Result<ProofProducingExpr, String> {
        let ReadTrace {
            stores,
            index,
            mut value,
            boolean,
        } = self.sparse_array_trace(result, array, key, value_width)?;
        // Reapply stores from oldest to newest, preserving last-write-wins.
        for store in stores.into_iter().rev() {
            self.poll_lowering()?;
            value = match self.sparse_address_equal(key, store.key, index_width)? {
                Some(true) => store.value,
                Some(false) => value,
                None if self
                    .disjoint_spans
                    .as_ref()
                    .is_some_and(|shape| shape.separates(self.terms, key, store.key)) =>
                {
                    value
                }
                None => {
                    let condition = BvExpr::eq(index.clone(), store.index);
                    let nodes = self
                        .count_bv_nodes(&condition)?
                        .saturating_mul(2)
                        .saturating_add(self.count_bv_nodes(&value)?)
                        .saturating_add(self.count_bv_nodes(&store.value)?)
                        .saturating_add(7);
                    self.preflight_expr_nodes(nodes, "sparse array read mux")?;
                    Self::mux_leaf(condition, store.value, value, value_width)
                }
            };
        }
        Ok(if boolean {
            ProofProducingExpr::Bool(value)
        } else {
            ProofProducingExpr::BitVec(value, value_width)
        })
    }

    // Validate the complete trace before using a separately proved memory
    // property. This performs the same type, value, source, store-count,
    // cancellation and allocation checks as scalarization, without building
    // read muxes which that property has already proved unnecessary.
    pub(in crate::checker::bv_bitblast) fn validate_sparse_read(
        &mut self,
        result: TermId,
    ) -> Result<(), String> {
        self.terms
            .entry_stamp(result)
            .ok_or("missing sparse read")?;
        let TermData::App(Symbol::Named(op), args) = self.terms.get(result) else {
            return Err("expected a sparse array read".into());
        };
        let [array, key] = args.as_slice() else {
            return Err("malformed sparse read".into());
        };
        if op != "select" {
            return Err("expected select".into());
        }
        let (array, key) = (*array, *key);
        self.terms
            .entry_stamp(array)
            .ok_or("missing sparse read array")?;
        let Sort::Array(shape) = self.terms.sort(array) else {
            return Err("expected array".into());
        };
        let (Sort::BitVec(index), Sort::BitVec(value)) = (&shape.index_sort, &shape.element_sort)
        else {
            return Err("expected bit-vector memory".into());
        };
        if index.width <= array_finite::MAX_EXACT_FINITE_ARRAY_INDEX_WIDTH
            || index.width > MAX_PROOF_PRODUCING_INTERNAL_BV_WIDTH
            || value.width == 0
            || value.width > MAX_PROOF_PRODUCING_INTERNAL_BV_WIDTH
        {
            return Err("unsupported sparse memory width".into());
        }
        self.sparse_array_trace(result, array, key, value.width)?;
        Ok(())
    }

    fn sparse_array_trace(
        &mut self,
        result: TermId,
        array: TermId,
        key: TermId,
        value_width: u32,
    ) -> Result<ReadTrace, String> {
        let array_sort = self.terms.sort(array).clone();
        let Sort::Array(sort) = &array_sort else {
            return Err("sparse read requires an array sort".into());
        };
        self.sparse_require_sort(key, &sort.index_sort)?;
        self.sparse_require_sort(result, &sort.element_sort)?;
        let (index, _) = self.lower_bv(key)?;
        let mut stores = Vec::new();
        stores.try_reserve_exact(MAX_STORES).map_err(|error| {
            self.resource_exhausted = true;
            format!("sparse store allocation failed: {error}")
        })?;
        let mut cursor = array;
        let value = loop {
            self.poll_lowering()?;
            self.sparse_require_sort(cursor, &array_sort)?;
            self.visited_nodes = self.visited_nodes.saturating_add(1);
            if self.visited_nodes > MAX_PROOF_PRODUCING_TERM_NODES {
                self.resource_exhausted = true;
                return Err("sparse array source node budget exceeded".into());
            }
            if matches!(self.terms.get(cursor), TermData::Var(..)) {
                // Every concrete array interpretation supplies a value for this
                // read. Distinct syntactic indices may alias in the source but
                // remain independent here, which enlarges the model set. Never
                // expose a SAT assignment from this abstraction as a model.
                self.used_uninterpreted_leaves = true;
                let value = BvExpr::leaf(
                    &format!("proof_array_read_{}_{}", cursor.index(), key.index()),
                    value_width,
                );
                if !self.sparse_base_keys.contains(&(cursor, key)) {
                    let nodes = self.count_bv_nodes(&index)?.saturating_add(1);
                    self.charge_constructed_expr_nodes(nodes)?;
                    self.sparse_base_keys.try_reserve(1).map_err(|error| {
                        self.resource_exhausted = true;
                        format!("sparse read key allocation failed: {error}")
                    })?;
                    self.sparse_base_reads.try_reserve(1).map_err(|error| {
                        self.resource_exhausted = true;
                        format!("sparse read ledger allocation failed: {error}")
                    })?;
                    self.sparse_base_keys.insert((cursor, key));
                    self.sparse_base_reads.push(SparseBaseRead {
                        array: cursor,
                        key,
                        index: index.clone(),
                        value: value.clone(),
                    });
                }
                break value;
            }
            let TermData::App(Symbol::Named(name), args) = self.terms.get(cursor) else {
                return Err("sparse read requires a constant or variable array base".into());
            };
            self.visited_edges = self.visited_edges.saturating_add(args.len());
            if self.visited_edges > MAX_PROOF_PRODUCING_TERM_EDGES {
                self.resource_exhausted = true;
                return Err("sparse array source edge budget exceeded".into());
            }
            match (name.as_str(), args.as_slice()) {
                ("const-array", [fill]) => {
                    break self.sparse_scalar(*fill, &sort.element_sort)?;
                }
                ("store", [base, at, stored]) => {
                    if stores.len() == MAX_STORES {
                        self.resource_exhausted = true;
                        return Err("sparse array store-chain budget exceeded".into());
                    }
                    let (base, at, stored) = (*base, *at, *stored);
                    self.sparse_require_sort(at, &sort.index_sort)?;
                    let (index, _) = self.lower_bv(at)?;
                    let value = self.sparse_scalar(stored, &sort.element_sort)?;
                    stores.push(Store {
                        key: at,
                        index,
                        value,
                    });
                    cursor = base;
                }
                _ => return Err("malformed or unsupported sparse array node".into()),
            }
        };
        Ok(ReadTrace {
            stores,
            index,
            value,
            boolean: sort.element_sort == Sort::Bool,
        })
    }

    fn sparse_require_sort(&self, term: TermId, sort: &Sort) -> Result<(), String> {
        if self.terms.entry_stamp(term).is_none() || self.terms.sort(term) != sort {
            return Err("sparse array child is absent or has the wrong sort".into());
        }
        Ok(())
    }

    fn sparse_scalar(&mut self, term: TermId, sort: &Sort) -> Result<BvExpr, String> {
        self.sparse_require_sort(term, sort)?;
        if *sort == Sort::Bool {
            self.lower_bool(term)
        } else {
            self.lower_bv(term).map(|(value, _)| value)
        }
    }

    fn sparse_address_equal(
        &mut self,
        a: TermId,
        b: TermId,
        width: u32,
    ) -> Result<Option<bool>, String> {
        let mask = if width == 128 {
            u128::MAX
        } else {
            (1_u128 << width) - 1
        };
        let a = self.sparse_address(a, mask, 0)?;
        let b = self.sparse_address(b, mask, 0)?;
        // Translation is a bijection modulo 2^width, including wraparound.
        Ok((a.base == b.base).then_some(a.offset == b.offset))
    }

    fn sparse_address(
        &mut self,
        term: TermId,
        mask: u128,
        depth: usize,
    ) -> Result<Address, String> {
        self.sparse_address_with_height(term, mask, depth)
            .map(|(address, _)| address)
    }

    fn sparse_address_with_height(
        &mut self,
        term: TermId,
        mask: u128,
        depth: usize,
    ) -> Result<(Address, usize), String> {
        self.charge_array_work(1, "sparse array address normalization")?;
        if depth > MAX_ADDRESS_DEPTH {
            self.resource_exhausted = true;
            return Err("sparse array address normalization depth exceeded".into());
        }
        if let Some(&(address, height)) = self.sparse_addresses.entries.get(&(term, mask)) {
            if height > MAX_ADDRESS_DEPTH - depth {
                self.resource_exhausted = true;
                return Err("sparse array address normalization depth exceeded".into());
            }
            return Ok((address, height));
        }
        if self.sparse_addresses.entries.len() >= MAX_PROOF_PRODUCING_TERM_NODES {
            self.resource_exhausted = true;
            return Err("sparse array address memo source-node budget exceeded".into());
        }
        let result = match self.terms.get(term) {
            TermData::Const(Constant::BitVec { value, .. }) => (
                Address {
                    base: None,
                    offset: value.to_u128().ok_or("invalid sparse address constant")? & mask,
                },
                0,
            ),
            TermData::App(Symbol::Named(name), args)
                if matches!(name.as_str(), "bvadd" | "bvsub") && args.len() == 2 =>
            {
                let subtract = name == "bvsub";
                let (left, right) = (args[0], args[1]);
                let (a, ah) = self.sparse_address_with_height(left, mask, depth + 1)?;
                let (b, bh) = self.sparse_address_with_height(right, mask, depth + 1)?;
                let height = 1 + ah.max(bh);
                let address = if subtract && (b.base.is_none() || a.base == b.base) {
                    Address {
                        base: if a.base == b.base { None } else { a.base },
                        offset: a.offset.wrapping_sub(b.offset) & mask,
                    }
                } else if !subtract && (a.base.is_none() || b.base.is_none()) {
                    Address {
                        base: a.base.or(b.base),
                        offset: a.offset.wrapping_add(b.offset) & mask,
                    }
                } else {
                    Address {
                        base: Some(term),
                        offset: 0,
                    }
                };
                (address, height)
            }
            _ => (
                Address {
                    base: Some(term),
                    offset: 0,
                },
                0,
            ),
        };
        // Pending parents count too: children may fill the final slots while
        // this frame is open. A refused insertion never escapes as a reading.
        if self.sparse_addresses.entries.len() >= MAX_PROOF_PRODUCING_TERM_NODES {
            self.resource_exhausted = true;
            return Err("sparse array address memo source-node budget exceeded".into());
        }
        self.sparse_addresses.entries.insert((term, mask), result);
        Ok(result)
    }
}

#[cfg(test)]
#[path = "sparse/address_tests.rs"]
mod address_tests;

impl ProofProducingLowerer<'_, '_> {
    /// Consume the read ledger after lowering ALL roots of one conjunction.
    ///
    /// Finite Ackermann consistency: every source array interpretation
    /// satisfies equal-index => equal-value for reads of that SAME array.
    /// Thus every source model extends to a model of the lowered roots AND
    /// these constraints. Only independently replayed UNSAT grants authority;
    /// a SAT abstraction still cannot be presented as a source model.
    /// Stores keep their existing ordered mux semantics. No assertion, sort,
    /// index, or value from another array is substituted or assumed.
    pub(in crate::checker::bv_bitblast) fn take_sparse_read_consistency(
        &mut self,
    ) -> Result<Vec<BvExpr>, String> {
        let reads = std::mem::take(&mut self.sparse_base_reads);
        let mut constraints = Vec::new();
        // These implicit address equalities were absent from the source-root
        // census. Count them before choosing an encoding, so byte reads over
        // two offset words can share one difference instead of asking the SAT
        // proof to rederive a pair of carry chains for every byte pair.
        for (position, left) in reads.iter().enumerate() {
            for right in &reads[..position] {
                self.poll_lowering()?;
                self.charge_lowering_walk(1)?;
                if left.array == right.array {
                    self.offset_shares.count(self.terms, left.key, right.key);
                }
            }
        }
        for (position, left) in reads.iter().enumerate() {
            for right in &reads[..position] {
                self.poll_lowering()?;
                self.charge_lowering_walk(1)?;
                if left.array != right.array {
                    continue;
                }
                let (width, _) = self
                    .sparse_read_shape(left.array)
                    .ok_or("invalid sparse read ledger sort")?;
                let known = self.sparse_address_equal(left.key, right.key, width)?;
                if known == Some(false) {
                    continue;
                }
                if known == Some(true) {
                    self.push_sparse_read_constraint(&mut constraints, 3, || {
                        BvExpr::eq(left.value.clone(), right.value.clone())
                    })?;
                } else if let Some(reading) = self.offset_equality(left.key, right.key) {
                    let guard = self.lower_offset_equality(&reading)?;
                    let nodes = self.count_bv_nodes(&guard)?.saturating_add(5);
                    self.push_sparse_read_constraint(&mut constraints, nodes, || {
                        BvExpr::or(
                            BvExpr::not(guard),
                            BvExpr::eq(left.value.clone(), right.value.clone()),
                        )
                    })?;
                } else {
                    // BvExpr owns recursive Box children. Count the borrowed
                    // operands before either clone, then admit the SAME full
                    // constraint cost: Eq(indexes), Eq(values), Not and Or.
                    let nodes = self
                        .count_bv_nodes(&left.index)?
                        .saturating_add(self.count_bv_nodes(&right.index)?)
                        .saturating_add(6);
                    // The old whole-guard count also visited its Eq root.
                    self.charge_lowering_walk(1)?;
                    self.push_sparse_read_constraint(&mut constraints, nodes, || {
                        let guard = BvExpr::eq(left.index.clone(), right.index.clone());
                        BvExpr::or(
                            BvExpr::not(guard),
                            BvExpr::eq(left.value.clone(), right.value.clone()),
                        )
                    })?;
                }
            }
        }
        Ok(constraints)
    }

    /// Admit the complete constraint before its builder may copy expression
    /// trees. Resource/cancellation failures retain their existing sticky
    /// attribution; a failed allocation does not refund counted work.
    pub(super) fn push_sparse_read_constraint(
        &mut self,
        constraints: &mut Vec<BvExpr>,
        nodes: usize,
        build: impl FnOnce() -> BvExpr,
    ) -> Result<(), String> {
        self.preflight_expr_nodes(nodes, "sparse read consistency")?;
        self.charge_constructed_expr_nodes(nodes)?;
        constraints.try_reserve(1).map_err(|error| {
            self.resource_exhausted = true;
            format!("sparse consistency allocation failed: {error}")
        })?;
        constraints.push(build());
        Ok(())
    }
}
