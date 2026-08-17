// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Resource accounting and shape checks for exact finite-array lowering.

use ay_core::{time::Instant, TermId};

use super::super::{bv_expr_nodes, BvExpr, ProofProducingLowerer, MAX_PROOF_PRODUCING_EXPR_NODES};
use super::{
    classify_source_sort, FiniteArrayExpr, FiniteSortShape, FiniteSourceSort,
    MAX_EXACT_FINITE_ARRAY_WORK,
};

impl ProofProducingLowerer<'_> {
    pub(super) fn term_shape(&mut self, term: TermId) -> Result<FiniteSortShape, String> {
        if self.terms.entry_stamp(term).is_none() {
            return Err(format!(
                "finite-array operand term {} is outside the live term store",
                term.index()
            ));
        }
        match classify_source_sort(self.terms.sort(term)) {
            Ok(FiniteSourceSort::Bool) => Ok(FiniteSortShape::bool_scalar()),
            Ok(FiniteSourceSort::BitVec(width)) => Ok(FiniteSortShape::bitvec_scalar(width)),
            Ok(FiniteSourceSort::Array(shape)) => Ok(shape),
            Err(error) => {
                if error.is_resource_limit() {
                    self.resource_exhausted = true;
                }
                Err(error.into_reason())
            }
        }
    }

    pub(super) fn require_term_shape(
        &mut self,
        term: TermId,
        expected: &FiniteSortShape,
        context: &str,
    ) -> Result<(), String> {
        let actual = self.term_shape(term)?;
        if &actual == expected {
            Ok(())
        } else {
            Err(format!("{context} has a mismatched source sort"))
        }
    }

    pub(super) fn element_shape_or_resource(
        &mut self,
        shape: &FiniteSortShape,
    ) -> Result<FiniteSortShape, String> {
        shape.element_shape().inspect_err(|error| {
            if error.contains("allocation failed") {
                self.resource_exhausted = true;
            }
        })
    }

    pub(super) fn reserve_cells<T>(
        &mut self,
        cells: &mut Vec<T>,
        count: usize,
        context: &str,
    ) -> Result<(), String> {
        cells.try_reserve_exact(count).map_err(|error| {
            self.resource_exhausted = true;
            format!("{context} allocation failed: {error}")
        })
    }

    pub(super) fn charge_array_work(&mut self, amount: usize, context: &str) -> Result<(), String> {
        if Instant::now() >= self.deadline {
            self.resource_exhausted = true;
            return Err("proof-producing finite-array deadline exceeded".to_string());
        }
        let work = self
            .exact_finite_array_work
            .checked_add(amount)
            .ok_or_else(|| {
                self.resource_exhausted = true;
                format!("{context} work counter overflow")
            })?;
        if work > MAX_EXACT_FINITE_ARRAY_WORK {
            self.resource_exhausted = true;
            return Err(format!(
                "finite-array scalarization work exceeds {MAX_EXACT_FINITE_ARRAY_WORK}"
            ));
        }
        self.exact_finite_array_work = work;
        Ok(())
    }

    pub(super) fn preflight_expr_nodes(
        &mut self,
        nodes: usize,
        context: &str,
    ) -> Result<(), String> {
        if nodes > MAX_PROOF_PRODUCING_EXPR_NODES {
            self.resource_exhausted = true;
            Err(format!(
                "{context} would produce {nodes} BvExpr nodes, above limit {MAX_PROOF_PRODUCING_EXPR_NODES}"
            ))
        } else {
            Ok(())
        }
    }

    pub(super) fn array_expr_nodes(
        &mut self,
        array: &FiniteArrayExpr,
        context: &str,
    ) -> Result<usize, String> {
        let mut nodes = 0_usize;
        for cell in &array.cells {
            let cell_nodes = bv_expr_nodes(cell).map_err(|error| {
                self.resource_exhausted = true;
                format!("{context}: {error}")
            })?;
            nodes = nodes.checked_add(cell_nodes).ok_or_else(|| {
                self.resource_exhausted = true;
                format!("{context} node-count overflow")
            })?;
            if nodes > MAX_PROOF_PRODUCING_EXPR_NODES {
                self.resource_exhausted = true;
                return Err(format!(
                    "{context} exceeds {MAX_PROOF_PRODUCING_EXPR_NODES} BvExpr nodes"
                ));
            }
        }
        Ok(nodes)
    }

    pub(super) fn store_node_count(
        &mut self,
        base: &FiniteArrayExpr,
        value: &[BvExpr],
        conditions: &[BvExpr],
        shape: &FiniteSortShape,
    ) -> Result<usize, String> {
        let base_nodes = self.array_expr_nodes(base, "finite-array store base")?;
        let count = (|| {
            let mut value_nodes = 0_usize;
            for cell in value {
                value_nodes = value_nodes
                    .checked_add(bv_expr_nodes(cell).map_err(|_| ())?)
                    .ok_or(())?;
            }
            let mut condition_nodes = 0_usize;
            for condition in conditions {
                let mask_nodes = bv_expr_nodes(condition)
                    .map_err(|_| ())?
                    .checked_add(usize::from(shape.leaf_width() > 1))
                    .ok_or(())?;
                condition_nodes = condition_nodes.checked_add(mask_nodes).ok_or(())?;
            }
            let element_cells = value.len();
            base_nodes
                .checked_add(value_nodes.checked_mul(conditions.len()).ok_or(())?)
                .and_then(|nodes| {
                    condition_nodes
                        .checked_mul(2)
                        .and_then(|n| n.checked_mul(element_cells))
                        .and_then(|n| nodes.checked_add(n))
                })
                .and_then(|nodes| {
                    shape
                        .scalar_cells
                        .checked_mul(4)
                        .and_then(|n| nodes.checked_add(n))
                })
                .ok_or(())
        })();
        count.map_err(|()| {
            self.resource_exhausted = true;
            "finite-array store node-count overflow".to_string()
        })
    }

    pub(super) fn select_node_count(
        &mut self,
        array: &FiniteArrayExpr,
        element: &FiniteSortShape,
        conditions: &[BvExpr],
    ) -> Result<usize, String> {
        let array_nodes = self.array_expr_nodes(array, "finite-array select source")?;
        let count = (|| {
            let mut mask_nodes = 0_usize;
            for condition in conditions {
                let condition_nodes = bv_expr_nodes(condition)
                    .map_err(|_| ())?
                    .checked_add(usize::from(element.leaf_width() > 1))
                    .ok_or(())?;
                mask_nodes = mask_nodes.checked_add(condition_nodes).ok_or(())?;
            }
            let per_element_gates = conditions
                .len()
                .checked_add(conditions.len().saturating_sub(1))
                .ok_or(())?;
            array_nodes
                .checked_add(mask_nodes.checked_mul(element.scalar_cells).ok_or(())?)
                .and_then(|nodes| {
                    per_element_gates
                        .checked_mul(element.scalar_cells)
                        .and_then(|gates| nodes.checked_add(gates))
                })
                .ok_or(())
        })();
        count.map_err(|()| {
            self.resource_exhausted = true;
            "finite-array select node-count overflow".to_string()
        })
    }

    pub(super) fn condition_mask(condition: BvExpr, width: u32) -> BvExpr {
        if width == 1 {
            condition
        } else {
            BvExpr::sign_ext(condition, width - 1)
        }
    }

    pub(super) fn mux_leaf(
        condition: BvExpr,
        then_expr: BvExpr,
        else_expr: BvExpr,
        width: u32,
    ) -> BvExpr {
        let mask = Self::condition_mask(condition, width);
        BvExpr::or(
            BvExpr::and(mask.clone(), then_expr),
            BvExpr::and(BvExpr::not(mask), else_expr),
        )
    }

    pub(super) fn balanced_or(
        &mut self,
        mut expressions: Vec<BvExpr>,
        width: u32,
    ) -> Result<BvExpr, String> {
        if expressions.is_empty() {
            return Ok(BvExpr::const_val(0, width));
        }
        while expressions.len() > 1 {
            let mut next = Vec::new();
            self.reserve_cells(
                &mut next,
                expressions.len().div_ceil(2),
                "finite-array balanced select",
            )?;
            let mut current = expressions.into_iter();
            while let Some(lhs) = current.next() {
                next.push(match current.next() {
                    Some(rhs) => BvExpr::or(lhs, rhs),
                    None => lhs,
                });
            }
            expressions = next;
        }
        expressions
            .pop()
            .ok_or_else(|| "finite-array balanced select lost its final expression".to_string())
    }
}
