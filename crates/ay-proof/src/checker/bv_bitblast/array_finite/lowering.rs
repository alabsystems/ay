// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Exact scalar lowering for recursively finite array values.

use ay_core::TermId;

use super::super::{
    bv_expr_nodes, proof_producing_expr_nodes, BvExpr, ProofProducingExpr, ProofProducingLowerer,
};
use super::{FiniteArrayExpr, FiniteIndexSort, FiniteScalarSort, FiniteSortShape};

impl ProofProducingLowerer<'_> {
    pub(super) fn lower_array_variable(
        &mut self,
        term: TermId,
        shape: FiniteSortShape,
    ) -> Result<FiniteArrayExpr, String> {
        self.preflight_expr_nodes(shape.scalar_cells, "finite-array variable")?;
        self.charge_array_work(shape.scalar_cells, "finite-array variable")?;
        let mut cells = Vec::new();
        self.reserve_cells(&mut cells, shape.scalar_cells, "finite-array variable")?;
        for cell in 0..shape.scalar_cells {
            cells.push(BvExpr::leaf(
                &format!("proof_array_{}_cell_{cell}", term.index()),
                shape.leaf_width(),
            ));
        }
        Ok(FiniteArrayExpr { shape, cells })
    }

    pub(super) fn lower_const_array(
        &mut self,
        shape: FiniteSortShape,
        args: &[TermId],
    ) -> Result<FiniteArrayExpr, String> {
        let [fill_term] = args else {
            return Err("canonical `const-array` requires exactly one argument".to_string());
        };
        let element_shape = self.element_shape_or_resource(&shape)?;
        self.require_term_shape(*fill_term, &element_shape, "const-array fill")?;
        let fill = self.lower(*fill_term)?;
        let fill_nodes = proof_producing_expr_nodes(&fill).inspect_err(|_| {
            self.resource_exhausted = true;
        })?;
        let domain = shape.outer_index()?.domain_size();
        let output_nodes = fill_nodes.checked_mul(domain).ok_or_else(|| {
            self.resource_exhausted = true;
            "const-array node-count overflow".to_string()
        })?;
        self.preflight_expr_nodes(output_nodes, "const-array")?;
        self.charge_array_work(shape.scalar_cells, "const-array")?;
        let fill_cells = self.expression_into_cells(fill, &element_shape, "const-array fill")?;
        let mut cells = Vec::new();
        self.reserve_cells(&mut cells, shape.scalar_cells, "const-array")?;
        for _ in 0..domain {
            cells.extend(fill_cells.iter().cloned());
        }
        Ok(FiniteArrayExpr { shape, cells })
    }

    pub(super) fn lower_array_store(
        &mut self,
        shape: FiniteSortShape,
        args: &[TermId],
    ) -> Result<FiniteArrayExpr, String> {
        let [base_term, index_term, value_term] = args else {
            return Err("canonical `store` requires exactly three arguments".to_string());
        };
        self.require_term_shape(*base_term, &shape, "store base")?;
        let index_sort = shape.outer_index()?;
        self.require_term_shape(*index_term, &index_sort.scalar_shape(), "store index")?;
        let element_shape = self.element_shape_or_resource(&shape)?;
        self.require_term_shape(*value_term, &element_shape, "store value")?;

        let base = self.lower_array_value(*base_term, &shape, "store base")?;
        let index = self.lower_index(*index_term, index_sort)?;
        let value_expr = self.lower(*value_term)?;
        let value = self.expression_into_cells(value_expr, &element_shape, "store value")?;
        let conditions = self.complete_index_conditions(index, index_sort)?;
        let predicted = self.store_node_count(&base, &value, &conditions, &shape)?;
        self.preflight_expr_nodes(predicted, "finite-array store")?;
        self.charge_array_work(shape.scalar_cells, "finite-array store")?;

        let element_cells = element_shape.scalar_cells;
        let mut cells = Vec::new();
        self.reserve_cells(&mut cells, shape.scalar_cells, "finite-array store")?;
        for (point, condition) in conditions.into_iter().enumerate() {
            let offset = point * element_cells;
            for (cell, value_cell) in value.iter().enumerate() {
                cells.push(Self::mux_leaf(
                    condition.clone(),
                    value_cell.clone(),
                    base.cells[offset + cell].clone(),
                    shape.leaf_width(),
                ));
            }
        }
        Ok(FiniteArrayExpr { shape, cells })
    }

    pub(super) fn lower_array_ite(
        &mut self,
        shape: FiniteSortShape,
        condition_term: TermId,
        then_term: TermId,
        else_term: TermId,
    ) -> Result<FiniteArrayExpr, String> {
        self.require_term_shape(
            condition_term,
            &FiniteSortShape::bool_scalar(),
            "array ite condition",
        )?;
        self.require_term_shape(then_term, &shape, "array ite then branch")?;
        self.require_term_shape(else_term, &shape, "array ite else branch")?;
        let condition = self.lower_bool(condition_term)?;
        let then_array = self.lower_array_value(then_term, &shape, "array ite then branch")?;
        let else_array = self.lower_array_value(else_term, &shape, "array ite else branch")?;
        let condition_nodes = bv_expr_nodes(&condition).inspect_err(|_| {
            self.resource_exhausted = true;
        })?;
        let mask_nodes = condition_nodes + usize::from(shape.leaf_width() > 1);
        let predicted = self
            .array_expr_nodes(&then_array, "finite-array ite then branch")?
            .checked_add(self.array_expr_nodes(&else_array, "finite-array ite else branch")?)
            .and_then(|nodes| {
                shape
                    .scalar_cells
                    .checked_mul(4 + 2 * mask_nodes)
                    .and_then(|extra| nodes.checked_add(extra))
            })
            .ok_or_else(|| {
                self.resource_exhausted = true;
                "finite-array ite node-count overflow".to_string()
            })?;
        self.preflight_expr_nodes(predicted, "finite-array ite")?;
        self.charge_array_work(shape.scalar_cells, "finite-array ite")?;

        let mut cells = Vec::new();
        self.reserve_cells(&mut cells, shape.scalar_cells, "finite-array ite")?;
        for (then_cell, else_cell) in then_array.cells.into_iter().zip(else_array.cells) {
            cells.push(Self::mux_leaf(
                condition.clone(),
                then_cell,
                else_cell,
                shape.leaf_width(),
            ));
        }
        Ok(FiniteArrayExpr { shape, cells })
    }

    pub(super) fn select_complete_domain(
        &mut self,
        array: &FiniteArrayExpr,
        element_shape: &FiniteSortShape,
        index: BvExpr,
        index_sort: FiniteIndexSort,
    ) -> Result<Vec<BvExpr>, String> {
        let conditions = self.complete_index_conditions(index, index_sort)?;
        let predicted = self.select_node_count(array, element_shape, &conditions)?;
        self.preflight_expr_nodes(predicted, "finite-array select")?;
        let work = conditions
            .len()
            .checked_mul(element_shape.scalar_cells)
            .ok_or_else(|| {
                self.resource_exhausted = true;
                "finite-array select work overflow".to_string()
            })?;
        self.charge_array_work(work, "finite-array select")?;

        let mut cells = Vec::new();
        self.reserve_cells(
            &mut cells,
            element_shape.scalar_cells,
            "finite-array select result",
        )?;
        for cell in 0..element_shape.scalar_cells {
            let mut candidates = Vec::new();
            self.reserve_cells(
                &mut candidates,
                conditions.len(),
                "finite-array select candidates",
            )?;
            for (point, condition) in conditions.iter().enumerate() {
                let source = point * element_shape.scalar_cells + cell;
                candidates.push(BvExpr::and(
                    Self::condition_mask(condition.clone(), element_shape.leaf_width()),
                    array.cells[source].clone(),
                ));
            }
            cells.push(self.balanced_or(candidates, element_shape.leaf_width())?);
        }
        Ok(cells)
    }

    pub(super) fn complete_index_conditions(
        &mut self,
        index: BvExpr,
        index_sort: FiniteIndexSort,
    ) -> Result<Vec<BvExpr>, String> {
        let domain = index_sort.domain_size();
        let index_nodes = bv_expr_nodes(&index).inspect_err(|_| {
            self.resource_exhausted = true;
        })?;
        let condition_nodes = match index_sort {
            FiniteIndexSort::Bool => index_nodes
                .checked_mul(2)
                .and_then(|nodes| nodes.checked_add(1)),
            FiniteIndexSort::BitVec(_) => index_nodes
                .checked_add(2)
                .and_then(|nodes| nodes.checked_mul(domain)),
        }
        .ok_or_else(|| {
            self.resource_exhausted = true;
            "finite-array index-condition node-count overflow".to_string()
        })?;
        self.preflight_expr_nodes(condition_nodes, "finite-array index conditions")?;
        self.charge_array_work(domain, "finite-array index enumeration")?;
        let mut conditions = Vec::new();
        self.reserve_cells(&mut conditions, domain, "finite-array index conditions")?;
        match index_sort {
            FiniteIndexSort::Bool => {
                conditions.push(BvExpr::not(index.clone()));
                conditions.push(index);
            }
            FiniteIndexSort::BitVec(width) => {
                for point in 0..domain {
                    conditions.push(BvExpr::eq(
                        index.clone(),
                        BvExpr::const_val(point as u128, width),
                    ));
                }
            }
        }
        Ok(conditions)
    }

    pub(super) fn lower_index(
        &mut self,
        term: TermId,
        index_sort: FiniteIndexSort,
    ) -> Result<BvExpr, String> {
        match index_sort {
            FiniteIndexSort::Bool => self.lower_bool(term),
            FiniteIndexSort::BitVec(expected) => {
                let (index, actual) = self.lower_bv(term)?;
                if actual != expected {
                    return Err(format!(
                        "array index lowers to BitVec({actual}), expected BitVec({expected})"
                    ));
                }
                Ok(index)
            }
        }
    }

    pub(super) fn lower_array_value(
        &mut self,
        term: TermId,
        expected: &FiniteSortShape,
        context: &str,
    ) -> Result<FiniteArrayExpr, String> {
        match self.lower(term)? {
            ProofProducingExpr::Array(array) if &array.shape == expected => Ok(array),
            ProofProducingExpr::Array(_) => {
                Err(format!("{context} lowers to a different array sort"))
            }
            _ => Err(format!("{context} does not lower to an array")),
        }
    }

    pub(super) fn expression_into_cells(
        &mut self,
        expression: ProofProducingExpr,
        expected: &FiniteSortShape,
        context: &str,
    ) -> Result<Vec<BvExpr>, String> {
        match (expression, expected.indices.is_empty(), expected.leaf) {
            (ProofProducingExpr::Bool(expr), true, FiniteScalarSort::Bool) => {
                let mut cells = Vec::new();
                self.reserve_cells(&mut cells, 1, context)?;
                cells.push(expr);
                Ok(cells)
            }
            (
                ProofProducingExpr::BitVec(expr, actual),
                true,
                FiniteScalarSort::BitVec(expected),
            ) if actual == expected => {
                let mut cells = Vec::new();
                self.reserve_cells(&mut cells, 1, context)?;
                cells.push(expr);
                Ok(cells)
            }
            (ProofProducingExpr::Array(array), false, _) if array.shape == *expected => {
                Ok(array.cells)
            }
            _ => Err(format!("{context} lowers to a value of the wrong sort")),
        }
    }

    pub(super) fn cells_into_expression(
        &mut self,
        shape: FiniteSortShape,
        mut cells: Vec<BvExpr>,
    ) -> Result<ProofProducingExpr, String> {
        if cells.len() != shape.scalar_cells {
            return Err("finite-array scalarization produced the wrong cell count".to_string());
        }
        if shape.is_array() {
            return Ok(ProofProducingExpr::Array(FiniteArrayExpr { shape, cells }));
        }
        let cell = cells
            .pop()
            .ok_or_else(|| "finite-array scalar result has no cell".to_string())?;
        Ok(match shape.leaf {
            FiniteScalarSort::Bool => ProofProducingExpr::Bool(cell),
            FiniteScalarSort::BitVec(width) => ProofProducingExpr::BitVec(cell, width),
        })
    }
}
