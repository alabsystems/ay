// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Exact source lowering for recursively finite Bool/BV arrays.
//!
//! Every admitted array is scalarized over its complete finite index domain.
//! Consequently array equality is extensional equality of every scalar cell,
//! and `select`, `store`, `const-array`, and array `ite` are exact encodings,
//! not theory lemmas or production-solver hints. The resulting Bool/BV graph
//! still goes through the independent bit-blast, LRAT production, and replay
//! path in the parent module.

use ay_core::{Sort, Symbol, TermData, TermId};

use super::{
    balanced_bool_expr, BvExpr, ProofProducingExpr, ProofProducingLowerer,
    MAX_PROOF_PRODUCING_INTERNAL_BV_WIDTH,
};

mod budget;
mod lowering;

/// Full-domain enumeration is exponential in an index width. Eight bits keeps
/// each individual domain at 256 points while the independent aggregate cell,
/// expression, work, and deadline limits below remain authoritative.
pub(super) const MAX_EXACT_FINITE_ARRAY_INDEX_WIDTH: u32 = 8;

/// Bound recursive sort walks independently of source-expression depth.
pub(super) const MAX_EXACT_FINITE_ARRAY_NESTING: usize = 32;

/// Maximum number of terminal Bool/BV cells represented by one array value.
pub(super) const MAX_EXACT_FINITE_ARRAY_SCALAR_CELLS: usize = 4_096;

/// Deterministic scalarization-work envelope, separate from the downstream
/// bit-blast/SAT/replay limits.
const MAX_EXACT_FINITE_ARRAY_WORK: usize = 100_000;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum FiniteIndexSort {
    Bool,
    BitVec(u32),
}

impl FiniteIndexSort {
    fn domain_size(self) -> usize {
        match self {
            Self::Bool => 2,
            Self::BitVec(width) => 1_usize << width,
        }
    }

    fn scalar_shape(self) -> FiniteSortShape {
        match self {
            Self::Bool => FiniteSortShape::bool_scalar(),
            Self::BitVec(width) => FiniteSortShape::bitvec_scalar(width),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum FiniteScalarSort {
    Bool,
    BitVec(u32),
}

impl FiniteScalarSort {
    fn width(self) -> u32 {
        match self {
            Self::Bool => 1,
            Self::BitVec(width) => width,
        }
    }
}

/// A bounded, non-recursive descriptor for a scalar or recursively nested
/// array sort. `indices` is ordered outermost to innermost.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct FiniteSortShape {
    indices: Box<[FiniteIndexSort]>,
    leaf: FiniteScalarSort,
    scalar_cells: usize,
}

impl FiniteSortShape {
    pub(super) fn bool_scalar() -> Self {
        Self {
            indices: Box::new([]),
            leaf: FiniteScalarSort::Bool,
            scalar_cells: 1,
        }
    }

    pub(super) fn bitvec_scalar(width: u32) -> Self {
        Self {
            indices: Box::new([]),
            leaf: FiniteScalarSort::BitVec(width),
            scalar_cells: 1,
        }
    }

    fn is_array(&self) -> bool {
        !self.indices.is_empty()
    }

    fn leaf_width(&self) -> u32 {
        self.leaf.width()
    }

    fn outer_index(&self) -> Result<FiniteIndexSort, String> {
        self.indices
            .first()
            .copied()
            .ok_or_else(|| "finite-array operation received a scalar sort".to_string())
    }

    fn element_shape(&self) -> Result<Self, String> {
        let outer = self.outer_index()?;
        let mut indices = Vec::new();
        indices
            .try_reserve_exact(self.indices.len().saturating_sub(1))
            .map_err(|error| format!("finite-array element-shape allocation failed: {error}"))?;
        indices.extend_from_slice(&self.indices[1..]);
        Ok(Self {
            indices: indices.into_boxed_slice(),
            leaf: self.leaf,
            scalar_cells: self.scalar_cells / outer.domain_size(),
        })
    }
}

#[derive(Clone)]
pub(super) struct FiniteArrayExpr {
    shape: FiniteSortShape,
    pub(super) cells: Vec<BvExpr>,
}

pub(super) enum FiniteSourceSort {
    Bool,
    BitVec(u32),
    Array(FiniteSortShape),
}

pub(super) struct SourceSortError {
    reason: String,
    resource_limit: bool,
}

impl SourceSortError {
    fn unsupported(reason: impl Into<String>) -> Self {
        Self {
            reason: reason.into(),
            resource_limit: false,
        }
    }

    fn resource(reason: impl Into<String>) -> Self {
        Self {
            reason: reason.into(),
            resource_limit: true,
        }
    }

    pub(super) fn is_resource_limit(&self) -> bool {
        self.resource_limit
    }

    pub(super) fn into_reason(self) -> String {
        self.reason
    }
}

pub(super) fn classify_source_sort(sort: &Sort) -> Result<FiniteSourceSort, SourceSortError> {
    match sort {
        Sort::Bool => Ok(FiniteSourceSort::Bool),
        Sort::BitVec(width)
            if width.width > 0 && width.width <= MAX_PROOF_PRODUCING_INTERNAL_BV_WIDTH =>
        {
            Ok(FiniteSourceSort::BitVec(width.width))
        }
        Sort::BitVec(width) => Err(SourceSortError::unsupported(format!(
            "BitVec width {} is outside proof-producing range 1..={MAX_PROOF_PRODUCING_INTERNAL_BV_WIDTH}",
            width.width
        ))),
        Sort::Array(_) => classify_finite_shape(sort).map(FiniteSourceSort::Array),
        other => Err(SourceSortError::unsupported(format!(
            "unsupported source sort {other:?}; expected Bool, BitVec, or a recursively finite array"
        ))),
    }
}

fn classify_finite_shape(sort: &Sort) -> Result<FiniteSortShape, SourceSortError> {
    let mut cursor = sort;
    let mut indices = Vec::new();
    let mut scalar_cells = Some(1_usize);
    let mut deferred_resource = None;

    loop {
        match cursor {
            Sort::Array(array) => {
                if indices.len() >= MAX_EXACT_FINITE_ARRAY_NESTING {
                    return Err(SourceSortError::resource(format!(
                        "finite-array nesting exceeds {MAX_EXACT_FINITE_ARRAY_NESTING}"
                    )));
                }
                let index = match &array.index_sort {
                    Sort::Bool => FiniteIndexSort::Bool,
                    Sort::BitVec(width) if width.width == 0 => {
                        return Err(SourceSortError::unsupported(
                            "finite-array BitVec index width must be nonzero",
                        ));
                    }
                    Sort::BitVec(width) => {
                        if width.width > MAX_EXACT_FINITE_ARRAY_INDEX_WIDTH
                            && deferred_resource.is_none()
                        {
                            deferred_resource = Some(format!(
                                "finite-array BitVec index width {} exceeds full-domain limit {MAX_EXACT_FINITE_ARRAY_INDEX_WIDTH}",
                                width.width
                            ));
                            scalar_cells = None;
                        }
                        FiniteIndexSort::BitVec(width.width)
                    }
                    other => {
                        return Err(SourceSortError::unsupported(format!(
                            "finite-array index sort {other:?} is neither Bool nor BitVec"
                        )));
                    }
                };
                if let Some(current_cells) = scalar_cells {
                    match current_cells.checked_mul(index.domain_size()) {
                        Some(next_cells) if next_cells <= MAX_EXACT_FINITE_ARRAY_SCALAR_CELLS => {
                            scalar_cells = Some(next_cells);
                        }
                        Some(next_cells) => {
                            deferred_resource = Some(format!(
                                "finite-array scalarization requires {next_cells} cells, above limit {MAX_EXACT_FINITE_ARRAY_SCALAR_CELLS}"
                            ));
                            scalar_cells = None;
                        }
                        None => {
                            deferred_resource =
                                Some("finite-array scalar-cell count overflow".to_string());
                            scalar_cells = None;
                        }
                    }
                }
                indices.try_reserve(1).map_err(|error| {
                    SourceSortError::resource(format!(
                        "finite-array sort descriptor allocation failed: {error}"
                    ))
                })?;
                indices.push(index);
                cursor = &array.element_sort;
            }
            Sort::Bool => {
                return finish_finite_shape(
                    indices,
                    FiniteScalarSort::Bool,
                    scalar_cells,
                    deferred_resource,
                );
            }
            Sort::BitVec(width)
                if width.width > 0 && width.width <= MAX_PROOF_PRODUCING_INTERNAL_BV_WIDTH =>
            {
                return finish_finite_shape(
                    indices,
                    FiniteScalarSort::BitVec(width.width),
                    scalar_cells,
                    deferred_resource,
                );
            }
            Sort::BitVec(width) => {
                return Err(SourceSortError::unsupported(format!(
                    "finite-array leaf BitVec width {} is outside proof-producing range 1..={MAX_PROOF_PRODUCING_INTERNAL_BV_WIDTH}",
                    width.width
                )));
            }
            other => {
                return Err(SourceSortError::unsupported(format!(
                    "finite-array leaf sort {other:?} is neither Bool nor BitVec"
                )));
            }
        }
    }
}

fn finish_finite_shape(
    indices: Vec<FiniteIndexSort>,
    leaf: FiniteScalarSort,
    scalar_cells: Option<usize>,
    deferred_resource: Option<String>,
) -> Result<FiniteSortShape, SourceSortError> {
    if let Some(reason) = deferred_resource {
        return Err(SourceSortError::resource(reason));
    }
    let Some(scalar_cells) = scalar_cells else {
        return Err(SourceSortError::resource(
            "finite-array scalar-cell count is unavailable",
        ));
    };
    Ok(FiniteSortShape {
        indices: indices.into_boxed_slice(),
        leaf,
        scalar_cells,
    })
}

impl ProofProducingLowerer<'_> {
    pub(super) fn lower_exact_finite_array_node(
        &mut self,
        term: TermId,
        shape: FiniteSortShape,
        data: TermData,
    ) -> Result<ProofProducingExpr, String> {
        if !shape.is_array() {
            return Err("finite-array node has a scalar source sort".to_string());
        }
        let array = match data {
            TermData::Var(..) => self.lower_array_variable(term, shape)?,
            TermData::App(Symbol::Named(name), args) if name == "const-array" => {
                self.lower_const_array(shape, &args)?
            }
            TermData::App(Symbol::Named(name), args) if name == "store" => {
                self.lower_array_store(shape, &args)?
            }
            TermData::App(Symbol::Named(name), args) if name == "select" => {
                match self.lower_exact_finite_array_select(term, &args, &shape)? {
                    ProofProducingExpr::Array(array) => array,
                    _ => {
                        return Err(
                            "nested array select did not produce its declared array sort"
                                .to_string(),
                        );
                    }
                }
            }
            TermData::Ite(condition, then_term, else_term) => {
                self.lower_array_ite(shape, condition, then_term, else_term)?
            }
            TermData::App(symbol, _) => {
                return Err(format!(
                    "unsupported finite-array operator `{symbol}`; expected const-array, store, select, or ite"
                ));
            }
            other => return Err(format!("unsupported finite-array source node {other:?}")),
        };
        self.used_exact_finite_arrays = true;
        Ok(ProofProducingExpr::Array(array))
    }

    pub(super) fn lower_exact_finite_array_select(
        &mut self,
        result_term: TermId,
        args: &[TermId],
        expected_result: &FiniteSortShape,
    ) -> Result<ProofProducingExpr, String> {
        let [array_term, index_term] = args else {
            return Err("canonical `select` requires exactly two arguments".to_string());
        };
        self.require_term_shape(result_term, expected_result, "select result")?;
        let array_shape = self.term_shape(*array_term)?;
        if !array_shape.is_array() {
            return Err("`select` first argument is not an array".to_string());
        }
        let element_shape = self.element_shape_or_resource(&array_shape)?;
        if &element_shape != expected_result {
            return Err("`select` result sort disagrees with the array element sort".to_string());
        }
        let index_sort = array_shape.outer_index()?;
        self.require_term_shape(*index_term, &index_sort.scalar_shape(), "select index")?;

        let array = self.lower_array_value(*array_term, &array_shape, "select array")?;
        let index = self.lower_index(*index_term, index_sort)?;
        let cells = self.select_complete_domain(&array, &element_shape, index, index_sort)?;
        let result = self.cells_into_expression(element_shape, cells)?;
        self.used_exact_finite_arrays = true;
        Ok(result)
    }

    pub(super) fn lower_exact_finite_array_equality(
        &mut self,
        lhs: FiniteArrayExpr,
        rhs: FiniteArrayExpr,
    ) -> Result<BvExpr, String> {
        if lhs.shape != rhs.shape || lhs.cells.len() != rhs.cells.len() {
            return Err("array equality operands have different finite sorts".to_string());
        }
        let lhs_nodes = self.array_expr_nodes(&lhs, "finite-array equality lhs")?;
        let rhs_nodes = self.array_expr_nodes(&rhs, "finite-array equality rhs")?;
        let equality_nodes = lhs
            .cells
            .len()
            .checked_mul(2)
            .and_then(|nodes| nodes.checked_sub(1))
            .and_then(|gates| lhs_nodes.checked_add(rhs_nodes)?.checked_add(gates))
            .ok_or_else(|| {
                self.resource_exhausted = true;
                "finite-array equality node-count overflow".to_string()
            })?;
        self.preflight_expr_nodes(equality_nodes, "finite-array equality")?;
        self.charge_array_work(lhs.cells.len(), "finite-array equality")?;
        let mut equalities = Vec::new();
        self.reserve_cells(&mut equalities, lhs.cells.len(), "array equality")?;
        for (left, right) in lhs.cells.into_iter().zip(rhs.cells) {
            equalities.push(BvExpr::eq(left, right));
        }
        let equality = balanced_bool_expr(equalities, true, BvExpr::and).inspect_err(|_| {
            self.resource_exhausted = true;
        })?;
        self.used_exact_finite_arrays = true;
        Ok(equality)
    }
}
