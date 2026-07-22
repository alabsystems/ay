// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::DetHashMap as HashMap;

use super::{Context, ElaborateError, Result};
use crate::command;
use crate::sexp::{PARSE_STACK_RED_ZONE, PARSE_STACK_SIZE};
use ay_core::{Sort, TermId};

/// Match the established CHC parser bound. SMT terms are represented densely
/// during bit-blasting, so accepting a larger compact width would permit an
/// unbounded allocation before the solver's resource limit can intervene.
pub(super) const MAX_BITVECTOR_WIDTH: u32 = 1 << 20;

/// `FpPrecision` exposes its exponent bias as `u32`; formats with 32 or more
/// exponent bits cannot be represented by that API without overflowing.
pub(super) const MAX_FP_EXPONENT_BITS: u32 = 31;

/// Significands are bit-blasted densely. Use the same width envelope as BV.
pub(super) const MAX_FP_SIGNIFICAND_BITS: u32 = MAX_BITVECTOR_WIDTH;

impl Context {
    /// Run one lazy sort-synonym expansion while keeping the recursion guard
    /// balanced even if an internal bug panics during recursive elaboration.
    /// This mirrors the unwind-safe restoration used for native global-
    /// declaration tracking: a caught panic must not poison later work on the
    /// same context with a false "recursive sort synonym" diagnosis.
    pub(super) fn with_sort_synonym_expansion<T>(
        &mut self,
        name: String,
        operation: impl FnOnce(&mut Self) -> T,
    ) -> T {
        self.expanding_sort_synonyms.push(name);
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| operation(self)));
        self.expanding_sort_synonyms.pop();
        match result {
            Ok(value) => value,
            Err(payload) => std::panic::resume_unwind(payload),
        }
    }

    pub(super) fn expect_bv_operand_width(&self, operation: &str, operand: TermId) -> Result<u32> {
        match self.terms.sort(operand) {
            Sort::BitVec(bv) => Ok(bv.width),
            actual => Err(ElaborateError::SortMismatch {
                expected: format!("(_ BitVec n): {operation} operand"),
                actual: actual.to_string(),
            }),
        }
    }

    pub(super) fn expect_int_operand(&self, operation: &str, operand: TermId) -> Result<()> {
        match self.terms.sort(operand) {
            Sort::Int => Ok(()),
            actual => Err(ElaborateError::SortMismatch {
                expected: format!("Int: {operation} operand"),
                actual: actual.to_string(),
            }),
        }
    }

    pub(super) fn expect_floating_point_operand(
        &self,
        operation: &str,
        operand: TermId,
    ) -> Result<(u32, u32)> {
        match self.terms.sort(operand) {
            Sort::FloatingPoint(eb, sb) => Ok((*eb, *sb)),
            actual => Err(ElaborateError::SortMismatch {
                expected: format!("FloatingPoint: {operation} operand"),
                actual: actual.to_string(),
            }),
        }
    }

    pub(super) fn expect_rounding_mode_operand(
        &self,
        operation: &str,
        operand: TermId,
    ) -> Result<()> {
        match self.terms.sort(operand) {
            Sort::Uninterpreted(name) if name == "RoundingMode" => Ok(()),
            actual => Err(ElaborateError::SortMismatch {
                expected: format!("RoundingMode: {operation} operand"),
                actual: actual.to_string(),
            }),
        }
    }

    pub(super) fn validate_indexed_fp_application(
        &self,
        operation: &str,
        indices: &[u32],
        args: &[TermId],
    ) -> Result<Sort> {
        match operation {
            "to_fp" => {
                if indices.len() != 2 {
                    return Err(ElaborateError::InvalidConstant(
                        "to_fp requires 2 indices (eb sb)".to_string(),
                    ));
                }
                let fp_sort = Self::checked_floating_point_sort(indices[0], indices[1])?;
                match args {
                    [source] => {
                        let source_width = self.expect_bv_operand_width("to_fp", *source)?;
                        let expected_width =
                            indices[0].checked_add(indices[1]).ok_or_else(|| {
                                ElaborateError::InvalidConstant(
                                    "to_fp source width overflows".to_string(),
                                )
                            })?;
                        Self::checked_bitvector_sort(expected_width)?;
                        if source_width != expected_width {
                            return Err(ElaborateError::SortMismatch {
                                expected: format!("(_ BitVec {expected_width})"),
                                actual: format!("(_ BitVec {source_width})"),
                            });
                        }
                    }
                    [rounding_mode, source] => {
                        self.expect_rounding_mode_operand("to_fp", *rounding_mode)?;
                        if !matches!(
                            self.terms.sort(*source),
                            Sort::FloatingPoint(_, _) | Sort::Real | Sort::Int | Sort::BitVec(_)
                        ) {
                            return Err(ElaborateError::SortMismatch {
                                expected: "FloatingPoint, Real, Int, or BitVec".to_string(),
                                actual: self.terms.sort(*source).to_string(),
                            });
                        }
                    }
                    _ => {
                        return Err(ElaborateError::InvalidConstant(
                            "to_fp requires 1 argument, or a rounding mode and value".to_string(),
                        ));
                    }
                }
                Ok(fp_sort)
            }
            "to_fp_unsigned" => {
                if indices.len() != 2 || args.len() != 2 {
                    return Err(ElaborateError::InvalidConstant(
                        "to_fp_unsigned requires 2 indices, a rounding mode, and a BitVec"
                            .to_string(),
                    ));
                }
                let fp_sort = Self::checked_floating_point_sort(indices[0], indices[1])?;
                self.expect_rounding_mode_operand("to_fp_unsigned", args[0])?;
                self.expect_bv_operand_width("to_fp_unsigned", args[1])?;
                Ok(fp_sort)
            }
            "fp.to_ubv" | "fp.to_sbv" => {
                if indices.len() != 1 || args.len() != 2 {
                    return Err(ElaborateError::InvalidConstant(format!(
                        "{operation} requires 1 width index, a rounding mode, and a FloatingPoint value"
                    )));
                }
                let bv_sort = Self::checked_bitvector_sort(indices[0])?;
                self.expect_rounding_mode_operand(operation, args[0])?;
                self.expect_floating_point_operand(operation, args[1])?;
                Ok(bv_sort)
            }
            _ => Err(ElaborateError::Unsupported(format!(
                "unknown indexed floating-point operation: {operation}"
            ))),
        }
    }

    pub(super) fn checked_bitvector_sort(width: u32) -> Result<Sort> {
        if width == 0 || width > MAX_BITVECTOR_WIDTH {
            return Err(ElaborateError::InvalidConstant(format!(
                "BitVec width {width} is outside the supported range 1..={MAX_BITVECTOR_WIDTH}"
            )));
        }
        Ok(Sort::bitvec(width))
    }

    pub(super) fn checked_floating_point_sort(eb: u32, sb: u32) -> Result<Sort> {
        if !(2..=MAX_FP_EXPONENT_BITS).contains(&eb) {
            return Err(ElaborateError::InvalidConstant(format!(
                "FloatingPoint exponent width {eb} is outside the supported range 2..={MAX_FP_EXPONENT_BITS}"
            )));
        }
        if !(2..=MAX_FP_SIGNIFICAND_BITS).contains(&sb) {
            return Err(ElaborateError::InvalidConstant(format!(
                "FloatingPoint significand width {sb} is outside the supported range 2..={MAX_FP_SIGNIFICAND_BITS}"
            )));
        }
        Ok(Sort::FloatingPoint(eb, sb))
    }

    pub(super) fn checked_bv_extract(
        &mut self,
        hi: u32,
        lo: u32,
        operand: TermId,
    ) -> Result<TermId> {
        if hi < lo {
            return Err(ElaborateError::InvalidConstant(format!(
                "extract high index {hi} is below low index {lo}"
            )));
        }
        let result_width = hi
            .checked_sub(lo)
            .and_then(|width| width.checked_add(1))
            .ok_or_else(|| {
                ElaborateError::InvalidConstant("extract result width overflows".to_string())
            })?;
        Self::checked_bitvector_sort(result_width)?;
        let operand_width = self.expect_bv_operand_width("extract", operand)?;
        if hi >= operand_width {
            return Err(ElaborateError::InvalidConstant(format!(
                "extract high index {hi} is out of range for bit-vector width {operand_width}"
            )));
        }
        Ok(self.terms.mk_bvextract(hi, lo, operand))
    }

    pub(super) fn check_bv_extension_width(
        &self,
        operation: &str,
        amount: u32,
        operand: TermId,
    ) -> Result<()> {
        let operand_width = self.expect_bv_operand_width(operation, operand)?;
        let width = operand_width.checked_add(amount).ok_or_else(|| {
            ElaborateError::InvalidConstant(format!("{operation} result width overflows"))
        })?;
        Self::checked_bitvector_sort(width)?;
        Ok(())
    }

    pub(super) fn check_bv_repeat_width(&self, count: u32, operand: TermId) -> Result<()> {
        let operand_width = self.expect_bv_operand_width("repeat", operand)?;
        let width = operand_width.checked_mul(count).ok_or_else(|| {
            ElaborateError::InvalidConstant("repeat result width overflows".to_string())
        })?;
        Self::checked_bitvector_sort(width)?;
        Ok(())
    }

    /// Convert a parsed sort to internal sort.
    ///
    /// Takes `&mut self` because elaborating an applied parametric-datatype sort
    /// `(Name A1 .. An)` lazily monomorphizes the instance (registering its
    /// constructors/selectors/testers) on first use — see
    /// [`Context::instantiate_parametric_datatype`].
    pub(crate) fn elaborate_sort(&mut self, sort: &command::Sort) -> Result<Sort> {
        let empty: HashMap<String, Sort> = HashMap::default();
        self.elaborate_sort_inner(sort, &empty)
    }

    /// Core sort elaboration, threading a type-parameter substitution `subst`.
    ///
    /// `subst` maps a parametric datatype's bound type-parameter names (e.g.
    /// `T`) to the already-elaborated argument sorts at a given instantiation.
    /// It is empty for every non-template call, so monomorphic elaboration is
    /// unchanged.
    pub(super) fn elaborate_sort_inner(
        &mut self,
        sort: &command::Sort,
        subst: &HashMap<String, Sort>,
    ) -> Result<Sort> {
        // Stack-safety guard for deeply nested sorts (Array/Seq/Set/Multiset/Map),
        // which would otherwise overflow the stack on adversarial nesting.
        stacker::maybe_grow(PARSE_STACK_RED_ZONE, PARSE_STACK_SIZE, || {
            self.elaborate_sort_dispatch(sort, subst)
        })
    }

    fn elaborate_sort_dispatch(
        &mut self,
        sort: &command::Sort,
        subst: &HashMap<String, Sort>,
    ) -> Result<Sort> {
        match sort {
            command::Sort::Simple(name) => {
                // A bound type parameter substitutes to its instantiation sort.
                if let Some(arg) = subst.get(name) {
                    return Ok(arg.clone());
                }
                match name.as_str() {
                    "Bool" => Ok(Sort::Bool),
                    "Int" => Ok(Sort::Int),
                    "Real" => Ok(Sort::Real),
                    "String" => Ok(Sort::String),
                    "RegLan" => Ok(Sort::RegLan),
                    // SMT-LIB FloatingPoint theory sort abbreviations. Without these
                    // a `(declare-fun x () Float32)` would fall through to the
                    // Uninterpreted fallback below, and `x` would never route through
                    // the eager FP-to-BV bit-blaster (the structural-`=` branch in
                    // bitblast_fp_predicate is gated on Sort::FloatingPoint). That
                    // gap caused symbolic-variable QF_FP conflicts such as
                    // `x = 1.0 AND x = 2.0` to be reported SAT (false-SAT).
                    "Float16" => Ok(Sort::FloatingPoint(5, 11)),
                    "Float32" => Ok(Sort::FloatingPoint(8, 24)),
                    "Float64" => Ok(Sort::FloatingPoint(11, 53)),
                    "Float128" => Ok(Sort::FloatingPoint(15, 113)),
                    other => {
                        if let Some(s) = self.sort_defs.get(other) {
                            Ok(s.clone())
                        } else {
                            Ok(Sort::Uninterpreted(other.to_string()))
                        }
                    }
                }
            }
            command::Sort::Indexed(name, indices) => match name.as_str() {
                "BitVec" => {
                    if indices.len() != 1 {
                        return Err(ElaborateError::InvalidConstant(
                            "BitVec sort requires exactly 1 width index".to_string(),
                        ));
                    }
                    let width: u32 = indices
                        .first()
                        .and_then(command::Index::as_numeral)
                        .and_then(|width| width.parse().ok())
                        .ok_or_else(|| {
                            ElaborateError::InvalidConstant(
                                "BitVec width must be a numeral token".to_string(),
                            )
                        })?;
                    Self::checked_bitvector_sort(width)
                }
                "FloatingPoint" => {
                    if indices.len() != 2 {
                        return Err(ElaborateError::InvalidConstant(
                            "FloatingPoint sort requires exactly 2 indices (eb sb)".to_string(),
                        ));
                    }
                    let eb: u32 = indices
                        .first()
                        .and_then(command::Index::as_numeral)
                        .and_then(|width| width.parse().ok())
                        .ok_or_else(|| {
                            ElaborateError::InvalidConstant(
                                "FloatingPoint exponent bits must be a numeral token".to_string(),
                            )
                        })?;
                    let sb: u32 = indices
                        .get(1)
                        .and_then(command::Index::as_numeral)
                        .and_then(|width| width.parse().ok())
                        .ok_or_else(|| {
                            ElaborateError::InvalidConstant(
                                "FloatingPoint significand bits must be a numeral token"
                                    .to_string(),
                            )
                        })?;
                    Self::checked_floating_point_sort(eb, sb)
                }
                other => Err(ElaborateError::Unsupported(format!(
                    "indexed sort: {other}"
                ))),
            },
            command::Sort::Parameterized(name, params) => match name.as_str() {
                "Array" => {
                    if params.len() != 2 {
                        return Err(ElaborateError::InvalidConstant(
                            "Array requires 2 type parameters".to_string(),
                        ));
                    }
                    let index = self.elaborate_sort_inner(&params[0], subst)?;
                    let element = self.elaborate_sort_inner(&params[1], subst)?;
                    Ok(Sort::array(index, element))
                }
                "Seq" => {
                    if params.len() != 1 {
                        return Err(ElaborateError::InvalidConstant(
                            "Seq requires 1 type parameter".to_string(),
                        ));
                    }
                    let element = self.elaborate_sort_inner(&params[0], subst)?;
                    Ok(Sort::seq(element))
                }
                // Finite sets are carried as `Array(T -> Bool)`: membership is
                // `member(s, e) = select(s, e)`. Cardinality and subset are
                // decided natively (ay-set); the array carrier decides
                // membership and set equality (extensionality).
                "Set" => {
                    if params.len() != 1 {
                        return Err(ElaborateError::InvalidConstant(
                            "Set requires 1 type parameter".to_string(),
                        ));
                    }
                    let element = self.elaborate_sort_inner(&params[0], subst)?;
                    Ok(Sort::array(element, Sort::Bool))
                }
                // Multisets (bags) are carried as `Array(T -> Int)`: the count is
                // `count(m, e) = select(m, e)`. Multiset equality is decided by
                // the array carrier (extensionality); count non-negativity and
                // subset are decided natively (ay-multiset) + injected axioms.
                "Multiset" => {
                    if params.len() != 1 {
                        return Err(ElaborateError::InvalidConstant(
                            "Multiset requires 1 type parameter".to_string(),
                        ));
                    }
                    let element = self.elaborate_sort_inner(&params[0], subst)?;
                    Ok(Sort::array(element, Sort::Int))
                }
                // Finite maps are carried as the value array `Array(K -> V)`:
                // `get(m, k) = select(value, k)` gated by the domain. The domain
                // travels alongside as `(map.dom m) : Array(K -> Bool)` and is
                // pushed through the constructors during elaboration. Map
                // equality is decided by the array carrier (extensionality);
                // get/dom read-through and subset are decided natively (ay-map)
                // + injected axioms.
                "Map" => {
                    if params.len() != 2 {
                        return Err(ElaborateError::InvalidConstant(
                            "Map requires 2 type parameters".to_string(),
                        ));
                    }
                    let key = self.elaborate_sort_inner(&params[0], subst)?;
                    let value = self.elaborate_sort_inner(&params[1], subst)?;
                    Ok(Sort::array(key, value))
                }
                // A parameterized sort synonym `(define-sort Name (T..) body)`
                // applied to ground arguments: substitute the type parameters and
                // elaborate the stored body template. (SMT-LIB define-sort; z3 parity)
                other if self.parametric_sort_defs.contains_key(other) => {
                    // Reject a self- or mutually-recursive synonym instead of
                    // overflowing the stack on the lazy template expansion (z3
                    // rejects these at define time as an unknown sort).
                    if self
                        .expanding_sort_synonyms
                        .iter()
                        .any(|n| n.as_str() == other)
                    {
                        return Err(ElaborateError::InvalidConstant(format!(
                            "recursive sort synonym: {other}"
                        )));
                    }
                    // Clone the template to release the immutable borrow before the
                    // `&mut self` elaboration calls below.
                    let (param_names, body) = self
                        .parametric_sort_defs
                        .get(other)
                        .cloned()
                        .ok_or_else(|| {
                            ElaborateError::InvalidConstant(format!(
                                "sort synonym disappeared during expansion: {other}"
                            ))
                        })?;
                    if params.len() != param_names.len() {
                        return Err(ElaborateError::InvalidConstant(format!(
                            "sort synonym {other} expects {} argument(s), got {}",
                            param_names.len(),
                            params.len()
                        )));
                    }
                    // Argument sorts are elaborated under the CURRENT subst (they
                    // may reference an enclosing template's parameters); the body
                    // then sees ONLY this synonym's parameters (lexical scoping).
                    let args: Vec<Sort> = params
                        .iter()
                        .map(|p| self.elaborate_sort_inner(p, subst))
                        .collect::<Result<Vec<_>>>()?;
                    let mut inner: HashMap<String, Sort> = HashMap::default();
                    for (name, arg) in param_names.into_iter().zip(args) {
                        inner.insert(name, arg);
                    }
                    self.with_sort_synonym_expansion(other.to_string(), |context| {
                        context.elaborate_sort_inner(&body, &inner)
                    })
                }
                // A user-declared parametric (polymorphic) datatype applied to
                // ground arguments: lazily monomorphize the instance.
                other if self.parametric_datatypes.contains_key(other) => {
                    let args: Vec<Sort> = params
                        .iter()
                        .map(|p| self.elaborate_sort_inner(p, subst))
                        .collect::<Result<Vec<_>>>()?;
                    self.instantiate_parametric_datatype(other, &args)
                }
                other => Err(ElaborateError::Unsupported(format!(
                    "parameterized sort: {other}"
                ))),
            },
        }
    }
}
