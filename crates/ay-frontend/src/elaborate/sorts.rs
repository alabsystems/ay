// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::DetHashMap as HashMap;

use super::{Context, ElaborateError, Result};
use crate::command;
use crate::sexp::{PARSE_STACK_RED_ZONE, PARSE_STACK_SIZE};
use ay_core::{Constant, Sort, Symbol, TermData, TermId};

/// Match the established CHC parser bound. SMT terms are represented densely
/// during bit-blasting, so accepting a larger compact width would permit an
/// unbounded allocation before the solver's resource limit can intervene.
pub(super) const MAX_BITVECTOR_WIDTH: u32 = 1 << 20;

/// The exponent carrier is u64; 63 bits also keeps its bias in signed i64.
/// Exact arithmetic has separate, smaller work/precision limits.
pub(super) const MAX_FP_EXPONENT_BITS: u32 = 63;

/// Significands are bit-blasted densely. Use the same width envelope as BV.
pub(super) const MAX_FP_SIGNIFICAND_BITS: u32 = MAX_BITVECTOR_WIDTH;

/// Builtin sort families whose availability depends on the selected
/// SMT-LIB logic's signature. z3 rejects a builtin sort outside the
/// declared logic (`unknown sort 'BitVec'`); AY historically accepted
/// every builtin in every logic, which changed verdicts on ill-formed
/// scripts (z3 errors and continues with a trivial problem). The table
/// below is measured against z3 5.1.0 (`declare-const` probes per
/// logic); logics not listed stay permissive. Builtin function symbols
/// are gated against the same table by
/// [`Context::require_logic_builtin_signature`] (DR-59).
pub(super) const FAM_INT: u16 = 1 << 0;
pub(super) const FAM_REAL: u16 = 1 << 1;
pub(super) const FAM_BV: u16 = 1 << 2;
pub(super) const FAM_ARRAY: u16 = 1 << 3;
pub(super) const FAM_STRING: u16 = 1 << 4;
pub(super) const FAM_REGLAN: u16 = 1 << 5;
pub(super) const FAM_SEQ: u16 = 1 << 6;
pub(super) const FAM_FP: u16 = 1 << 7;
pub(super) const FAM_RM: u16 = 1 << 8;
pub(super) const FAM_FF: u16 = 1 << 9;

/// Logics whose shell signature rejects nonlinear arithmetic
/// applications (products of degree ≥ 2, divisions by a non-numeral),
/// measured against z3 5.1.0 with `(* x y)` / `(div x y)` probes over
/// every logic in [`LOGIC_SORT_FAMILIES`]. Quantified `LIA`/`UFDTLIA`
/// accept nonlinear terms; `AUFLIA`/`AUFLIRA`/`LRA`/`UFLRA` reject.
const NONLINEAR_REJECTING_LOGICS: &[&str] = &[
    "AUFLIA",
    "AUFLIRA",
    "LRA",
    "QF_AUFLIA",
    "QF_IDL",
    "QF_LIA",
    "QF_LRA",
    "QF_RDL",
    "QF_S",
    "QF_SLIA",
    "QF_UFIDL",
    "QF_UFLIA",
    "QF_UFLRA",
    "UFLRA",
];

/// Logics whose shell signature admits only difference-arithmetic
/// applications, measured against z3 5.1.0 (`(+ x y)` probes).
/// `QF_UFRDL` is measured unrestricted and is deliberately absent.
const DIFFERENCE_LOGICS: &[&str] = &["QF_IDL", "QF_RDL", "QF_UFIDL"];

/// Logics whose shell signature installs the `^` power operator,
/// measured against z3 5.1.0. Every other measured logic reports
/// `unknown constant ^`; with no logic selected `^` is also known.
const POWER_KNOWN_LOGICS: &[&str] = &["ALL", "EIA", "QF_EIA", "QF_SEQ"];

/// The builtin sort families a (possibly nested) sort mentions.
fn sort_family_mask(sort: &Sort) -> u16 {
    let mut mask = 0u16;
    let mut pending = vec![sort];
    while let Some(current) = pending.pop() {
        match current {
            Sort::Int => mask |= FAM_INT,
            Sort::Real => mask |= FAM_REAL,
            Sort::BitVec(_) => mask |= FAM_BV,
            Sort::String | Sort::Char => mask |= FAM_STRING,
            Sort::RegLan => mask |= FAM_REGLAN,
            Sort::FloatingPoint(..) => mask |= FAM_FP,
            Sort::FiniteField(_) => mask |= FAM_FF,
            Sort::Uninterpreted(name) if name == "RoundingMode" => mask |= FAM_RM,
            Sort::Array(array) => {
                mask |= FAM_ARRAY;
                pending.push(&array.index_sort);
                pending.push(&array.element_sort);
            }
            Sort::Seq(element) => {
                mask |= FAM_SEQ;
                pending.push(element);
            }
            _ => {}
        }
    }
    mask
}

fn is_arithmetic_builtin(name: &str) -> bool {
    matches!(
        name,
        "+" | "-"
            | "~"
            | "*"
            | "/"
            | "div"
            | "mod"
            | "rem"
            | "abs"
            | "<"
            | "<="
            | ">"
            | ">="
            | "^"
            | "to_real"
            | "to_int"
            | "is_int"
    )
}

/// The builtin sort families `logic`'s signature provides, or `None`
/// for a logic with no measured signature (permissive).
const LOGIC_SORT_FAMILIES: &[(&str, u16)] = &[
    (
        "ALL",
        FAM_INT
            | FAM_REAL
            | FAM_BV
            | FAM_STRING
            | FAM_REGLAN
            | FAM_SEQ
            | FAM_FP
            | FAM_RM
            | FAM_ARRAY
            | FAM_FF,
    ),
    ("QF_FF", FAM_FF),
    ("AUFDT", FAM_ARRAY),
    ("AUFDTLIA", FAM_INT | FAM_REAL | FAM_ARRAY),
    ("AUFDTLIRA", FAM_INT | FAM_REAL | FAM_ARRAY),
    ("AUFLIA", FAM_INT | FAM_ARRAY),
    ("AUFLIRA", FAM_INT | FAM_REAL | FAM_ARRAY),
    ("AUFLRA", FAM_INT | FAM_REAL | FAM_ARRAY),
    (
        "EIA",
        FAM_INT
            | FAM_REAL
            | FAM_BV
            | FAM_STRING
            | FAM_REGLAN
            | FAM_SEQ
            | FAM_FP
            | FAM_RM
            | FAM_ARRAY,
    ),
    ("HORN", FAM_INT | FAM_REAL | FAM_BV | FAM_ARRAY),
    ("LIA", FAM_INT | FAM_REAL),
    ("LIRA", FAM_INT | FAM_REAL),
    ("LRA", FAM_REAL),
    ("NIA", FAM_INT | FAM_REAL),
    ("NIRA", FAM_INT | FAM_REAL),
    ("NRA", FAM_REAL),
    ("QF_ABV", FAM_BV | FAM_ARRAY),
    (
        "QF_ABVFP",
        FAM_INT | FAM_REAL | FAM_BV | FAM_FP | FAM_RM | FAM_ARRAY,
    ),
    ("QF_ALIA", FAM_INT | FAM_REAL | FAM_ARRAY),
    ("QF_AUFBV", FAM_BV | FAM_ARRAY),
    ("QF_AUFBVLIA", FAM_INT | FAM_REAL | FAM_BV | FAM_ARRAY),
    ("QF_AUFBVLRA", FAM_INT | FAM_REAL | FAM_BV | FAM_ARRAY),
    ("QF_AUFLIA", FAM_INT | FAM_ARRAY),
    ("QF_AUFLIRA", FAM_INT | FAM_REAL | FAM_ARRAY),
    ("QF_AUFLRA", FAM_INT | FAM_REAL | FAM_ARRAY),
    ("QF_AX", FAM_ARRAY),
    ("QF_BV", FAM_BV),
    ("QF_BVFP", FAM_INT | FAM_REAL | FAM_BV | FAM_FP | FAM_RM),
    ("QF_DT", 0),
    (
        "QF_EIA",
        FAM_INT
            | FAM_REAL
            | FAM_BV
            | FAM_STRING
            | FAM_REGLAN
            | FAM_SEQ
            | FAM_FP
            | FAM_RM
            | FAM_ARRAY,
    ),
    ("QF_FP", FAM_INT | FAM_REAL | FAM_FP | FAM_RM),
    ("QF_FPLRA", FAM_INT | FAM_REAL | FAM_FP | FAM_RM),
    ("QF_IDL", FAM_INT),
    ("QF_LIA", FAM_INT),
    ("QF_LIRA", FAM_INT | FAM_REAL),
    ("QF_LRA", FAM_REAL),
    ("QF_NIA", FAM_INT),
    ("QF_NIRA", FAM_INT | FAM_REAL),
    ("QF_NRA", FAM_REAL),
    ("QF_RDL", FAM_REAL),
    (
        "QF_S",
        FAM_INT | FAM_REAL | FAM_STRING | FAM_REGLAN | FAM_SEQ,
    ),
    (
        "QF_SEQ",
        FAM_INT
            | FAM_REAL
            | FAM_BV
            | FAM_STRING
            | FAM_REGLAN
            | FAM_SEQ
            | FAM_FP
            | FAM_RM
            | FAM_ARRAY,
    ),
    (
        "QF_SLIA",
        FAM_INT | FAM_REAL | FAM_STRING | FAM_REGLAN | FAM_SEQ,
    ),
    (
        "QF_SNIA",
        FAM_INT | FAM_REAL | FAM_STRING | FAM_REGLAN | FAM_SEQ,
    ),
    ("QF_UF", 0),
    ("QF_UFBV", FAM_BV),
    ("QF_UFBVLIA", FAM_INT | FAM_REAL | FAM_BV),
    ("QF_UFDT", 0),
    ("QF_UFIDL", FAM_INT),
    ("QF_UFLIA", FAM_INT),
    ("QF_UFLRA", FAM_REAL),
    ("QF_UFNIA", FAM_INT | FAM_REAL),
    ("QF_UFNIRA", FAM_INT | FAM_REAL),
    ("QF_UFNRA", FAM_REAL),
    ("QF_UFRDL", FAM_INT | FAM_REAL),
    ("UF", 0),
    ("UFDT", 0),
    ("UFDTLIA", FAM_INT | FAM_REAL),
    ("UFDTLIRA", FAM_INT | FAM_REAL),
    ("UFDTLRA", FAM_INT | FAM_REAL),
    ("UFDTNIA", FAM_INT | FAM_REAL),
    ("UFDTNIRA", FAM_INT | FAM_REAL),
    ("UFDTNRA", FAM_INT | FAM_REAL),
    ("UFLIA", FAM_INT | FAM_REAL),
    ("UFLRA", FAM_REAL),
    ("UFNIA", FAM_INT),
    ("UFNIRA", FAM_INT | FAM_REAL),
    ("UFNRA", FAM_INT | FAM_REAL),
];

fn logic_sort_families(logic: &str) -> Option<u16> {
    LOGIC_SORT_FAMILIES
        .iter()
        .find_map(|&(name, mask)| (name == logic).then_some(mask))
}

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
    /// Reject a builtin sort outside the declared logic's signature.
    /// z3 answers the arithmetic-sibling shapes (`Int` where only
    /// `Real` is signed, `Real` where only `Int` is) with its
    /// `logic does not support integers/reals` messages and other
    /// absent families with `unknown sort` (measured; declaration
    /// wrappers like `Invalid constant declaration:` are z3
    /// parser-context prefixes AY does not reproduce — DR-59
    /// residual). No logic selected (or an unmeasured one) is
    /// permissive.
    fn require_logic_sort_family(&self, family: u16, display: &str) -> Result<()> {
        if !self.enforce_logic_sort_signatures || self.strict_logic_compliance {
            return Ok(());
        }
        let Some(logic) = self.logic.as_deref() else {
            return Ok(());
        };
        match logic_sort_families(logic) {
            Some(allowed) if allowed & family == 0 => {
                if family == FAM_INT && allowed & FAM_REAL != 0 {
                    Err(ElaborateError::LogicDoesNotSupportIntegers)
                } else if family == FAM_REAL && allowed & FAM_INT != 0 {
                    Err(ElaborateError::LogicDoesNotSupportReals)
                } else {
                    Err(ElaborateError::UnknownSort(display.to_string()))
                }
            }
            _ => Ok(()),
        }
    }

    /// Reject a non-bitvector array index under the BV-array logics.
    /// Same gating as [`Self::require_logic_sort_family`]: shell-only,
    /// never under strict SMT-LIB compliance (z3's own C-API parser is
    /// permissive here too). Only the index is restricted; z3 accepts
    /// any element sort its signature knows.
    fn require_logic_array_index(&self, index: &Sort) -> Result<()> {
        if !self.enforce_logic_sort_signatures || self.strict_logic_compliance {
            return Ok(());
        }
        if matches!(self.logic.as_deref(), Some("QF_ABV" | "QF_AUFBV"))
            && !matches!(index, Sort::BitVec(_))
        {
            return Err(ElaborateError::LogicArrayIndexNotBitVec);
        }
        Ok(())
    }

    /// Reject a builtin whose single sort family is outside the
    /// declared logic's shell signature, with z3's `unknown constant`
    /// shape (the CLI renders [`ElaborateError::UndefinedSymbol`]
    /// with the application signature). Used for indexed identifiers
    /// and bare builtin constants, whose family is known from the
    /// name alone. Same gating as [`Self::require_logic_sort_family`].
    pub(super) fn require_logic_builtin_family(&self, name: &str, family: u16) -> Result<()> {
        if !self.enforce_logic_sort_signatures || self.strict_logic_compliance {
            return Ok(());
        }
        let Some(logic) = self.logic.as_deref() else {
            return Ok(());
        };
        match logic_sort_families(logic) {
            Some(allowed) if allowed & family == 0 => {
                Err(ElaborateError::UndefinedSymbol(name.to_string()))
            }
            _ => Ok(()),
        }
    }

    /// Reject a builtin application outside the declared logic's
    /// shell signature, mirroring z3 5.1.0's term-level checks
    /// (measured; DR-59). Called only from the surface application
    /// path after builtin dispatch, so user-declared symbols, macro
    /// expansions already resolved to declarations, and the native
    /// canonical-application API are never gated. Same shell-only
    /// gating as [`Self::require_logic_sort_family`].
    pub(super) fn require_logic_builtin_signature(
        &self,
        name: &str,
        args: &[TermId],
        result: TermId,
    ) -> Result<()> {
        if !self.enforce_logic_sort_signatures || self.strict_logic_compliance {
            return Ok(());
        }
        // Extension spellings z3's SMT-LIB shell installs in no
        // signature at all (measured, including `ALL` and no logic).
        if matches!(name, "min" | "max" | "**") {
            return Err(ElaborateError::UndefinedSymbol(name.to_string()));
        }
        let Some(logic) = self.logic.as_deref() else {
            return Ok(());
        };
        let Some(allowed) = logic_sort_families(logic) else {
            return Ok(());
        };
        if name == "^" && !POWER_KNOWN_LOGICS.contains(&logic) {
            return Err(ElaborateError::UndefinedSymbol(name.to_string()));
        }
        if matches!(name, "and" | "or" | "not" | "xor" | "=>" | "ite" | "if") {
            return Ok(());
        }
        if matches!(name, "=" | "distinct") {
            return self.require_logic_equality_families(args, allowed);
        }
        let mut signature = sort_family_mask(self.terms.sort(result));
        for &arg in args {
            signature |= sort_family_mask(self.terms.sort(arg));
        }
        // In an FP signature, bit-vectors are the FP literal/conversion
        // currency even though the BitVec sort itself is not declarable
        // there: z3 accepts the `fp` constructor over BV literals under
        // QF_FP/QF_FPLRA (measured against 4.16.0) while still rejecting
        // BV operators and `(_ BitVec n)` declarations. So an
        // FP-involving application's BV signature bits are excused; a
        // purely-BV application (no FP anywhere) still rejects.
        let missing = if signature & FAM_FP != 0 && allowed & FAM_FP != 0 {
            signature & !allowed & !FAM_BV
        } else {
            signature & !allowed
        };
        // z3 types bare numerals as Real in a real signature, so a
        // dual-sorted operator over Int numerals only is its Real
        // instance there (measured: `(+ 1 2)`, `(< 1 2)`, `(abs …)`,
        // `(is_int 1)` under QF_LRA/QF_NRA/QF_RDL) — and the same
        // holds for numeral composites under `ite`/arithmetic
        // (`(<= (+ (ite b 1 0) (ite c 1 0)) 1)`, the CVC-translated
        // QF_LRA shape). AY folds those numerals as Int, so excuse
        // exactly that shape. Int-only operators
        // (`div`/`mod`/`rem`/`to_int`) stay rejected, and
        // `to_real` — the identity cast there — gets z3's casting
        // message instead.
        let int_numerals_in_real_signature = missing == FAM_INT
            && allowed & FAM_REAL != 0
            && is_arithmetic_builtin(name)
            && !matches!(name, "div" | "mod" | "rem" | "to_int")
            && args
                .iter()
                .all(|&arg| self.terms.sort(arg) != &Sort::Int || self.is_numeral_composite(arg))
            && (self.terms.sort(result) != &Sort::Int || self.is_numeral_composite(result));
        if int_numerals_in_real_signature && name == "to_real" {
            return Err(ElaborateError::LogicDoesNotSupportCastingOperators);
        }
        if missing != 0 && !int_numerals_in_real_signature {
            if is_arithmetic_builtin(name) {
                if missing & FAM_REAL != 0 && allowed & FAM_INT != 0 {
                    return Err(ElaborateError::LogicDoesNotSupportReals);
                }
                if missing & FAM_INT != 0 && allowed & FAM_REAL != 0 {
                    return Err(ElaborateError::LogicDoesNotSupportIntegers);
                }
            }
            return Err(ElaborateError::UndefinedSymbol(name.to_string()));
        }
        if is_arithmetic_builtin(name) {
            self.require_logic_arithmetic_profile(logic, name, args)?;
        }
        Ok(())
    }

    /// z3 reports a core equality over BV/Real/Int literals in a
    /// logic without that family as `logic does not support …`
    /// rather than `unknown constant =`. String literal equalities
    /// are measured accepted even where `String` is not declarable,
    /// so only these three families are checked. Int is excused
    /// where Real is available: numerals are polymorphic there, and
    /// declared Int symbols are already sort-gated.
    fn require_logic_equality_families(&self, args: &[TermId], allowed: u16) -> Result<()> {
        for &arg in args {
            let families = sort_family_mask(self.terms.sort(arg));
            // BV is excused where FP is available: BV literals and
            // FP->BV conversion results are equality-comparable in an FP
            // signature (measured against z3 4.16.0: `(= #b01 #b01)` and
            // `(= ((_ fp.to_ubv 8) r x) #b00000001)` are accepted under
            // QF_FP, rejected under QF_LIA).
            if families & FAM_BV != 0 && allowed & (FAM_BV | FAM_FP) == 0 {
                return Err(ElaborateError::LogicDoesNotSupportBitvectors);
            }
            if families & FAM_REAL != 0 && allowed & FAM_REAL == 0 {
                return Err(ElaborateError::LogicDoesNotSupportReals);
            }
            if families & FAM_INT != 0 && allowed & (FAM_INT | FAM_REAL) == 0 {
                return Err(ElaborateError::LogicDoesNotSupportIntegers);
            }
        }
        Ok(())
    }

    /// The linear/difference application shapes z3's shell enforces
    /// for the measured logics. Runs only once every sort family in
    /// the signature is available, so cross-family applications keep
    /// their `does not support` / `unknown constant` shapes. Checks
    /// the elaborated operands: a syntactically nontrivial but
    /// constant-folded divisor such as `(div x (+ 1 1))` is accepted
    /// here where z3's syntactic check rejects it — a documented
    /// permissive residual (DR-59), never a wrong verdict.
    fn require_logic_arithmetic_profile(
        &self,
        logic: &str,
        name: &str,
        args: &[TermId],
    ) -> Result<()> {
        if NONLINEAR_REJECTING_LOGICS.contains(&logic) {
            match name {
                "*" => {
                    let degree: u32 = args.iter().map(|&arg| self.arith_term_degree(arg)).sum();
                    if degree >= 2 {
                        return Err(ElaborateError::LogicNonlinearArithmetic);
                    }
                }
                "/" | "div" | "mod" | "rem" => {
                    if args.iter().skip(1).any(|&d| !self.is_numeral_term(d)) {
                        return Err(ElaborateError::LogicNonlinearArithmetic);
                    }
                }
                _ => {}
            }
        }
        if DIFFERENCE_LOGICS.contains(&logic) && !self.is_difference_application(name, args) {
            return Err(ElaborateError::LogicOnlyDifferenceArithmetic);
        }
        Ok(())
    }

    /// Polynomial degree of an elaborated arithmetic term, capped
    /// at 2 (the linear/nonlinear boundary is all the gate needs).
    fn arith_term_degree(&self, term: TermId) -> u32 {
        stacker::maybe_grow(PARSE_STACK_RED_ZONE, PARSE_STACK_SIZE, || {
            match self.terms.get(term) {
                TermData::Const(Constant::Int(_) | Constant::Rational(_)) => 0,
                TermData::App(Symbol::Named(op), operands) if op == "*" => operands
                    .iter()
                    .map(|&operand| self.arith_term_degree(operand))
                    .sum::<u32>()
                    .min(2),
                TermData::App(Symbol::Named(op), operands)
                    if matches!(op.as_str(), "+" | "-" | "~" | "to_real" | "to_int" | "abs") =>
                {
                    operands
                        .iter()
                        .map(|&operand| self.arith_term_degree(operand))
                        .max()
                        .unwrap_or(0)
                }
                _ if matches!(self.terms.sort(term), Sort::Int | Sort::Real) => 1,
                _ => 0,
            }
        })
    }

    /// Whether an elaborated term is a numeric literal, peeling the
    /// unary-negation applications the term store may keep unfolded.
    /// A division of numerals counts: z3's parser produces it as a
    /// rational numeral, so `(/ 4.0 2.0)` is a literal where
    /// `(+ 1.0 1.0)` is not (measured in QF_RDL/QF_IDL).
    fn is_numeral_term(&self, term: TermId) -> bool {
        stacker::maybe_grow(PARSE_STACK_RED_ZONE, PARSE_STACK_SIZE, || {
            self.is_numeral_term_inner(term)
        })
    }

    /// An Int-sorted term z3's shell types as Real in a real
    /// signature: a numeral, or a composite of numerals under
    /// dual-sorted constructs (`ite` branches, `+`/`-`/`*`/`abs`).
    /// z3 assigns numerals the expected sort top-down, so
    /// `(<= (+ (ite b 1 0) (ite c 1 0)) 1)` is Real arithmetic
    /// under QF_LRA (measured); AY types the same leaves Int
    /// bottom-up. Int-only operators and non-numeral Int leaves
    /// (declared symbols are sort-gated at declaration) stay out.
    fn is_numeral_composite(&self, term: TermId) -> bool {
        stacker::maybe_grow(PARSE_STACK_RED_ZONE, PARSE_STACK_SIZE, || {
            self.is_numeral_composite_inner(term)
        })
    }

    fn is_numeral_composite_inner(&self, term: TermId) -> bool {
        if self.is_numeral_term(term) {
            return true;
        }
        if self.terms.sort(term) != &Sort::Int {
            return false;
        }
        match self.terms.get(term) {
            TermData::Ite(_, then_t, else_t) => {
                self.is_numeral_composite(*then_t) && self.is_numeral_composite(*else_t)
            }
            TermData::App(Symbol::Named(op), operands)
                if matches!(op.as_str(), "+" | "-" | "~" | "*" | "abs") =>
            {
                !operands.is_empty() && operands.iter().all(|&o| self.is_numeral_composite(o))
            }
            _ => false,
        }
    }

    fn is_numeral_term_inner(&self, term: TermId) -> bool {
        match self.terms.get(term) {
            TermData::Const(Constant::Int(_) | Constant::Rational(_)) => true,
            TermData::App(Symbol::Named(op), operands)
                if matches!(op.as_str(), "-" | "~") && operands.len() == 1 =>
            {
                self.is_numeral_term(operands[0])
            }
            TermData::App(Symbol::Named(op), operands) if op == "/" && operands.len() == 2 => {
                operands.iter().all(|&o| self.is_numeral_term(o))
            }
            _ => false,
        }
    }

    /// Whether a term may appear as an operand of a difference
    /// application: anything that is not itself an arithmetic
    /// application (variables, literals, `ite`, user applications).
    fn is_difference_atom(&self, term: TermId) -> bool {
        match self.terms.get(term) {
            TermData::App(Symbol::Named(op), _) => !matches!(
                op.as_str(),
                "+" | "-"
                    | "~"
                    | "*"
                    | "/"
                    | "div"
                    | "mod"
                    | "rem"
                    | "abs"
                    | "^"
                    | "to_real"
                    | "to_int"
            ),
            _ => true,
        }
    }

    /// Whether `term` is an elaborated sum that counts as a single
    /// difference atom: a `+` application whose own arguments are all
    /// numerals or difference atoms. Elaboration normalizes `(- x y)`
    /// to addition form, so a plain `+` head is not enough — the
    /// normalized subtraction carries a negated non-numeral argument
    /// and must not count, while a surface sum or an atom±numeral
    /// difference (`(- x 1)` → `(+ x -1)`) does. Measured against
    /// z3 4.16.0: `(+ 1 (+ 1 x))` and `(+ (- x 1) 19)` are admissible
    /// under QF_UFIDL, `(+ (- x y) 1)` is not.
    fn is_difference_plus_atom(&self, term: TermId) -> bool {
        match self.terms.get(term) {
            TermData::App(Symbol::Named(op), args) if op.as_str() == "+" => args
                .iter()
                .all(|&arg| self.is_numeral_term(arg) || self.is_difference_atom(arg)),
            _ => false,
        }
    }

    /// The application shapes measured admissible under the
    /// difference logics: sums with at most one non-numeral atom (a
    /// nested difference sum counting as one atom), binary
    /// differences of atoms or of a difference sum minus a numeral,
    /// negation of numerals, and comparisons over (recursively
    /// checked) operands. Every other arithmetic head — including
    /// all-numeral `(* 2 3)` — is rejected, matching z3's syntactic
    /// check.
    fn is_difference_application(&self, name: &str, args: &[TermId]) -> bool {
        match name {
            "+" => {
                let non_numerals: Vec<TermId> = args
                    .iter()
                    .copied()
                    .filter(|&arg| !self.is_numeral_term(arg))
                    .collect();
                non_numerals.len() <= 1
                    && non_numerals.iter().all(|&arg| {
                        self.is_difference_atom(arg) || self.is_difference_plus_atom(arg)
                    })
            }
            "-" | "~" if args.len() == 1 => self.is_numeral_term(args[0]),
            "-" if args.len() == 2 => {
                let (left, right) = (args[0], args[1]);
                let left_ok = self.is_difference_atom(left) || self.is_difference_plus_atom(left);
                let right_ok = self.is_numeral_term(right)
                    || (self.is_difference_atom(left) && self.is_difference_atom(right));
                left_ok && right_ok
            }
            // A division of numerals is a rational literal in z3's
            // parser, admissible even under QF_RDL (measured); the
            // nonlinear divisor check has already run.
            "/" => args.iter().all(|&arg| self.is_numeral_term(arg)),
            "<" | "<=" | ">" | ">=" => true,
            _ => false,
        }
    }

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
        // Stack-safety guard for deeply nested sorts
        // (Array/Seq/Set/FiniteSet/Multiset/Map), which would otherwise overflow
        // the stack on adversarial nesting.
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
                    // Z3 5.0.0 exposes this user-friendly alias only before a
                    // logic is selected.  Under `(set-logic ...)`, lowercase
                    // `bool` is free for an explicit user sort declaration.
                    "bool" if self.logic.is_none() => Ok(Sort::Bool),
                    // The proof carrier is likewise part of only the no-logic
                    // basic signature. AY does not manufacture proof-object
                    // terms here, but user declarations over the carrier have
                    // the ordinary sound equality/UF semantics.
                    "Proof" if self.logic.is_none() => Ok(Sort::Uninterpreted("Proof".to_string())),
                    "Int" => {
                        self.require_logic_sort_family(FAM_INT, "Int")?;
                        Ok(Sort::Int)
                    }
                    "Real" => {
                        self.require_logic_sort_family(FAM_REAL, "Real")?;
                        Ok(Sort::Real)
                    }
                    "Complex" if matches!(self.logic(), None | Some("ALL")) => Ok(Sort::Complex),
                    "String" => {
                        self.require_logic_sort_family(FAM_STRING, "String")?;
                        Ok(Sort::String)
                    }
                    "RegLan" => {
                        self.require_logic_sort_family(FAM_REGLAN, "RegLan")?;
                        Ok(Sort::RegLan)
                    }
                    // SMT-LIB FloatingPoint theory sort abbreviations. Without these
                    // a `(declare-fun x () Float32)` would fall through to the
                    // Uninterpreted fallback below, and `x` would never route through
                    // the eager FP-to-BV bit-blaster (the structural-`=` branch in
                    // bitblast_fp_predicate is gated on Sort::FloatingPoint). That
                    // gap caused symbolic-variable QF_FP conflicts such as
                    // `x = 1.0 AND x = 2.0` to be reported SAT (false-SAT).
                    "Float16" => {
                        self.require_logic_sort_family(FAM_FP, "FloatingPoint")?;
                        Ok(Sort::FloatingPoint(5, 11))
                    }
                    "Float32" => {
                        self.require_logic_sort_family(FAM_FP, "FloatingPoint")?;
                        Ok(Sort::FloatingPoint(8, 24))
                    }
                    "Float64" => {
                        self.require_logic_sort_family(FAM_FP, "FloatingPoint")?;
                        Ok(Sort::FloatingPoint(11, 53))
                    }
                    "Float128" => {
                        self.require_logic_sort_family(FAM_FP, "FloatingPoint")?;
                        Ok(Sort::FloatingPoint(15, 113))
                    }
                    // The FloatingPoint theory's `RoundingMode` is a BUILTIN
                    // sort that is never `declare-sort`ed, so it is not in
                    // `sort_defs`. Its carrier is the reserved name
                    // `Uninterpreted("RoundingMode")` — the same sort the RM
                    // literals (`RNE` … `roundTowardZero`) elaborate to, and the
                    // name the executor's finite-domain pass keys on.
                    // `ensure_sort_name_available` already forbids redeclaring
                    // it, so this can never shadow a user sort.
                    "RoundingMode" => {
                        self.require_logic_sort_family(FAM_RM, "RoundingMode")?;
                        Ok(Sort::Uninterpreted("RoundingMode".to_string()))
                    }
                    other => {
                        if let Some(s) = self.sort_defs.get(other) {
                            return Ok(s.clone());
                        }
                        // PROGRAMMATIC (non-SMT-LIB) declarations only: naming
                        // an uninterpreted sort CREATES it, the way
                        // `Z3_mk_uninterpreted_sort` does — an embedder calling
                        // `declare_fun("f", &[Sort::uninterpreted("U")], …)` has
                        // no `declare-sort` command to issue and holds a sort
                        // handle that outlives SMT-LIB assertion scopes. The
                        // flag is set ONLY by
                        // `Context::execute_native_global_declaration`, so the
                        // SMT-LIB TEXT path — where `declare-sort`/`define-sort`
                        // ARE the way to extend the signature — stays strict.
                        // Registering it (rather than returning an unregistered
                        // sort) is what makes the name resolvable afterwards.
                        if self.native_global_declaration {
                            let identity = self.allocate_nominal_sort_identity(other, other);
                            let sort = Sort::Uninterpreted(identity);
                            self.sort_defs.insert(other.to_string(), sort.clone());
                            self.track_scoped_sort_def(other.to_string());
                            return Ok(sort);
                        }
                        // An UNRESOLVED sort name is an ERROR, not a silent new
                        // uninterpreted sort (SMT-LIB 2.6 §3.4/§4.2.1: every
                        // sort symbol in a term or declaration must already be
                        // in the signature; `declare-sort`/`define-sort` are the
                        // only ways to add one, and an assertion level owns the
                        // declarations made in it, so `(pop n)` removes them —
                        // `:global-declarations` exists to opt out and defaults
                        // to false).
                        //
                        // The fallback silently accepted every MISTYPED sort
                        // name in every script, and it is what let a sort
                        // declared inside a `push` keep working after the
                        // matching `pop`: the scope machinery removed the
                        // `sort_defs` entry correctly, but the next use just
                        // re-invented the name here. A popped `declare-datatypes`
                        // degraded the same way — the name survived as an
                        // UNINTERPRETED sort with the datatype's interpretation
                        // (and its finite domain) lost, so `(distinct x y z)`
                        // over a popped 2-element datatype answered `sat`.
                        Err(ElaborateError::UnknownSort(other.to_string()))
                    }
                }
            }
            command::Sort::Indexed(name, indices) => match name.as_str() {
                "FiniteField" => {
                    if !matches!(self.logic(), None | Some("ALL" | "QF_FF")) {
                        return Err(ElaborateError::UnknownSort(name.clone()));
                    }
                    let field = if indices.len() == 1 {
                        indices[0]
                            .as_numeral()
                            .and_then(|n| n.parse().ok())
                            .and_then(ay_core::FiniteFieldSort::new)
                    } else {
                        None
                    };
                    field.map(Sort::FiniteField).ok_or_else(|| {
                        ElaborateError::InvalidConstant(
                            "FiniteField requires one prime modulus from 2 through 4294967291"
                                .into(),
                        )
                    })
                }
                "BitVec" => {
                    self.require_logic_sort_family(FAM_BV, "BitVec")?;
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
                    self.require_logic_sort_family(FAM_FP, "FloatingPoint")?;
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
            // z3 4.12.5 knows none of these; `FiniteSet` is z3 5's. Under
            // `--z3-mode` they are unknown sorts, which only drops a command
            // z3 4.12.5 drops too.
            command::Sort::Parameterized(name, _)
                if self.z3_mode && matches!(name.as_str(), "FiniteSet" | "Multiset" | "Map") =>
            {
                Err(ElaborateError::UnknownSort(name.clone()))
            }
            command::Sort::Parameterized(name, params) => match name.as_str() {
                "Array" => {
                    self.require_logic_sort_family(FAM_ARRAY, "Array")?;
                    if params.len() != 2 {
                        return Err(ElaborateError::InvalidConstant(
                            "Array requires 2 type parameters".to_string(),
                        ));
                    }
                    let index = self.elaborate_sort_inner(&params[0], subst)?;
                    let element = self.elaborate_sort_inner(&params[1], subst)?;
                    self.require_logic_array_index(&index)?;
                    Ok(Sort::array(index, element))
                }
                "->" if self
                    .logic
                    .as_deref()
                    .is_none_or(|logic| matches!(logic, "HORN" | "ALL")) =>
                {
                    if params.len() != 2 {
                        return Err(ElaborateError::InvalidConstant(
                            "-> requires 2 type parameters in AY's supported Z3 array fragment"
                                .to_string(),
                        ));
                    }
                    let index = self.elaborate_sort_inner(&params[0], subst)?;
                    let element = self.elaborate_sort_inner(&params[1], subst)?;
                    Ok(Sort::array(index, element))
                }
                "Seq" => {
                    self.require_logic_sort_family(FAM_SEQ, "Seq")?;
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
                // Z3 5.0.0 exposes a distinct `(FiniteSet T)` theory sort. AY's
                // textual frontend lowers it to the same characteristic-array
                // carrier used by the native set theory, while retaining the
                // exact Z3 5 operator vocabulary in `app/set.rs`. Marking set
                // usage here is load-bearing: a script that mentions the sort
                // but reaches it only through equality still has to route
                // through the set-aware decision path instead of looking like
                // an ordinary Bool-valued array problem.
                "FiniteSet" => {
                    if params.len() != 1 {
                        return Err(ElaborateError::InvalidConstant(
                            "FiniteSet requires 1 type parameter".to_string(),
                        ));
                    }
                    self.mark_uses_set();
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
