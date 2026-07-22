// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ay_core::{Sort, Symbol, TermId};

use super::{Context, ElaborateError, Result};

impl Context {
    /// Require every operand to be FloatingPoint with one identical format.
    fn expect_same_fp_operands(&self, operation: &str, ids: &[TermId]) -> Result<Sort> {
        let mut expected: Option<(u32, u32)> = None;
        for &id in ids {
            let (eb, sb) = self.expect_floating_point_operand(operation, id)?;
            match expected {
                None => expected = Some((eb, sb)),
                Some((e0, s0)) if (e0, s0) != (eb, sb) => {
                    return Err(ElaborateError::SortMismatch {
                        expected: format!("(_ FloatingPoint {e0} {s0})"),
                        actual: format!("(_ FloatingPoint {eb} {sb})"),
                    });
                }
                Some(_) => {}
            }
        }
        let (eb, sb) = expected.ok_or_else(|| {
            ElaborateError::InvalidConstant(format!(
                "{operation} requires at least one FloatingPoint operand"
            ))
        })?;
        Ok(Sort::FloatingPoint(eb, sb))
    }

    pub(super) fn try_elaborate_floating_point_app(
        &mut self,
        name: &str,
        arg_ids: &[TermId],
    ) -> Result<Option<TermId>> {
        match name {
            "fp.abs" | "fp.neg" => {
                self.expect_exact_arity(name, arg_ids, 1)?;
                let result_sort = self.expect_same_fp_operands(name, arg_ids)?;
                Ok(Some(self.terms.mk_app(
                    Symbol::named(name),
                    arg_ids,
                    result_sort,
                )))
            }
            "fp.add" | "fp.sub" | "fp.mul" | "fp.div" => {
                self.expect_exact_arity(name, arg_ids, 3)?;
                self.expect_rounding_mode_operand(name, arg_ids[0])?;
                let result_sort = self.expect_same_fp_operands(name, &arg_ids[1..])?;
                Ok(Some(self.terms.mk_app(
                    Symbol::named(name),
                    arg_ids,
                    result_sort,
                )))
            }
            "fp.sqrt" | "fp.roundToIntegral" => {
                self.expect_exact_arity(name, arg_ids, 2)?;
                self.expect_rounding_mode_operand(name, arg_ids[0])?;
                let result_sort = self.expect_same_fp_operands(name, &arg_ids[1..])?;
                Ok(Some(self.terms.mk_app(
                    Symbol::named(name),
                    arg_ids,
                    result_sort,
                )))
            }
            "fp.fma" => {
                self.expect_exact_arity("fp.fma", arg_ids, 4)?;
                self.expect_rounding_mode_operand("fp.fma", arg_ids[0])?;
                let result_sort = self.expect_same_fp_operands("fp.fma", &arg_ids[1..])?;
                Ok(Some(self.terms.mk_app(
                    Symbol::named("fp.fma"),
                    arg_ids,
                    result_sort,
                )))
            }
            "fp.rem" | "fp.min" | "fp.max" => {
                self.expect_exact_arity(name, arg_ids, 2)?;
                let result_sort = self.expect_same_fp_operands(name, arg_ids)?;
                Ok(Some(self.terms.mk_app(
                    Symbol::named(name),
                    arg_ids,
                    result_sort,
                )))
            }
            "fp.eq" | "fp.lt" | "fp.leq" | "fp.gt" | "fp.geq" => {
                // SMT-LIB FloatingPoint theory declares these `:chainable`, so
                // `(fp.leq a b c)` means `(and (fp.leq a b) (fp.leq b c))`. The
                // downstream FP theory only ever sees the binary form. (matches z3)
                if arg_ids.len() < 2 {
                    return Err(ElaborateError::InvalidConstant(format!(
                        "{name} requires at least 2 arguments"
                    )));
                }
                self.expect_same_fp_operands(name, arg_ids)?;
                if arg_ids.len() == 2 {
                    Ok(Some(self.terms.mk_app(
                        Symbol::named(name),
                        arg_ids,
                        Sort::Bool,
                    )))
                } else {
                    let pairs = arg_ids
                        .windows(2)
                        .map(|w| self.terms.mk_app(Symbol::named(name), w, Sort::Bool))
                        .collect();
                    Ok(Some(self.terms.mk_and(pairs)))
                }
            }
            "fp.isNaN" | "fp.isInfinite" | "fp.isZero" | "fp.isNormal" | "fp.isSubnormal"
            | "fp.isPositive" | "fp.isNegative" => {
                self.expect_exact_arity(name, arg_ids, 1)?;
                self.expect_floating_point_operand(name, arg_ids[0])?;
                Ok(Some(self.terms.mk_app(
                    Symbol::named(name),
                    arg_ids,
                    Sort::Bool,
                )))
            }
            "fp.to_real" => {
                self.expect_exact_arity("fp.to_real", arg_ids, 1)?;
                let arg_sort = self.terms.sort(arg_ids[0]).clone();
                if !matches!(arg_sort, Sort::FloatingPoint(_, _)) {
                    return Err(ElaborateError::SortMismatch {
                        expected: "FloatingPoint".to_string(),
                        actual: arg_sort.to_string(),
                    });
                }
                Ok(Some(self.terms.mk_app(
                    Symbol::named("fp.to_real"),
                    arg_ids,
                    Sort::Real,
                )))
            }
            "fp.to_ieee_bv" => {
                self.expect_exact_arity("fp.to_ieee_bv", arg_ids, 1)?;
                match self.terms.sort(arg_ids[0]).clone() {
                    Sort::FloatingPoint(eb, sb) => {
                        let width = eb.checked_add(sb).ok_or_else(|| {
                            ElaborateError::InvalidConstant(
                                "fp.to_ieee_bv result width overflows".to_string(),
                            )
                        })?;
                        let result_sort = Self::checked_bitvector_sort(width)?;
                        Ok(Some(self.terms.mk_app(
                            Symbol::named("fp.to_ieee_bv"),
                            arg_ids,
                            result_sort,
                        )))
                    }
                    actual => Err(ElaborateError::SortMismatch {
                        expected: "FloatingPoint".to_string(),
                        actual: actual.to_string(),
                    }),
                }
            }
            "fp" => {
                self.expect_exact_arity("fp", arg_ids, 3)?;
                let sign_width = self.expect_bv_operand_width("fp sign", arg_ids[0])?;
                if sign_width != 1 {
                    return Err(ElaborateError::SortMismatch {
                        expected: "(_ BitVec 1)".to_string(),
                        actual: format!("(_ BitVec {sign_width})"),
                    });
                }
                let eb = match self.terms.sort(arg_ids[1]) {
                    Sort::BitVec(w) => w.width,
                    _ => {
                        return Err(ElaborateError::InvalidConstant(
                            "fp exponent must be a bitvector".to_string(),
                        ))
                    }
                };
                let sb = match self.terms.sort(arg_ids[2]) {
                    Sort::BitVec(w) => w.width.checked_add(1).ok_or_else(|| {
                        ElaborateError::InvalidConstant(
                            "fp significand width + 1 overflows".to_string(),
                        )
                    })?,
                    _ => {
                        return Err(ElaborateError::InvalidConstant(
                            "fp significand must be a bitvector".to_string(),
                        ))
                    }
                };
                let fp_sort = Self::checked_floating_point_sort(eb, sb)?;
                Ok(Some(self.terms.mk_app(
                    Symbol::named("fp"),
                    arg_ids,
                    fp_sort,
                )))
            }
            _ => Ok(None),
        }
    }
}
