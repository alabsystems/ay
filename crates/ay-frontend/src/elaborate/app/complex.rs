// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Z3 5.3.3 arithmetic signature: Complex is available without a selected
//! logic and under ALL. Arithmetic lowers to exact Real components.
//! Reference: src/ast/arith_decl_plugin.cpp and rewriter/arith_rewriter.cpp.

use super::{Context, ElaborateError, Result, Sort, TermId};

impl Context {
    pub(super) fn try_elaborate_complex_app(
        &mut self,
        name: &str,
        args: &mut [TermId],
    ) -> Result<Option<TermId>> {
        if !matches!(self.logic(), None | Some("ALL")) {
            return Ok(None);
        }
        let constructed = match name {
            "complex.make" => {
                expect_complex_arity(name, args, 2)?;
                if !self.int_real_coercions() {
                    for &arg in args.iter() {
                        if self.terms.sort(arg) != &Sort::Real {
                            return Err(ElaborateError::SortMismatch {
                                expected: "Real".to_string(),
                                actual: self.terms.sort(arg).to_string(),
                            });
                        }
                    }
                }
                Some(self.terms.mk_complex(args[0], args[1]))
            }
            "complex.real" | "complex.imag" => {
                expect_complex_arity(name, args, 1)?;
                let sort = self.terms.sort(args[0]);
                if sort != &Sort::Complex
                    && !(self.int_real_coercions() && matches!(sort, Sort::Int | Sort::Real))
                {
                    return Err(ElaborateError::SortMismatch {
                        expected: "Complex".to_string(),
                        actual: self.terms.sort(args[0]).to_string(),
                    });
                }
                Some(if name == "complex.real" {
                    self.terms.mk_complex_real(args[0])
                } else {
                    self.terms.mk_complex_imaginary(args[0])
                })
            }
            _ => None,
        };
        if let Some(result) = constructed {
            return result.map(Some).ok_or_else(|| {
                ElaborateError::InvalidConstant(format!("invalid operands for {name}"))
            });
        }
        if !args
            .iter()
            .any(|&arg| self.terms.sort(arg) == &Sort::Complex)
        {
            return Ok(None);
        }
        match name {
            "+" | "-" | "*" | "/" | "~" => self.elaborate_complex_arithmetic(name, args).map(Some),
            "=" | "distinct" => {
                self.promote_complex_operands(args)?;
                Ok(None)
            }
            "ite" if args.len() == 3 => {
                self.promote_complex_operands(&mut args[1..])?;
                Ok(None)
            }
            _ => Ok(None),
        }
    }

    fn promote_complex_operands(&mut self, args: &mut [TermId]) -> Result<()> {
        for argument in args {
            match self.terms.sort(*argument) {
                Sort::Complex => continue,
                Sort::Int | Sort::Real if self.int_real_coercions() => {
                    let zero = self.terms.mk_int(0.into());
                    *argument = self.terms.mk_complex(*argument, zero).ok_or_else(|| {
                        ElaborateError::InvalidConstant("Complex promotion unavailable".to_string())
                    })?;
                }
                other => {
                    return Err(ElaborateError::SortMismatch {
                        expected: "Int, Real or Complex".to_string(),
                        actual: other.to_string(),
                    })
                }
            }
        }
        Ok(())
    }

    fn elaborate_complex_arithmetic(&mut self, name: &str, args: &mut [TermId]) -> Result<TermId> {
        self.expect_min_arity(name, args, 1)?;
        if name == "~" {
            expect_complex_arity(name, args, 1)?;
        }
        self.promote_complex_operands(args)?;
        let mut result = args[0];
        if args.len() == 1 && matches!(name, "-" | "~") {
            return self.terms.mk_complex_negate(result).ok_or_else(|| {
                ElaborateError::InvalidConstant("Complex negation unavailable".to_string())
            });
        }
        for &argument in &args[1..] {
            result = match name {
                "+" => self.terms.mk_complex_add(result, argument),
                "-" => self.terms.mk_complex_subtract(result, argument),
                "*" => self.terms.mk_complex_multiply(result, argument),
                "/" => self.terms.mk_complex_divide(result, argument),
                _ => None,
            }
            .ok_or_else(|| {
                ElaborateError::InvalidConstant(format!("Complex arithmetic unavailable: {name}"))
            })?;
        }
        Ok(result)
    }
}

fn expect_complex_arity(name: &str, args: &[TermId], arity: usize) -> Result<()> {
    if args.len() == arity {
        Ok(())
    } else {
        Err(ElaborateError::InvalidConstant(format!(
            "{name} requires {arity} arguments, got {}",
            args.len()
        )))
    }
}
