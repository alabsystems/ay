// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! String/BV bridge API for combined reasoning (#8333).
//!
//! Provides operations that bridge the String theory and BV theory, enabling
//! analysis of format string vulnerabilities and other scenarios where string
//! operations produce bitvector values (atoi, strtol) or BV operations produce
//! strings (sprintf, itoa).
//!
//! # Encoding Strategy
//!
//! For `string_to_bv`: Uses `str.to_int` (String -> Int) then `int2bv` (Int -> BV).
//! This leverages the existing theory combination rather than unrolling digit
//! extraction manually. The SMT solver's String theory already handles `str.to_int`
//! correctly for decimal digit strings.
//!
//! For `bv_to_string`: Uses `bv2int` (BV -> Int) then `str.from_int` (Int -> String).
//!
//! For `string_length_bv`: Uses `str.len` (String -> Int) then `int2bv` (Int -> BV32).
//!
//! For `format_string_vuln_check`: Builds constraints modeling whether concatenated
//! format output exceeds a given buffer size.

use super::types::{SolverError, Term};
use super::Solver;

impl Solver {
    /// Convert a string of decimal digits to a bitvector of the given width.
    ///
    /// Models `atoi`/`strtol`: parses the string as a non-negative decimal integer
    /// and returns its BV representation of `width` bits. The encoding chains
    /// `str.to_int` (which returns -1 for non-numeric strings) with `int2bv`.
    ///
    /// For strings that do not represent valid non-negative integers, `str.to_int`
    /// returns -1, which maps to the two's complement representation in BV.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError::SortMismatch`] if `str_expr` is not `String`.
    /// Returns [`SolverError::InvalidArgument`] if `width` is 0.
    ///
    /// # Example
    ///
    /// ```
    /// use ay_dpll::api::{Logic, Solver};
    ///
    /// let mut solver = Solver::try_new(Logic::QfSlia).expect("valid logic");
    /// let s = solver.string_const("42");
    /// let bv = solver.try_string_to_bv(s, 32).expect("valid conversion");
    /// let expected = solver.bv_const(42, 32);
    /// let eq = solver.try_eq(bv, expected).expect("same sort");
    /// solver.try_assert_term(eq).expect("bool assertion");
    /// ```
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_string_to_bv(&mut self, str_expr: Term, width: u32) -> Result<Term, SolverError> {
        if width == 0 {
            return Err(SolverError::InvalidArgument {
                operation: "string_to_bv",
                message: "bitvector width must be > 0".to_string(),
            });
        }
        self.expect_string("string_to_bv", str_expr)?;
        // str.to_int returns the integer value of the decimal string, or -1 if invalid
        let int_val = self.try_str_to_int(str_expr)?;
        // int2bv converts the integer to a bitvector of the given width (mod 2^width)
        self.try_int2bv(int_val, width)
    }

    /// Convert a bitvector value to its decimal string representation.
    ///
    /// Models `itoa`/`sprintf("%d", ...)`: interprets the bitvector as an unsigned
    /// integer and produces its decimal string representation. The encoding chains
    /// `bv2int` (unsigned) with `str.from_int`.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError::SortMismatch`] if `bv_expr` is not a bitvector sort.
    ///
    /// # Example
    ///
    /// ```
    /// use ay_dpll::api::{Logic, Solver};
    ///
    /// let mut solver = Solver::try_new(Logic::QfSlia).expect("valid logic");
    /// let bv = solver.bv_const(42, 32);
    /// let s = solver.try_bv_to_string(bv).expect("valid conversion");
    /// let expected = solver.string_const("42");
    /// let eq = solver.try_eq(s, expected).expect("same sort");
    /// solver.try_assert_term(eq).expect("bool assertion");
    /// ```
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_bv_to_string(&mut self, bv_expr: Term) -> Result<Term, SolverError> {
        self.expect_bitvec("bv_to_string", bv_expr)?;
        // bv2int (unsigned) gives the non-negative integer value
        let int_val = self.try_bv2int(bv_expr)?;
        // str.from_int converts a non-negative integer to its decimal string
        self.try_str_from_int(int_val)
    }

    /// Convert a bitvector value (signed) to its decimal string representation.
    ///
    /// Like [`try_bv_to_string`](Self::try_bv_to_string) but uses signed
    /// interpretation. Negative values produce `str.from_int` of a negative
    /// integer, which returns the empty string per SMT-LIB semantics.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError::SortMismatch`] if `bv_expr` is not a bitvector sort.
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_bv_to_string_signed(&mut self, bv_expr: Term) -> Result<Term, SolverError> {
        self.expect_bitvec("bv_to_string_signed", bv_expr)?;
        let int_val = self.try_bv2int_signed(bv_expr)?;
        self.try_str_from_int(int_val)
    }

    /// Return the string length as a 32-bit bitvector.
    ///
    /// Useful when string lengths participate in bitvector arithmetic, such as
    /// buffer size calculations in binary analysis. The encoding chains
    /// `str.len` (String -> Int) with `int2bv(32, ...)`.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError::SortMismatch`] if `str_expr` is not `String`.
    ///
    /// # Example
    ///
    /// ```
    /// use ay_dpll::api::{Logic, Solver};
    ///
    /// let mut solver = Solver::try_new(Logic::QfSlia).expect("valid logic");
    /// let s = solver.string_const("hello");
    /// let len_bv = solver.try_string_length_bv(s).expect("valid conversion");
    /// let five_bv = solver.bv_const(5, 32);
    /// let eq = solver.try_eq(len_bv, five_bv).expect("same sort");
    /// solver.try_assert_term(eq).expect("bool assertion");
    /// ```
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_string_length_bv(&mut self, str_expr: Term) -> Result<Term, SolverError> {
        self.expect_string("string_length_bv", str_expr)?;
        let len_int = self.try_str_len(str_expr)?;
        self.try_int2bv(len_int, 32)
    }

    /// Return the string length as a bitvector of the given width.
    ///
    /// Generalization of [`try_string_length_bv`](Self::try_string_length_bv)
    /// for architectures with non-32-bit size types.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError::SortMismatch`] if `str_expr` is not `String`.
    /// Returns [`SolverError::InvalidArgument`] if `width` is 0.
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_string_length_bv_width(
        &mut self,
        str_expr: Term,
        width: u32,
    ) -> Result<Term, SolverError> {
        if width == 0 {
            return Err(SolverError::InvalidArgument {
                operation: "string_length_bv_width",
                message: "bitvector width must be > 0".to_string(),
            });
        }
        self.expect_string("string_length_bv_width", str_expr)?;
        let len_int = self.try_str_len(str_expr)?;
        self.try_int2bv(len_int, width)
    }

    /// Check if a format string with given arguments can produce output exceeding
    /// a buffer of `buf_size_bv` bytes.
    ///
    /// Models a simplified format string vulnerability check: given a format
    /// string `fmt` and argument strings `args`, checks whether the total output
    /// length (concatenation of format and all arguments) exceeds the buffer size.
    ///
    /// Returns a Bool term that is `true` when the output *could* overflow the
    /// buffer (i.e., total length > buffer size). Assert this term and check SAT
    /// to determine if an overflow is possible.
    ///
    /// This is a simplified model. A full format string analysis would parse `%`
    /// specifiers, but this captures the core constraint: total output bytes vs
    /// buffer capacity.
    ///
    /// # Arguments
    ///
    /// * `fmt` - The format string (String sort)
    /// * `args` - Additional argument strings that contribute to output length
    /// * `buf_size_bv` - Buffer capacity as a 32-bit bitvector
    ///
    /// # Errors
    ///
    /// Returns [`SolverError::SortMismatch`] if `fmt` or any arg is not `String`,
    /// or if `buf_size_bv` is not `BitVec(32)`.
    ///
    /// # Example
    ///
    /// ```
    /// use ay_dpll::api::{Logic, Solver};
    ///
    /// let mut solver = Solver::try_new(Logic::QfSlia).expect("valid logic");
    /// let fmt = solver.string_const("hello ");
    /// let arg = solver.string_var("user_input");
    /// let buf = solver.bv_const(8, 32);  // 8-byte buffer
    /// let overflow = solver.try_format_string_vuln_check(fmt, &[arg], buf)
    ///     .expect("valid check");
    /// solver.try_assert_term(overflow).expect("bool assertion");
    /// // check_sat() == Sat means overflow is possible
    /// ```
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_format_string_vuln_check(
        &mut self,
        fmt: Term,
        args: &[Term],
        buf_size_bv: Term,
    ) -> Result<Term, SolverError> {
        self.expect_string("format_string_vuln_check (fmt)", fmt)?;
        for (i, arg) in args.iter().enumerate() {
            // We allow both String and BV args. BV args contribute their decimal
            // string length. String args contribute directly.
            let sort = self.terms().sort(arg.0).clone();
            match &sort {
                ay_core::Sort::String | ay_core::Sort::BitVec(_) => {}
                _ => {
                    return Err(SolverError::SortMismatch {
                        operation: "format_string_vuln_check",
                        expected: "String or BitVec",
                        got: vec![sort],
                    });
                }
            }
            let _ = i; // suppress unused warning
        }
        let bv_width =
            self.expect_bitvec_width("format_string_vuln_check (buf_size)", buf_size_bv)?;
        if bv_width != 32 {
            return Err(SolverError::InvalidArgument {
                operation: "format_string_vuln_check",
                message: format!("buf_size must be BitVec(32), got BitVec({bv_width})"),
            });
        }

        // Accumulate total output length in Int sort.
        // Start with format string length.
        let mut total_len = self.try_str_len(fmt)?;

        // Add each argument's contribution.
        for arg in args {
            let sort = self.terms().sort(arg.0).clone();
            let arg_len = match &sort {
                ay_core::Sort::String => self.try_str_len(*arg)?,
                ay_core::Sort::BitVec(_) => {
                    // BV argument: convert to string first, then take length.
                    // This models sprintf("%d", bv_val) output length.
                    let as_str = self.try_bv_to_string(*arg)?;
                    self.try_str_len(as_str)?
                }
                _ => unreachable!("sort already validated above"),
            };
            total_len = self.try_add(total_len, arg_len)?;
        }

        // Convert total length to BV32 and compare against buffer size.
        let total_len_bv = self.try_int2bv(total_len, 32)?;

        // overflow := total_len_bv >u buf_size_bv
        // Using unsigned greater-than since sizes are non-negative.
        self.try_bvugt(total_len_bv, buf_size_bv)
    }
}
