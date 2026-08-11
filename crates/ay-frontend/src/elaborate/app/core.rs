// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ay_core::{Sort, Symbol, TermId};

use super::super::term::arith_coercible;
use super::{Context, ElaborateError, Result};

impl Context {
    fn expect_bool_operands(&self, operation: &str, args: &[TermId]) -> Result<()> {
        for &arg in args {
            self.expect_arg_sort(arg, &Sort::Bool)
                .map_err(|_| ElaborateError::SortMismatch {
                    expected: format!("Bool: {operation} operand"),
                    actual: self.terms.sort(arg).to_string(),
                })?;
        }
        Ok(())
    }

    fn expect_array_operand(&self, operation: &str, operand: TermId) -> Result<(Sort, Sort)> {
        match self.terms.sort(operand) {
            Sort::Array(array) => Ok((array.index_sort.clone(), array.element_sort.clone())),
            actual => Err(ElaborateError::SortMismatch {
                expected: format!("Array: {operation} first operand"),
                actual: actual.to_string(),
            }),
        }
    }

    /// Reject `=`/`distinct` between two FloatingPoint operands of DIFFERENT
    /// sorts (e.g. `(_ FloatingPoint 11 53)` vs `(_ FloatingPoint 8 24)`).
    /// SMT-LIB requires same-sort `=` args and z3 errors on a mismatch; AY
    /// previously bit-blasted it and PANICKED with an index-out-of-bounds in the
    /// FP gate (`make_bits_equal` over unequal bit widths, #fp-sort-mismatch — a
    /// release crash, guarded only by a compiled-out `debug_assert`). Rejecting
    /// at elaboration returns a `SortMismatch`; the CLI's dropped-command path
    /// then fails closed to `unknown` (never a silent `sat`). A mismatched-FP `=`
    /// never appears in valid SMT-LIB, so this cannot reject a well-sorted term.
    fn reject_incompatible_fp_eq(&self, a: TermId, b: TermId) -> Result<()> {
        if let (Sort::FloatingPoint(ea, sa), Sort::FloatingPoint(eb, sb)) =
            (self.terms.sort(a), self.terms.sort(b))
        {
            if (ea, sa) != (eb, sb) {
                return Err(ElaborateError::SortMismatch {
                    expected: format!("(_ FloatingPoint {ea} {sa})"),
                    actual: format!("(_ FloatingPoint {eb} {sb})"),
                });
            }
        }
        Ok(())
    }

    pub(super) fn try_elaborate_core_app(
        &mut self,
        name: &str,
        arg_ids: &mut [TermId],
    ) -> Result<Option<TermId>> {
        // Z3 5.0.0 installs these user-friendly aliases only while no logic
        // has been selected.  `if` is different: it is an unconditional
        // spelling of `ite`.  User declarations are resolved before this
        // builtin path, so an explicitly declared alias still shadows it just
        // as it does in Z3.
        let canonical_name = match name {
            "if" => "ite",
            "implies" if self.logic.is_none() => "=>",
            "if_then_else" if self.logic.is_none() => "ite",
            "&&" if self.logic.is_none() => "and",
            "||" if self.logic.is_none() => "or",
            "equals" | "equiv" | "iff" if self.logic.is_none() => "=",
            _ => name,
        };

        match canonical_name {
            "to_real" => {
                if arg_ids.len() != 1 {
                    return Err(ElaborateError::InvalidConstant(
                        "to_real requires 1 argument".to_string(),
                    ));
                }
                self.maybe_promote_arithmetic_args(arg_ids)?;
                let arg_sort = self.terms.sort(arg_ids[0]).clone();
                match arg_sort {
                    Sort::Int => Ok(Some(self.terms.mk_app(
                        Symbol::named("to_real"),
                        &arg_ids,
                        Sort::Real,
                    ))),
                    // Z3 treats an already-Real coercion application as the
                    // identity, even when :int-real-coercions is false.
                    Sort::Real => Ok(Some(arg_ids[0])),
                    actual => Err(ElaborateError::SortMismatch {
                        expected: Sort::Int.to_string(),
                        actual: actual.to_string(),
                    }),
                }
            }
            "to_int" => {
                if arg_ids.len() != 1 {
                    return Err(ElaborateError::InvalidConstant(
                        "to_int requires 1 argument".to_string(),
                    ));
                }
                self.maybe_promote_arithmetic_args(arg_ids)?;
                let arg_sort = self.terms.sort(arg_ids[0]).clone();
                match arg_sort {
                    // Z3 treats an already-Int coercion application as the
                    // identity, independently of :int-real-coercions.
                    Sort::Int => Ok(Some(arg_ids[0])),
                    Sort::Real => Ok(Some(self.terms.mk_to_int(arg_ids[0]))),
                    actual => Err(ElaborateError::SortMismatch {
                        expected: Sort::Real.to_string(),
                        actual: actual.to_string(),
                    }),
                }
            }
            "is_int" => {
                if arg_ids.len() != 1 {
                    return Err(ElaborateError::InvalidConstant(
                        "is_int requires 1 argument".to_string(),
                    ));
                }
                self.maybe_promote_arithmetic_args(arg_ids)?;
                let arg_sort = self.terms.sort(arg_ids[0]).clone();
                match arg_sort {
                    Sort::Real => Ok(Some(self.terms.mk_is_int(arg_ids[0]))),
                    // Unlike the identity overloads above, Z3 admits Int here
                    // only while arithmetic coercions are enabled. A Bool was
                    // converted to Int by the same option-controlled path.
                    Sort::Int if self.int_real_coercions() => Ok(Some(self.terms.mk_bool(true))),
                    actual => Err(ElaborateError::SortMismatch {
                        expected: Sort::Real.to_string(),
                        actual: actual.to_string(),
                    }),
                }
            }
            "not" => {
                if arg_ids.len() != 1 {
                    return Err(ElaborateError::InvalidConstant(
                        "not requires 1 argument".to_string(),
                    ));
                }
                // Guard: mk_not requires Bool-sorted argument. Non-Bool can
                // reach here if ITE promotion or other elaboration produces a
                // non-Bool term. Return a sort mismatch error instead of
                // panicking. (#8481)
                let arg_sort = self.terms.sort(arg_ids[0]).clone();
                if arg_sort != Sort::Bool {
                    return Err(ElaborateError::SortMismatch {
                        expected: Sort::Bool.to_string(),
                        actual: arg_sort.to_string(),
                    });
                }
                Ok(Some(self.terms.mk_not(arg_ids[0])))
            }
            "and" => {
                // Z3's associative basic declarations accept a unary
                // application as the identity rewrite, but reject zero args.
                self.expect_min_arity("and", arg_ids, 1)?;
                self.expect_bool_operands("and", arg_ids)?;
                Ok(Some(self.terms.mk_and(arg_ids.to_vec())))
            }
            "or" => {
                self.expect_min_arity("or", arg_ids, 1)?;
                self.expect_bool_operands("or", arg_ids)?;
                Ok(Some(self.terms.mk_or(arg_ids.to_vec())))
            }
            "=>" => {
                self.expect_min_arity(canonical_name, arg_ids, 2)?;
                self.expect_bool_operands(canonical_name, arg_ids)?;
                let (last, prefix) = arg_ids.split_last().ok_or_else(|| {
                    ElaborateError::InvalidConstant(format!(
                        "{canonical_name} requires at least 2 arguments"
                    ))
                })?;
                let mut result = *last;
                for &arg in prefix.iter().rev() {
                    result = self.terms.mk_implies(arg, result);
                }
                Ok(Some(result))
            }
            "xor" => {
                self.expect_min_arity("xor", arg_ids, 1)?;
                self.expect_bool_operands("xor", arg_ids)?;
                if arg_ids.len() == 1 {
                    return Ok(Some(arg_ids[0]));
                }
                let mut result = self.terms.mk_xor(arg_ids[0], arg_ids[1]);
                for &arg in &arg_ids[2..] {
                    result = self.terms.mk_xor(result, arg);
                }
                Ok(Some(result))
            }
            "ite" => {
                if arg_ids.len() != 3 {
                    return Err(ElaborateError::InvalidConstant(
                        "ite requires 3 arguments".to_string(),
                    ));
                }
                // ITE branches must have the same sort. z3 coerces a differing
                // pair only within {Bool, Int, Real} (Bool -> (ite b 1 0), Int
                // -> Real), tracking the join as the result sort T; any other
                // differing pair is a sort error. All-Bool (equal) branches are
                // left Bool — the != guard means maybe_promote_numeric_args (which
                // would rewrite Bool to (ite b 1 0), changing the result sort and
                // breaking (not (ite c a b)) for Bool ITEs, #8481) is reached ONLY
                // when the branches already differ, so #8481 is unaffected.
                let then_sort = self.terms.sort(arg_ids[1]).clone();
                let else_sort = self.terms.sort(arg_ids[2]).clone();
                if then_sort != else_sort {
                    if arith_coercible(&then_sort) && arith_coercible(&else_sort) {
                        self.maybe_promote_numeric_args(&mut arg_ids[1..3])?;
                    } else if !self.lenient_sort_coercions() {
                        // Non-coercible differing branches: z3 reports the pair as
                        // `Sorts <then> and <else> are incompatible`.
                        return Err(ElaborateError::SortMismatch {
                            expected: then_sort.to_string(),
                            actual: else_sort.to_string(),
                        });
                    }
                    // lenient && not coercible: legacy fall-through (mk_ite; the
                    // solver later fail-closes a mismatched-branch ite to unknown).
                }
                // The condition must be Bool. z3 reports a non-Bool condition as
                // an argument-#1 mismatch against the ite signature specialized to
                // the (post-coercion) branch sort T. Checked after branch
                // reconciliation so T reflects the join (e.g. (ite 1 x r) -> Real).
                if !self.lenient_sort_coercions() {
                    let cond_sort = self.terms.sort(arg_ids[0]).clone();
                    if cond_sort != Sort::Bool {
                        let t = self.terms.sort(arg_ids[1]).to_string();
                        return Err(ElaborateError::IllSorted(format!(
                            "Sort mismatch at argument #1 for function \
                             (declare-fun ite (Bool {t} {t}) {t}) supplied sort is {cond_sort}"
                        )));
                    }
                }
                Ok(Some(self.terms.mk_ite(arg_ids[0], arg_ids[1], arg_ids[2])))
            }
            "=" => {
                if arg_ids.len() < 2 {
                    return Err(ElaborateError::InvalidConstant(
                        "= requires at least 2 arguments".to_string(),
                    ));
                }
                // z3 4.15.4 parity: reject ill-sorted operands (a differing pair
                // not both in {Bool, Int, Real}) as a sort error. The equal-sort
                // identity rule inside check_chain_sorts keeps every matching
                // non-coercible sort (Seq/Array/datatype/uninterpreted/same-width
                // BitVec/FP/String) ACCEPTED, exactly as z3 does. Skipped under
                // the legacy lenient flag (which restores #5115 BV zero-extend).
                if !self.lenient_sort_coercions() {
                    self.check_chain_sorts(arg_ids)?;
                }
                // Only promote when args have mixed sorts. When all args share
                // the same sort (including Bool), no promotion is needed — mk_eq
                // handles same-sort equality natively. Without this guard,
                // `(= (not x) (not y))` gets both Bool args promoted to Int,
                // destroying negation-lifting simplifications. (#8481)
                let all_same_sort = arg_ids
                    .windows(2)
                    .all(|w| self.terms.sort(w[0]) == self.terms.sort(w[1]));
                if !all_same_sort {
                    self.maybe_promote_numeric_args(arg_ids)?;
                }
                if arg_ids.len() == 2 {
                    self.reject_incompatible_fp_eq(arg_ids[0], arg_ids[1])?;
                    // #5115: coerce BV width mismatches (e.g., #x1 vs extract result)
                    self.maybe_coerce_bv_widths(arg_ids);
                    Ok(Some(self.terms.mk_eq(arg_ids[0], arg_ids[1])))
                } else {
                    let mut eqs = Vec::new();
                    for i in 0..arg_ids.len() - 1 {
                        self.reject_incompatible_fp_eq(arg_ids[i], arg_ids[i + 1])?;
                        let mut pair = [arg_ids[i], arg_ids[i + 1]];
                        self.maybe_coerce_bv_widths(&mut pair);
                        eqs.push(self.terms.mk_eq(pair[0], pair[1]));
                    }
                    Ok(Some(self.terms.mk_and(eqs)))
                }
            }
            "distinct" => {
                // Unlike `=`, Z3 5.0.0 accepts unary `distinct` (true).  Its
                // SMT2 parser still rejects an application with no operands.
                self.expect_min_arity("distinct", arg_ids, 1)?;
                // z3 4.15.4 parity: same sort-checking as "=" (see above).
                if !self.lenient_sort_coercions() {
                    self.check_chain_sorts(arg_ids)?;
                }
                // Same as "=": only promote when sorts are mixed. (#8481)
                let all_same_sort = arg_ids
                    .windows(2)
                    .all(|w| self.terms.sort(w[0]) == self.terms.sort(w[1]));
                if !all_same_sort {
                    self.maybe_promote_numeric_args(arg_ids)?;
                }
                for i in 0..arg_ids.len().saturating_sub(1) {
                    self.reject_incompatible_fp_eq(arg_ids[i], arg_ids[i + 1])?;
                }
                // #5115: coerce BV width mismatches for distinct too
                if arg_ids.len() == 2 {
                    self.maybe_coerce_bv_widths(arg_ids);
                }
                Ok(Some(self.terms.mk_distinct(arg_ids.to_vec())))
            }
            "select" => {
                if arg_ids.len() != 2 {
                    return Err(ElaborateError::InvalidConstant(
                        "select requires 2 arguments".to_string(),
                    ));
                }
                let (expected_index_sort, _) = self.expect_array_operand("select", arg_ids[0])?;
                let index_sort = self.terms.sort(arg_ids[1]).clone();
                if index_sort != expected_index_sort {
                    return Err(ElaborateError::SortMismatch {
                        expected: expected_index_sort.to_string(),
                        actual: index_sort.to_string(),
                    });
                }
                Ok(Some(self.terms.mk_select(arg_ids[0], arg_ids[1])))
            }
            "store" => {
                if arg_ids.len() != 3 {
                    return Err(ElaborateError::InvalidConstant(
                        "store requires 3 arguments".to_string(),
                    ));
                }
                let (expected_index_sort, expected_value_sort) =
                    self.expect_array_operand("store", arg_ids[0])?;
                let index_sort = self.terms.sort(arg_ids[1]).clone();
                if index_sort != expected_index_sort {
                    return Err(ElaborateError::SortMismatch {
                        expected: expected_index_sort.to_string(),
                        actual: index_sort.to_string(),
                    });
                }
                let value_sort = self.terms.sort(arg_ids[2]).clone();
                if value_sort != expected_value_sort {
                    return Err(ElaborateError::SortMismatch {
                        expected: expected_value_sort.to_string(),
                        actual: value_sort.to_string(),
                    });
                }
                Ok(Some(
                    self.terms.mk_store(arg_ids[0], arg_ids[1], arg_ids[2]),
                ))
            }
            "default" => {
                // Array default: (default a) returns the else-case value of an array.
                // Z3 ref: array_decl_plugin.h:58 (OP_ARRAY_DEFAULT)
                if arg_ids.len() != 1 {
                    return Err(ElaborateError::InvalidConstant(
                        "default requires 1 argument".to_string(),
                    ));
                }
                self.expect_array_operand("default", arg_ids[0])?;
                Ok(Some(self.terms.mk_array_default(arg_ids[0])))
            }
            _ => Ok(None),
        }
    }
}
