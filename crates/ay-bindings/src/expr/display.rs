// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates
//
//! Display implementation for AY expressions.
//!
//! Outputs SMT-LIB2 formatted expressions.

use crate::format_symbol;
use std::fmt::{self, Display, Formatter};

use super::{
    all_ones_literal, int_min_literal, normalize_bitvec_value, zero_literal, Expr, ExprValue,
};

/// Extract BV width from an expression's sort, panicking on invariant violation.
///
/// All BV overflow variants are constructed only by APIs that require BitVec
/// sorts (`crates/ay-bindings/src/expr/overflow.rs`). A non-BV sort here
/// indicates a bug in the constructor, not a recoverable condition.
fn expect_bv_width(expr: &Expr, context: &str) -> u32 {
    expr.sort().bitvec_width().unwrap_or_else(|| {
        panic!(
            "BV invariant violation in {context}: expected BitVec sort, got {:?}",
            expr.sort()
        )
    })
}

/// Red zone for `stacker::maybe_grow` in Expr Display (#8414).
const DISPLAY_STACK_RED_ZONE: usize = 32 * 1024;

/// Stack growth segment for Expr Display.
const DISPLAY_STACK_SIZE: usize = 1024 * 1024;

impl Display for Expr {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        stacker::maybe_grow(DISPLAY_STACK_RED_ZONE, DISPLAY_STACK_SIZE, || {
            self.fmt_inner(f)
        })
    }
}

impl Expr {
    fn fmt_inner(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.value.as_ref() {
            ExprValue::BoolConst(b) => write!(f, "{b}"),
            ExprValue::BitVecConst { value, width } => {
                // SMT-LIB2 hex format #xN always has 4 bits per hex digit.
                // For widths that aren't multiples of 4, use binary format (#b...).
                if *width % 4 == 0 {
                    // Width is a multiple of 4, safe to use hex format
                    let hex_digits = (*width as usize) / 4;
                    let normalized = normalize_bitvec_value(value.clone(), *width);
                    write!(f, "#x{normalized:0>hex_digits$x}")
                } else {
                    let normalized = normalize_bitvec_value(value.clone(), *width);
                    let mut bits = normalized.to_str_radix(2);
                    let expected_width = *width as usize;
                    if bits.len() < expected_width {
                        bits = format!("{bits:0>expected_width$}");
                    }
                    write!(f, "#b{bits}")
                }
            }
            ExprValue::IntConst(v) => write!(f, "{v}"),
            ExprValue::RealConst(v) => write!(f, "{v}.0"),
            ExprValue::Var { name } => write!(f, "{}", format_symbol(name)),
            ExprValue::Not(e) => write!(f, "(not {e})"),
            ExprValue::And(es) => {
                write!(f, "(and")?;
                for e in es {
                    write!(f, " {e}")?;
                }
                write!(f, ")")
            }
            ExprValue::Or(es) => {
                write!(f, "(or")?;
                for e in es {
                    write!(f, " {e}")?;
                }
                write!(f, ")")
            }
            ExprValue::Xor(a, b) => write!(f, "(xor {a} {b})"),
            ExprValue::Implies(a, b) => write!(f, "(=> {a} {b})"),
            ExprValue::Ite {
                cond,
                then_expr,
                else_expr,
            } => {
                write!(f, "(ite {cond} {then_expr} {else_expr})")
            }
            ExprValue::Eq(a, b) => write!(f, "(= {a} {b})"),
            ExprValue::Distinct(es) => {
                write!(f, "(distinct")?;
                for e in es {
                    write!(f, " {e}")?;
                }
                write!(f, ")")
            }
            ExprValue::BvAdd(a, b) => write!(f, "(bvadd {a} {b})"),
            ExprValue::BvSub(a, b) => write!(f, "(bvsub {a} {b})"),
            ExprValue::BvMul(a, b) => write!(f, "(bvmul {a} {b})"),
            ExprValue::BvUDiv(a, b) => write!(f, "(bvudiv {a} {b})"),
            ExprValue::BvSDiv(a, b) => write!(f, "(bvsdiv {a} {b})"),
            ExprValue::BvURem(a, b) => write!(f, "(bvurem {a} {b})"),
            ExprValue::BvSRem(a, b) => write!(f, "(bvsrem {a} {b})"),
            ExprValue::BvNeg(e) => write!(f, "(bvneg {e})"),
            ExprValue::BvNot(e) => write!(f, "(bvnot {e})"),
            ExprValue::BvAnd(a, b) => write!(f, "(bvand {a} {b})"),
            ExprValue::BvOr(a, b) => write!(f, "(bvor {a} {b})"),
            ExprValue::BvXor(a, b) => write!(f, "(bvxor {a} {b})"),
            ExprValue::BvShl(a, b) => write!(f, "(bvshl {a} {b})"),
            ExprValue::BvLShr(a, b) => write!(f, "(bvlshr {a} {b})"),
            ExprValue::BvAShr(a, b) => write!(f, "(bvashr {a} {b})"),
            ExprValue::BvULt(a, b) => write!(f, "(bvult {a} {b})"),
            ExprValue::BvULe(a, b) => write!(f, "(bvule {a} {b})"),
            ExprValue::BvUGt(a, b) => write!(f, "(bvugt {a} {b})"),
            ExprValue::BvUGe(a, b) => write!(f, "(bvuge {a} {b})"),
            ExprValue::BvSLt(a, b) => write!(f, "(bvslt {a} {b})"),
            ExprValue::BvSLe(a, b) => write!(f, "(bvsle {a} {b})"),
            ExprValue::BvSGt(a, b) => write!(f, "(bvsgt {a} {b})"),
            ExprValue::BvSGe(a, b) => write!(f, "(bvsge {a} {b})"),
            ExprValue::BvZeroExtend { expr, extra_bits } => {
                write!(f, "((_ zero_extend {extra_bits}) {expr})")
            }
            ExprValue::BvSignExtend { expr, extra_bits } => {
                write!(f, "((_ sign_extend {extra_bits}) {expr})")
            }
            ExprValue::BvExtract { expr, high, low } => {
                write!(f, "((_ extract {high} {low}) {expr})")
            }
            ExprValue::BvConcat(a, b) => write!(f, "(concat {a} {b})"),

            // Overflow checks - expanded to SMT-LIB2 logical encodings
            // Note: Z3 has bvadd_no_overflow/etc but they're not standard SMT-LIB2,
            // so we expand to portable encodings.

            // Unsigned add no overflow: NOT (result < a)
            // result < a means overflow occurred, so NOT that for no-overflow
            ExprValue::BvAddNoOverflowUnsigned(a, b) => {
                // no_overflow <==> (bvadd a b) >= a
                write!(f, "(bvuge (bvadd {a} {b}) {a})")
            }

            // Signed add no overflow:
            // overflow <==> (a>0 && b>0 && r<0) || (a<0 && b<0 && r>0)
            // no_overflow <==> NOT that
            ExprValue::BvAddNoOverflowSigned(a, b) => {
                let w = expect_bv_width(a, "BvAddNoOverflowSigned");
                let zero = zero_literal(w);
                // Let r = a + b
                // Sign bit: if a[n-1] = 0 then a >= 0 (in signed)
                // pos_pos_neg: both positive, result negative
                // neg_neg_pos: both negative, result positive
                write!(
                    f,
                    "(not (or (and (bvsge {a} {zero}) (bvsge {b} {zero}) (bvslt (bvadd {a} {b}) {zero})) \
                               (and (bvslt {a} {zero}) (bvslt {b} {zero}) (bvsge (bvadd {a} {b}) {zero}))))", // neg_neg_pos
                )
            }

            // Unsigned sub no underflow: a >= b
            ExprValue::BvSubNoUnderflowUnsigned(a, b) => {
                write!(f, "(bvuge {a} {b})")
            }

            // Signed sub no overflow:
            // overflow <==> (a>0 && b<0 && r<0) || (a<0 && b>0 && r>0)
            ExprValue::BvSubNoOverflowSigned(a, b) => {
                let w = expect_bv_width(a, "BvSubNoOverflowSigned");
                let zero = zero_literal(w);
                write!(
                    f,
                    "(not (or (and (bvsge {a} {zero}) (bvslt {b} {zero}) (bvslt (bvsub {a} {b}) {zero})) \
                               (and (bvslt {a} {zero}) (bvsge {b} {zero}) (bvsge (bvsub {a} {b}) {zero}))))", // neg_pos_pos
                )
            }

            // Unsigned mul no overflow: zero_extend to double width, multiply, check high bits are zero
            ExprValue::BvMulNoOverflowUnsigned(a, b) => {
                let w = expect_bv_width(a, "BvMulNoOverflowUnsigned");
                let zero = zero_literal(w);
                // (= ((_ extract (2w-1) w) (bvmul (zext a) (zext b))) 0)
                write!(
                    f,
                    "(= ((_ extract {} {}) (bvmul ((_ zero_extend {}) {}) ((_ zero_extend {}) {}))) {})",
                    2 * w - 1,
                    w,
                    w,
                    a,
                    w,
                    b,
                    zero,
                )
            }

            // Signed mul no overflow: more complex, use sign-extended multiply
            ExprValue::BvMulNoOverflowSigned(a, b) => {
                let w = expect_bv_width(a, "BvMulNoOverflowSigned");
                // Sign extend both to 2w bits, multiply, extract high w+1 bits,
                // check they're all same (all 0s or all 1s = sign extension of result)
                let hi_width = w + 1;
                let all_zeros = zero_literal(hi_width);
                let all_ones = all_ones_literal(hi_width);
                write!(
                    f,
                    "(let ((res (bvmul ((_ sign_extend {}) {}) ((_ sign_extend {}) {})))) \
                       (let ((hi ((_ extract {} {}) res)) (sign ((_ extract {} {}) res))) \
                         (or (= hi {}) (= hi {}))))",
                    w,
                    a,
                    w,
                    b,
                    2 * w - 1,
                    w - 1, // high w+1 bits
                    w - 1,
                    w - 1,     // sign bit of result
                    all_zeros, // all zeros
                    all_ones,  // all ones
                )
            }

            // Negation no overflow: a != INT_MIN
            // INT_MIN has sign bit 1 and all other bits 0: 0x80...0
            ExprValue::BvNegNoOverflow(a) => {
                let w = expect_bv_width(a, "BvNegNoOverflow");
                // Use helper that handles non-multiple-of-4 widths correctly
                let int_min = int_min_literal(w);
                write!(f, "(not (= {a} {int_min}))")
            }

            // Signed division no overflow: !(a == INT_MIN && b == -1)
            // This is the only case where signed division can overflow:
            // INT_MIN / -1 = -INT_MIN, which exceeds INT_MAX
            ExprValue::BvSdivNoOverflow(a, b) => {
                let w = expect_bv_width(a, "BvSdivNoOverflow");
                let int_min = int_min_literal(w);
                let minus_one = all_ones_literal(w);
                write!(f, "(not (and (= {a} {int_min}) (= {b} {minus_one})))")
            }

            ExprValue::IntAdd(a, b) | ExprValue::RealAdd(a, b) => write!(f, "(+ {a} {b})"),
            ExprValue::IntSub(a, b) | ExprValue::RealSub(a, b) => write!(f, "(- {a} {b})"),
            ExprValue::IntMul(a, b) | ExprValue::RealMul(a, b) => write!(f, "(* {a} {b})"),
            ExprValue::IntDiv(a, b) => write!(f, "(div {a} {b})"),
            ExprValue::IntMod(a, b) => write!(f, "(mod {a} {b})"),
            ExprValue::IntNeg(e) | ExprValue::RealNeg(e) => write!(f, "(- {e})"),
            ExprValue::IntLt(a, b) | ExprValue::RealLt(a, b) => write!(f, "(< {a} {b})"),
            ExprValue::IntLe(a, b) | ExprValue::RealLe(a, b) => write!(f, "(<= {a} {b})"),
            ExprValue::IntGt(a, b) | ExprValue::RealGt(a, b) => write!(f, "(> {a} {b})"),
            ExprValue::IntGe(a, b) | ExprValue::RealGe(a, b) => write!(f, "(>= {a} {b})"),
            // Real (rational) operations - Part of #911
            ExprValue::IntToReal(e) => write!(f, "(to_real {e})"),
            ExprValue::RealToInt(e) => write!(f, "(to_int {e})"),
            ExprValue::IsInt(e) => write!(f, "(is_int {e})"),
            ExprValue::RealDiv(a, b) => write!(f, "(/ {a} {b})"),
            ExprValue::Select { array, index } => write!(f, "(select {array} {index})"),
            ExprValue::Store {
                array,
                index,
                value,
            } => {
                write!(f, "(store {array} {index} {value})")
            }
            ExprValue::ConstArray { index_sort, value } => {
                write!(
                    f,
                    "((as const (Array {} {})) {})",
                    index_sort,
                    value.sort(),
                    value
                )
            }
            ExprValue::DatatypeConstructor {
                datatype_name,
                constructor_name,
                args,
            } => {
                let constructor_name = format_symbol(constructor_name);
                if args.is_empty() {
                    // Nullary constructors still need sort qualification to avoid
                    // ambiguous constant references across datatype families.
                    write!(
                        f,
                        "(as {} {})",
                        constructor_name,
                        format_symbol(datatype_name)
                    )
                } else {
                    // Non-nullary constructor applications should use the bare
                    // constructor symbol; `((as Ctor Sort) arg ...)` is rejected
                    // by AY's elaboration path for the emitted datatype terms.
                    write!(f, "({constructor_name}")?;
                    for arg in args {
                        write!(f, " {arg}")?;
                    }
                    write!(f, ")")
                }
            }
            ExprValue::DatatypeSelector {
                selector_name,
                expr,
                ..
            } => {
                write!(f, "({} {})", format_symbol(selector_name), expr)
            }
            ExprValue::DatatypeTester {
                datatype_name: _,
                constructor_name,
                expr,
            } => {
                // Z3 `(_ is ...)` tester does NOT accept `(as Name Sort)` qualification.
                // Scoped constructor names (e.g., Some_Option_bv32) are already unique,
                // so bare names work. This fixes a Z3 parse error on qualified testers.
                write!(f, "((_ is {}) {})", format_symbol(constructor_name), expr)
            }
            ExprValue::Forall {
                vars,
                body,
                triggers,
            } => {
                write!(f, "(forall (")?;
                for (name, sort) in vars {
                    write!(f, "({} {}) ", format_symbol(name), sort)?;
                }
                if triggers.is_empty() {
                    write!(f, ") {body})")
                } else {
                    write!(f, ") (! {body}")?;
                    for trigger in triggers {
                        write!(f, " :pattern (")?;
                        for (i, t) in trigger.iter().enumerate() {
                            if i > 0 {
                                write!(f, " ")?;
                            }
                            write!(f, "{t}")?;
                        }
                        write!(f, ")")?;
                    }
                    write!(f, "))")
                }
            }
            ExprValue::Exists {
                vars,
                body,
                triggers,
            } => {
                write!(f, "(exists (")?;
                for (name, sort) in vars {
                    write!(f, "({} {}) ", format_symbol(name), sort)?;
                }
                if triggers.is_empty() {
                    write!(f, ") {body})")
                } else {
                    write!(f, ") (! {body}")?;
                    for trigger in triggers {
                        write!(f, " :pattern (")?;
                        for (i, t) in trigger.iter().enumerate() {
                            if i > 0 {
                                write!(f, " ")?;
                            }
                            write!(f, "{t}")?;
                        }
                        write!(f, ")")?;
                    }
                    write!(f, "))")
                }
            }
            ExprValue::FuncApp { name, args } => {
                if args.is_empty() {
                    write!(f, "{}", format_symbol(name))
                } else {
                    write!(f, "({}", format_symbol(name))?;
                    for arg in args {
                        write!(f, " {arg}")?;
                    }
                    write!(f, ")")
                }
            }
            // Sort conversions
            ExprValue::Bv2Int(expr) => write!(f, "(bv2int {expr})"),
            ExprValue::Int2Bv(expr, width) => write!(f, "((_ int2bv {width}) {expr})"),

            // Floating-point constants
            ExprValue::FpPlusInfinity { eb, sb } => write!(f, "(_ +oo {eb} {sb})"),
            ExprValue::FpMinusInfinity { eb, sb } => write!(f, "(_ -oo {eb} {sb})"),
            ExprValue::FpNaN { eb, sb } => write!(f, "(_ NaN {eb} {sb})"),
            ExprValue::FpPlusZero { eb, sb } => write!(f, "(_ +zero {eb} {sb})"),
            ExprValue::FpMinusZero { eb, sb } => write!(f, "(_ -zero {eb} {sb})"),

            // FP unary
            ExprValue::FpAbs(x) => write!(f, "(fp.abs {x})"),
            ExprValue::FpNeg(x) => write!(f, "(fp.neg {x})"),

            // FP arithmetic (with rounding mode)
            ExprValue::FpAdd(rm, a, b) => write!(f, "(fp.add {} {a} {b})", rm.smt_name()),
            ExprValue::FpSub(rm, a, b) => write!(f, "(fp.sub {} {a} {b})", rm.smt_name()),
            ExprValue::FpMul(rm, a, b) => write!(f, "(fp.mul {} {a} {b})", rm.smt_name()),
            ExprValue::FpDiv(rm, a, b) => write!(f, "(fp.div {} {a} {b})", rm.smt_name()),
            ExprValue::FpFma(rm, x, y, z) => {
                write!(f, "(fp.fma {} {x} {y} {z})", rm.smt_name())
            }
            ExprValue::FpSqrt(rm, x) => write!(f, "(fp.sqrt {} {x})", rm.smt_name()),
            ExprValue::FpRoundToIntegral(rm, x) => {
                write!(f, "(fp.roundToIntegral {} {x})", rm.smt_name())
            }

            // FP binary (no rounding mode)
            ExprValue::FpRem(a, b) => write!(f, "(fp.rem {a} {b})"),
            ExprValue::FpMin(a, b) => write!(f, "(fp.min {a} {b})"),
            ExprValue::FpMax(a, b) => write!(f, "(fp.max {a} {b})"),

            // FP comparisons
            ExprValue::FpEq(a, b) => write!(f, "(fp.eq {a} {b})"),
            ExprValue::FpLt(a, b) => write!(f, "(fp.lt {a} {b})"),
            ExprValue::FpLe(a, b) => write!(f, "(fp.leq {a} {b})"),
            ExprValue::FpGt(a, b) => write!(f, "(fp.gt {a} {b})"),
            ExprValue::FpGe(a, b) => write!(f, "(fp.geq {a} {b})"),

            // FP classification predicates
            ExprValue::FpIsNaN(x) => write!(f, "(fp.isNaN {x})"),
            ExprValue::FpIsInfinite(x) => write!(f, "(fp.isInfinite {x})"),
            ExprValue::FpIsZero(x) => write!(f, "(fp.isZero {x})"),
            ExprValue::FpIsNormal(x) => write!(f, "(fp.isNormal {x})"),
            ExprValue::FpIsSubnormal(x) => write!(f, "(fp.isSubnormal {x})"),
            ExprValue::FpIsPositive(x) => write!(f, "(fp.isPositive {x})"),
            ExprValue::FpIsNegative(x) => write!(f, "(fp.isNegative {x})"),

            // FP conversions
            ExprValue::FpToSbv(rm, x, w) => {
                write!(f, "((_ fp.to_sbv {w}) {} {x})", rm.smt_name())
            }
            ExprValue::FpToUbv(rm, x, w) => {
                write!(f, "((_ fp.to_ubv {w}) {} {x})", rm.smt_name())
            }
            ExprValue::FpToReal(x) => write!(f, "(fp.to_real {x})"),
            ExprValue::FpToIeeeBv(x) => write!(f, "(fp.to_ieee_bv {x})"),

            // FP construction
            ExprValue::FpFromBvs(sign, exp, sig) => write!(f, "(fp {sign} {exp} {sig})"),

            // Conversions to FP
            ExprValue::BvToFp(rm, x, eb, sb) => {
                write!(f, "((_ to_fp {eb} {sb}) {} {x})", rm.smt_name())
            }
            ExprValue::BvToFpUnsigned(rm, x, eb, sb) => {
                write!(f, "((_ to_fp_unsigned {eb} {sb}) {} {x})", rm.smt_name())
            }
            ExprValue::FpToFp(rm, x, eb, sb) => {
                write!(f, "((_ to_fp {eb} {sb}) {} {x})", rm.smt_name())
            }

            // String operations
            ExprValue::StrConcat(a, b) => write!(f, "(str.++ {a} {b})"),
            ExprValue::StrLen(s) => write!(f, "(str.len {s})"),
            ExprValue::StrAt(s, i) => write!(f, "(str.at {s} {i})"),
            ExprValue::StrSubstr(s, off, len) => write!(f, "(str.substr {s} {off} {len})"),
            ExprValue::StrContains(s, t) => write!(f, "(str.contains {s} {t})"),
            ExprValue::StrPrefixOf(pre, s) => write!(f, "(str.prefixof {pre} {s})"),
            ExprValue::StrSuffixOf(suf, s) => write!(f, "(str.suffixof {suf} {s})"),
            ExprValue::StrIndexOf(s, t, i) => write!(f, "(str.indexof {s} {t} {i})"),
            ExprValue::StrReplace(s, from, to) => write!(f, "(str.replace {s} {from} {to})"),
            ExprValue::StrReplaceAll(s, from, to) => {
                write!(f, "(str.replace_all {s} {from} {to})")
            }
            ExprValue::StrToInt(s) => write!(f, "(str.to_int {s})"),
            ExprValue::StrFromInt(i) => write!(f, "(str.from_int {i})"),
            ExprValue::StrToRe(s) => write!(f, "(str.to_re {s})"),
            ExprValue::StrInRe(s, re) => write!(f, "(str.in_re {s} {re})"),

            // Regex operations
            ExprValue::ReStar(re) => write!(f, "(re.* {re})"),
            ExprValue::RePlus(re) => write!(f, "(re.+ {re})"),
            ExprValue::ReUnion(a, b) => write!(f, "(re.union {a} {b})"),
            ExprValue::ReConcat(a, b) => write!(f, "(re.++ {a} {b})"),

            // Sequence operations
            ExprValue::SeqEmpty(sort) => write!(f, "(as seq.empty (Seq {sort}))"),
            ExprValue::SeqUnit(elem) => write!(f, "(seq.unit {elem})"),
            ExprValue::SeqConcat(a, b) => write!(f, "(seq.++ {a} {b})"),
            ExprValue::SeqLen(s) => write!(f, "(seq.len {s})"),
            ExprValue::SeqNth(s, i) => write!(f, "(seq.nth {s} {i})"),
            ExprValue::SeqExtract(s, off, len) => write!(f, "(seq.extract {s} {off} {len})"),
            ExprValue::SeqContains(s, t) => write!(f, "(seq.contains {s} {t})"),
            ExprValue::SeqPrefixOf(pre, s) => write!(f, "(seq.prefixof {pre} {s})"),
            ExprValue::SeqSuffixOf(suf, s) => write!(f, "(seq.suffixof {suf} {s})"),
            ExprValue::SeqIndexOf(s, t, i) => write!(f, "(seq.indexof {s} {t} {i})"),
            ExprValue::SeqReplace(s, from, to) => write!(f, "(seq.replace {s} {from} {to})"),
        }
    }
}
