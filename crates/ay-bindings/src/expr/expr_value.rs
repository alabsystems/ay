// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates
//
//! ExprValue enum definition and core methods.
//!
//! Extracted from `mod.rs` for navigability (#5970).

use super::{Expr, RoundingMode};
use crate::sort::Sort;
use num_bigint::BigInt;

/// The different kinds of expression values.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum ExprValue {
    // ===== Constants =====
    /// Boolean constant (true/false).
    BoolConst(bool),

    /// Bitvector constant with value and width.
    /// Value is stored as BigInt to support arbitrary widths.
    BitVecConst { value: BigInt, width: u32 },

    /// Integer constant (unbounded).
    IntConst(BigInt),

    /// Real constant (integer value, coerced to Real sort).
    ///
    /// In SMT-LIB2, integer literals can be used directly in Real context.
    /// This provides a direct constructor without requiring int_to_real conversion.
    RealConst(BigInt),

    // ===== Variables =====
    /// Symbolic variable (from declare-const).
    Var { name: String },

    // ===== Boolean Operations =====
    /// Logical NOT.
    Not(Expr),

    /// Logical AND (n-ary).
    And(Vec<Expr>),

    /// Logical OR (n-ary).
    Or(Vec<Expr>),

    /// Logical XOR.
    Xor(Expr, Expr),

    /// Logical implication (a => b).
    Implies(Expr, Expr),

    /// If-then-else (ite c t e).
    Ite {
        cond: Expr,
        then_expr: Expr,
        else_expr: Expr,
    },

    // ===== Equality and Comparison =====
    /// Equality (=).
    Eq(Expr, Expr),

    /// Distinct (not equal, n-ary).
    Distinct(Vec<Expr>),

    // ===== Bitvector Operations =====
    /// Bitvector addition.
    BvAdd(Expr, Expr),

    /// Bitvector subtraction.
    BvSub(Expr, Expr),

    /// Bitvector multiplication.
    BvMul(Expr, Expr),

    /// Unsigned bitvector division.
    BvUDiv(Expr, Expr),

    /// Signed bitvector division.
    BvSDiv(Expr, Expr),

    /// Unsigned bitvector remainder.
    BvURem(Expr, Expr),

    /// Signed bitvector remainder.
    BvSRem(Expr, Expr),

    /// Bitvector negation (two's complement).
    BvNeg(Expr),

    /// Bitwise NOT.
    BvNot(Expr),

    /// Bitwise AND.
    BvAnd(Expr, Expr),

    /// Bitwise OR.
    BvOr(Expr, Expr),

    /// Bitwise XOR.
    BvXor(Expr, Expr),

    /// Logical shift left.
    BvShl(Expr, Expr),

    /// Logical shift right.
    BvLShr(Expr, Expr),

    /// Arithmetic shift right.
    BvAShr(Expr, Expr),

    /// Unsigned less than.
    BvULt(Expr, Expr),

    /// Unsigned less than or equal.
    BvULe(Expr, Expr),

    /// Unsigned greater than.
    BvUGt(Expr, Expr),

    /// Unsigned greater than or equal.
    BvUGe(Expr, Expr),

    /// Signed less than.
    BvSLt(Expr, Expr),

    /// Signed less than or equal.
    BvSLe(Expr, Expr),

    /// Signed greater than.
    BvSGt(Expr, Expr),

    /// Signed greater than or equal.
    BvSGe(Expr, Expr),

    /// Zero extend to wider bitvector.
    BvZeroExtend { expr: Expr, extra_bits: u32 },

    /// Sign extend to wider bitvector.
    BvSignExtend { expr: Expr, extra_bits: u32 },

    /// Extract bits `[high:low]` (inclusive).
    BvExtract { expr: Expr, high: u32, low: u32 },

    /// Concatenate two bitvectors.
    BvConcat(Expr, Expr),

    // ===== Overflow Detection Operations =====
    // These return Bool indicating whether overflow/underflow occurred.
    /// Unsigned addition overflow: (result < a) or (result < b)
    BvAddNoOverflowUnsigned(Expr, Expr),

    /// Signed addition overflow:
    /// (a > 0 && b > 0 && result < 0) || (a < 0 && b < 0 && result > 0)
    BvAddNoOverflowSigned(Expr, Expr),

    /// Unsigned subtraction underflow: b > a
    BvSubNoUnderflowUnsigned(Expr, Expr),

    /// Signed subtraction overflow:
    /// (a > 0 && b < 0 && result < 0) || (a < 0 && b > 0 && result > 0)
    BvSubNoOverflowSigned(Expr, Expr),

    /// Unsigned multiplication overflow: if either is zero => false, else high bits of wide result != 0
    BvMulNoOverflowUnsigned(Expr, Expr),

    /// Signed multiplication overflow: more complex, checks sign and magnitude
    BvMulNoOverflowSigned(Expr, Expr),

    /// Signed negation overflow: a == INT_MIN
    BvNegNoOverflow(Expr),

    /// Signed division overflow: a == INT_MIN && b == -1
    BvSdivNoOverflow(Expr, Expr),

    // ===== Integer Operations =====
    /// Integer addition.
    IntAdd(Expr, Expr),

    /// Integer subtraction.
    IntSub(Expr, Expr),

    /// Integer multiplication.
    IntMul(Expr, Expr),

    /// Integer division.
    IntDiv(Expr, Expr),

    /// Integer modulo.
    IntMod(Expr, Expr),

    /// Integer negation.
    IntNeg(Expr),

    /// Integer less than.
    IntLt(Expr, Expr),

    /// Integer less than or equal.
    IntLe(Expr, Expr),

    /// Integer greater than.
    IntGt(Expr, Expr),

    /// Integer greater than or equal.
    IntGe(Expr, Expr),

    /// Convert Int to Real.
    IntToReal(Expr),

    /// Convert Real to Int (floor).
    /// SMT-LIB: (to_int r) returns floor(r).
    RealToInt(Expr),

    /// Test if Real is integral.
    /// SMT-LIB: (is_int r) returns true iff r is an integer value.
    IsInt(Expr),

    // ===== Real (Rational) Operations =====
    // Part of #911: BigRational interception for CHC codegen.
    // Real arithmetic on rational inputs produces rational outputs.
    /// Real addition.
    RealAdd(Expr, Expr),

    /// Real subtraction.
    RealSub(Expr, Expr),

    /// Real multiplication.
    RealMul(Expr, Expr),

    /// Real division.
    RealDiv(Expr, Expr),

    /// Real negation.
    RealNeg(Expr),

    /// Real less than.
    RealLt(Expr, Expr),

    /// Real less than or equal.
    RealLe(Expr, Expr),

    /// Real greater than.
    RealGt(Expr, Expr),

    /// Real greater than or equal.
    RealGe(Expr, Expr),

    // ===== Array Operations =====
    /// Array select (read): (select arr idx).
    Select { array: Expr, index: Expr },

    /// Array store (write): (store arr idx val).
    Store {
        array: Expr,
        index: Expr,
        value: Expr,
    },

    /// Constant array: ((as const (Array K V)) val).
    ConstArray { index_sort: Sort, value: Expr },

    // ===== Datatype Operations =====
    /// Datatype constructor application.
    DatatypeConstructor {
        datatype_name: String,
        constructor_name: String,
        args: Vec<Expr>,
    },

    /// Datatype field access (selector).
    DatatypeSelector {
        datatype_name: String,
        selector_name: String,
        expr: Expr,
    },

    /// Test if expression matches constructor.
    DatatypeTester {
        datatype_name: String,
        constructor_name: String,
        expr: Expr,
    },

    // ===== Floating-Point Operations =====
    // IEEE 754 operations per SMT-LIB2 FloatingPoint theory.
    /// FP positive infinity: (_ +oo eb sb).
    FpPlusInfinity { eb: u32, sb: u32 },

    /// FP negative infinity: (_ -oo eb sb).
    FpMinusInfinity { eb: u32, sb: u32 },

    /// FP NaN: (_ NaN eb sb).
    FpNaN { eb: u32, sb: u32 },

    /// FP positive zero: (_ +zero eb sb).
    FpPlusZero { eb: u32, sb: u32 },

    /// FP negative zero: (_ -zero eb sb).
    FpMinusZero { eb: u32, sb: u32 },

    /// FP absolute value: (fp.abs x).
    FpAbs(Expr),

    /// FP negation: (fp.neg x).
    FpNeg(Expr),

    /// FP addition: (fp.add rm x y).
    FpAdd(RoundingMode, Expr, Expr),

    /// FP subtraction: (fp.sub rm x y).
    FpSub(RoundingMode, Expr, Expr),

    /// FP multiplication: (fp.mul rm x y).
    FpMul(RoundingMode, Expr, Expr),

    /// FP division: (fp.div rm x y).
    FpDiv(RoundingMode, Expr, Expr),

    /// FP fused multiply-add: (fp.fma rm x y z).
    FpFma(RoundingMode, Expr, Expr, Expr),

    /// FP square root: (fp.sqrt rm x).
    FpSqrt(RoundingMode, Expr),

    /// FP remainder: (fp.rem x y).
    FpRem(Expr, Expr),

    /// FP round to integral: (fp.roundToIntegral rm x).
    FpRoundToIntegral(RoundingMode, Expr),

    /// FP minimum: (fp.min x y).
    FpMin(Expr, Expr),

    /// FP maximum: (fp.max x y).
    FpMax(Expr, Expr),

    /// FP equality: (fp.eq x y).
    FpEq(Expr, Expr),

    /// FP less than: (fp.lt x y).
    FpLt(Expr, Expr),

    /// FP less than or equal: (fp.leq x y).
    FpLe(Expr, Expr),

    /// FP greater than: (fp.gt x y).
    FpGt(Expr, Expr),

    /// FP greater than or equal: (fp.geq x y).
    FpGe(Expr, Expr),

    /// FP isNaN: (fp.isNaN x).
    FpIsNaN(Expr),

    /// FP isInfinite: (fp.isInfinite x).
    FpIsInfinite(Expr),

    /// FP isZero: (fp.isZero x).
    FpIsZero(Expr),

    /// FP isNormal: (fp.isNormal x).
    FpIsNormal(Expr),

    /// FP isSubnormal: (fp.isSubnormal x).
    FpIsSubnormal(Expr),

    /// FP isPositive: (fp.isPositive x).
    FpIsPositive(Expr),

    /// FP isNegative: (fp.isNegative x).
    FpIsNegative(Expr),

    /// Convert FP to signed bitvector: ((_ fp.to_sbv w) rm x).
    FpToSbv(RoundingMode, Expr, u32),

    /// Convert FP to unsigned bitvector: ((_ fp.to_ubv w) rm x).
    FpToUbv(RoundingMode, Expr, u32),

    /// Convert FP to real: (fp.to_real x).
    FpToReal(Expr),

    /// Construct FP from sign, exponent, significand bitvectors: (fp sign exp sig).
    FpFromBvs(Expr, Expr, Expr),

    /// Convert bitvector to floating-point (interpret as IEEE 754): ((_ to_fp eb sb) rm bv).
    BvToFp(RoundingMode, Expr, u32, u32),

    /// Convert unsigned bitvector to floating-point: ((_ to_fp_unsigned eb sb) rm bv).
    BvToFpUnsigned(RoundingMode, Expr, u32, u32),

    /// Convert floating-point to different precision: ((_ to_fp eb sb) rm fp).
    FpToFp(RoundingMode, Expr, u32, u32),

    /// Convert FP to IEEE 754 bitvector (bit-pattern reinterpretation): (fp.to_ieee_bv x).
    FpToIeeeBv(Expr),

    // ===== Quantifiers =====
    /// Universal quantifier: (forall ((x T)) body).
    /// Optional triggers (`:pattern` annotations) guide E-matching instantiation.
    Forall {
        vars: Vec<(String, Sort)>,
        body: Expr,
        triggers: Vec<Vec<Expr>>,
    },

    /// Existential quantifier: (exists ((x T)) body).
    /// Optional triggers (`:pattern` annotations) guide E-matching instantiation.
    Exists {
        vars: Vec<(String, Sort)>,
        body: Expr,
        triggers: Vec<Vec<Expr>>,
    },

    // ===== Sort Conversions =====
    /// Convert bitvector to integer (bv2int).
    /// The result is an unbounded integer with the unsigned value of the bitvector.
    Bv2Int(Expr),

    /// Convert integer to bitvector ((_ int2bv w)).
    /// The first field is the integer expression, the second is the target width.
    /// The result is a bitvector of the given width with value (i mod 2^w).
    Int2Bv(Expr, u32),

    // ===== String Operations =====
    /// String concatenation (str.++ s1 s2).
    StrConcat(Expr, Expr),
    /// String length (str.len s), returns Int.
    StrLen(Expr),
    /// Character at index (str.at s i), returns String.
    StrAt(Expr, Expr),
    /// Substring extraction (str.substr s offset len), returns String.
    StrSubstr(Expr, Expr, Expr),
    /// String containment test (str.contains s t), returns Bool.
    StrContains(Expr, Expr),
    /// String prefix test (str.prefixof pre s), returns Bool.
    StrPrefixOf(Expr, Expr),
    /// String suffix test (str.suffixof suf s), returns Bool.
    StrSuffixOf(Expr, Expr),
    /// String index-of (str.indexof s t i), returns Int.
    StrIndexOf(Expr, Expr, Expr),
    /// String replace first occurrence (str.replace s from to), returns String.
    StrReplace(Expr, Expr, Expr),
    /// String replace all occurrences (str.replace_all s from to), returns String.
    StrReplaceAll(Expr, Expr, Expr),
    /// String to integer conversion (str.to_int s), returns Int.
    StrToInt(Expr),
    /// Integer to string conversion (str.from_int i), returns String.
    StrFromInt(Expr),
    /// String to regex conversion (str.to_re s), returns RegLan.
    StrToRe(Expr),
    /// Regex membership test (str.in_re s re), returns Bool.
    StrInRe(Expr, Expr),

    // ===== Regex Operations =====
    /// Regex Kleene star (re.* re).
    ReStar(Expr),
    /// Regex Kleene plus (re.+ re).
    RePlus(Expr),
    /// Regex union (re.union re1 re2).
    ReUnion(Expr, Expr),
    /// Regex concatenation (re.++ re1 re2).
    ReConcat(Expr, Expr),

    // ===== Sequence Operations =====
    /// Empty sequence (as seq.empty (Seq T)).
    SeqEmpty(Sort),
    /// Unit sequence (seq.unit elem).
    SeqUnit(Expr),
    /// Sequence concatenation (seq.++ s t).
    SeqConcat(Expr, Expr),
    /// Sequence length (seq.len s), returns Int.
    SeqLen(Expr),
    /// Element at index (seq.nth s i), returns element sort.
    SeqNth(Expr, Expr),
    /// Subsequence extraction (seq.extract s offset len).
    SeqExtract(Expr, Expr, Expr),
    /// Sequence containment test (seq.contains s t), returns Bool.
    SeqContains(Expr, Expr),
    /// Sequence prefix test (seq.prefixof pre s), returns Bool.
    SeqPrefixOf(Expr, Expr),
    /// Sequence suffix test (seq.suffixof suf s), returns Bool.
    SeqSuffixOf(Expr, Expr),
    /// Sequence index-of (seq.indexof s t i), returns Int.
    SeqIndexOf(Expr, Expr, Expr),
    /// Sequence replace first occurrence (seq.replace s from to).
    SeqReplace(Expr, Expr, Expr),

    /// Uninterpreted function application: (func arg1 arg2 ...).
    ///
    /// Used for CHC relation applications and uninterpreted functions.
    FuncApp { name: String, args: Vec<Expr> },
}
