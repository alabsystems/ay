// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Finite floating-point witnesses against pinned Z3 5.3.3 `z3_fpa.h`.
//! IEEE equality differs from SMT equality for NaN and signed zeros. FP(3,3)
//! has precision three, maximum finite 14, and minimum subnormal 1/16; these
//! exact bounds give independent halfway and overflow cases. A separate
//! binary32 identity witnesses fused rounding with a normal exact residual.
//! No expectation depends on host floating-point rounding or a NaN payload.

use super::{Aspect, Claim, Family};

pub(super) const REMAINING_SCOPE: &str = "Floating-point checks cover only the named binary32 special values, selected FP(3,3) arithmetic and rounding boundaries, exact in-range conversions, and two retained binary32 models. Arbitrary widths, all representable values, invalid arguments, unspecified NaN signs/payloads or out-of-range conversions, floating-point min/max signed-zero choices, alternate solver settings, proof validity, cross-context translation, concurrency, resource exhaustion and every unlisted argument or state domain remain unqualified.";

pub(super) const FAMILIES: &[Family] = &[
    Family {
        id: "contract-float-specials",
        source: concat!(
            include_str!("../contracts/common.h"),
            include_str!("../contracts/float_helpers.h"),
            include_str!("../contracts/float_specials.c")
        ),
        checks: &[
            "float.specials.context-created",
            "float.specials.sort-reflection",
            "float.specials.values-created",
            "float.specials.signed-zero-bits",
            "float.specials.signed-zero-equality",
            "float.specials.zero-classification",
            "float.specials.infinity-order",
            "float.specials.nan-equality",
            "float.specials.nan-unordered",
            "float.specials.normal-subnormal-boundary",
            "float.specials.negation-absolute-value",
        ],
    },
    Family {
        id: "contract-float-rounding",
        source: concat!(
            include_str!("../contracts/common.h"),
            include_str!("../contracts/float_helpers.h"),
            include_str!("../contracts/float_rounding.c")
        ),
        checks: &[
            "float.rounding.context-created",
            "float.rounding.five-distinct-modes",
            "float.rounding.positive-halfway",
            "float.rounding.negative-halfway",
            "float.rounding.exact-arithmetic",
            "float.rounding.fused-sort-created",
            "float.rounding.fused-operands-created",
            "float.rounding.fused-versus-separate",
            "float.rounding.cancellation-zero-sign",
            "float.rounding.overflow-direction",
            "float.rounding.underflow-halfway",
            "float.rounding.integral-ties-and-directions",
        ],
    },
    Family {
        id: "contract-float-conversions",
        source: concat!(
            include_str!("../contracts/common.h"),
            include_str!("../contracts/float_helpers.h"),
            include_str!("../contracts/float_conversions.c")
        ),
        checks: &[
            "float.conversions.context-created",
            "float.conversions.sorts-and-modes",
            "float.conversions.ieee-reinterpretation",
            "float.conversions.exact-real-roundtrip",
            "float.conversions.narrowing-halfway",
            "float.conversions.signed-unsigned-bv",
            "float.conversions.rounded-integer-directions",
            "float.conversions.in-range-integer-boundaries",
            "float.conversions.solver-created",
            "float.conversions.nan-model-satisfiable",
            "float.conversions.model-distinguishes-equalities",
            "float.conversions.nan-self-equality-unsatisfiable",
            "float.conversions.signed-zero-model-satisfiable",
            "float.conversions.independent-retained-models",
            "float.conversions.retained-after-solver-release",
        ],
    },
];

pub(super) const CLAIMS: &[Claim] = &[
    Claim { family: "contract-float-specials", check: "float.specials.sort-reflection", aspect: Aspect::Output, functions: &["Z3_mk_fpa_sort", "Z3_mk_fpa_sort_single", "Z3_mk_fpa_sort_double", "Z3_mk_fpa_rounding_mode_sort", "Z3_fpa_get_ebits", "Z3_fpa_get_sbits", "Z3_get_sort_kind", "Z3_is_eq_sort"], statement: "The single alias equals FP(8,24), differs from double FP(11,53), and both formats and the rounding-mode sort report their exact kinds and dimensions." },
    Claim { family: "contract-float-specials", check: "float.specials.values-created", aspect: Aspect::Output, functions: &["Z3_mk_fpa_zero", "Z3_mk_fpa_inf", "Z3_mk_fpa_nan", "Z3_mk_fpa_numeral_double", "Z3_get_sort"], statement: "Signed binary32 zeros, infinities, NaN and exact one are constructed, and the NaN has the requested FP sort." },
    Claim { family: "contract-float-specials", check: "float.specials.signed-zero-bits", aspect: Aspect::Output, functions: &["Z3_mk_fpa_zero", "Z3_mk_fpa_to_ieee_bv", "Z3_get_numeral_uint64", "Z3_simplify"], statement: "Positive and negative binary32 zero have exact interchange encodings 0 and 0x80000000; no NaN encoding is requested." },
    Claim { family: "contract-float-specials", check: "float.specials.signed-zero-equality", aspect: Aspect::Output, functions: &["Z3_mk_fpa_eq", "Z3_mk_eq", "Z3_get_bool_value"], statement: "The two signed zeros are equal under IEEE equality and unequal under SMT equality." },
    Claim { family: "contract-float-specials", check: "float.specials.zero-classification", aspect: Aspect::Output, functions: &["Z3_fpa_is_numeral", "Z3_fpa_is_numeral_zero", "Z3_fpa_is_numeral_positive", "Z3_fpa_is_numeral_negative", "Z3_mk_fpa_is_zero", "Z3_mk_fpa_is_negative", "Z3_mk_fpa_is_positive"], statement: "Both signed zeros classify as zero, with their corresponding sign; negative zero satisfies isNegative and fails isPositive." },
    Claim { family: "contract-float-specials", check: "float.specials.infinity-order", aspect: Aspect::Output, functions: &["Z3_fpa_is_numeral_inf", "Z3_mk_fpa_is_infinite", "Z3_mk_fpa_lt", "Z3_mk_fpa_gt", "Z3_mk_fpa_to_ieee_bv"], statement: "The two infinities have the expected binary32 encodings, classify as infinite, and lie below and above finite one respectively." },
    Claim { family: "contract-float-specials", check: "float.specials.nan-equality", aspect: Aspect::Output, functions: &["Z3_fpa_is_numeral_nan", "Z3_mk_fpa_is_nan", "Z3_mk_fpa_eq", "Z3_mk_eq"], statement: "A constructed NaN classifies as NaN, is IEEE-unequal to itself and SMT-equal to itself, without assumptions about its sign or payload." },
    Claim { family: "contract-float-specials", check: "float.specials.nan-unordered", aspect: Aspect::Output, functions: &["Z3_mk_fpa_lt", "Z3_mk_fpa_leq", "Z3_mk_fpa_geq", "Z3_mk_fpa_gt"], statement: "All four ordered comparisons of NaN with one evaluate to false." },
    Claim { family: "contract-float-specials", check: "float.specials.normal-subnormal-boundary", aspect: Aspect::Output, functions: &["Z3_mk_fpa_numeral_double", "Z3_mk_fpa_numeral_float", "Z3_fpa_is_numeral_normal", "Z3_fpa_is_numeral_subnormal", "Z3_mk_fpa_is_normal", "Z3_mk_fpa_is_subnormal"], statement: "Exact 2^-126 through the double constructor and 2^-149 through the matching single constructor classify as binary32 normal and subnormal respectively, reject the opposite classification, and have encodings 0x00800000 and 1." },
    Claim { family: "contract-float-specials", check: "float.specials.negation-absolute-value", aspect: Aspect::Output, functions: &["Z3_mk_fpa_neg", "Z3_mk_fpa_abs"], statement: "Negating positive zero preserves the negative-zero sign, absolute value clears that sign, and negating positive infinity yields negative infinity." },
    Claim { family: "contract-float-rounding", check: "float.rounding.five-distinct-modes", aspect: Aspect::Output, functions: &["Z3_mk_fpa_rne", "Z3_mk_fpa_rna", "Z3_mk_fpa_rtp", "Z3_mk_fpa_rtn", "Z3_mk_fpa_rtz", "Z3_is_eq_ast", "Z3_get_sort"], statement: "The five rounding-mode constructors return distinct retained ASTs of the rounding-mode sort." },
    Claim { family: "contract-float-rounding", check: "float.rounding.positive-halfway", aspect: Aspect::Output, functions: &["Z3_mk_fpa_add", "Z3_mk_fpa_rne", "Z3_mk_fpa_rna", "Z3_mk_fpa_rtp", "Z3_mk_fpa_rtn", "Z3_mk_fpa_rtz"], statement: "In FP(3,3), adding 1 and 1/8 yields 1, 5/4, 5/4, 1 and 1 under RNE, RNA, RTP, RTN and RTZ respectively." },
    Claim { family: "contract-float-rounding", check: "float.rounding.negative-halfway", aspect: Aspect::Output, functions: &["Z3_mk_fpa_add"], statement: "Adding -1 and -1/8 yields -1, -5/4, -1, -5/4 and -1 under the same ordered five rounding modes." },
    Claim { family: "contract-float-rounding", check: "float.rounding.exact-arithmetic", aspect: Aspect::Output, functions: &["Z3_mk_fpa_sub", "Z3_mk_fpa_mul", "Z3_mk_fpa_div", "Z3_mk_fpa_sqrt"], statement: "RNE arithmetic gives exact 3-1=2, 2*3=6, 3/2=1.5 and sqrt(4)=2 in FP(3,3)." },
    Claim { family: "contract-float-rounding", check: "float.rounding.fused-versus-separate", aspect: Aspect::Output, functions: &["Z3_mk_fpa_fma", "Z3_mk_fpa_mul", "Z3_mk_fpa_add"], statement: "In binary32 with RNE and a=2^-23, fused (1+a)*(1-a)-1 yields exact normal -2^-46, while separately rounded multiplication and addition yield positive zero." },
    Claim { family: "contract-float-rounding", check: "float.rounding.cancellation-zero-sign", aspect: Aspect::Output, functions: &["Z3_mk_fpa_add", "Z3_mk_fpa_to_ieee_bv"], statement: "Exact 1+(-1) yields positive zero under RNE and negative zero under RTN, whose six-bit encoding is 32." },
    Claim { family: "contract-float-rounding", check: "float.rounding.overflow-direction", aspect: Aspect::Output, functions: &["Z3_mk_fpa_mul"], statement: "Multiplying FP(3,3) maximum finite 14 by 2 yields positive infinity under RNE and maximum finite 14 under RTZ." },
    Claim { family: "contract-float-rounding", check: "float.rounding.underflow-halfway", aspect: Aspect::Output, functions: &["Z3_mk_fpa_div"], statement: "Dividing minimum subnormal 1/16 by 2 rounds to positive zero under RNE and to 1/16 under RNA." },
    Claim { family: "contract-float-rounding", check: "float.rounding.integral-ties-and-directions", aspect: Aspect::Output, functions: &["Z3_mk_fpa_round_to_integral"], statement: "Rounding positive and negative 2.5 to integral FP values distinguishes ties-to-even, ties-away, the two directed modes and truncation toward zero." },
    Claim { family: "contract-float-conversions", check: "float.conversions.ieee-reinterpretation", aspect: Aspect::Output, functions: &["Z3_mk_fpa_to_fp_bv", "Z3_mk_fpa_to_ieee_bv"], statement: "Reinterpreting binary32 bit pattern 0x3fc00000 yields exact 1.5, which converts back to the same non-NaN bit pattern." },
    Claim { family: "contract-float-conversions", check: "float.conversions.exact-real-roundtrip", aspect: Aspect::Output, functions: &["Z3_mk_fpa_to_fp_real", "Z3_mk_fpa_to_real", "Z3_mk_numeral", "Z3_mk_real_sort"], statement: "Exact Real 3/2 converts to binary32 1.5 under RNE and that finite FP value converts back to Real 3/2." },
    Claim { family: "contract-float-conversions", check: "float.conversions.narrowing-halfway", aspect: Aspect::Output, functions: &["Z3_mk_fpa_to_fp_float", "Z3_mk_fpa_to_fp_real"], statement: "The exact binary64 midpoint 1+2^-24 narrows to binary32 1 under RNE and to its immediate successor under RTP." },
    Claim { family: "contract-float-conversions", check: "float.conversions.signed-unsigned-bv", aspect: Aspect::Output, functions: &["Z3_mk_fpa_to_fp_signed", "Z3_mk_fpa_to_fp_unsigned", "Z3_mk_unsigned_int", "Z3_mk_bv_sort"], statement: "The same eight-bit all-ones value converts to binary32 -1 as signed two's complement and to 255 as unsigned." },
    Claim { family: "contract-float-conversions", check: "float.conversions.rounded-integer-directions", aspect: Aspect::Output, functions: &["Z3_mk_fpa_to_sbv", "Z3_mk_fpa_to_ubv"], statement: "For in-range eight-bit results, -2.75 rounds to -2 under RTZ and -3 under RTN; +2.75 rounds to 2 under RTZ and 3 under RTP." },
    Claim { family: "contract-float-conversions", check: "float.conversions.in-range-integer-boundaries", aspect: Aspect::Output, functions: &["Z3_mk_fpa_to_sbv", "Z3_mk_fpa_to_ubv"], statement: "Exact binary32 -128 and 127 convert to the eight-bit signed endpoints and 255 converts to the eight-bit unsigned maximum; no unspecified out-of-range result is asserted." },
    Claim { family: "contract-float-conversions", check: "float.conversions.nan-model-satisfiable", aspect: Aspect::State, functions: &["Z3_mk_const", "Z3_mk_solver", "Z3_solver_inc_ref", "Z3_solver_assert", "Z3_solver_check"], statement: "A binary32 symbolic value constrained to satisfy isNaN has a satisfiable model." },
    Claim { family: "contract-float-conversions", check: "float.conversions.model-distinguishes-equalities", aspect: Aspect::Output, functions: &["Z3_solver_get_model", "Z3_model_inc_ref", "Z3_model_eval", "Z3_fpa_is_numeral_nan"], statement: "Without model completion, that model evaluates the symbolic value to NaN, IEEE self-equality to false and SMT self-equality to true." },
    Claim { family: "contract-float-conversions", check: "float.conversions.nan-self-equality-unsatisfiable", aspect: Aspect::State, functions: &["Z3_solver_push", "Z3_solver_assert", "Z3_solver_check", "Z3_mk_fpa_eq"], statement: "Adding IEEE self-equality contradicts isNaN, while the explicitly retained earlier model still evaluates its value to NaN." },
    Claim { family: "contract-float-conversions", check: "float.conversions.independent-retained-models", aspect: Aspect::Lifetime, functions: &["Z3_solver_reset", "Z3_solver_get_model", "Z3_model_eval"], statement: "After reset and solving the same value equal to negative zero, the new model preserves its zero sign and rejects isNaN, while the retained old model still yields NaN." },
    Claim { family: "contract-float-conversions", check: "float.conversions.retained-after-solver-release", aspect: Aspect::Lifetime, functions: &["Z3_inc_ref", "Z3_dec_ref", "Z3_get_ast_id", "Z3_model_inc_ref", "Z3_model_dec_ref", "Z3_solver_dec_ref"], statement: "Before context destruction, the retained symbolic AST keeps its identity and both retained NaN/negative-zero models remain independently evaluable after solver release." },
];
