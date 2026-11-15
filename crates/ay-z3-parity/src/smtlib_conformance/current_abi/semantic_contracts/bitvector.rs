// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Selected finite bit-vector ABI semantics for the pinned Z3 5.3.3 headers.
//! Small-domain arithmetic expectations are computed in bounded C integers,
//! independently from Z3 simplification. Each family also rejects a symbolic
//! counterexample through the solver API. These are not all-width proofs.
//! The pinned rewriter's default hi_div0=true defines the tested zero-divisor
//! branches; no alternative parameter mode or arbitrary argument domain is
//! qualified. Invalid widths/sorts, wider arithmetic, rotations, overflow
//! beyond these finite domains, memory/lifetime stress and other unlisted
//! state sequences remain open.

use super::{Aspect, Claim, Family};

pub(super) const FAMILIES: &[Family] = &[
    Family {
        id: "contract-bitvector-constructors",
        source: concat!(
            include_str!("../contracts/common.h"),
            include_str!("../contracts/bitvector_helpers.h"),
            include_str!("../contracts/bitvector_constructors.c")
        ),
        checks: &[
            "bitvector.constructors.context-created",
            "bitvector.constructors.sort-widths",
            "bitvector.constructors.all-four-bit-numerals",
            "bitvector.constructors.all-four-bit-extracts",
            "bitvector.constructors.all-four-bit-extensions",
            "bitvector.constructors.all-four-bit-repetitions",
            "bitvector.constructors.all-three-bit-concatenations",
            "bitvector.constructors.symbolic-split-join",
        ],
    },
    Family {
        id: "contract-bitvector-arithmetic",
        source: concat!(
            include_str!("../contracts/common.h"),
            include_str!("../contracts/bitvector_helpers.h"),
            include_str!("../contracts/bitvector_arithmetic.c")
        ),
        checks: &[
            "bitvector.arithmetic.context-created",
            "bitvector.arithmetic.sort-created",
            "bitvector.arithmetic.all-three-bit-unary",
            "bitvector.arithmetic.all-three-bit-modular",
            "bitvector.arithmetic.all-three-bit-bitwise",
            "bitvector.arithmetic.all-three-bit-unsigned-order",
            "bitvector.arithmetic.all-three-bit-signed-order",
            "bitvector.arithmetic.symbolic-modular-inverse",
        ],
    },
    Family {
        id: "contract-bitvector-division",
        source: concat!(
            include_str!("../contracts/common.h"),
            include_str!("../contracts/bitvector_helpers.h"),
            include_str!("../contracts/bitvector_division.c")
        ),
        checks: &[
            "bitvector.division.context-created",
            "bitvector.division.sort-created",
            "bitvector.division.all-three-bit-unsigned-including-zero",
            "bitvector.division.all-three-bit-signed-including-zero",
            "bitvector.division.all-three-bit-signed-modulo",
            "bitvector.division.all-three-bit-shifts-including-oversized",
            "bitvector.division.all-three-bit-reconstruction",
            "bitvector.division.signed-minimum-over-minus-one",
            "bitvector.division.symbolic-reconstruction-including-zero",
        ],
    },
    Family {
        id: "contract-bitvector-overflow",
        source: concat!(
            include_str!("../contracts/common.h"),
            include_str!("../contracts/bitvector_helpers.h"),
            include_str!("../contracts/bitvector_overflow.c")
        ),
        checks: &[
            "bitvector.overflow.context-created",
            "bitvector.overflow.sorts-created",
            "bitvector.overflow.all-three-bit-unsigned-add",
            "bitvector.overflow.all-three-bit-signed-add",
            "bitvector.overflow.all-three-bit-subtraction",
            "bitvector.overflow.all-three-bit-multiplication",
            "bitvector.overflow.all-three-bit-negation-and-division",
            "bitvector.overflow.all-three-bit-signed-unsigned-conversion",
            "bitvector.overflow.integer-to-bv-modular-reduction",
            "bitvector.overflow.numeral-conversion-boundaries",
            "bitvector.overflow.exact-large-decimal",
            "bitvector.overflow.exact-large-binary",
            "bitvector.overflow.symbolic-carry-equivalence",
        ],
    },
];

pub(super) const CLAIMS: &[Claim] = &[
    Claim { family: "contract-bitvector-constructors", check: "bitvector.constructors.sort-widths", aspect: Aspect::Output, functions: &["Z3_mk_bv_sort", "Z3_get_bv_sort_size", "Z3_get_sort_kind"], statement: "Three-, four-, and six-bit sorts report their declared bit-vector kind and width." },
    Claim { family: "contract-bitvector-constructors", check: "bitvector.constructors.all-four-bit-numerals", aspect: Aspect::Output, functions: &["Z3_mk_unsigned_int64", "Z3_mk_bv_numeral", "Z3_mk_numeral", "Z3_get_numeral_uint64", "Z3_simplify"], statement: "Every four-bit value 0 through 15 is reconstructed from little-endian Boolean bits and decimal text, equals the unsigned numeral, and differs from its low-bit-flipped value." },
    Claim { family: "contract-bitvector-constructors", check: "bitvector.constructors.all-four-bit-extracts", aspect: Aspect::Output, functions: &["Z3_mk_extract"], statement: "For all sixteen four-bit numerals, extract(3,1) equals unsigned division by two and extract(0,0) equals the low bit." },
    Claim { family: "contract-bitvector-constructors", check: "bitvector.constructors.all-four-bit-extensions", aspect: Aspect::Output, functions: &["Z3_mk_zero_ext", "Z3_mk_sign_ext"], statement: "For all sixteen four-bit numerals, zero extension to eight bits preserves the unsigned value and sign extension preserves the two-complement signed value." },
    Claim { family: "contract-bitvector-constructors", check: "bitvector.constructors.all-four-bit-repetitions", aspect: Aspect::Output, functions: &["Z3_mk_repeat"], statement: "Repeating each four-bit numeral twice produces the eight-bit value 17 times the original." },
    Claim { family: "contract-bitvector-constructors", check: "bitvector.constructors.all-three-bit-concatenations", aspect: Aspect::Output, functions: &["Z3_mk_concat"], statement: "All 64 ordered pairs of three-bit numerals concatenate with the first operand as the high bits, yielding 8*a+b." },
    Claim { family: "contract-bitvector-constructors", check: "bitvector.constructors.symbolic-split-join", aspect: Aspect::State, functions: &["Z3_mk_extract", "Z3_mk_concat", "Z3_mk_const", "Z3_solver_assert", "Z3_solver_check"], statement: "A solver rejects inequality between a six-bit symbolic value and the concatenation of its high and low three-bit slices." },
    Claim { family: "contract-bitvector-arithmetic", check: "bitvector.arithmetic.all-three-bit-unary", aspect: Aspect::Output, functions: &["Z3_mk_bvnot", "Z3_mk_bvneg", "Z3_mk_bvredand", "Z3_mk_bvredor"], statement: "All eight three-bit values match independent bitwise complement, modular negation, all-ones reduction and nonzero reduction expectations." },
    Claim { family: "contract-bitvector-arithmetic", check: "bitvector.arithmetic.all-three-bit-modular", aspect: Aspect::Output, functions: &["Z3_mk_bvadd", "Z3_mk_bvsub", "Z3_mk_bvmul"], statement: "Addition, subtraction and multiplication over all 64 three-bit pairs equal the independently computed unsigned results modulo eight." },
    Claim { family: "contract-bitvector-arithmetic", check: "bitvector.arithmetic.all-three-bit-bitwise", aspect: Aspect::Output, functions: &["Z3_mk_bvand", "Z3_mk_bvor", "Z3_mk_bvxor", "Z3_mk_bvnand", "Z3_mk_bvnor", "Z3_mk_bvxnor"], statement: "All 64 pairs match independent AND, OR, XOR and their three-bit complements." },
    Claim { family: "contract-bitvector-arithmetic", check: "bitvector.arithmetic.all-three-bit-unsigned-order", aspect: Aspect::Output, functions: &["Z3_mk_bvult", "Z3_mk_bvule", "Z3_mk_bvugt", "Z3_mk_bvuge"], statement: "All four unsigned comparisons match the ordinary order of integers 0 through 7 over all 64 pairs." },
    Claim { family: "contract-bitvector-arithmetic", check: "bitvector.arithmetic.all-three-bit-signed-order", aspect: Aspect::Output, functions: &["Z3_mk_bvslt", "Z3_mk_bvsle", "Z3_mk_bvsgt", "Z3_mk_bvsge"], statement: "All four signed comparisons match independent two-complement integer decoding into -4 through 3 over all 64 pairs." },
    Claim { family: "contract-bitvector-arithmetic", check: "bitvector.arithmetic.symbolic-modular-inverse", aspect: Aspect::State, functions: &["Z3_mk_bvadd", "Z3_mk_bvsub", "Z3_solver_check"], statement: "A solver rejects a three-bit symbolic counterexample to (x+y)-y=x under modular arithmetic." },
    Claim { family: "contract-bitvector-division", check: "bitvector.division.all-three-bit-unsigned-including-zero", aspect: Aspect::Output, functions: &["Z3_mk_bvudiv", "Z3_mk_bvurem"], statement: "All 64 pairs match unsigned quotient/remainder; zero divisors yield quotient seven and remainder equal to the dividend under the pinned default SMT semantics." },
    Claim { family: "contract-bitvector-division", check: "bitvector.division.all-three-bit-signed-including-zero", aspect: Aspect::Output, functions: &["Z3_mk_bvsdiv", "Z3_mk_bvsrem"], statement: "All 64 pairs match signed division truncated toward zero and dividend-signed remainder; division by zero yields one for negative dividends and all ones otherwise, with the original dividend as remainder." },
    Claim { family: "contract-bitvector-division", check: "bitvector.division.all-three-bit-signed-modulo", aspect: Aspect::Output, functions: &["Z3_mk_bvsmod"], statement: "All 64 pairs match divisor-signed modulo computed from signed remainder; zero divisors preserve the dividend." },
    Claim { family: "contract-bitvector-division", check: "bitvector.division.all-three-bit-shifts-including-oversized", aspect: Aspect::Output, functions: &["Z3_mk_bvshl", "Z3_mk_bvlshr", "Z3_mk_bvashr"], statement: "All 64 value/count pairs, including shifts of three through seven, match explicit logical zero-fill and arithmetic sign-fill expectations without undefined C shifts." },
    Claim { family: "contract-bitvector-division", check: "bitvector.division.all-three-bit-reconstruction", aspect: Aspect::Output, functions: &["Z3_mk_bvudiv", "Z3_mk_bvurem", "Z3_mk_bvmul", "Z3_mk_bvadd"], statement: "For all 64 pairs including zero divisors, unsigned quotient times divisor plus remainder reconstructs the dividend modulo eight." },
    Claim { family: "contract-bitvector-division", check: "bitvector.division.signed-minimum-over-minus-one", aspect: Aspect::Output, functions: &["Z3_mk_bvsdiv", "Z3_mk_bvsrem", "Z3_mk_bvsmod"], statement: "Dividing signed minimum -4 by -1 wraps the quotient to three-bit -4 and both remainder variants are zero." },
    Claim { family: "contract-bitvector-division", check: "bitvector.division.symbolic-reconstruction-including-zero", aspect: Aspect::State, functions: &["Z3_mk_bvudiv", "Z3_mk_bvurem", "Z3_mk_bvmul", "Z3_mk_bvadd", "Z3_solver_check"], statement: "A solver rejects a three-bit symbolic counterexample to unsigned quotient/remainder reconstruction, without excluding zero divisors." },
    Claim { family: "contract-bitvector-overflow", check: "bitvector.overflow.all-three-bit-unsigned-add", aspect: Aspect::Output, functions: &["Z3_mk_bvadd_no_overflow"], statement: "For all 64 pairs the unsigned-add predicate is true exactly when the ordinary sum is at most seven." },
    Claim { family: "contract-bitvector-overflow", check: "bitvector.overflow.all-three-bit-signed-add", aspect: Aspect::Output, functions: &["Z3_mk_bvadd_no_overflow", "Z3_mk_bvadd_no_underflow"], statement: "For all 64 pairs signed-add overflow and underflow predicates separately match upper bound three and lower bound minus four." },
    Claim { family: "contract-bitvector-overflow", check: "bitvector.overflow.all-three-bit-subtraction", aspect: Aspect::Output, functions: &["Z3_mk_bvsub_no_overflow", "Z3_mk_bvsub_no_underflow"], statement: "All 64 pairs match independent signed subtraction upper/lower bounds and unsigned subtraction non-underflow." },
    Claim { family: "contract-bitvector-overflow", check: "bitvector.overflow.all-three-bit-multiplication", aspect: Aspect::Output, functions: &["Z3_mk_bvmul_no_overflow", "Z3_mk_bvmul_no_underflow"], statement: "All 64 pairs match independent unsigned product upper bound seven and signed product upper/lower bounds three and minus four." },
    Claim { family: "contract-bitvector-overflow", check: "bitvector.overflow.all-three-bit-negation-and-division", aspect: Aspect::Output, functions: &["Z3_mk_bvneg_no_overflow", "Z3_mk_bvsdiv_no_overflow"], statement: "Negation is non-overflowing except at signed minimum, and signed division is non-overflowing except signed minimum divided by minus one; zero-divisor inputs are included." },
    Claim { family: "contract-bitvector-overflow", check: "bitvector.overflow.all-three-bit-signed-unsigned-conversion", aspect: Aspect::Output, functions: &["Z3_mk_bv2int", "Z3_get_numeral_int64"], statement: "Every three-bit numeral converts to the independently decoded unsigned and two-complement signed integer values." },
    Claim { family: "contract-bitvector-overflow", check: "bitvector.overflow.integer-to-bv-modular-reduction", aspect: Aspect::Output, functions: &["Z3_mk_int2bv", "Z3_mk_int"], statement: "Every integer from -17 through 17 converts to its three-bit residue modulo eight." },
    Claim { family: "contract-bitvector-overflow", check: "bitvector.overflow.numeral-conversion-boundaries", aspect: Aspect::Errors, functions: &["Z3_get_numeral_uint64", "Z3_get_numeral_int64", "Z3_get_error_code"], statement: "The unsigned 64-bit maximum is retrieved exactly, fails signed-64 retrieval, and the 65-bit value 2^64 fails unsigned-64 retrieval without an API error." },
    Claim { family: "contract-bitvector-overflow", check: "bitvector.overflow.exact-large-decimal", aspect: Aspect::Output, functions: &["Z3_get_numeral_string"], statement: "The 65-bit numeral 2^64 preserves its exact decimal string, without truncation through a native integer." },
    Claim { family: "contract-bitvector-overflow", check: "bitvector.overflow.exact-large-binary", aspect: Aspect::Output, functions: &["Z3_get_numeral_binary_string"], statement: "The 65-bit numeral 2^64 preserves its exact 65-character binary string." },
    Claim { family: "contract-bitvector-overflow", check: "bitvector.overflow.symbolic-carry-equivalence", aspect: Aspect::State, functions: &["Z3_mk_bvadd_no_overflow", "Z3_mk_zero_ext", "Z3_mk_extract", "Z3_solver_check"], statement: "A solver rejects a three-bit symbolic disagreement between unsigned-add non-overflow and a zero carry bit in the four-bit extended sum." },
];
